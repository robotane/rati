package fr.univreunion.rati.rank;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;
import java.util.Map;

import fr.univreunion.rati.ranking.FarkasRanking;

/**
 * Standalone CLI for the in-house Farkas/ADFG termination prover. Reads an
 * Integer Transition System in the KoAT text format (see {@link KoatParser} /
 * {@link fr.univreunion.rati.its.KoatPrinter}) and prints a termination verdict
 * plus, on success, a ranking-function certificate.
 *
 * <p>It is the BCTerm-independent face of {@link FarkasRanking}: the ranking
 * engine ({@code ranking.*}) and the ITS model ({@code its.*}) carry no bytecode
 * or path-length coupling, so any front-end that emits KoAT can be ranked here
 * without the JVM-bytecode pipeline. Apron (JNI) is still required at runtime
 * (the invariant / loop-summary / disjunctive stages use it), so run with
 * {@code -Djava.library.path=<dir with libjapron.so>}.
 *
 * <pre>
 *   java -Djava.library.path=lib -jar rank.jar &lt;file.koat&gt; [--entry F] [--quiet]
 * </pre>
 *
 * <p>Exit code: {@code 0} TERMINATES, {@code 1} UNKNOWN, {@code 2} usage/IO error.
 */
public final class RankMain {

    private RankMain() {}

    public static void main(String[] args) {
        String file = null, entry = null;
        boolean quiet = false;
        for (int i = 0; i < args.length; i++) {
            String a = args[i];
            if (a.equals("--entry") && i + 1 < args.length) entry = args[++i];
            else if (a.equals("--quiet")) quiet = true;
            else if (a.startsWith("--")) { usage("unknown option: " + a); return; }
            else if (file == null) file = a;
            else { usage("unexpected argument: " + a); return; }
        }
        if (file == null) { usage("missing <file.koat>"); return; }

        String text;
        try {
            text = new String(Files.readAllBytes(Paths.get(file)), StandardCharsets.UTF_8);
        } catch (IOException e) {
            System.err.println("error: cannot read " + file + ": " + e.getMessage());
            System.exit(2);
            return;
        }

        KoatParser.Parsed parsed = KoatParser.parse(text);
        String start = entry != null ? entry : parsed.start;
        if (start == null) {
            System.err.println("error: no start functor (no (STARTTERM …) and no --entry given)");
            System.exit(2);
            return;
        }
        if (parsed.its.location(start) == null) {
            System.err.println("error: start functor '" + start + "' is not a location in the ITS");
            System.exit(2);
            return;
        }

        FarkasRanking.Certificate cert;
        try {
            cert = FarkasRanking.proveWithCertificate(parsed.its, start);
        } catch (UnsatisfiedLinkError | NoClassDefFoundError e) {
            // Apron's native library could not be loaded — a configuration error, not
            // an analysis outcome. RuntimeException's catch would miss it (it is an
            // Error), leaving a raw stack trace and an exit code outside {0,1,2}. Give
            // the actionable hint instead and exit with the usage/setup code (2).
            System.err.println("error: Apron native library not loaded (" + e
                    + ").\n  Run with -Djava.library.path=<dir with libjapron.so> "
                    + "and LD_LIBRARY_PATH set to the same directory.");
            System.exit(2);
            return;
        } catch (RuntimeException e) {
            // A prover bug must not masquerade as a clean MAYBE: report UNKNOWN
            // (sound) but surface the cause on stderr so it is visible.
            System.err.println("[rati] internal error: " + e);
            System.out.println("UNKNOWN");
            System.exit(1);
            return;
        }

        if (cert.verdict == FarkasRanking.Verdict.TERMINATES) {
            System.out.println("TERMINATES");
            if (!quiet) printCertificate(cert);
            System.exit(0);
        } else {
            System.out.println("UNKNOWN");
            System.exit(1);
        }
    }

    private static void printCertificate(FarkasRanking.Certificate cert) {
        if (cert.sccs.isEmpty()) {
            System.out.println("certificate: no non-trivial SCC (acyclic — trivially terminating)");
            return;
        }
        System.out.println("certificate:");
        for (FarkasRanking.SccProof scc : cert.sccs) {
            System.out.println("  SCC " + scc.locations + ": " + scc.method);
            for (int r = 0; r < scc.rounds.size(); r++) {
                System.out.println("    lexicographic component " + (r + 1) + ":");
                for (Map.Entry<String, String> e : scc.rounds.get(r).entrySet()) {
                    System.out.println("      rho(" + e.getKey() + ") = " + e.getValue());
                }
            }
            if (scc.rounds.isEmpty()) {
                System.out.println("    (certificate: see technique above; coefficients not surfaced for this stage)");
            }
        }
    }

    private static void usage(String err) {
        if (err != null) System.err.println("error: " + err);
        System.err.println("usage: rank <file.koat> [--entry <functor>] [--quiet]");
        System.err.println("  reads a KoAT-format ITS, prints TERMINATES (+ ranking certificate) or UNKNOWN");
        System.err.println("  run with -Djava.library.path=<dir with libjapron.so> (Apron JNI)");
        System.exit(2);
    }
}
