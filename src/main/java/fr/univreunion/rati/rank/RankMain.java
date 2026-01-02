package fr.univreunion.rati.rank;

import java.io.IOException;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;
import java.util.Map;

import fr.univreunion.rati.its.ItsTransition;
import fr.univreunion.rati.ranking.FarkasRanking;
import fr.univreunion.rati.ranking.NonTermination;

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
 * <p>Exit code: {@code 0} TERMINATES, {@code 1} UNKNOWN, {@code 2} usage/IO error,
 * {@code 3} NONTERMINATES (with a recurrent-set witness).
 */
public final class RankMain {

    private RankMain() {}

    public static void main(String[] args) {
        String file = null, entry = null, cpfOut = null;
        boolean quiet = false;
        for (int i = 0; i < args.length; i++) {
            String a = args[i];
            if (a.equals("--entry") && i + 1 < args.length) entry = args[++i];
            else if (a.equals("--quiet")) quiet = true;
            else if (a.equals("--cpf") && i + 1 < args.length) cpfOut = args[++i];
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

        KoatParser.Parsed parsed;
        try {
            parsed = KoatParser.parse(text);
        } catch (RuntimeException e) {
            // A malformed input is a usage error (exit 2), not an analysis outcome:
            // an uncaught parse exception would leak a stack trace and exit with the
            // JVM's default 1 — indistinguishable from UNKNOWN for a caller.
            System.err.println("error: cannot parse " + file + ": " + e.getMessage());
            System.exit(2);
            return;
        }
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

        // Optional §8 dimensionality cap: existentially eliminate the operand-stack
        // variables, keeping only local-to-local relations. Sound over-approximation
        // (see StackProjection); cuts the bignum blow-up that makes a few systems
        // (Ackermann, Numerical3) grind for tens of seconds in the rational LP.
        fr.univreunion.rati.its.IntegerTransitionSystem its = parsed.its;
        if (Boolean.getBoolean("rati.projectStack")) {
            its = fr.univreunion.rati.its.StackProjection.project(its);
            if (its.location(start) == null) its = parsed.its;   // defensive: keep entry
            String dump = System.getProperty("rati.dumpProjected");
            if (dump != null) {
                try {
                    Files.write(Paths.get(dump),
                        fr.univreunion.rati.its.KoatPrinter.print(its, start)
                            .getBytes(StandardCharsets.UTF_8));
                } catch (IOException e) { System.err.println("[rati] dump failed: " + e); }
            }
        }

        FarkasRanking.Certificate cert;
        try {
            cert = FarkasRanking.proveWithCertificate(its, start);
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
            if (cpfOut != null) writeCpf(its, start, cert, cpfOut);
            System.exit(0);
        } else if (cert.verdict == FarkasRanking.Verdict.NONTERMINATES
                && !Boolean.getBoolean("rati.projectStack")) {
            // A NONTERMINATES verdict is only sound on the exact (or under-approximated)
            // system. Stack projection is an OVER-approximation, so a recurrent set it
            // exposes can be spurious — downgrade to UNKNOWN when projecting.
            System.out.println("NONTERMINATES");
            if (!quiet) printNonTermination(cert.nonTermination);
            System.exit(3);
        } else {
            System.out.println("UNKNOWN");
            System.exit(1);
        }
    }

    private static void printNonTermination(NonTermination.Witness w) {
        System.out.println("certificate (non-termination):");
        System.out.println("  location: " + w.location);
        System.out.println("  recurrent set: { " + String.join(", ", w.recurrentSet) + " }");
        System.out.println("  cycle: " + edgeChain(w.cycle, w.location));
        System.out.println("  determinised step: " + String.join(", ", w.loopStep));
        System.out.println("  path: " + (w.path.isEmpty() ? "(entry is the loop head)"
                : edgeChain(w.path, w.path.get(0).source().name())));
        System.out.println("  entry state: " + renderState(w.entryState));
        System.out.println("  state entering the loop: " + renderState(w.headState));
    }

    /** {@code a -> b -> c} from a transition list starting at {@code first}. */
    private static String edgeChain(List<ItsTransition> ts, String first) {
        StringBuilder sb = new StringBuilder(first);
        for (ItsTransition t : ts) sb.append(" -> ").append(t.target().name());
        return sb.toString();
    }

    private static String renderState(Map<String, BigInteger> state) {
        if (state.isEmpty()) return "(no variables)";
        StringBuilder sb = new StringBuilder();
        for (Map.Entry<String, BigInteger> e : state.entrySet()) {
            if (sb.length() > 0) sb.append(", ");
            sb.append(e.getKey()).append(" = ").append(e.getValue());
        }
        return sb.toString();
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

    /**
     * Writes a CPF LTS termination certificate for CeTA to {@code out}, or, when the
     * proof shape is not exportable, leaves no file and warns — the caller treats a
     * missing file as "terminating but not certified" (never as wrong).
     */
    private static void writeCpf(fr.univreunion.rati.its.IntegerTransitionSystem its,
            String start, FarkasRanking.Certificate cert, String out) {
        String xml = fr.univreunion.rati.cpf.CpfExporter.export(its, start, cert);
        if (xml == null) {
            System.err.println("[rati] no CPF certificate written: proof shape not exportable");
            return;
        }
        try {
            Files.write(Paths.get(out), xml.getBytes(StandardCharsets.UTF_8));
        } catch (IOException e) {
            System.err.println("[rati] could not write CPF certificate to " + out + ": " + e.getMessage());
        }
    }

    private static void usage(String err) {
        if (err != null) System.err.println("error: " + err);
        System.err.println("usage: rank <file.koat> [--entry <functor>] [--quiet] [--cpf <out.xml>]");
        System.err.println("  --cpf writes a CPF LTS termination certificate for CeTA on a TERMINATES verdict");
        System.err.println("  reads a KoAT-format ITS, prints TERMINATES (+ ranking certificate),");
        System.err.println("  NONTERMINATES (+ recurrent-set witness) or UNKNOWN");
        System.err.println("  exit code: 0 TERMINATES, 1 UNKNOWN, 2 usage/IO error, 3 NONTERMINATES");
        System.err.println("  run with -Djava.library.path=<dir with libjapron.so> (Apron JNI)");
        System.exit(2);
    }
}
