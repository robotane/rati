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

    /**
     * Computes the bare termination exit code for a KoAT-format ITS — {@code 0}
     * TERMINATES, {@code 1} UNKNOWN, {@code 2} usage/parse/setup error, {@code 3}
     * NONTERMINATES — applying the <em>same</em> property-gated cascade as
     * {@link #main} (binterm → projectStack|chainOnly → sctFirst → Farkas) but
     * performing no printing, no CPF export, no instrumentation, and never calling
     * {@link System#exit}. It is the in-process face of the CLI: an embedding
     * analyser (BCTerm's {@code RatiProver}) can call it directly instead of forking
     * a JVM, and because both entry points run the identical cascade the forked and
     * in-process verdicts cannot drift. The properties (e.g. {@code rati.sctFirst},
     * {@code rati.projectStack}) are read from the live JVM, exactly as {@link #main}
     * reads them, so an embedder controls the cascade by setting them on its own JVM.
     *
     * @param text  the KoAT-format ITS source
     * @param entryOverride mirrors {@code --entry}: the start functor, or {@code null}
     *        to use the ITS's own {@code (STARTTERM …)}
     */
    public static int proveExitCode(String text, String entryOverride) {
        KoatParser.Parsed parsed;
        try {
            parsed = KoatParser.parse(text);
        } catch (RuntimeException e) {
            return 2;   // malformed input is a usage error, not an analysis outcome
        }
        String start = entryOverride != null ? entryOverride : parsed.start;
        if (start == null || parsed.its.location(start) == null) return 2;
        return proveExitCode(parsed.its, start);
    }

    /**
     * Object-handoff face of {@link #proveExitCode(String, String)}: ranks an ITS that
     * an embedder has already built in memory, skipping the KoAT text serialise/parse
     * round-trip entirely. It runs the <em>identical</em> property-gated cascade
     * (binterm → projectStack|chainOnly → sctFirst → Farkas) and returns the same exit
     * codes, so a verdict obtained this way cannot drift from the forked CLI or the
     * text entry point — the only difference is that the {@code its} was constructed
     * directly rather than parsed from {@code (RULES …)}. The {@code its} must be the
     * exact (non-over-approximated) system; the §8 transforms are applied here, exactly
     * as the text path applies them to {@code parsed.its}.
     *
     * @param its   the integer transition system to rank (already built, not text)
     * @param start the start functor; must be a location of {@code its}
     * @return {@code 0} TERMINATES, {@code 1} UNKNOWN, {@code 2} usage/setup error,
     *         {@code 3} NONTERMINATES
     */
    public static int proveExitCode(fr.univreunion.rati.its.IntegerTransitionSystem its0,
            String start) {
        if (its0 == null || start == null || its0.location(start) == null) return 2;

        if (Boolean.getBoolean("rati.binterm")) {
            fr.univreunion.rati.ranking.BinTerm.Result r =
                    fr.univreunion.rati.ranking.BinTerm.analyze(its0, start);
            return r.terminates() ? 0 : 1;
        }

        // §8 over-approximating transforms (see main() for the rationale of each gate).
        fr.univreunion.rati.its.IntegerTransitionSystem its = its0;
        boolean overApprox = false;
        if (Boolean.getBoolean("rati.projectStack")) {
            its = fr.univreunion.rati.its.StackProjection.project(its);
            if (its.location(start) == null) its = its0;
            overApprox = true;
        } else if (Boolean.getBoolean("rati.chainOnly")) {
            int gate = Integer.getInteger("rati.chainGate", 0);
            if (gate <= 0 || FarkasRanking.maxSccTransitions(its, start) >= gate) {
                its = fr.univreunion.rati.its.StackProjection.chain(its);
                if (its.location(start) == null) its = its0;
                overApprox = true;
            }
        }

        // No-Apron size-change triage (short-circuits a TERMINATES; a NO falls through).
        if (Boolean.getBoolean("rati.sctFirst")) {
            fr.univreunion.rati.ranking.SizeChangeTermination.Result sct =
                    fr.univreunion.rati.ranking.SizeChangeTermination.analyze(its, start);
            if (sct.terminates()) return 0;
        }

        FarkasRanking.Certificate cert;
        try {
            cert = FarkasRanking.proveWithCertificate(its, start);
        } catch (UnsatisfiedLinkError | NoClassDefFoundError e) {
            return 2;   // Apron native library not loaded — a setup error
        } catch (RuntimeException e) {
            return 1;   // a prover bug must not masquerade as a clean MAYBE → sound UNKNOWN
        }

        if (cert.verdict == FarkasRanking.Verdict.TERMINATES) return 0;
        // A NONTERMINATES verdict is only sound on the exact (non-over-approximated)
        // system; a witness on a projected/chained ITS may be spurious → UNKNOWN.
        if (cert.verdict == FarkasRanking.Verdict.NONTERMINATES && !overApprox) return 3;
        return 1;
    }

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

        // Faithful BINTERM cascade (Algorithm 1, TOPLAS 2010 §7): no-Apron SCT
        // triage first, fast punt of oversized SCCs, then the Apron tiers only on
        // the small residual. Opt-in (--binterm) for measurement; routes the whole
        // verdict through BinTerm.analyze and bypasses the Farkas/Apron path below.
        if (Boolean.getBoolean("rati.binterm")) {
            fr.univreunion.rati.ranking.BinTerm.Result r =
                    fr.univreunion.rati.ranking.BinTerm.analyze(parsed.its, start);
            if (!quiet) System.out.println("[binterm] tier=" + r.tier + " " + r.detail);
            if (r.terminates()) { System.out.println("TERMINATES"); System.exit(0); }
            System.out.println("UNKNOWN"); System.exit(1);
            return;
        }

        // Optional §8 dimensionality cap: existentially eliminate the operand-stack
        // variables, keeping only local-to-local relations. Sound over-approximation
        // (see StackProjection); cuts the bignum blow-up that makes a few systems
        // (Ackermann, Numerical3) grind for tens of seconds in the rational LP.
        fr.univreunion.rati.its.IntegerTransitionSystem its = parsed.its;
        boolean overApprox = false;   // an over-approximating transform was applied
        if (Boolean.getBoolean("rati.projectStack")) {
            its = fr.univreunion.rati.its.StackProjection.project(its);
            if (its.location(start) == null) its = parsed.its;   // defensive: keep entry
            overApprox = true;
        } else if (Boolean.getBoolean("rati.chainOnly")) {
            // Narrow chaining: collapse single-in/single-out pass-through locations
            // by exact composition, keeping the stack. Shrinks the per-bytecode
            // transition mesh of a big SCC without the whole-graph FVS blow-up that
            // makes projectStack fall back. Sound over-approximation (see chain()).
            //
            // Gated by -Drati.chainGate=N (default 0 = chain always): chain()'s
            // composition cost is non-trivial on the FULL state (locals + stack), so
            // a Kitten A/B showed blanket chaining is a net wall LOSS — it taxes the
            // easy mass more than it saves on grinders. With N>0 we chain ONLY methods
            // whose raw max-SCC cyclic-transition count >= N (the same deterministic,
            // machine-independent §8 signal as the cap), so the cost is paid only
            // where the LP grind makes it pay off.
            int gate = Integer.getInteger("rati.chainGate", 0);
            if (gate <= 0
                    || fr.univreunion.rati.ranking.FarkasRanking.maxSccTransitions(its, start) >= gate) {
                its = fr.univreunion.rati.its.StackProjection.chain(its);
                if (its.location(start) == null) its = parsed.its;   // defensive: keep entry
                overApprox = true;
            }
        }
        if (overApprox) {
            String dump = System.getProperty("rati.dumpProjected");
            if (dump != null) {
                try {
                    Files.write(Paths.get(dump),
                        fr.univreunion.rati.its.KoatPrinter.print(its, start)
                            .getBytes(StandardCharsets.UTF_8));
                } catch (IOException e) { System.err.println("[rati] dump failed: " + e); }
            }
        }

        // Tier-1 of the "pure Julia" cascade: the cheap,
        // PTIME, no-Apron size-change test triages the easy SCCs in milliseconds
        // before the heavyweight Farkas/Apron tier ever runs. Opt-in
        // (-Drati.sctFirst), default OFF until the corpus sweep + CeTA byte-id bars
        // are clean. It only SHORT-CIRCUITS a TERMINATES verdict; a NO answer falls
        // through to Farkas unchanged (sound: SCT never claims false termination).
        // When a CPF certificate is requested (--cpf) we do NOT short-circuit —
        // SCT does not yet emit CPF, so the cert path stays on Farkas and CeTA
        // output is byte-identical.
        if (Boolean.getBoolean("rati.sctFirst") && cpfOut == null) {
            fr.univreunion.rati.ranking.SizeChangeTermination.Result sct =
                    fr.univreunion.rati.ranking.SizeChangeTermination.analyze(its, start);
            if (sct.terminates()) {
                // Optional instrumentation: append one line per short-circuit to the
                // file named by -Drati.sctLog (counting SCT firings across a child-per-
                // method run, where stderr is merged into the parsed stdout so a stderr
                // marker would be swallowed). Off unless the property is set.
                String sctLog = System.getProperty("rati.sctLog");
                if (sctLog != null) {
                    try {
                        Files.write(Paths.get(sctLog),
                                ("SCT " + start + " " + sct.sccProved + "\n")
                                        .getBytes(StandardCharsets.UTF_8),
                                java.nio.file.StandardOpenOption.CREATE,
                                java.nio.file.StandardOpenOption.APPEND);
                    } catch (IOException ignored) { /* counting is best-effort */ }
                }
                System.out.println("TERMINATES");
                if (!quiet) System.out.println("certificate: size-change termination ("
                        + sct.sccProved + " SCC(s) proved; no idempotent self-graph "
                        + "lacks an in-situ strict thread)");
                System.exit(0);
            }
        }

        // Optional calibration instrumentation (off unless -Drati.proveLog is set):
        // record the raw (un-chained) max-SCC transition count BEFORE the prove, so a
        // method killed by the wall cap still leaves its maxScc on a "PRE" line; the
        // "DONE" line after the prove adds the elapsed ms + verdict. A single run thus
        // yields the (maxScc, time) separation used to choose -Drati.chainGate, with the
        // heaviest grinders (the ones that benefit most from chaining) still covered.
        String proveLog = System.getProperty("rati.proveLog");
        int rawMaxScc = proveLog == null ? -1
                : FarkasRanking.maxSccTransitions(parsed.its, start);
        if (proveLog != null) appendLine(proveLog, start + " " + rawMaxScc + " PRE");

        long proveT0 = System.nanoTime();
        FarkasRanking.Certificate cert;
        try {
            // Force eager invariants when a CPF will be written, so the proof reaches the
            // emittable DIRECT multiphase synthesis (a lazy pass can settle for the
            // non-exportable loop-summary fallback). A plain verdict run keeps lazy.
            cert = FarkasRanking.proveWithCertificate(its, start, cpfOut != null);
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

        if (proveLog != null) {
            long ms = (System.nanoTime() - proveT0) / 1_000_000L;
            appendLine(proveLog, start + " " + rawMaxScc + " " + ms + " " + cert.verdict);
        }

        if (cert.verdict == FarkasRanking.Verdict.TERMINATES) {
            System.out.println("TERMINATES");
            if (!quiet) printCertificate(cert);
            if (cpfOut != null) writeCpf(its, start, cert, cpfOut);
            System.exit(0);
        } else if (cert.verdict == FarkasRanking.Verdict.NONTERMINATES && !overApprox) {
            // A NONTERMINATES verdict is only sound on the exact (or under-approximated)
            // system. Stack projection / chaining is an OVER-approximation, so a recurrent
            // set it exposes can be spurious — downgrade to UNKNOWN when one was applied.
            // (When chainGate skips chaining, overApprox stays false and a non-termination
            // witness on the exact system is reported as before — strictly more precise.)
            System.out.println("NONTERMINATES");
            if (!quiet) printNonTermination(cert.nonTermination);
            System.exit(3);
        } else {
            System.out.println("UNKNOWN");
            System.exit(1);
        }
    }

    /** Best-effort atomic append of one line (+newline) to an instrumentation file. */
    private static void appendLine(String file, String line) {
        try {
            Files.write(Paths.get(file), (line + "\n").getBytes(StandardCharsets.UTF_8),
                    java.nio.file.StandardOpenOption.CREATE,
                    java.nio.file.StandardOpenOption.APPEND);
        } catch (IOException ignored) { /* counting is best-effort */ }
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
