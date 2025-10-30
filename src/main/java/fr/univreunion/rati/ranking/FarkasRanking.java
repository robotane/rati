package fr.univreunion.rati.ranking;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fr.univreunion.rati.its.IntegerTransitionSystem;
import fr.univreunion.rati.its.ItsLinearConstraint;
import fr.univreunion.rati.its.ItsLinearExpression;
import fr.univreunion.rati.its.ItsLocation;
import fr.univreunion.rati.its.ItsTransition;

/**
 * In-house linear-ranking-function synthesiser for an {@link IntegerTransitionSystem}
 * — the local fallback that lifts cTI's level-mapping blind spots (free-variable
 * callee atoms, multi-predicate SCC conflation) without an external tool.
 *
 * <p>Implements the SAS&nbsp;2010 algorithm of Alias, Darte, Feautrier &amp; Gonnord,
 * <em>"Multi-dimensional Rankings, Program Termination, and Complexity Bounds of
 * Flowchart Programs"</em> — the method iRankFinder is built on:
 * <ol>
 *   <li>restrict to the locations reachable from the entry;</li>
 *   <li>decompose into strongly connected components (Tarjan);</li>
 *   <li>for each non-trivial SCC, synthesise a <em>lexicographic</em> linear
 *       ranking function by repeatedly solving, via Farkas' lemma, a single
 *       linear program that orients (strictly decreases, while keeping all active
 *       transitions bounded below and non-increasing) a maximal set of the
 *       still-unranked transitions, then peeling those transitions off.</li>
 * </ol>
 * An SCC is ranked iff every transition is eventually peeled. If every reachable
 * non-trivial SCC is ranked (and no reachable transition is
 * {@link ItsTransition#isSupported() unsupported}), the system — hence the
 * program's path length — terminates.
 *
 * <p>Soundness rests on exact rational arithmetic ({@link LinearProgram}): a
 * peeled transition has a Farkas-certified strict positive decrease and a lower
 * bound of 0, so over a well-founded measure (path length) only finitely many
 * steps are possible. Strict inequalities in a guard are relaxed to non-strict
 * (enlarging the guard) — conservative, hence sound.
 */
public final class FarkasRanking {

    public enum Verdict { TERMINATES, UNKNOWN }

    private static final boolean DEBUG = Boolean.getBoolean("rati.rankingDebug");

    private FarkasRanking() {}

    /**
     * A termination certificate: the verdict plus, per non-trivial SCC, the
     * proof that ranks it — its locations, the technique used, and (for the
     * lexicographic-linear ADFG path) the ordered list of per-location ranking
     * functions, one map per peeling round. Surfaced by {@link
     * #proveWithCertificate} so the standalone solver can print a verifiable
     * witness, not just a yes/no.
     */
    public static final class Certificate {
        public final Verdict verdict;
        public final List<SccProof> sccs;
        Certificate(Verdict verdict, List<SccProof> sccs) {
            this.verdict = verdict;
            this.sccs = sccs;
        }
    }

    /** Per-SCC proof: locations, ranking technique, and the lexicographic rounds. */
    public static final class SccProof {
        public final List<String> locations;
        /** e.g. "lexicographic linear (ADFG)", "multiphase (MΦRF)", "transition invariant". */
        public String method = "?";
        /** One entry per peeling round: location name → rendered ranking function. */
        public final List<Map<String, String>> rounds = new ArrayList<Map<String, String>>();
        SccProof(List<String> locations) { this.locations = locations; }
    }

    /** Proves termination AND, on success, collects a {@link Certificate}. */
    public static Certificate proveWithCertificate(IntegerTransitionSystem its, String entryLocation) {
        List<SccProof> proofs = new ArrayList<SccProof>();
        Verdict v = prove(its, entryLocation, proofs);
        return new Certificate(v, proofs);
    }

    public static Verdict prove(IntegerTransitionSystem its, String entryLocation) {
        return prove(its, entryLocation, null);
    }

    private static Verdict prove(IntegerTransitionSystem its, String entryLocation,
            List<SccProof> proofs) {
        if (entryLocation == null || its.location(entryLocation) == null) return Verdict.UNKNOWN;

        Set<String> reachable = reachableFrom(its, entryLocation);

        // A reachable transition the model could not express faithfully forces a
        // sound UNKNOWN (it may hide an unranked loop) — unless its guard is
        // infeasible, in which case it can never fire and cannot hide anything.
        for (ItsTransition t : its.transitions())
            if (!t.isSupported() && reachable.contains(t.source().name())
                    && !ItsInvariants.isInfeasible(t)) return Verdict.UNKNOWN;

        // SCCs over the reachable sub-graph.
        Map<String, Integer> scc = tarjan(its, reachable);

        // Group the cyclic transitions (both endpoints in one SCC) by component,
        // and record which SCCs are non-trivial (contain a cycle).
        Map<Integer, List<ItsTransition>> cyclic = new LinkedHashMap<Integer, List<ItsTransition>>();
        Set<Integer> nonTrivial = nonTrivialSccs(its, reachable, scc, cyclic);

        // Drop cyclic transitions whose guard is empty: they can never fire, so
        // they are irrelevant to termination. Crucially this removes contradictory
        // identity self-loops (ρ_source − ρ_target ≡ 0 ⇒ unrankable) that would
        // otherwise sink an entire SCC into UNKNOWN.
        for (List<ItsTransition> ts : cyclic.values()) ts.removeIf(ItsInvariants::isInfeasible);
        nonTrivial.removeIf(c -> cyclic.get(c).isEmpty());

        if (DEBUG) {
            System.err.println("[ranking] entry=" + entryLocation + " reachable=" + reachable.size()
                    + " nonTrivialSCCs=" + nonTrivial.size());
            int edges = 0;
            for (ItsTransition t : its.transitions())
                if (reachable.contains(t.source().name()) && reachable.contains(t.target().name())) {
                    edges++;
                    if (t.source().name().contains("reverse") || t.target().name().contains("reverse"))
                        System.err.println("    edge " + t.source().name() + "[scc" + scc.get(t.source().name())
                                + "] -> " + t.target().name() + "[scc" + scc.get(t.target().name())
                                + "] supported=" + t.isSupported());
                }
            System.err.println("  reachable intra-edges=" + edges);
            for (Integer c : nonTrivial) {
                System.err.println("  SCC#" + c + " cyclic transitions:");
                for (ItsTransition t : cyclic.get(c))
                    System.err.println("    " + t.source().name() + " -> " + t.target().name()
                            + "  guard=" + t.constraints());
            }
        }
        if (nonTrivial.isEmpty()) return Verdict.TERMINATES;   // no loop to rank

        // Supporting invariants: boundedness of a ranking function often depends on
        // a fact established before the loop, absent from the per-transition guards.
        Map<String, List<ItsLinearConstraint>> invariants =
                ItsInvariants.compute(its, entryLocation, reachable);

        for (Integer comp : nonTrivial) {
            if (rankScc(its, invariants, cyclic.get(comp), proofs) != Verdict.TERMINATES)
                return Verdict.UNKNOWN;
        }
        return Verdict.TERMINATES;
    }

    // -------------------------------------------------------------------------
    // Graph pre-processing
    // -------------------------------------------------------------------------

    private static Set<String> reachableFrom(IntegerTransitionSystem its, String entry) {
        Map<String, List<String>> succ = new HashMap<String, List<String>>();
        for (ItsTransition t : its.transitions())
            succ.computeIfAbsent(t.source().name(), k -> new ArrayList<String>())
                .add(t.target().name());
        Set<String> seen = new HashSet<String>();
        Deque<String> work = new ArrayDeque<String>();
        seen.add(entry); work.add(entry);
        while (!work.isEmpty()) {
            String cur = work.poll();
            for (String n : succ.getOrDefault(cur, java.util.Collections.emptyList()))
                if (seen.add(n)) work.add(n);
        }
        return seen;
    }

    /** Tarjan SCC; returns location name → component id, over reachable nodes only. */
    private static Map<String, Integer> tarjan(IntegerTransitionSystem its, Set<String> reachable) {
        Map<String, List<String>> succ = new HashMap<String, List<String>>();
        for (String n : reachable) succ.put(n, new ArrayList<String>());
        for (ItsTransition t : its.transitions()) {
            String s = t.source().name(), d = t.target().name();
            if (reachable.contains(s) && reachable.contains(d)) succ.get(s).add(d);
        }
        Tarjan tj = new Tarjan(succ);
        for (String n : reachable) if (!tj.index.containsKey(n)) tj.connect(n);
        return tj.comp;
    }

    /** Iterative-explicit-stack Tarjan (robust on the small, possibly deep ITS graphs). */
    private static final class Tarjan {
        final Map<String, List<String>> succ;
        final Map<String, Integer> index = new HashMap<String, Integer>();
        final Map<String, Integer> low = new HashMap<String, Integer>();
        final Map<String, Integer> comp = new HashMap<String, Integer>();
        final Deque<String> stack = new ArrayDeque<String>();
        final Set<String> onStack = new HashSet<String>();
        int idx = 0, nextComp = 0;

        Tarjan(Map<String, List<String>> succ) { this.succ = succ; }

        // Explicit work-stack DFS. Each frame tracks the next successor to visit.
        void connect(String root) {
            Deque<String> node = new ArrayDeque<String>();
            Deque<Integer> it = new ArrayDeque<Integer>();
            open(root, node, it);
            while (!node.isEmpty()) {
                String v = node.peek();
                int i = it.pop();
                List<String> ws = succ.get(v);
                if (i < ws.size()) {
                    it.push(i + 1);
                    String w = ws.get(i);
                    if (!index.containsKey(w)) {
                        open(w, node, it);                       // recurse into tree edge
                    } else if (onStack.contains(w)) {
                        low.put(v, Math.min(low.get(v), index.get(w)));   // back/cross edge
                    }
                } else {
                    // All successors done: fold children's low-links, then maybe close an SCC root.
                    node.pop();
                    if (!node.isEmpty())
                        low.put(node.peek(), Math.min(low.get(node.peek()), low.get(v)));
                    if (low.get(v).equals(index.get(v))) {
                        int id = nextComp++;
                        String w;
                        do { w = stack.pop(); onStack.remove(w); comp.put(w, id); } while (!w.equals(v));
                    }
                }
            }
        }

        private void open(String v, Deque<String> node, Deque<Integer> it) {
            index.put(v, idx); low.put(v, idx); idx++;
            stack.push(v); onStack.add(v);
            node.push(v); it.push(0);
        }
    }

    private static Set<Integer> nonTrivialSccs(IntegerTransitionSystem its, Set<String> reachable,
            Map<String, Integer> scc, Map<Integer, List<ItsTransition>> cyclic) {
        Set<Integer> nonTrivial = new LinkedHashSet<Integer>();
        for (ItsTransition t : its.transitions()) {
            String s = t.source().name(), d = t.target().name();
            if (!reachable.contains(s) || !reachable.contains(d)) continue;
            Integer cs = scc.get(s), cd = scc.get(d);
            if (cs == null || !cs.equals(cd)) continue;       // not an intra-SCC edge
            cyclic.computeIfAbsent(cs, k -> new ArrayList<ItsTransition>()).add(t);
            nonTrivial.add(cs);   // any intra-SCC edge ⇒ a cycle (self-loop or ≥2 nodes)
        }
        return nonTrivial;
    }

    // -------------------------------------------------------------------------
    // Lexicographic ranking of one SCC (ADFG peeling)
    // -------------------------------------------------------------------------

    private static Verdict rankScc(IntegerTransitionSystem its,
                                   Map<String, List<ItsLinearConstraint>> invariants,
                                   List<ItsTransition> cyclicTrans, List<SccProof> proofs) {
        SccProof proof = proofs == null ? null : new SccProof(sccLocations(cyclicTrans));
        // First the raw per-transition method (cheap; ranks single-block loops). If
        // it fails — typically a multi-block diamond / nested loop where boundedness
        // holds only after merging the body — retry on the cut-point loop summary.
        List<Map<String, String>> rounds = proof == null ? null : new ArrayList<Map<String, String>>();
        if (rankTransitions(its, invariants, cyclicTrans, rounds) == Verdict.TERMINATES)
            return record(proofs, proof, "lexicographic linear (ADFG)", rounds);
        List<ItsTransition> summary = LoopSummary.summarize(cyclicTrans);
        List<ItsTransition> best = cyclicTrans;
        if (summary != cyclicTrans) {
            if (DEBUG) System.err.println("  retry on loop summary (" + summary.size() + " transitions)");
            List<Map<String, String>> sRounds = proof == null ? null : new ArrayList<Map<String, String>>();
            if (rankTransitions(its, invariants, summary, sRounds) == Verdict.TERMINATES)
                return record(proofs, proof, "lexicographic linear (ADFG, loop summary)", sRounds);
            best = summary;
        }
        // A multiphase (MΦRF) ranking function — handles phase loops (a quantity
        // grows while another is positive, then shrinks) that no single lexicographic
        // linear ranking covers. Ben-Amram-Genaim nested-RF synthesis.
        if (MultiphaseRanking.ranks(best, invariants)) {
            if (DEBUG) System.err.println("  ranked by a multiphase (MΦRF) function");
            return record(proofs, proof, "multiphase (MΦRF)", null);
        }
        // Last resort: disjunctive termination (Podelski-Rybalchenko transition
        // invariants) — proves loops covered only by a UNION of well-founded
        // relations (e.g. integer counters unbounded below, one per phase), which
        // no single ranking function of any kind captures.
        if (DEBUG) {
            Set<String> ls = new LinkedHashSet<String>();
            for (ItsTransition t : best) ls.add(t.source().name() + "->" + t.target().name());
            System.err.println("  disjunctive input: " + best.size() + " transitions, edges=" + ls);
        }
        if (DisjunctiveTermination.terminates(best)) {
            if (DEBUG) System.err.println("  proved by a transition invariant (disjunctive)");
            return record(proofs, proof, "transition invariant (disjunctive)", null);
        }
        return Verdict.UNKNOWN;
    }

    /** Commits a completed SCC proof to the certificate (when collecting) and returns TERMINATES. */
    private static Verdict record(List<SccProof> proofs, SccProof proof,
            String method, List<Map<String, String>> rounds) {
        if (proofs != null && proof != null) {
            proof.method = method;
            if (rounds != null) proof.rounds.addAll(rounds);
            proofs.add(proof);
        }
        return Verdict.TERMINATES;
    }

    /** Sorted location names appearing in an SCC's transitions. */
    private static List<String> sccLocations(List<ItsTransition> trans) {
        Set<String> names = new LinkedHashSet<String>();
        for (ItsTransition t : trans) { names.add(t.source().name()); names.add(t.target().name()); }
        List<String> l = new ArrayList<String>(names);
        java.util.Collections.sort(l);
        return l;
    }

    /**
     * ADFG peeling on a transition set: TERMINATES iff every transition is
     * eventually oriented. Each round first tries the standard global-bound round
     * ({@link #orientRound}); if that peels nothing it retries the per-anchor
     * relaxed round ({@link #orientRoundRelaxed}), which requires boundedness only
     * on the transitions it actually peels. The relaxed retry is purely additive —
     * it only ever fires on a round the global one could not advance, and the full
     * fallback chain still runs on the original transition set — so the set of
     * provable systems can only grow relative to the global-only prover.
     */
    private static Verdict rankTransitions(IntegerTransitionSystem its,
                                   Map<String, List<ItsLinearConstraint>> invariants,
                                   List<ItsTransition> transitions, List<Map<String, String>> rounds) {
        Set<String> locNames = new LinkedHashSet<String>();
        for (ItsTransition t : transitions) { locNames.add(t.source().name()); locNames.add(t.target().name()); }
        List<String> locs = new ArrayList<String>(locNames);
        java.util.Collections.sort(locs);

        List<ItsTransition> active = new ArrayList<ItsTransition>(transitions);
        while (!active.isEmpty()) {
            Map<String, String> roundFn = rounds == null ? null : new LinkedHashMap<String, String>();
            List<ItsTransition> strict = orientRound(its, invariants, locs, active, roundFn);
            if (strict.isEmpty()) {
                // Global-bound round stuck (e.g. a region-split loop where no single ρ
                // is bounded below on every active transition): retry the relaxed round.
                if (roundFn != null) roundFn.clear();
                strict = orientRoundRelaxed(its, invariants, locs, active, roundFn);
            }
            if (DEBUG) {
                StringBuilder sb = new StringBuilder();
                for (ItsTransition t : strict) sb.append(t.source().name()).append("->").append(t.target().name()).append(' ');
                System.err.println("  round: peeled " + strict.size() + " [" + sb.toString().trim() + "]");
            }
            if (strict.isEmpty()) return Verdict.UNKNOWN;     // no linear component peels
            if (rounds != null) rounds.add(roundFn);
            active.removeAll(strict);
        }
        return Verdict.TERMINATES;
    }

    /**
     * One ADFG round: builds and solves the Farkas LP that orients a maximal set
     * of the {@code active} transitions, and returns those it strictly decreases.
     * When {@code roundFn} is non-null, also records each location's synthesised
     * affine ranking function ρ (read off the λ coefficients) for the certificate.
     */
    private static List<ItsTransition> orientRound(IntegerTransitionSystem its,
            Map<String, List<ItsLinearConstraint>> invariants,
            List<String> locs, List<ItsTransition> active, Map<String, String> roundFn) {
        Builder b = new Builder(its, invariants);
        b.allocLambdas(locs);
        for (ItsTransition t : active) b.allocEps(t);
        for (ItsTransition t : active) {
            b.boundedImplication(t);      // guard ⊨ ρ_source ≥ 0
            b.decreaseImplication(t);     // guard ⊨ ρ_source − ρ_target ≥ ε_t,  0 ≤ ε_t ≤ 1
        }
        LinearProgram.Solution sol = b.solveMaximisingStrictness(active);
        List<ItsTransition> strict = new ArrayList<ItsTransition>();
        if (!sol.feasible || sol.x == null) return strict;
        for (ItsTransition t : active)
            if (sol.x[b.eps.get(t)].isPositive()) strict.add(t);    // certified positive decrease
        if (roundFn != null) for (String loc : locs) roundFn.put(loc, b.renderRho(loc, sol.x, its));
        return strict;
    }

    /**
     * Relaxed ADFG round, used when {@link #orientRound} (which requires the
     * single affine ρ to be bounded below on <em>every</em> active transition)
     * peels nothing. Standard lexicographic-ranking soundness only needs ρ
     * non-increasing on all transitions and bounded-below + strictly decreasing
     * on the transitions actually peeled. So here ρ is forced bounded on just one
     * <em>anchor</em> transition (whose guard supplies the lower bound), every
     * active transition is kept non-increasing, and a transition is peeled iff it
     * both ends strictly decreasing and is — checked against its own guard via
     * {@link ItsInvariants#entailsNonNegative} — bounded below. The anchor giving
     * the largest peel wins. This recovers region-split loops (counters bounded
     * on the half of the SCC where they decrease, free on the other half) that no
     * globally-non-negative ρ covers.
     */
    private static List<ItsTransition> orientRoundRelaxed(IntegerTransitionSystem its,
            Map<String, List<ItsLinearConstraint>> invariants,
            List<String> locs, List<ItsTransition> active, Map<String, String> roundFn) {
        List<ItsTransition> best = new ArrayList<ItsTransition>();
        Builder bestB = null;
        Rational[] bestX = null;
        for (ItsTransition anchor : active) {
            Builder b = new Builder(its, invariants);
            b.allocLambdas(locs);
            for (ItsTransition t : active) b.allocEps(t);
            for (ItsTransition t : active) b.decreaseImplication(t);   // ρ_s − ρ_t ≥ ε_t ≥ 0 ⇒ non-increasing on all
            b.boundedImplication(anchor);                              // ρ ≥ 0 on the anchor's guard only
            LinearProgram.Solution sol = b.solveMaximisingStrictness(active);
            if (!sol.feasible || sol.x == null) continue;
            List<ItsTransition> peeled = new ArrayList<ItsTransition>();
            for (ItsTransition t : active)
                if (sol.x[b.eps.get(t)].isPositive() && b.sourceBounded(t, sol.x)) peeled.add(t);
            if (DEBUG && !peeled.isEmpty())
                System.err.println("    relaxed anchor " + anchor.source().name() + "->"
                        + anchor.target().name() + " peeled " + peeled.size());
            if (peeled.size() > best.size()) { best = peeled; bestB = b; bestX = sol.x; }
        }
        if (roundFn != null && bestB != null)
            for (String loc : locs) roundFn.put(loc, bestB.renderRho(loc, bestX, its));
        return best;
    }

    // -------------------------------------------------------------------------
    // Farkas LP builder for one round
    // -------------------------------------------------------------------------

    private static final class Builder {
        final IntegerTransitionSystem its;
        final Map<String, List<ItsLinearConstraint>> invariants;
        int next = 0;
        // λ_{loc,i}: a free coefficient split into pos − neg parts (i = arity ⇒ constant).
        final Map<String, int[]> lamPos = new HashMap<String, int[]>();
        final Map<String, int[]> lamNeg = new HashMap<String, int[]>();
        final Map<ItsTransition, Integer> eps = new HashMap<ItsTransition, Integer>();
        final List<Map<Integer, Rational>> rows = new ArrayList<Map<Integer, Rational>>();
        final List<LinearProgram.Op> ops = new ArrayList<LinearProgram.Op>();
        final List<Rational> rhs = new ArrayList<Rational>();

        Builder(IntegerTransitionSystem its, Map<String, List<ItsLinearConstraint>> invariants) {
            this.its = its;
            this.invariants = invariants;
        }

        void allocLambdas(List<String> locs) {
            for (String loc : locs) {
                int arity = its.location(loc).arity();
                int[] pos = new int[arity + 1], neg = new int[arity + 1];
                for (int i = 0; i <= arity; i++) { pos[i] = next++; neg[i] = next++; }
                lamPos.put(loc, pos); lamNeg.put(loc, neg);
            }
        }

        void allocEps(ItsTransition t) {
            int e = next++;
            eps.put(t, e);
            // ε_t ≤ 1 (ε_t ≥ 0 is implicit: every LP variable is non-negative).
            Map<Integer, Rational> r = new HashMap<Integer, Rational>();
            r.put(e, Rational.ONE);
            rows.add(r); ops.add(LinearProgram.Op.LE); rhs.add(Rational.ONE);
        }

        /** Adds {@code coeff · λ_{loc,i}} into equation {@code eq} (pos − neg split). */
        private void addLambda(Map<Integer, Rational> eq, String loc, int i, Rational coeff) {
            if (coeff.isZero()) return;
            add(eq, lamPos.get(loc)[i], coeff);
            add(eq, lamNeg.get(loc)[i], coeff.negate());
        }

        private static void add(Map<Integer, Rational> eq, int var, Rational coeff) {
            Rational cur = eq.get(var);
            Rational nv = cur == null ? coeff : cur.add(coeff);
            if (nv.isZero()) eq.remove(var); else eq.put(var, nv);
        }

        /**
         * Renders the affine ranking function ρ synthesised for {@code loc} from an
         * LP solution: ρ = Σ_i λ_{loc,i}·formal_i + λ_{loc,arity}, where
         * λ_{loc,i} = x[lamPos] − x[lamNeg] (the pos−neg split). For the certificate.
         */
        String renderRho(String loc, Rational[] x, IntegerTransitionSystem its) {
            List<String> formals = its.location(loc).variables();
            int arity = formals.size();
            int[] pos = lamPos.get(loc), neg = lamNeg.get(loc);
            StringBuilder sb = new StringBuilder();
            for (int i = 0; i < arity; i++) {
                Rational c = x[pos[i]].subtract(x[neg[i]]);
                if (!c.isZero()) appendTerm(sb, c, formals.get(i));
            }
            Rational k = x[pos[arity]].subtract(x[neg[arity]]);
            if (!k.isZero() || sb.length() == 0) appendTerm(sb, k, null);
            return sb.length() == 0 ? "0" : sb.toString();
        }

        /**
         * Boundedness filter for the relaxed round: is {@code ρ_source(t) ≥ 0}
         * entailed by {@code t}'s own premises (guard ∪ source invariant)? Reads
         * ρ's rational coefficients off the LP solution, scales them to integers
         * by their common denominator (a positive scale preserves the sign of the
         * inequality), and checks the entailment with Apron. Conservative: any
         * arithmetic/decision failure returns {@code false} (not peeled — sound).
         */
        boolean sourceBounded(ItsTransition t, Rational[] x) {
            try {
                String loc = t.source().name();
                List<String> formals = t.source().variables();
                int arity = formals.size();
                int[] pos = lamPos.get(loc), neg = lamNeg.get(loc);
                Rational[] r = new Rational[arity + 1];
                for (int i = 0; i <= arity; i++) r[i] = x[pos[i]].subtract(x[neg[i]]);
                BigInteger den = BigInteger.ONE;
                for (Rational q : r) {
                    BigInteger d = q.denominator();
                    den = den.divide(den.gcd(d)).multiply(d);   // lcm
                }
                Map<String, Long> terms = new LinkedHashMap<String, Long>();
                for (int i = 0; i < arity; i++) {
                    BigInteger c = r[i].numerator().multiply(den).divide(r[i].denominator());
                    if (c.signum() != 0) terms.put(formals.get(i), c.longValueExact());
                }
                long k = r[arity].numerator().multiply(den).divide(r[arity].denominator()).longValueExact();
                return ItsInvariants.entailsNonNegative(premises(t), terms, k);
            } catch (ArithmeticException e) {
                return false;
            }
        }

        /** Appends {@code ± c·var} (or {@code ± c} when {@code var} is null) with sign joining. */
        private static void appendTerm(StringBuilder sb, Rational c, String var) {
            boolean neg = c.isNegative();
            Rational mag = neg ? c.negate() : c;
            sb.append(sb.length() == 0 ? (neg ? "-" : "") : (neg ? " - " : " + "));
            if (var == null) sb.append(mag);
            else if (mag.equals(Rational.ONE)) sb.append(var);
            else sb.append(mag).append('*').append(var);
        }

        // Premises of a transition as forms {@code p ≥ 0}: its guard PLUS the
        // forward invariant holding at its source location (a transition fires
        // only from reachable source states, so adding the invariant is sound and
        // supplies the boundedness facts the raw guards lack). An equality
        // contributes p and −p, i.e. a free multiplier.
        private List<ItsLinearExpression> premises(ItsTransition t) {
            List<ItsLinearExpression> ps = new ArrayList<ItsLinearExpression>();
            addPremises(ps, t.constraints());
            if (invariants != null) addPremises(ps, invariants.get(t.source().name()));
            return ps;
        }

        private static void addPremises(List<ItsLinearExpression> ps, List<ItsLinearConstraint> cs) {
            if (cs == null) return;
            for (ItsLinearConstraint c : cs) {
                ps.add(c.lhs());
                if (c.op() == ItsLinearConstraint.Op.EQ) ps.add(negate(c.lhs()));
            }
        }

        private static ItsLinearExpression negate(ItsLinearExpression e) {
            ItsLinearExpression.Builder nb = new ItsLinearExpression.Builder();
            for (Map.Entry<String, Long> t : e.coefficients().entrySet()) nb.addTerm(t.getKey(), -t.getValue());
            nb.addConstant(-e.constant());
            return nb.build();
        }

        /** Variable universe of an implication: source formals ∪ (target updates) ∪ premises. */
        private Set<String> universe(ItsTransition t, boolean withTarget) {
            Set<String> v = new LinkedHashSet<String>(t.source().variables());
            if (withTarget) for (ItsLinearExpression e : t.updates()) v.addAll(e.variables());
            for (ItsLinearExpression p : premises(t)) v.addAll(p.variables());
            return v;
        }

        // coeff of variable `var` in ρ_source(state) = Σ λ_{s,i}·formal_i + λ_{s,const}
        private void addSourceCoeff(Map<Integer, Rational> eq, ItsTransition t, String var, Rational sign) {
            List<String> formals = t.source().variables();
            int i = formals.indexOf(var);
            if (i >= 0) addLambda(eq, t.source().name(), i, sign);
        }
        private void addSourceConst(Map<Integer, Rational> eq, ItsTransition t, Rational sign) {
            addLambda(eq, t.source().name(), t.source().arity(), sign);
        }

        // coeff of `var` in ρ_target(update) = Σ_j λ_{t,j}·E_j(var)
        private void addTargetCoeff(Map<Integer, Rational> eq, ItsTransition t, String var, Rational sign) {
            List<ItsLinearExpression> upd = t.updates();
            String tloc = t.target().name();
            for (int j = 0; j < upd.size(); j++) {
                long c = upd.get(j).coefficient(var);
                if (c != 0) addLambda(eq, tloc, j, sign.multiply(Rational.of(c)));
            }
        }
        private void addTargetConst(Map<Integer, Rational> eq, ItsTransition t, Rational sign) {
            List<ItsLinearExpression> upd = t.updates();
            String tloc = t.target().name();
            for (int j = 0; j < upd.size(); j++) {
                long d = upd.get(j).constant();
                if (d != 0) addLambda(eq, tloc, j, sign.multiply(Rational.of(d)));
            }
            addLambda(eq, tloc, t.target().arity(), sign);   // λ_{t,const}
        }

        /** Encodes {@code guard(t) ⊨ ρ_source ≥ 0} via Farkas. */
        void boundedImplication(ItsTransition t) {
            List<ItsLinearExpression> ps = premises(t);
            int[] mu = new int[ps.size()];
            for (int k = 0; k < ps.size(); k++) mu[k] = next++;
            int mu0 = next++;
            // Per-variable matches:  coeff_v(ρ_source) − Σ μ_k·coeff_v(p_k) = 0
            for (String v : universe(t, false)) {
                Map<Integer, Rational> eq = new HashMap<Integer, Rational>();
                addSourceCoeff(eq, t, v, Rational.ONE);
                for (int k = 0; k < ps.size(); k++) add(eq, mu[k], Rational.of(-ps.get(k).coefficient(v)));
                pushEq(eq);
            }
            // Constant match:  const(ρ_source) − Σ μ_k·const(p_k) − μ0 = 0
            Map<Integer, Rational> eq = new HashMap<Integer, Rational>();
            addSourceConst(eq, t, Rational.ONE);
            for (int k = 0; k < ps.size(); k++) add(eq, mu[k], Rational.of(-ps.get(k).constant()));
            add(eq, mu0, Rational.of(-1));
            pushEq(eq);
        }

        /** Encodes {@code guard(t) ⊨ ρ_source − ρ_target − ε_t ≥ 0} via Farkas. */
        void decreaseImplication(ItsTransition t) {
            List<ItsLinearExpression> ps = premises(t);
            int[] mu = new int[ps.size()];
            for (int k = 0; k < ps.size(); k++) mu[k] = next++;
            int mu0 = next++;
            for (String v : universe(t, true)) {
                Map<Integer, Rational> eq = new HashMap<Integer, Rational>();
                addSourceCoeff(eq, t, v, Rational.ONE);
                addTargetCoeff(eq, t, v, Rational.of(-1));     // − ρ_target
                for (int k = 0; k < ps.size(); k++) add(eq, mu[k], Rational.of(-ps.get(k).coefficient(v)));
                pushEq(eq);
            }
            Map<Integer, Rational> eq = new HashMap<Integer, Rational>();
            addSourceConst(eq, t, Rational.ONE);
            addTargetConst(eq, t, Rational.of(-1));
            add(eq, eps.get(t), Rational.of(-1));              // − ε_t (in the constant)
            for (int k = 0; k < ps.size(); k++) add(eq, mu[k], Rational.of(-ps.get(k).constant()));
            add(eq, mu0, Rational.of(-1));
            pushEq(eq);
        }

        private void pushEq(Map<Integer, Rational> eq) {
            rows.add(eq); ops.add(LinearProgram.Op.EQ); rhs.add(Rational.ZERO);
        }

        LinearProgram.Solution solveMaximisingStrictness(List<ItsTransition> active) {
            LinearProgram lp = new LinearProgram(next);
            for (int r = 0; r < rows.size(); r++)
                lp.addConstraint(dense(rows.get(r)), ops.get(r), rhs.get(r));
            Rational[] obj = new Rational[next];
            for (int j = 0; j < next; j++) obj[j] = Rational.ZERO;
            for (ItsTransition t : active) obj[eps.get(t)] = Rational.ONE;
            lp.setObjective(obj);
            return lp.solve();
        }

        private Rational[] dense(Map<Integer, Rational> sparse) {
            Rational[] r = new Rational[next];
            for (int j = 0; j < next; j++) r[j] = Rational.ZERO;
            for (Map.Entry<Integer, Rational> e : sparse.entrySet()) r[e.getKey()] = e.getValue();
            return r;
        }
    }
}
