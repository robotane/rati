package fr.univreunion.rati.ranking;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import apron.ApronException;

import fr.univreunion.rati.its.IntegerTransitionSystem;
import fr.univreunion.rati.its.ItsLinearConstraint;
import fr.univreunion.rati.its.ItsLinearExpression;
import fr.univreunion.rati.its.ItsLocation;
import fr.univreunion.rati.its.ItsTransition;

/**
 * BINTERM — a faithful implementation of <em>Algorithm 1</em> of Spoto, Mesnard
 * &amp; Payet, <em>A Termination Analyser for Java Bytecode Based on Path-Length</em>
 * (ACM TOPLAS 2010, §7, p.50). This is the phase-5 termination prover that Julia
 * runs on a CLP(PL) program; here it runs on the path-length {@link
 * IntegerTransitionSystem} our front-end already produces.
 *
 * <p>The algorithm is a staged "try a cheap test, else the next, else UNKNOWN":
 * <pre>
 *   1: P1* ← binary unfoldings of P_CLP w.r.t. the polyhedral domain
 *   2: if every recursive rule of P1* has an affine ranking function: TERMINATES
 *   5: P2  ← abstraction w.r.t. the bounded-monotonicity domain
 *   6: P2* ← binary unfoldings of P2
 *   7: if every recursive rule of P2* has an affine ranking function: TERMINATES
 *  10: if for each SCC, each predicate has a (global) affine ranking function: TERMINATES
 *  13: else: UNKNOWN
 * </pre>
 *
 * <p>Mapping onto the components this repo already has (§7):
 * <ul>
 *   <li><b>Tier&nbsp;1</b> (polyhedra, lines&nbsp;1-2): the widened binary-unfolding
 *       loop relation {@code R_hh} of {@link BinUnfoldProbe#loopRelation}, ranked by
 *       a <em>single</em> affine function synthesised here by exact Farkas
 *       ({@link #affineRankable}). The polyhedral domain joins a predicate's calls by
 *       convex hull, so this faithfully <em>fails</em> on the lexicographic loop
 *       (the hull of "x₁ down" and "x₂ down" admits no single affine rank) — which is
 *       exactly why tier&nbsp;2 exists.</li>
 *   <li><b>Tier&nbsp;2</b> (bounded monotonicity, lines&nbsp;5-7): the no-Apron
 *       size-change test {@link SizeChangeTermination}. This is a faithful — not a
 *       stand-in — realisation of the paper's bounded-monotonicity tier: Codish,
 *       Lagoon &amp; Stuckey (ICLP 2005, <em>Testing for Termination with Monotonicity
 *       Constraints</em>, {@code docs/references/iclp05.pdf}) prove the
 *       monotonicity-constraint termination test is exactly the size-change approach —
 *       a size-change graph <em>is</em> a (bounded) monotonicity constraint between the
 *       in/out arguments, its composition closure <em>is</em> the binary unfolding on
 *       that domain, and the idempotent in-situ strict-thread test <em>is</em> the
 *       per-rule affine ranking. So lines&nbsp;5-7 over this domain and the SCT test
 *       decide the same loops; we run the latter (PTIME, no Apron). This is the tier
 *       that proves the lexicographic loop, which the convex hull of tier&nbsp;1 cannot.</li>
 *   <li><b>Tier&nbsp;3</b> (global per-SCC affine, line&nbsp;10): {@link FarkasRanking}
 *       — the Mesnard-Serebrenik global parametric affine ranking, which is what rati
 *       already does (and stronger).</li>
 *   <li><b>Call contexts</b> (improvement, all tiers): {@link ItsInvariants} gives a
 *       per-location reachable invariant; a transition that is infeasible under its
 *       source invariant is dropped before any tier runs (this disables the divergent
 *       clause of the BubbleSort/Double example — non-terminating in isolation, but
 *       unreachable from the entry context).</li>
 * </ul>
 *
 * <p><b>Soundness.</b> Every tier only ever <em>proves</em> termination; a failure
 * falls through. Dropping a call-context-infeasible transition is sound because the
 * invariant over-approximates the reachable states. So a {@link Verdict#TERMINATES}
 * is a real proof and a {@link Verdict#UNKNOWN} is "no proof found here".
 *
 * <p><b>Status.</b> Diagnostic / library form, not wired into any verdict pipeline.
 * The four worked examples of §7 (BubbleSort, div2, lex, gcd) are its acceptance
 * tests ({@code BinTermTest}), pinning that each lands at the faithful tier.
 */
public final class BinTerm {

    private BinTerm() {}

    /** Per-system verdict. */
    public enum Verdict { TERMINATES, UNKNOWN }

    /** The Algorithm-1 line that produced a {@link Verdict#TERMINATES}. */
    public enum Tier {
        /** No non-trivial SCC: acyclic, trivially terminating. */
        ACYCLIC,
        /** Line 2: polyhedral binary unfoldings + local affine ranking. */
        POLYHEDRAL,
        /** Line 7: bounded-monotonicity (size-change) ranking. */
        MONOTONICITY,
        /** Line 11: global per-SCC affine ranking (rati/Farkas). */
        GLOBAL,
        /** Line 13: no tier proved it. */
        NONE
    }

    /** Outcome of {@link #analyze}: the verdict and the tier that decided it. */
    public static final class Result {
        public final Verdict verdict;
        public final Tier tier;
        public final String detail;

        Result(Verdict verdict, Tier tier, String detail) {
            this.verdict = verdict; this.tier = tier; this.detail = detail;
        }

        public boolean terminates() { return verdict == Verdict.TERMINATES; }

        @Override public String toString() { return verdict + " (" + tier + ": " + detail + ")"; }
    }

    /**
     * Runs Algorithm 1 on {@code its} from {@code entry}. Apron (JNI) is required at
     * runtime for tiers 1 and 3 (the polyhedral closure and the Farkas LP); tier 2 is
     * pure Java.
     */
    public static Result analyze(IntegerTransitionSystem its, String entry) {
        Set<String> reachable = BinUnfoldProbe.reachableFrom(its, entry);

        // Raw supported/reachable graph — built WITHOUT any Apron pass, so the cheap
        // triage below pays nothing for the expensive call-context invariant.
        Map<String, List<ItsTransition>> rawBySource = new HashMap<String, List<ItsTransition>>();
        IntegerTransitionSystem raw = new IntegerTransitionSystem(its.name(), entry);
        for (String loc : reachable) {
            ItsLocation l = its.location(loc);
            if (l != null) raw.addLocation(l);
        }
        for (ItsTransition t : its.transitions()) {
            if (!t.isSupported()) continue;
            String s = t.source().name(), d = t.target().name();
            if (!reachable.contains(s) || !reachable.contains(d)) continue;
            rawBySource.computeIfAbsent(s, k -> new ArrayList<ItsTransition>()).add(t);
            raw.addTransition(t);
        }
        List<Set<String>> rawNonTrivial = new ArrayList<Set<String>>();
        for (Set<String> c : BinUnfoldProbe.sccs(reachable, rawBySource))
            if (BinUnfoldProbe.isCyclic(c, rawBySource)) rawNonTrivial.add(c);
        if (rawNonTrivial.isEmpty())
            return new Result(Verdict.TERMINATES, Tier.ACYCLIC, "no non-trivial reachable SCC");

        Result r;

        // (1) UNIVERSAL CHEAP TRIAGE: size-change termination, NO Apron, PTIME. On a
        //     Kitten-scale jar this proves the easy majority and bails on the rest in
        //     milliseconds — the real per-program-time lever (the expensive Apron tiers
        //     never run for these).
        if ((r = tryMonotonicity(raw, entry)) != null) return r;

        // (2) FAIL FAST WITHOUT APRON: if the cheap tier could not prove it and the
        //     largest SCC is too big to be worth the heavyweight tiers, punt to UNKNOWN
        //     immediately — no call-context invariant, no polyhedral closure, no global
        //     Farkas. These big dense SCCs are the basic-block-graph "Family-A" loops
        //     Julia also fails on; the win is failing in ms instead of grinding. Default
        //     is unbounded (no punt, fully complete); set {@code binterm.maxGlobalLoc} to
        //     trade completeness for speed on grinder-heavy jars.
        int maxScc = 0;
        for (Set<String> c : rawNonTrivial) maxScc = Math.max(maxScc, c.size());
        int cap = Integer.getInteger("binterm.maxGlobalLoc", Integer.MAX_VALUE);
        if (maxScc > cap)
            return new Result(Verdict.UNKNOWN, Tier.NONE,
                    "punted fast (no Apron): largest SCC " + maxScc
                    + " locations exceeds binterm.maxGlobalLoc=" + cap);

        // (3) SMALL RESIDUAL → the heavyweight Apron tiers. Only here do we pay for the
        //     call-context invariant (Algorithm-1 improvement): a per-location reachable
        //     invariant whose infeasible transitions are dropped (disables a divergent
        //     clause unreachable from the entry context).
        Map<String, List<ItsLinearConstraint>> inv;
        try {
            inv = ItsInvariants.compute(its, entry, reachable);
        } catch (RuntimeException | UnsatisfiedLinkError | NoClassDefFoundError e) {
            inv = Collections.emptyMap();   // no Apron / failure ⇒ no context (sound: weaker)
        }
        Map<String, List<ItsTransition>> bySource = new HashMap<String, List<ItsTransition>>();
        IntegerTransitionSystem filtered = new IntegerTransitionSystem(its.name(), entry);
        for (String loc : reachable) {
            ItsLocation l = its.location(loc);
            if (l != null) filtered.addLocation(l);
        }
        boolean droppedAny = false;
        for (ItsTransition t : its.transitions()) {
            if (!t.isSupported()) continue;
            String s = t.source().name(), d = t.target().name();
            if (!reachable.contains(s) || !reachable.contains(d)) continue;
            if (isContextInfeasible(t, inv.get(s))) { droppedAny = true; continue; }
            bySource.computeIfAbsent(s, k -> new ArrayList<ItsTransition>()).add(t);
            filtered.addTransition(t);
        }
        List<Set<String>> nonTrivial = new ArrayList<Set<String>>();
        for (Set<String> c : BinUnfoldProbe.sccs(reachable, bySource))
            if (BinUnfoldProbe.isCyclic(c, bySource)) nonTrivial.add(c);
        if (nonTrivial.isEmpty())
            return new Result(Verdict.TERMINATES, Tier.ACYCLIC,
                    "call context disabled the only divergent clause");

        // Tier 1 (polyhedra), then size-change again on the now context-filtered system
        // (the context may have removed a clause that blocked it), then the global tier.
        if ((r = tryPolyhedral(filtered, bySource, nonTrivial)) != null) return r;
        if (droppedAny && (r = tryMonotonicity(filtered, entry)) != null) return r;
        if ((r = tryGlobal(filtered, entry)) != null) return r;

        return new Result(Verdict.UNKNOWN, Tier.NONE, "no tier proved termination within budget");
    }

    // --------------------------------------------------------------- tier dispatch

    /** Tier 1 (lines 1-2), time-bounded; {@code null} if it does not prove the system. */
    private static Result tryPolyhedral(IntegerTransitionSystem its,
            Map<String, List<ItsTransition>> bySource, List<Set<String>> nonTrivial) {
        List<String> witnesses = new ArrayList<String>();
        if (Boolean.TRUE.equals(tier1Polyhedral(its, bySource, nonTrivial, witnesses)))
            return new Result(Verdict.TERMINATES, Tier.POLYHEDRAL,
                    "single affine ranking per binary-unfolding loop relation ["
                    + String.join("; ", witnesses) + "]");
        return null;
    }

    /** Tier 2 (lines 5-7), the cheap size-change test; {@code null} if it does not prove it. */
    private static Result tryMonotonicity(IntegerTransitionSystem its, String entry) {
        try {
            if (SizeChangeTermination.analyze(its, entry).terminates())
                return new Result(Verdict.TERMINATES, Tier.MONOTONICITY,
                        "every idempotent self-graph has an in-situ strict thread");
        } catch (RuntimeException ignored) { /* fall through */ }
        return null;
    }

    /** Tier 3 (line 11), the global per-SCC affine ranking; {@code null} if it does not prove it. */
    private static Result tryGlobal(IntegerTransitionSystem its, String entry) {
        try {
            if (FarkasRanking.prove(its, entry) == FarkasRanking.Verdict.TERMINATES)
                return new Result(Verdict.TERMINATES, Tier.GLOBAL,
                        "global per-SCC affine ranking (Mesnard-Serebrenik)");
        } catch (RuntimeException | UnsatisfiedLinkError | NoClassDefFoundError ignored) { /* fall through */ }
        return null;
    }

    // ----------------------------------------------------------------- tier 1

    /**
     * Tier 1, lines 1-2: every loop header's polyhedral binary-unfolding relation
     * {@code R_hh} must admit a single affine ranking function. Returns {@code TRUE}
     * if all do, {@code FALSE} if some header's relation is not affine-rankable, and
     * {@code null} if the closure could not be computed (no Apron / error) or the time
     * budget ran out — the caller treats both {@code FALSE} and {@code null} as "tier 1
     * did not prove it".
     *
     * <p>The widened polyhedral closure is the expensive part (seconds per header on a
     * dense Kitten SCC). Two caps bound it (handoff §8b.A — bounded proof): a per-header
     * closure cap {@code binterm.headerMs} (default 1500 ms) and a total tier budget
     * {@code binterm.tier1Ms} (default 4000 ms) checked between headers. Exceeding either
     * makes tier 1 inconclusive ({@code null}) and the cascade falls through — so a
     * grinder returns fast instead of grinding the whole SCC. Sound: a truncated closure
     * only weakens the relation, so we never wrongly rank.
     */
    private static Boolean tier1Polyhedral(IntegerTransitionSystem its,
            Map<String, List<ItsTransition>> bySource, List<Set<String>> nonTrivial,
            List<String> witnesses) {
        long headerMs = Long.getLong("binterm.headerMs", 1500L);
        long deadline = System.currentTimeMillis() + Long.getLong("binterm.tier1Ms", 4000L);
        try {
            for (Set<String> scc : nonTrivial) {
                for (String h : BinUnfoldProbe.feedbackVertexSet(scc, bySource)) {
                    if (System.currentTimeMillis() >= deadline) return null;   // budget out ⇒ inconclusive
                    List<ItsLinearConstraint> rhh =
                            BinUnfoldProbe.loopRelation(its, scc, bySource, h, headerMs);
                    if (rhh == null) continue;   // ⊥: no actual iteration, vacuously fine
                    AffineRank rank = affineRank(its.location(h).variables(), rhh);
                    if (rank == null) return Boolean.FALSE;
                    witnesses.add(h + ": " + rank);
                }
            }
            return Boolean.TRUE;
        } catch (ApronException | RuntimeException | UnsatisfiedLinkError | NoClassDefFoundError e) {
            return null;
        }
    }

    /**
     * Exact Farkas test: does a single affine function {@code f(x⃗) = Σ aᵥ·xᵥ + a₀}
     * exist that ranks the binary loop relation {@code R_hh} (given as constraints over
     * {@code I@v} = the loop entry's arguments and {@code C@v} = its arguments on the
     * next visit)? "Ranks" means {@code R_hh} entails both
     * {@code f(I) − f(C) ≥ 1} (strict decrease) and {@code f(I) ≥ 0} (bounded below).
     *
     * <p>By Farkas' lemma each entailment holds iff the target affine form is a
     * non-negative combination of the premises (the {@code R_hh} facts) plus a
     * non-negative constant. We encode both certificates as one exact-rational LP
     * feasibility ({@link LinearProgram}), sharing the template coefficients {@code aᵥ}.
     * Equalities are modelled as two opposed {@code ≥ 0} premises; the free template
     * coefficients are split into non-negative positive/negative parts. Feasible iff
     * a ranking function exists — and the constant term of the decrease certificate
     * forces a genuine (non-zero) certificate, so a {@code ⊤} relation is not rankable.
     *
     * <p>Returns the synthesised ranking function {@code f} as the proof's
     * <em>certificate</em> (the affine function the paper's tier 1 produces), or
     * {@code null} when none exists.
     */
    static AffineRank affineRank(List<String> formals, List<ItsLinearConstraint> rhh) {
        // Premises pᵢ ≥ 0: a ≥/> facet contributes its lhs; an equality contributes
        // its lhs and the negation (lhs ≥ 0 ∧ −lhs ≥ 0). A strict > is weakened to ≥,
        // which only makes the premise weaker — sound (never a false rank).
        List<ItsLinearExpression> prem = new ArrayList<ItsLinearExpression>();
        for (ItsLinearConstraint c : rhh) {
            prem.add(c.lhs());
            if (c.op() == ItsLinearConstraint.Op.EQ) prem.add(negate(c.lhs()));
        }
        int n = formals.size();
        int nP = prem.size();

        // Unknown layout:
        //   a[v]           : aᵥ                       (native free)
        //   a0             : a₀                       (native free)
        //   lamD[i], lam0D : decrease certificate     (≥ 0)
        //   lamB[i], lam0B : boundedness certificate  (≥ 0)
        int A = 0, A0 = n;
        int LAMD = n + 1, LAM0D = LAMD + nP;
        int LAMB = LAM0D + 1, LAM0B = LAMB + nP;
        int numVars = LAM0B + 1;

        LinearProgram lp = new LinearProgram(numVars);
        for (int vi = 0; vi <= n; vi++) lp.markFree(A + vi);   // a_v and a_0 unrestricted

        for (int target = 0; target < 2; target++) {           // 0 = decrease, 1 = boundedness
            boolean decrease = target == 0;
            int lam = decrease ? LAMD : LAMB;
            int lam0 = decrease ? LAM0D : LAM0B;

            // Monomial I@v: coeff of f(I)−f(C)−1 is aᵥ (decrease) / coeff of f(I) is aᵥ.
            for (int vi = 0; vi < n; vi++) {
                Rational[] row = zeros(numVars);
                row[A + vi] = Rational.ONE;
                String iv = "I@" + formals.get(vi);
                for (int i = 0; i < nP; i++)
                    addCoeff(row, lam + i, -prem.get(i).coefficient(iv));
                lp.addConstraint(row, LinearProgram.Op.EQ, Rational.ZERO);
            }
            // Monomial C@v: coeff is −aᵥ (decrease) / 0 (boundedness).
            for (int vi = 0; vi < n; vi++) {
                Rational[] row = zeros(numVars);
                if (decrease) row[A + vi] = NEG_ONE;
                String cv = "C@" + formals.get(vi);
                for (int i = 0; i < nP; i++)
                    addCoeff(row, lam + i, -prem.get(i).coefficient(cv));
                lp.addConstraint(row, LinearProgram.Op.EQ, Rational.ZERO);
            }
            // Constant monomial: decrease has known constant −1 (⇒ rhs 1); boundedness
            // has a₀.
            Rational[] row = zeros(numVars);
            Rational rhs;
            if (decrease) {
                rhs = Rational.ONE;
            } else {
                row[A0] = Rational.ONE;
                rhs = Rational.ZERO;
            }
            for (int i = 0; i < nP; i++)
                addCoeff(row, lam + i, -prem.get(i).constant());
            addCoeff(row, lam0, -1);
            lp.addConstraint(row, LinearProgram.Op.EQ, rhs);
        }

        LinearProgram.Solution s = lp.solve();
        if (!s.feasible) return null;
        Rational[] a = new Rational[n];
        for (int vi = 0; vi < n; vi++) a[vi] = s.x[A + vi];
        Rational a0 = s.x[A0];
        return new AffineRank(formals, a, a0);
    }

    /** Boolean form of {@link #affineRank}. */
    static boolean affineRankable(List<String> formals, List<ItsLinearConstraint> rhh) {
        return affineRank(formals, rhh) != null;
    }

    /**
     * A synthesised single affine ranking function {@code f(x⃗) = Σ aᵥ·xᵥ + a₀} — the
     * certificate of a tier-1 proof (the affine function the paper produces for a
     * binary recursive rule). The coefficients are exact rationals.
     */
    static final class AffineRank {
        final List<String> formals;
        final Rational[] a;
        final Rational a0;

        AffineRank(List<String> formals, Rational[] a, Rational a0) {
            this.formals = formals; this.a = a; this.a0 = a0;
        }

        @Override public String toString() {
            StringBuilder sb = new StringBuilder("f = ");
            boolean first = true;
            for (int i = 0; i < a.length; i++) {
                if (a[i].isZero()) continue;
                if (!first) sb.append(" + ");
                sb.append(a[i]).append("·").append(formals.get(i));
                first = false;
            }
            if (!a0.isZero() || first) sb.append(first ? "" : " + ").append(a0);
            return sb.toString();
        }
    }

    // ----------------------------------------------------------------- helpers

    /** Treats a transition as droppable iff its guard is empty under its source context. */
    private static boolean isContextInfeasible(ItsTransition t, List<ItsLinearConstraint> srcInv) {
        try {
            return ItsInvariants.isInfeasibleUnder(t, srcInv);
        } catch (RuntimeException | UnsatisfiedLinkError | NoClassDefFoundError e) {
            return false;   // undecided ⇒ keep the transition (sound)
        }
    }

    private static ItsLinearExpression negate(ItsLinearExpression e) {
        ItsLinearExpression.Builder b = new ItsLinearExpression.Builder();
        for (Map.Entry<String, Long> t : e.coefficients().entrySet())
            b.addTerm(t.getKey(), -t.getValue());
        b.addConstant(-e.constant());
        return b.build();
    }

    private static final Rational NEG_ONE = Rational.ONE.negate();

    private static Rational[] zeros(int n) {
        Rational[] a = new Rational[n];
        for (int i = 0; i < n; i++) a[i] = Rational.ZERO;
        return a;
    }

    private static void addCoeff(Rational[] row, int idx, long delta) {
        if (delta != 0) row[idx] = row[idx].add(Rational.of(delta));
    }
}
