package fr.univreunion.rati.ranking;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import apron.Abstract1;
import apron.ApronException;
import apron.Environment;
import apron.Lincons1;
import apron.Linexpr1;
import apron.Manager;

import fr.univreunion.rati.its.IntegerTransitionSystem;
import fr.univreunion.rati.its.ItsLinearConstraint;
import fr.univreunion.rati.its.ItsLinearExpression;
import fr.univreunion.rati.its.ItsLocation;
import fr.univreunion.rati.its.ItsTransition;

/**
 * Forward polyhedral invariant generation over an {@link IntegerTransitionSystem}
 * (standard convex-polyhedra abstract interpretation with widening, Cousot &amp;
 * Halbwachs 1978, on Apron's {@code Polka}).
 *
 * <p>This is the invariant half of the "invariants + ranking" pipeline: a Farkas
 * ranking ({@link FarkasRanking}) on a loop whose boundedness depends on a fact
 * established <em>before</em> the loop (e.g. a counter never exceeds its bound,
 * or a length stays {@code ≥ 0}) cannot succeed from the per-transition guards
 * alone. We over-approximate the reachable state at each location and feed that
 * invariant into the ranking LP as an extra Farkas premise — sound because a
 * transition only ever fires from a reachable source state.
 *
 * <p>The result for a location is expressed as {@link ItsLinearConstraint}s over
 * that location's own formal variables, so {@code FarkasRanking} consumes them
 * without touching Apron.
 */
public final class ItsInvariants {

    /** Joins before widening kicks in on a location (keeps a little precision first). */
    private static final int WIDEN_DELAY = 2;

    private static final boolean DEBUG = Boolean.getBoolean("rati.rankingDebug");

    /**
     * Deterministic budget on Apron post-image WORK in one invariant computation —
     * the running sum of each {@link #postImage}'s environment dimension. The
     * worklist's step budget ({@code 200·|reachable|}) bounds the number of iterations
     * but not their cost: on a dense, deeply mutually-recursive reachable graph (e.g. a
     * Kitten visitor where {@code checkForDeadcode} of every statement kind sits in one
     * SCC) each post-image is a high-dimensional polyhedral transfer (change-environment
     * + meet + project), super-linear in the dimension, so the fixpoint grinds tens of
     * seconds while the step count stays modest. Charging by dimension bounds that grind
     * deterministically (run-to-run identical, unlike a wall clock).
     *
     * <p>On exhaustion the whole computation is abandoned (a {@link RuntimeException} the
     * caller — {@link FarkasRanking#prove} — turns into an empty invariant map): a
     * half-finished worklist holds under-approximations (locations not yet reached along
     * every path), which would be UNSOUND as Farkas premises, so all invariants are
     * dropped. Sound, since absent invariants only ever forgo a proof, never fabricate
     * one. {@code -Drati.invariantOpBudget=N} overrides it; {@code 0} disables it.
     *
     * <p>Calibrated on the Julia09 corpus: the heaviest invariant-dependent proof
     * (KnapsackDP.SolveDP) charges ≈4.2·10³, every other proof less, while a dense Kitten
     * visitor SCC passes 1.2·10⁵. The {@code 1·10⁴} default clears every measured proof
     * (≈2.4× margin) yet bounds the grinder's fixpoint much sooner than the headroom alone
     * would suggest is safe: a Kitten (774) + Julia09 (36) sweep at 5·10⁴ → 1·10⁴ → 5·10³
     * → 2·10³ left the verdict of every one of the 810 methods byte-identical (664
     * TERMINATES / 137 UNKNOWN at every budget — the grinders pass the budget without it
     * ever buying them a proof), while cutting the aggregate rati wall by 37% at 1·10⁴
     * (≈50% at 2·10³). 1·10⁴ banks the bulk of that win at a comfortable margin over the
     * heaviest real proof; tighten further (down to ≈3·10³) only with a fresh CeTA byte-id
     * check, since a dropped invariant can change a certificate even when the verdict holds.
     */
    private static final long INV_OP_BUDGET = Long.getLong("rati.invariantOpBudget", 10_000L);

    private final Manager man = ApronManagers.polka();
    private long invOpSpent;   // per-compute cumulative post-image work; single-threaded

    private ItsInvariants() {}

    /** Computes a per-location invariant (over each location's formals) for the reachable sub-ITS. */
    public static Map<String, List<ItsLinearConstraint>> compute(
            IntegerTransitionSystem its, String entry, Set<String> reachable) {
        return new ItsInvariants().run(its, entry, reachable);
    }

    /**
     * True when {@code t}'s guard polyhedron is empty — the transition can never
     * fire, so it is irrelevant to termination and may be dropped. This in
     * particular removes self-contradictory <em>identity</em> self-loops
     * ({@code f(x⃗) -> f(x⃗) :|: A≥B+1 && B≥A}) which a ranking function can never
     * orient (ρ_source − ρ_target ≡ 0) and which would otherwise block the SCC.
     * Conservative: a guard Apron cannot refute is kept (returns {@code false}).
     */
    public static boolean isInfeasible(ItsTransition t) {
        try {
            Manager man = ApronManagers.polka();
            LinkedHashSet<String> names = new LinkedHashSet<String>();
            for (ItsLinearConstraint c : t.constraints()) names.addAll(c.lhs().variables());
            Environment env = new Environment(new String[0], names.toArray(new String[0]));
            Abstract1 a = new Abstract1(man, env);   // ⊤
            List<Lincons1> cons = new ArrayList<Lincons1>();
            for (ItsLinearConstraint c : t.constraints()) cons.add(ApronBridge.toLincons(env, c));
            if (!cons.isEmpty()) a = a.meetCopy(man, cons.toArray(new Lincons1[0]));
            return a.isBottom(man);
        } catch (ApronException e) {
            return false;   // undecided ⇒ keep the transition (sound)
        }
    }

    /**
     * True when {@code t} can never fire from a state satisfying its source
     * location's invariant — i.e. {@code srcInvariant ∧ guard} is empty. Unlike
     * {@link #isInfeasible}, which tests the guard in isolation, this also rules out
     * transitions that are individually satisfiable yet <em>unreachable</em>: e.g.
     * the {@code x ≤ −1} half of a split {@code x != 0} guard under a source
     * invariant {@code x ≥ 0} (an array index/length), or the {@code i ≥ n+1} half of
     * a split {@code i != n} under {@code i ≤ n}. Dropping such a half is sound (it
     * fires from no reachable state, since the invariant over-approximates the
     * reachable states) and keeps the {@code !=}-split from leaving a spurious
     * divergent transition that no ranking function can orient — which would
     * otherwise sink the SCC into the expensive disjunctive fallback. The source
     * invariant uses the location's formals (the {@code LIk} / {@code SIk} names),
     * the same names the guard's input side carries, so they conjoin directly.
     * Conservative: anything
     * Apron cannot refute is kept (returns {@code false}).
     */
    public static boolean isInfeasibleUnder(ItsTransition t, List<ItsLinearConstraint> srcInvariant) {
        if (srcInvariant == null || srcInvariant.isEmpty()) return isInfeasible(t);
        try {
            Manager man = ApronManagers.polka();
            LinkedHashSet<String> names = new LinkedHashSet<String>();
            for (ItsLinearConstraint c : t.constraints()) names.addAll(c.lhs().variables());
            for (ItsLinearConstraint c : srcInvariant) names.addAll(c.lhs().variables());
            Environment env = new Environment(new String[0], names.toArray(new String[0]));
            Abstract1 a = new Abstract1(man, env);   // ⊤
            List<Lincons1> cons = new ArrayList<Lincons1>();
            for (ItsLinearConstraint c : t.constraints()) cons.add(ApronBridge.toLincons(env, c));
            for (ItsLinearConstraint c : srcInvariant) cons.add(ApronBridge.toLincons(env, c));
            if (!cons.isEmpty()) a = a.meetCopy(man, cons.toArray(new Lincons1[0]));
            return a.isBottom(man);
        } catch (ApronException e) {
            return false;   // undecided ⇒ keep the transition (sound)
        }
    }

    /**
     * True when the premises (each {@link ItsLinearExpression} {@code p} read as
     * {@code p ≥ 0}, exactly as {@link FarkasRanking} feeds its Farkas LP) entail
     * {@code Σ rhoTerms·v + rhoConst ≥ 0}, i.e. the polyhedron
     * {@code premises ∧ (ρ < 0)} is empty. Used as the boundedness filter of the
     * relaxed ADFG round: a ranking component need only be bounded below on the
     * transitions it strictly decreases, not on every active one. Conservative:
     * an entailment Apron cannot establish returns {@code false} (the transition
     * is simply not peeled — never unsound).
     */
    public static boolean entailsNonNegative(List<ItsLinearExpression> premises,
                                             Map<String, Long> rhoTerms, long rhoConst) {
        try {
            Manager man = ApronManagers.polka();
            LinkedHashSet<String> names = new LinkedHashSet<String>();
            if (premises != null) for (ItsLinearExpression p : premises) names.addAll(p.variables());
            names.addAll(rhoTerms.keySet());
            Environment env = new Environment(new String[0], names.toArray(new String[0]));
            Abstract1 a = new Abstract1(man, env);   // ⊤
            List<Lincons1> cons = new ArrayList<Lincons1>();
            if (premises != null)
                for (ItsLinearExpression p : premises) cons.add(ApronBridge.geLincons(env, p));
            if (!cons.isEmpty()) a = a.meetCopy(man, cons.toArray(new Lincons1[0]));
            // Meet with ρ ≤ −1, encoded as −ρ − 1 ≥ 0 (Apron SUPEQ). The non-strict
            // form is exact over integers — ρ here is integer-scaled, so ρ ≥ 0 over
            // ℤ iff no integer point has ρ ≤ −1 — and, unlike a strict SUP, is not
            // silently relaxed by the loose (non-strict) Polka domain used here.
            // Built in BigInteger: ρ's coefficients are lcm-scaled LP values, exactly
            // the kind an (int) cast would silently truncate.
            Map<String, BigInteger> neg = new LinkedHashMap<String, BigInteger>();
            for (Map.Entry<String, Long> e : rhoTerms.entrySet())
                neg.put(e.getKey(), BigInteger.valueOf(e.getValue()).negate());
            Linexpr1 le = ApronBridge.linexpr(env, neg,
                    BigInteger.valueOf(rhoConst).negate().subtract(BigInteger.ONE));
            a = a.meetCopy(man, new Lincons1(Lincons1.SUPEQ, le));
            return a.isBottom(man);
        } catch (ApronException e) {
            return false;   // could not prove ρ ≥ 0 ⇒ do not peel (sound)
        }
    }

    private Map<String, List<ItsLinearConstraint>> run(
            IntegerTransitionSystem its, String entry, Set<String> reachable) {
        Map<String, List<ItsLinearConstraint>> out = new HashMap<String, List<ItsLinearConstraint>>();
        try {
            // Transitions grouped by source, restricted to the reachable sub-graph.
            Map<String, List<ItsTransition>> bySource = new HashMap<String, List<ItsTransition>>();
            for (ItsTransition t : its.transitions()) {
                if (!t.isSupported()) continue;
                if (!reachable.contains(t.source().name()) || !reachable.contains(t.target().name())) continue;
                bySource.computeIfAbsent(t.source().name(), k -> new ArrayList<ItsTransition>()).add(t);
            }

            Map<String, Abstract1> inv = new HashMap<String, Abstract1>();
            for (String loc : reachable)
                inv.put(loc, new Abstract1(man, envOf(its.location(loc)), true));   // ⊥
            inv.put(entry, new Abstract1(man, envOf(its.location(entry))));          // ⊤

            Map<String, Integer> visits = new HashMap<String, Integer>();
            Deque<String> work = new ArrayDeque<String>();
            Set<String> inWork = new java.util.HashSet<String>();   // O(1) membership, vs O(n) Deque.contains
            work.add(entry);
            inWork.add(entry);
            int budget = 200 * Math.max(1, reachable.size());   // safety net (widening already bounds)
            while (!work.isEmpty() && budget-- > 0) {
                String loc = work.poll();
                inWork.remove(loc);
                Abstract1 src = inv.get(loc);
                if (src.isBottom(man)) continue;
                for (ItsTransition t : bySource.getOrDefault(loc, java.util.Collections.emptyList())) {
                    String tgt = t.target().name();
                    Abstract1 post = postImage(src, t);
                    Abstract1 old = inv.get(tgt);
                    Abstract1 joined = old.joinCopy(man, post);
                    int v = visits.getOrDefault(tgt, 0) + 1;
                    visits.put(tgt, v);
                    if (v > WIDEN_DELAY) joined = old.widening(man, joined);
                    if (!joined.isIncluded(man, old)) {   // grew ⇒ propagate
                        inv.put(tgt, joined);
                        if (inWork.add(tgt)) work.add(tgt);
                    }
                }
            }

            // Descending iterations recover the bounds widening over-shot (e.g. a
            // counter's upper bound implied by the loop guard). Re-applying the
            // monotone transfer to a post-fixpoint stays sound and only tightens.
            descend(its, entry, reachable, bySource, inv);

            // Exact read-back; a conjunct beyond the long model is dropped, which
            // only weakens the invariant — the sound direction for a premise.
            for (String loc : reachable) out.put(loc, ApronBridge.toConstraints(man, inv.get(loc)));
        } catch (ApronException e) {
            throw new RuntimeException(e);
        }
        if (DEBUG) System.err.println("[invariants] opWork=" + invOpSpent);
        return out;
    }

    /** Narrowing passes: {@code K} sound descending re-applications of the transfer. */
    private static final int DESCEND_PASSES = 4;

    private void descend(IntegerTransitionSystem its, String entry, Set<String> reachable,
            Map<String, List<ItsTransition>> bySource, Map<String, Abstract1> inv) throws ApronException {
        // Incoming transitions per target, over the reachable sub-graph.
        Map<String, List<ItsTransition>> byTarget = new HashMap<String, List<ItsTransition>>();
        for (List<ItsTransition> ts : bySource.values())
            for (ItsTransition t : ts)
                byTarget.computeIfAbsent(t.target().name(), k -> new ArrayList<ItsTransition>()).add(t);

        for (int pass = 0; pass < DESCEND_PASSES; pass++) {
            Map<String, Abstract1> next = new HashMap<String, Abstract1>();
            for (String loc : reachable) {
                if (loc.equals(entry)) { next.put(loc, inv.get(loc)); continue; }   // entry stays ⊤
                List<ItsTransition> incoming = byTarget.getOrDefault(loc, java.util.Collections.emptyList());
                Abstract1 acc = new Abstract1(man, envOf(its.location(loc)), true);  // ⊥
                for (ItsTransition t : incoming) {
                    Abstract1 srcInv = inv.get(t.source().name());
                    if (srcInv.isBottom(man)) continue;
                    acc = acc.joinCopy(man, postImage(srcInv, t));
                }
                // Sound only as a tightening: keep within the current (post-fixpoint) value.
                Abstract1 cur = inv.get(loc);
                next.put(loc, acc.isIncluded(man, cur) ? acc : cur);
            }
            inv.putAll(next);
        }
    }

    // -------------------------------------------------------------------------

    /** Post-image of {@code src} (over source formals) through {@code t}, over target formals. */
    private Abstract1 postImage(Abstract1 src, ItsTransition t) throws ApronException {
        List<String> sv = t.source().variables();
        List<String> tv = t.target().variables();

        // Combined environment: source formals ∪ all guard/update vars ∪ fresh result vars.
        Set<String> names = new LinkedHashSet<String>(sv);
        for (ItsLinearConstraint c : t.constraints()) names.addAll(c.lhs().variables());
        for (ItsLinearExpression e : t.updates()) names.addAll(e.variables());
        String[] res = new String[tv.size()];
        for (int j = 0; j < res.length; j++) { res[j] = "__res" + j; names.add(res[j]); }

        // Charge this post-image by its polyhedral dimension (the cost driver) and abort
        // the whole fixpoint — sound, via an empty invariant map — once the budget is spent.
        invOpSpent += names.size();
        if (INV_OP_BUDGET > 0 && invOpSpent > INV_OP_BUDGET)
            throw new RuntimeException("invariant op budget exhausted at " + invOpSpent);

        Environment full = new Environment(new String[0], names.toArray(new String[0]));
        Abstract1 a = src.changeEnvironmentCopy(man, full, false);

        List<Lincons1> cons = new ArrayList<Lincons1>();
        for (ItsLinearConstraint c : t.constraints()) cons.add(ApronBridge.toLincons(full, c));
        for (int j = 0; j < res.length; j++)
            cons.add(ApronBridge.bindEq(full, res[j], t.updates().get(j)));
        a = a.meetCopy(man, cons.toArray(new Lincons1[0]));

        // Project onto the result vars, then rename them to the target formals.
        Environment resEnv = new Environment(new String[0], res.clone());
        a = a.changeEnvironmentCopy(man, resEnv, true);
        if (res.length > 0) a = a.renameCopy(man, res.clone(), tv.toArray(new String[0]));

        // Normalise to exactly the target-formal environment.
        Environment tgtEnv = new Environment(new String[0], tv.toArray(new String[0]));
        return a.changeEnvironmentCopy(man, tgtEnv, false);
    }

    private static Environment envOf(ItsLocation loc) {
        return new Environment(new String[0], loc.variables().toArray(new String[0]));
    }

}
