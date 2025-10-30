package fr.univreunion.rati.ranking;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import apron.Abstract1;
import apron.ApronException;
import apron.Coeff;
import apron.Environment;
import apron.Lincons1;
import apron.Linexpr1;
import apron.Linterm1;
import apron.Manager;
import apron.MpqScalar;
import apron.Polka;
import apron.Scalar;

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

    private final Manager man = new Polka(false);

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
            Manager man = new Polka(false);
            LinkedHashSet<String> names = new LinkedHashSet<String>();
            for (ItsLinearConstraint c : t.constraints()) names.addAll(c.lhs().variables());
            Environment env = new Environment(new String[0], names.toArray(new String[0]));
            Abstract1 a = new Abstract1(man, env);   // ⊤
            List<Lincons1> cons = new ArrayList<Lincons1>();
            for (ItsLinearConstraint c : t.constraints()) cons.add(toLincons(env, c));
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
            Manager man = new Polka(false);
            LinkedHashSet<String> names = new LinkedHashSet<String>();
            if (premises != null) for (ItsLinearExpression p : premises) names.addAll(p.variables());
            names.addAll(rhoTerms.keySet());
            Environment env = new Environment(new String[0], names.toArray(new String[0]));
            Abstract1 a = new Abstract1(man, env);   // ⊤
            List<Lincons1> cons = new ArrayList<Lincons1>();
            if (premises != null) for (ItsLinearExpression p : premises) cons.add(geLincons(env, p));
            if (!cons.isEmpty()) a = a.meetCopy(man, cons.toArray(new Lincons1[0]));
            // Meet with ρ ≤ −1, encoded as −ρ − 1 ≥ 0 (Apron SUPEQ). The non-strict
            // form is exact over integers — ρ here is integer-scaled, so ρ ≥ 0 over
            // ℤ iff no integer point has ρ ≤ −1 — and, unlike a strict SUP, is not
            // silently relaxed by the loose (non-strict) Polka domain used here.
            List<Linterm1> terms = new ArrayList<Linterm1>();
            for (Map.Entry<String, Long> e : rhoTerms.entrySet())
                terms.add(new Linterm1(e.getKey(), new MpqScalar((int) -e.getValue())));
            Linexpr1 le = new Linexpr1(env, terms.toArray(new Linterm1[0]), new MpqScalar((int) (-rhoConst - 1)));
            a = a.meetCopy(man, new Lincons1(Lincons1.SUPEQ, le));
            return a.isBottom(man);
        } catch (ApronException e) {
            return false;   // could not prove ρ ≥ 0 ⇒ do not peel (sound)
        }
    }

    /** {@code expr ≥ 0} as an Apron constraint over {@code env}. */
    private static Lincons1 geLincons(Environment env, ItsLinearExpression expr) {
        List<Linterm1> terms = new ArrayList<Linterm1>();
        for (Map.Entry<String, Long> e : expr.coefficients().entrySet())
            terms.add(new Linterm1(e.getKey(), new MpqScalar((int) (long) e.getValue())));
        Linexpr1 le = new Linexpr1(env, terms.toArray(new Linterm1[0]), new MpqScalar((int) expr.constant()));
        return new Lincons1(Lincons1.SUPEQ, le);
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
            work.add(entry);
            int budget = 200 * Math.max(1, reachable.size());   // safety net (widening already bounds)
            while (!work.isEmpty() && budget-- > 0) {
                String loc = work.poll();
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
                        if (!work.contains(tgt)) work.add(tgt);
                    }
                }
            }

            // Descending iterations recover the bounds widening over-shot (e.g. a
            // counter's upper bound implied by the loop guard). Re-applying the
            // monotone transfer to a post-fixpoint stays sound and only tightens.
            descend(its, entry, reachable, bySource, inv);

            for (String loc : reachable) out.put(loc, toConstraints(inv.get(loc)));
        } catch (ApronException e) {
            throw new RuntimeException(e);
        }
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

        Environment full = new Environment(new String[0], names.toArray(new String[0]));
        Abstract1 a = src.changeEnvironmentCopy(man, full, false);

        List<Lincons1> cons = new ArrayList<Lincons1>();
        for (ItsLinearConstraint c : t.constraints()) cons.add(toLincons(full, c));
        for (int j = 0; j < res.length; j++) cons.add(resEq(full, res[j], t.updates().get(j)));
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

    /** {@code __res - expr = 0}. */
    private static Lincons1 resEq(Environment env, String res, ItsLinearExpression expr) {
        List<Linterm1> terms = new ArrayList<Linterm1>();
        terms.add(new Linterm1(res, new MpqScalar(1)));
        for (Map.Entry<String, Long> e : expr.coefficients().entrySet())
            terms.add(new Linterm1(e.getKey(), new MpqScalar((int) -e.getValue())));
        Linexpr1 le = new Linexpr1(env, terms.toArray(new Linterm1[0]), new MpqScalar((int) -expr.constant()));
        return new Lincons1(Lincons1.EQ, le);
    }

    private static Lincons1 toLincons(Environment env, ItsLinearConstraint c) {
        List<Linterm1> terms = new ArrayList<Linterm1>();
        for (Map.Entry<String, Long> e : c.lhs().coefficients().entrySet())
            terms.add(new Linterm1(e.getKey(), new MpqScalar((int) (long) e.getValue())));
        Linexpr1 le = new Linexpr1(env, terms.toArray(new Linterm1[0]), new MpqScalar((int) c.lhs().constant()));
        int kind = c.op() == ItsLinearConstraint.Op.EQ ? Lincons1.EQ
                 : c.op() == ItsLinearConstraint.Op.GT ? Lincons1.SUP : Lincons1.SUPEQ;
        return new Lincons1(kind, le);
    }

    /** Reads an Apron polyhedron back as ITS constraints over the same variable names. */
    private List<ItsLinearConstraint> toConstraints(Abstract1 a) throws ApronException {
        List<ItsLinearConstraint> out = new ArrayList<ItsLinearConstraint>();
        if (a.isBottom(man) || a.isTop(man)) return out;
        for (Lincons1 lc : a.toLincons(man)) {
            ItsLinearConstraint.Op op = ItsLinearConstraint.opFromApron(lc.getKind());
            if (op == null) continue;
            ItsLinearExpression.Builder b = new ItsLinearExpression.Builder();
            b.addConstant(scalarToLong(lc.getCst()));
            boolean anyVar = false;
            for (Linterm1 lt : lc.getLinterms()) {
                long co = scalarToLong(lt.getCoefficient());
                if (co == 0) continue;
                anyVar = true;
                b.addTerm(lt.getVariable().toString(), co);
            }
            if (!anyVar) continue;   // pure-constant facet carries no ranking information
            out.add(new ItsLinearConstraint(b.build(), op));
        }
        return out;
    }

    private static long scalarToLong(Coeff c) {
        if (c instanceof Scalar) {
            double[] d = new double[1];
            ((Scalar) c).toDouble(d, 0);
            return Math.round(d[0]);
        }
        return 0;
    }
}
