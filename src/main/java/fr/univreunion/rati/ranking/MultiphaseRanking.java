package fr.univreunion.rati.ranking;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fr.univreunion.rati.its.ItsLinearConstraint;
import fr.univreunion.rati.its.ItsLinearExpression;
import fr.univreunion.rati.its.ItsLocation;
import fr.univreunion.rati.its.ItsTransition;

/**
 * Multiphase-linear ranking function (MΦRF) synthesis for an SCC — the
 * Ben-Amram &amp; Genaim algorithm (CAV 2017, "On Multiphase-Linear Ranking
 * Functions"). Proves loops that progress through several <em>phases</em>, each
 * ranked by a different linear function (e.g. a quantity grows while a second is
 * positive, then shrinks) — beyond a single lexicographic linear ranking.
 *
 * <p>By their Theorem 3.4, a loop has a MΦRF of depth ≤ d iff it has a
 * <em>nested</em> ranking function of depth ≤ d, whose synthesis is a single
 * Farkas LP. A nested RF ⟨f_1,…,f_d⟩ for a transition (x → x'), with
 * Δf(x,x') = f(x) − f(x') and f_0 ≡ 0, satisfies for all transitions:
 * <pre>
 *   (12)   f_d(x) ≥ 0
 *   (13_i) (Δf_i(x,x') − 1) + f_{i−1}(x) ≥ 0     for i = 1..d
 * </pre>
 * (Definition 3.1 of the paper.) We try increasing depths until one is feasible
 * (TERMINATES) or the cap is reached (UNKNOWN). Each condition is a Farkas
 * implication over the SCC's transition guards plus their source invariants,
 * solved with the exact-rational {@link LinearProgram} — sound by construction.
 *
 * <p>Used only as a fallback after the lexicographic {@link FarkasRanking} on a
 * non-trivial SCC, so it can only turn UNKNOWN into TERMINATES.
 */
final class MultiphaseRanking {

    /** Max MΦRF depth attempted (number of phases). Tunable for an exotic deep phase
     *  loop; the degenerate-grind cost is bounded by the tier-local pivot budget (see
     *  {@link LinearProgram#MPHI_WORK_BUDGET}), not by capping depth, so full depth-4
     *  capability is kept. */
    private static final int MAX_DEPTH = Math.max(1, Integer.getInteger("rati.mphiMaxDepth", 4));

    private MultiphaseRanking() {}

    /**
     * Synthesises a MΦRF of depth ≤ {@link #MAX_DEPTH} for the SCC and surfaces its
     * components ({@link FarkasRanking.MphiCert}), or returns {@code null} when none
     * exists. Sound by construction (exact-rational LP); the returned functions are
     * the witness the CPF exporter turns into a per-phase {@code transitionRemoval}
     * chain.
     */
    static FarkasRanking.MphiCert rank(List<ItsTransition> transitions,
                       Map<String, List<ItsLinearConstraint>> invariants) {
        List<String> locs = locationsOf(transitions);
        // Bound the depth-1..MAX_DEPTH search with a tier-local pivot budget. On a loop that
        // admits NO MΦRF the exact-rational nested-RF simplex degenerates into a multi-second
        // grind whose pivots the GLOBAL budget is too coarse to bound (it is sized for the
        // lexicographic tier, where a genuinely-hard proof like BubbleSort.sort legitimately
        // spends ~15 s). Charged separately, so a degenerate MΦRF grind (Numerical3's gcd —
        // ~5·10⁸ pivots / 20 s) is cut to a sub-second UNKNOWN while a real MΦRF rank (found
        // fast, few pivots) and every lexicographic proof are untouched. Sound: exhaustion
        // forgoes the MΦRF step (→ UNKNOWN), never fabricates a TERMINATES.
        LinearProgram.beginMphiWindow();
        try {
            for (int d = 1; d <= MAX_DEPTH; d++) {
                FarkasRanking.MphiCert r = new Builder(invariants, d, locs).extract(transitions);
                if (r != null) return r;
            }
            return null;
        } finally {
            LinearProgram.endMphiWindow();
        }
    }

    /** True iff the SCC's transitions admit a MΦRF of depth ≤ {@link #MAX_DEPTH}. */
    static boolean ranks(List<ItsTransition> transitions,
                         Map<String, List<ItsLinearConstraint>> invariants) {
        return rank(transitions, invariants) != null;
    }

    private static List<String> locationsOf(List<ItsTransition> ts) {
        Set<String> names = new LinkedHashSet<String>();
        for (ItsTransition t : ts) { names.add(t.source().name()); names.add(t.target().name()); }
        List<String> l = new ArrayList<String>(names);
        java.util.Collections.sort(l);
        return l;
    }

    // -------------------------------------------------------------------------

    private static final class Builder {
        final Map<String, List<ItsLinearConstraint>> invariants;
        final int d;
        int next = 0;
        // λ_{i,loc}: free (unrestricted-in-sign) coefficients of phase i's template at a
        // location (index arity ⇒ the constant term). Keyed "i|loc". Declared as native
        // free LP columns (markFree) rather than a pos − neg split.
        final Map<String, int[]> lam = new HashMap<String, int[]>();
        final List<Integer> freeVars = new ArrayList<Integer>();
        final Map<String, Integer> arity = new HashMap<String, Integer>();
        final List<Map<Integer, Rational>> rows = new ArrayList<Map<Integer, Rational>>();
        final List<LinearProgram.Op> ops = new ArrayList<LinearProgram.Op>();
        final List<Rational> rhs = new ArrayList<Rational>();

        Builder(Map<String, List<ItsLinearConstraint>> invariants, int d, List<String> locs) {
            this.invariants = invariants;
            this.d = d;
            for (String loc : locs) arity.put(loc, -1);   // arity learned from transitions
        }

        /** Builds the nested-RF feasibility LP (Def 3.1 conditions) over the SCC. */
        private LinearProgram buildLp(List<ItsTransition> transitions) {
            // Learn each location's arity from the transitions it appears in.
            for (ItsTransition t : transitions) {
                arity.put(t.source().name(), t.source().arity());
                arity.put(t.target().name(), t.target().arity());
            }
            for (int i = 1; i <= d; i++)
                for (Map.Entry<String, Integer> e : arity.entrySet())
                    allocLambda(i, e.getKey(), e.getValue());

            for (ItsTransition t : transitions) {
                // (13_i): (f_i(src) − f_i(tgt) − 1) + f_{i−1}(src) ≥ 0
                for (int i = 1; i <= d; i++) {
                    List<Term> e = new ArrayList<Term>();
                    e.add(new Term(i, true, Rational.ONE));      // + f_i(src)
                    e.add(new Term(i, false, Rational.of(-1)));  // − f_i(tgt)
                    if (i > 1) e.add(new Term(i - 1, true, Rational.ONE));  // + f_{i−1}(src)
                    implication(t, e, Rational.of(-1));          // constant −1
                }
                // (12): f_d(src) ≥ 0
                List<Term> e = new ArrayList<Term>();
                e.add(new Term(d, true, Rational.ONE));
                implication(t, e, Rational.ZERO);
            }
            LinearProgram lp = new LinearProgram(next);
            for (int v : freeVars) lp.markFree(v);
            for (int r = 0; r < rows.size(); r++) lp.addConstraint(dense(rows.get(r)), ops.get(r), rhs.get(r));
            return lp;
        }

        /**
         * Solves the depth-{@code d} LP and, when feasible, reads the phase functions
         * {@code f_1,…,f_d} off the λ solution — one integer-scaled coefficient vector
         * per location and phase. Returns {@code null} when no MΦRF of this depth exists.
         */
        FarkasRanking.MphiCert extract(List<ItsTransition> transitions) {
            LinearProgram.Solution sol = buildLp(transitions).solve();
            if (!sol.feasible || sol.x == null) return null;
            List<String> locs = new ArrayList<String>(arity.keySet());
            java.util.Collections.sort(locs);
            List<Map<String, long[]>> phases = new ArrayList<Map<String, long[]>>();
            for (int i = 1; i <= d; i++) phases.add(scalePhase(i, locs, sol.x));
            return new FarkasRanking.MphiCert(d, phases);
        }

        /**
         * Integer-scaled {@code f_i} for every location, scaled by ONE common
         * denominator (the lcm over the phase's coefficients) so each phase function
         * is integer-valued — a uniform positive scale preserves both its sign region
         * ({@code f_i≤0}/{@code f_i≥1}) and the strict decrease a CeTA transitionRemoval
         * checks. Mirrors {@link FarkasRanking.Builder#scaledRound}.
         */
        private Map<String, long[]> scalePhase(int i, List<String> locs, Rational[] x) {
            Map<String, Rational[]> raw = new java.util.LinkedHashMap<String, Rational[]>();
            java.math.BigInteger den = java.math.BigInteger.ONE;
            for (String loc : locs) {
                int[] l = lam.get(i + "|" + loc);
                if (l == null) continue;
                Rational[] r = new Rational[l.length];
                for (int k = 0; k < l.length; k++) {
                    r[k] = x[l[k]];
                    java.math.BigInteger dn = r[k].denominator();
                    den = den.divide(den.gcd(dn)).multiply(dn);   // lcm of all denominators
                }
                raw.put(loc, r);
            }
            Map<String, long[]> out = new java.util.LinkedHashMap<String, long[]>();
            for (Map.Entry<String, Rational[]> e : raw.entrySet()) {
                Rational[] r = e.getValue();
                long[] c = new long[r.length];
                for (int k = 0; k < r.length; k++)
                    c[k] = r[k].numerator().multiply(den).divide(r[k].denominator()).longValueExact();
                out.put(e.getKey(), c);
            }
            return out;
        }

        private void allocLambda(int i, String loc, int ar) {
            String key = i + "|" + loc;
            if (lam.containsKey(key)) return;
            int[] l = new int[ar + 1];
            for (int k = 0; k <= ar; k++) { l[k] = next++; freeVars.add(l[k]); }
            lam.put(key, l);
        }

        /** A signed reference to a phase function evaluated at a transition endpoint. */
        private static final class Term {
            final int phase; final boolean source; final Rational sign;
            Term(int phase, boolean source, Rational sign) { this.phase = phase; this.source = source; this.sign = sign; }
        }

        /**
         * Encodes {@code guard(t) ∧ inv(src) ⊨ (Σ terms) + cst ≥ 0} via Farkas:
         * the linear form's coefficients (in the λ unknowns) must equal a
         * non-negative combination of the premises (+ a non-negative slack μ0).
         */
        private void implication(ItsTransition t, List<Term> terms, Rational cst) {
            List<ItsLinearExpression> ps = premises(t);
            int[] mu = new int[ps.size()];
            for (int k = 0; k < ps.size(); k++) mu[k] = next++;
            int mu0 = next++;

            for (String v : universe(t, terms, ps)) {
                Map<Integer, Rational> eq = new HashMap<Integer, Rational>();
                for (Term tm : terms) addTermCoeff(eq, tm, t, v);
                for (int k = 0; k < ps.size(); k++) add(eq, mu[k], Rational.of(-ps.get(k).coefficient(v)));
                pushEq(eq, Rational.ZERO);
            }
            // Constant slot: const(E) − Σ μ_k·const(p_k) − μ0 = 0, where const(E) carries cst.
            Map<Integer, Rational> eq = new HashMap<Integer, Rational>();
            for (Term tm : terms) addTermConst(eq, tm, t);
            for (int k = 0; k < ps.size(); k++) add(eq, mu[k], Rational.of(-ps.get(k).constant()));
            add(eq, mu0, Rational.of(-1));
            pushEq(eq, cst.negate());   // λ-consts − Σμ.. − μ0 = −cst
        }

        // coeff of variable `v` in sign·f_phase(src|tgt)
        private void addTermCoeff(Map<Integer, Rational> eq, Term tm, ItsTransition t, String v) {
            if (tm.source) {
                int i = t.source().variables().indexOf(v);
                if (i >= 0) addLambda(eq, tm.phase, t.source().name(), i, tm.sign);
            } else {
                List<ItsLinearExpression> upd = t.updates();
                String tloc = t.target().name();
                for (int j = 0; j < upd.size(); j++) {
                    long c = upd.get(j).coefficient(v);
                    if (c != 0) addLambda(eq, tm.phase, tloc, j, tm.sign.multiply(Rational.of(c)));
                }
            }
        }

        private void addTermConst(Map<Integer, Rational> eq, Term tm, ItsTransition t) {
            if (tm.source) {
                addLambda(eq, tm.phase, t.source().name(), t.source().arity(), tm.sign);
            } else {
                List<ItsLinearExpression> upd = t.updates();
                String tloc = t.target().name();
                for (int j = 0; j < upd.size(); j++) {
                    long dconst = upd.get(j).constant();
                    if (dconst != 0) addLambda(eq, tm.phase, tloc, j, tm.sign.multiply(Rational.of(dconst)));
                }
                addLambda(eq, tm.phase, tloc, t.target().arity(), tm.sign);
            }
        }

        private void addLambda(Map<Integer, Rational> eq, int phase, String loc, int k, Rational coeff) {
            if (coeff.isZero()) return;
            add(eq, lam.get(phase + "|" + loc)[k], coeff);
        }

        private static void add(Map<Integer, Rational> eq, int var, Rational c) {
            Rational cur = eq.get(var);
            Rational nv = cur == null ? c : cur.add(c);
            if (nv.isZero()) eq.remove(var); else eq.put(var, nv);
        }

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
            ItsLinearExpression.Builder b = new ItsLinearExpression.Builder();
            for (Map.Entry<String, Long> t : e.coefficients().entrySet()) b.addTerm(t.getKey(), -t.getValue());
            b.addConstant(-e.constant());
            return b.build();
        }

        private Set<String> universe(ItsTransition t, List<Term> terms, List<ItsLinearExpression> ps) {
            Set<String> v = new LinkedHashSet<String>(t.source().variables());
            boolean anyTarget = false;
            for (Term tm : terms) if (!tm.source) anyTarget = true;
            if (anyTarget) for (ItsLinearExpression e : t.updates()) v.addAll(e.variables());
            for (ItsLinearExpression p : ps) v.addAll(p.variables());
            return v;
        }

        private void pushEq(Map<Integer, Rational> eq, Rational r) {
            rows.add(eq); ops.add(LinearProgram.Op.EQ); rhs.add(r);
        }

        private Rational[] dense(Map<Integer, Rational> sparse) {
            Rational[] r = new Rational[next];
            for (int j = 0; j < next; j++) r[j] = Rational.ZERO;
            for (Map.Entry<Integer, Rational> e : sparse.entrySet()) r[e.getKey()] = e.getValue();
            return r;
        }
    }
}
