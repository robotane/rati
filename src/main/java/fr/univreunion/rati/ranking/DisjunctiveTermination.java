package fr.univreunion.rati.ranking;

import java.util.ArrayList;
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

import fr.univreunion.rati.its.ItsLinearConstraint;
import fr.univreunion.rati.its.ItsLinearExpression;
import fr.univreunion.rati.its.ItsTransition;

/**
 * Disjunctive termination via <em>transition invariants</em> (Podelski &amp;
 * Rybalchenko, LICS 2004) — the technique behind Terminator (Cook-Podelski-
 * Rybalchenko). Proves loops that no single lexicographic / multiphase ranking
 * function covers, e.g. {@code while (x>0 || y>0) { if (x>0) x-- else y-- }},
 * whose integer counters are unbounded below.
 *
 * <p>Instead of one ranking function, we prove that the transition relation
 * {@code T} of an SCC (summarised to self-loops on one cut-point) is, together
 * with its transitive closure, contained in a finite union of well-founded
 * relations {@code R_1 ∪ … ∪ R_k}, each {@code R_i = {f_i(x) ≥ 0 ∧ f_i(x) −
 * f_i(x') ≥ 1}} for a linear function {@code f_i}. By the Ramsey-based theorem,
 * such a <em>disjunctively well-founded transition invariant</em> implies
 * termination.
 *
 * <p>We avoid materialising {@code T⁺}: it suffices (Cook-Podelski-Rybalchenko)
 * to find a {@code TI = ⋃R_i} with {@code T ⊆ TI} and {@code TI ∘ T ⊆ TI}
 * (inductiveness), which gives {@code T⁺ ⊆ TI}. The candidate set is grown
 * counterexample-guided: start from a ranking function for each transition, and
 * whenever a composed relation {@code R_i ∘ τ} escapes the union, synthesise a
 * ranking function for the escaping part and add it.
 *
 * <p>Soundness rests on exact reasoning: each {@code R_i} is well-founded by
 * construction; the union-inclusion test {@code P ⊆ ⋃R_j} is decided by exact
 * polyhedral emptiness of {@code P} minus the union (strict complements, so the
 * rational relaxation is conservative for the integer relation). Used only as a
 * fallback after {@link FarkasRanking}/{@link MultiphaseRanking}, so it can only
 * turn UNKNOWN into TERMINATES.
 */
final class DisjunctiveTermination {

    /** Cap on synthesised well-founded relations (counterexample iterations). */
    private static final int MAX_RELATIONS = 12;

    /** Strict polyhedra (Polka true) so the union-complement {@code f < 0} is exact. */
    private final Manager man = new Polka(true);
    private final int n;                       // state dimension (cut-point arity)

    private DisjunctiveTermination(int n) { this.n = n; }

    /**
     * @param selfLoops transitions of a single-cut-point SCC (each source==target
     *                  with the same {@code n} variables); see {@link LoopSummary}
     * @return true iff a disjunctively well-founded transition invariant is found
     */
    static boolean terminates(List<ItsTransition> selfLoops) {
        if (selfLoops.isEmpty()) return true;
        String loc = selfLoops.get(0).source().name();
        int n = selfLoops.get(0).source().arity();
        for (ItsTransition t : selfLoops)
            if (!t.source().name().equals(loc) || !t.target().name().equals(loc)) return false; // not single cut-point
        try {
            return new DisjunctiveTermination(n).run(selfLoops);
        } catch (ApronException | RuntimeException e) {
            if (Boolean.getBoolean("rati.rankingDebug"))
                System.err.println("  [disjunctive] bailed: " + e);
            return false;   // sound fallback (Apron also throws IllegalArgumentException)
        }
    }

    private boolean run(List<ItsTransition> selfLoops) throws ApronException {
        List<Abstract1> T = new ArrayList<Abstract1>();       // the transitions, as relations
        for (ItsTransition t : selfLoops) T.add(relationOf(t));

        boolean dbg = Boolean.getBoolean("rati.rankingDebug");
        // Seed: a well-founded relation ranking each individual transition.
        List<Abstract1> R = new ArrayList<Abstract1>();
        for (Abstract1 t : T) {
            Abstract1 wf = rankRelation(t);
            if (dbg) System.err.println("  [disjunctive] seed ranked=" + (wf != null)
                    + (wf == null ? "  rel=" + java.util.Arrays.toString(t.toLincons(man)) : ""));
            if (wf == null) return false;                     // a transition with no LRF — give up (sound)
            R.add(wf);
        }
        // (1) T ⊆ ⋃R holds by construction. Grow R until (2) ⋃R ∘ T ⊆ ⋃R (inductive).
        for (int iter = 0; iter < MAX_RELATIONS; iter++) {
            Abstract1 escaping = null;
            for (Abstract1 r : R) {
                for (Abstract1 t : T) {
                    Abstract1 comp = compose(r, t);
                    if (comp.isBottom(man)) continue;
                    Abstract1 esc = notCovered(comp, R);      // comp minus ⋃R, as a witness region
                    if (esc != null && !esc.isBottom(man)) { escaping = esc; break; }
                }
                if (escaping != null) break;
            }
            if (escaping == null) return true;                // inductive ⇒ T⁺ ⊆ ⋃R ⇒ terminates
            Abstract1 wf = rankRelation(escaping);
            if (dbg) System.err.println("  [disjunctive] iter " + iter + ": escaping region, ranked=" + (wf != null));
            if (wf == null) return false;                     // escaping part not rankable — give up
            R.add(wf);
        }
        return false;                                          // did not converge within the cap
    }

    // -------------------------------------------------------------------------
    // Relations over (i_0..i_{n-1}, o_0..o_{n-1})
    // -------------------------------------------------------------------------

    private static final String IN = "i", OUT = "o", MID = "m";

    /** Builds the transition relation of a self-loop as a polyhedron over {@code i_*,o_*}. */
    private Abstract1 relationOf(ItsTransition t) throws ApronException {
        List<String> src = t.source().variables();
        Set<String> names = new LinkedHashSet<String>(src);
        for (ItsLinearConstraint c : t.constraints()) names.addAll(c.lhs().variables());
        for (ItsLinearExpression e : t.updates()) names.addAll(e.variables());
        String[] o = new String[n];
        for (int k = 0; k < n; k++) { o[k] = OUT + k; names.add(o[k]); }

        Environment env = new Environment(new String[0], names.toArray(new String[0]));
        List<Lincons1> cs = new ArrayList<Lincons1>();
        for (ItsLinearConstraint c : t.constraints()) cs.add(toLincons(env, c.lhs(), c.op()));
        for (int k = 0; k < n; k++) cs.add(bindEq(env, o[k], t.updates().get(k)));
        Abstract1 a = new Abstract1(man, env).meetCopy(man, cs.toArray(new Lincons1[0]));

        String[] keep = new String[2 * n];
        for (int k = 0; k < n; k++) { keep[k] = src.get(k); keep[n + k] = o[k]; }
        a = a.changeEnvironmentCopy(man, new Environment(new String[0], keep), true);
        String[] from = new String[n], to = new String[n];
        for (int k = 0; k < n; k++) { from[k] = src.get(k); to[k] = IN + k; }
        return a.renameCopy(man, from, to);
    }

    /** Relational composition {@code r ∘ t} = {(i,o): ∃m. (i,m)∈r ∧ (m,o)∈t}. */
    private Abstract1 compose(Abstract1 r, Abstract1 t) throws ApronException {
        Abstract1 a1 = rename(r, OUT, MID);     // r over (i, m)
        Abstract1 a2 = rename(t, IN, MID);      // t over (m, o)
        List<String> joint = new ArrayList<String>();
        for (int k = 0; k < n; k++) joint.add(IN + k);
        for (int k = 0; k < n; k++) joint.add(MID + k);
        for (int k = 0; k < n; k++) joint.add(OUT + k);
        Environment je = new Environment(new String[0], joint.toArray(new String[0]));
        Abstract1 met = a1.changeEnvironmentCopy(man, je, false)
                          .meetCopy(man, a2.changeEnvironmentCopy(man, je, false));
        String[] keep = new String[2 * n];
        for (int k = 0; k < n; k++) { keep[k] = IN + k; keep[n + k] = OUT + k; }
        return met.changeEnvironmentCopy(man, new Environment(new String[0], keep), true);
    }

    private Abstract1 rename(Abstract1 a, String fromPfx, String toPfx) throws ApronException {
        String[] f = new String[n], t = new String[n];
        for (int k = 0; k < n; k++) { f[k] = fromPfx + k; t[k] = toPfx + k; }
        return a.renameCopy(man, f, t);
    }

    // -------------------------------------------------------------------------
    // Well-founded relation synthesis: f(i) ≥ 0 ∧ f(i) − f(o) ≥ 1 implied by R
    // -------------------------------------------------------------------------

    /**
     * Synthesises a linear ranking function for relation {@code rel} via Farkas and
     * returns the well-founded relation {@code {f(i) ≥ 0 ∧ f(i) − f(o) ≥ 1}}, or
     * {@code null} if none exists.
     */
    private Abstract1 rankRelation(Abstract1 rel) throws ApronException {
        Lincons1[] cons = rel.toLincons(man);
        // Premises p ≥ 0 over {i_*, o_*}; an equality contributes p and −p.
        List<double[]> prem = new ArrayList<double[]>();   // each: [coeff_i0..,coeff_o0..,const]
        for (Lincons1 lc : cons) {
            ItsLinearConstraint.Op op = ItsLinearConstraint.opFromApron(lc.getKind());
            if (op == null) continue;
            double[] p = linconsToVec(lc);
            prem.add(p);
            if (op == ItsLinearConstraint.Op.EQ) prem.add(negVec(p));
        }
        Rational[] f = solveFarkasLRF(prem);
        if (f == null) return null;
        return wfRelation(f);
    }

    /** LP: find f-coeffs c (length n+1) s.t. premises ⊨ f(i)≥0 and ⊨ f(i)−f(o)−1≥0. */
    private Rational[] solveFarkasLRF(List<double[]> prem) {
        // Unknowns: c_0..c_n split into pos/neg (free), then per-implication μ's.
        // Vars over Farkas universe V = {i_0..i_{n-1}, o_0..o_{n-1}} (2n) + const slot.
        int cPos = 0, cNeg = (n + 1);
        int base = 2 * (n + 1);
        int p = prem.size();
        // implication A (bound): μ_a[0..p-1], μa0 ; implication B (decrease): μ_b[0..p-1], μb0
        int muA = base, muA0 = muA + p, muB = muA0 + 1, muB0 = muB + p;
        int total = muB0 + 1;

        LinearProgram lp = new LinearProgram(total);
        // ----- Bound implication: f(i) = Σ μa_l p_l + μa0  (identity over V and const) -----
        // variable i_k: coeff of f(i) is c_k ; coeff of o_k is 0.
        for (int k = 0; k < n; k++) {
            Rational[] row = new Rational[total];
            zero(row);
            row[cPos + k] = Rational.ONE; row[cNeg + k] = Rational.of(-1);     // c_k
            for (int l = 0; l < p; l++) row[muA + l] = Rational.of(-(long) prem.get(l)[k]);
            lp.addConstraint(row, LinearProgram.Op.EQ, Rational.ZERO);
        }
        for (int k = 0; k < n; k++) {        // o_k : f(i) has 0
            Rational[] row = new Rational[total]; zero(row);
            for (int l = 0; l < p; l++) row[muA + l] = Rational.of(-(long) prem.get(l)[n + k]);
            lp.addConstraint(row, LinearProgram.Op.EQ, Rational.ZERO);
        }
        { // const slot: c_n = Σ μa_l const_l + μa0
            Rational[] row = new Rational[total]; zero(row);
            row[cPos + n] = Rational.ONE; row[cNeg + n] = Rational.of(-1);
            for (int l = 0; l < p; l++) row[muA + l] = Rational.of(-(long) prem.get(l)[2 * n]);
            row[muA0] = Rational.of(-1);
            lp.addConstraint(row, LinearProgram.Op.EQ, Rational.ZERO);
        }
        // ----- Decrease implication: f(i) − f(o) − 1 = Σ μb_l p_l + μb0 -----
        for (int k = 0; k < n; k++) {        // i_k : coeff c_k
            Rational[] row = new Rational[total]; zero(row);
            row[cPos + k] = Rational.ONE; row[cNeg + k] = Rational.of(-1);
            for (int l = 0; l < p; l++) row[muB + l] = Rational.of(-(long) prem.get(l)[k]);
            lp.addConstraint(row, LinearProgram.Op.EQ, Rational.ZERO);
        }
        for (int k = 0; k < n; k++) {        // o_k : coeff −c_k
            Rational[] row = new Rational[total]; zero(row);
            row[cPos + k] = Rational.of(-1); row[cNeg + k] = Rational.ONE;
            for (int l = 0; l < p; l++) row[muB + l] = Rational.of(-(long) prem.get(l)[n + k]);
            lp.addConstraint(row, LinearProgram.Op.EQ, Rational.ZERO);
        }
        { // const slot: −1 = Σ μb_l const_l + μb0   →   0·c − Σμb const − μb0 = 1
            Rational[] row = new Rational[total]; zero(row);
            for (int l = 0; l < p; l++) row[muB + l] = Rational.of(-(long) prem.get(l)[2 * n]);
            row[muB0] = Rational.of(-1);
            lp.addConstraint(row, LinearProgram.Op.EQ, Rational.ONE);
        }
        LinearProgram.Solution sol = lp.solve();
        if (!sol.feasible) return null;
        Rational[] c = new Rational[n + 1];
        for (int k = 0; k <= n; k++) c[k] = sol.x[cPos + k].subtract(sol.x[cNeg + k]);
        return c;
    }

    /** The well-founded relation {@code {f(i) ≥ 0 ∧ f(i) − f(o) ≥ 1}} over {@code i_*,o_*}. */
    private Abstract1 wfRelation(Rational[] c) throws ApronException {
        Environment env = ioEnv();
        long d = lcmDen(c);
        // bound: Σ (d·c_k) i_k + d·c_n ≥ 0
        Linterm1[] b = new Linterm1[n];
        for (int k = 0; k < n; k++) b[k] = new Linterm1(IN + k, new MpqScalar(scaled(c[k], d)));
        Lincons1 bound = new Lincons1(Lincons1.SUPEQ, new Linexpr1(env, b, new MpqScalar(scaled(c[n], d))));
        // decrease: Σ d·c_k (i_k − o_k) − d ≥ 0
        Linterm1[] de = new Linterm1[2 * n];
        for (int k = 0; k < n; k++) {
            de[k] = new Linterm1(IN + k, new MpqScalar(scaled(c[k], d)));
            de[n + k] = new Linterm1(OUT + k, new MpqScalar(-scaled(c[k], d)));
        }
        Lincons1 decr = new Lincons1(Lincons1.SUPEQ, new Linexpr1(env, de, new MpqScalar((int) -d)));
        return new Abstract1(man, env).meetCopy(man, new Lincons1[]{bound, decr});
    }

    // -------------------------------------------------------------------------
    // Union inclusion: P ⊆ ⋃R  via exact emptiness of P ∧ ⋀ ¬R_j (strict complements)
    // -------------------------------------------------------------------------

    /**
     * Returns a non-empty sub-region of {@code p} not covered by {@code ⋃R} (a
     * witness for the inductiveness failure), or {@code null} if {@code p ⊆ ⋃R}.
     * Each {@code R_j} is a conjunction of two facets; its complement is the union
     * of the two strict negations. We DNF-expand and keep the first non-empty cell.
     */
    private Abstract1 notCovered(Abstract1 p, List<Abstract1> R) throws ApronException {
        List<Abstract1> cells = new ArrayList<Abstract1>();
        cells.add(p);
        for (Abstract1 r : R) {
            Lincons1[] facets = r.toLincons(man);            // exactly the 2 facets (bound, decrease)
            List<Abstract1> next = new ArrayList<Abstract1>();
            for (Abstract1 cell : cells) {
                if (cell.isBottom(man)) continue;
                for (Lincons1 facet : facets) {
                    Abstract1 refined = cell.meetCopy(man, new Lincons1[]{strictNegation(facet)});
                    if (!refined.isBottom(man)) next.add(refined);
                }
            }
            cells = next;
            if (cells.isEmpty()) return null;                // fully covered
        }
        return cells.isEmpty() ? null : cells.get(0);
    }

    /** Strict negation of {@code e ▷ 0} (▷ ∈ {≥,>}): {@code −e > 0}. */
    private Lincons1 strictNegation(Lincons1 lc) throws ApronException {
        Environment env = lc.getEnvironment();
        List<Linterm1> terms = new ArrayList<Linterm1>();
        for (Linterm1 lt : lc.getLinterms()) {
            long co = scalarToLong(lt.getCoefficient());
            if (co != 0) terms.add(new Linterm1(lt.getVariable().toString(), new MpqScalar((int) -co)));
        }
        long cst = scalarToLong(lc.getCst());
        return new Lincons1(Lincons1.SUP, new Linexpr1(env, terms.toArray(new Linterm1[0]), new MpqScalar((int) -cst)));
    }

    // -------------------------------------------------------------------------
    // Apron helpers
    // -------------------------------------------------------------------------

    private Environment ioEnv() {
        String[] v = new String[2 * n];
        for (int k = 0; k < n; k++) { v[k] = IN + k; v[n + k] = OUT + k; }
        return new Environment(new String[0], v);
    }

    private double[] linconsToVec(Lincons1 lc) {
        double[] v = new double[2 * n + 1];
        for (Linterm1 lt : lc.getLinterms()) {
            int idx = varIndex(lt.getVariable().toString());
            if (idx >= 0) v[idx] = scalarToLong(lt.getCoefficient());
        }
        v[2 * n] = scalarToLong(lc.getCst());
        return v;
    }

    private int varIndex(String name) {
        if (name.startsWith(IN)) return Integer.parseInt(name.substring(IN.length()));
        if (name.startsWith(OUT)) return n + Integer.parseInt(name.substring(OUT.length()));
        return -1;
    }

    private static double[] negVec(double[] v) {
        double[] r = new double[v.length];
        for (int i = 0; i < v.length; i++) r[i] = -v[i];
        return r;
    }

    private static void zero(Rational[] row) {
        for (int i = 0; i < row.length; i++) row[i] = Rational.ZERO;
    }

    private static long lcmDen(Rational[] c) {
        long d = 1;
        for (Rational r : c) d = lcm(d, r.denominator().longValueExact());
        return d;
    }
    private static long lcm(long a, long b) { return a / gcd(a, b) * b; }
    private static long gcd(long a, long b) { a = Math.abs(a); b = Math.abs(b); while (b != 0) { long t = b; b = a % b; a = t; } return a == 0 ? 1 : a; }
    private static int scaled(Rational r, long d) {
        return (int) (r.numerator().longValueExact() * (d / r.denominator().longValueExact()));
    }

    private static Lincons1 bindEq(Environment env, String var, ItsLinearExpression expr) {
        List<Linterm1> terms = new ArrayList<Linterm1>();
        terms.add(new Linterm1(var, new MpqScalar(1)));
        for (Map.Entry<String, Long> e : expr.coefficients().entrySet())
            terms.add(new Linterm1(e.getKey(), new MpqScalar((int) -e.getValue())));
        return new Lincons1(Lincons1.EQ, new Linexpr1(env, terms.toArray(new Linterm1[0]),
                new MpqScalar((int) -expr.constant())));
    }

    private static Lincons1 toLincons(Environment env, ItsLinearExpression lhs, ItsLinearConstraint.Op op) {
        List<Linterm1> terms = new ArrayList<Linterm1>();
        for (Map.Entry<String, Long> e : lhs.coefficients().entrySet())
            terms.add(new Linterm1(e.getKey(), new MpqScalar((int) (long) e.getValue())));
        Linexpr1 le = new Linexpr1(env, terms.toArray(new Linterm1[0]), new MpqScalar((int) lhs.constant()));
        int kind = op == ItsLinearConstraint.Op.EQ ? Lincons1.EQ
                 : op == ItsLinearConstraint.Op.GT ? Lincons1.SUP : Lincons1.SUPEQ;
        return new Lincons1(kind, le);
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
