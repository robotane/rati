package fr.univreunion.rati.ranking;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import apron.Abstract1;
import apron.ApronException;
import apron.Environment;
import apron.Lincons1;
import apron.Linexpr1;
import apron.Linterm1;
import apron.Manager;

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
    private final Manager man = ApronManagers.polkaStrict();
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
        for (ItsLinearConstraint c : t.constraints()) cs.add(ApronBridge.toLincons(env, c));
        for (int k = 0; k < n; k++) cs.add(ApronBridge.bindEq(env, o[k], t.updates().get(k)));
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
        // Premises p ≥ 0 over {i_*, o_*}, read EXACTLY; an equality contributes p
        // and −p. An unreadable premise (non-rational scalar) is skipped — fewer
        // premises only make the Farkas synthesis harder, never wrong, and the
        // returned relation stays well-founded by construction.
        List<Rational[]> prem = new ArrayList<Rational[]>();   // each: [coeff_i0..,coeff_o0..,const]
        for (Lincons1 lc : cons) {
            ItsLinearConstraint.Op op = ItsLinearConstraint.opFromApron(lc.getKind());
            if (op == null) continue;
            Rational[] p = linconsToVec(lc);
            if (p == null) continue;
            prem.add(p);
            if (op == ItsLinearConstraint.Op.EQ) prem.add(negVec(p));
        }
        Rational[] f = solveFarkasLRF(prem);
        if (f == null) return null;
        return wfRelation(f);
    }

    /** LP: find f-coeffs c (length n+1) s.t. premises ⊨ f(i)≥0 and ⊨ f(i)−f(o)−1≥0. */
    private Rational[] solveFarkasLRF(List<Rational[]> prem) {
        // Unknowns: c_0..c_n as native free (unrestricted-in-sign) columns, then
        // per-implication μ's. Vars over Farkas universe V = {i_0..i_{n-1}, o_0..o_{n-1}}
        // (2n) + const slot.
        int c0 = 0;
        int base = (n + 1);
        int p = prem.size();
        // implication A (bound): μ_a[0..p-1], μa0 ; implication B (decrease): μ_b[0..p-1], μb0
        int muA = base, muA0 = muA + p, muB = muA0 + 1, muB0 = muB + p;
        int total = muB0 + 1;

        LinearProgram lp = new LinearProgram(total);
        for (int k = 0; k <= n; k++) lp.markFree(c0 + k);
        // ----- Bound implication: f(i) = Σ μa_l p_l + μa0  (identity over V and const) -----
        // variable i_k: coeff of f(i) is c_k ; coeff of o_k is 0.
        for (int k = 0; k < n; k++) {
            Rational[] row = new Rational[total];
            zero(row);
            row[c0 + k] = Rational.ONE;     // c_k
            for (int l = 0; l < p; l++) row[muA + l] = prem.get(l)[k].negate();
            lp.addConstraint(row, LinearProgram.Op.EQ, Rational.ZERO);
        }
        for (int k = 0; k < n; k++) {        // o_k : f(i) has 0
            Rational[] row = new Rational[total]; zero(row);
            for (int l = 0; l < p; l++) row[muA + l] = prem.get(l)[n + k].negate();
            lp.addConstraint(row, LinearProgram.Op.EQ, Rational.ZERO);
        }
        { // const slot: c_n = Σ μa_l const_l + μa0
            Rational[] row = new Rational[total]; zero(row);
            row[c0 + n] = Rational.ONE;
            for (int l = 0; l < p; l++) row[muA + l] = prem.get(l)[2 * n].negate();
            row[muA0] = Rational.of(-1);
            lp.addConstraint(row, LinearProgram.Op.EQ, Rational.ZERO);
        }
        // ----- Decrease implication: f(i) − f(o) − 1 = Σ μb_l p_l + μb0 -----
        for (int k = 0; k < n; k++) {        // i_k : coeff c_k
            Rational[] row = new Rational[total]; zero(row);
            row[c0 + k] = Rational.ONE;
            for (int l = 0; l < p; l++) row[muB + l] = prem.get(l)[k].negate();
            lp.addConstraint(row, LinearProgram.Op.EQ, Rational.ZERO);
        }
        for (int k = 0; k < n; k++) {        // o_k : coeff −c_k
            Rational[] row = new Rational[total]; zero(row);
            row[c0 + k] = Rational.of(-1);
            for (int l = 0; l < p; l++) row[muB + l] = prem.get(l)[n + k].negate();
            lp.addConstraint(row, LinearProgram.Op.EQ, Rational.ZERO);
        }
        { // const slot: −1 = Σ μb_l const_l + μb0   →   0·c − Σμb const − μb0 = 1
            Rational[] row = new Rational[total]; zero(row);
            for (int l = 0; l < p; l++) row[muB + l] = prem.get(l)[2 * n].negate();
            row[muB0] = Rational.of(-1);
            lp.addConstraint(row, LinearProgram.Op.EQ, Rational.ONE);
        }
        LinearProgram.Solution sol = lp.solve();
        if (!sol.feasible) return null;
        Rational[] c = new Rational[n + 1];
        for (int k = 0; k <= n; k++) c[k] = sol.x[c0 + k];
        return c;
    }

    /** The well-founded relation {@code {f(i) ≥ 0 ∧ f(i) − f(o) ≥ 1}} over {@code i_*,o_*}. */
    private Abstract1 wfRelation(Rational[] c) throws ApronException {
        Environment env = ioEnv();
        // Apron scalars are exact rationals: no integer scaling (and no (int)
        // truncation) is needed — f's coefficients are used verbatim.
        Linterm1[] b = new Linterm1[n];
        for (int k = 0; k < n; k++) b[k] = new Linterm1(IN + k, ApronBridge.scalar(c[k]));
        Lincons1 bound = new Lincons1(Lincons1.SUPEQ, new Linexpr1(env, b, ApronBridge.scalar(c[n])));
        // decrease: Σ c_k (i_k − o_k) − 1 ≥ 0
        Linterm1[] de = new Linterm1[2 * n];
        for (int k = 0; k < n; k++) {
            de[k] = new Linterm1(IN + k, ApronBridge.scalar(c[k]));
            de[n + k] = new Linterm1(OUT + k, ApronBridge.scalar(c[k].negate()));
        }
        Lincons1 decr = new Lincons1(Lincons1.SUPEQ,
                new Linexpr1(env, de, ApronBridge.scalar(Rational.of(-1))));
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

    /**
     * Strict negation of {@code e ▷ 0} (▷ ∈ {≥,>}): {@code −e > 0}, exactly.
     * A rounded negation would shrink the complement and could hide an escaping
     * region (an unsound "covered"), so an unreadable facet aborts the whole
     * disjunctive attempt (caught in {@link #terminates} — a sound false).
     */
    private Lincons1 strictNegation(Lincons1 lc) throws ApronException {
        Environment env = lc.getEnvironment();
        List<Linterm1> terms = new ArrayList<Linterm1>();
        for (Linterm1 lt : lc.getLinterms()) {
            Rational co = ApronBridge.coeffToRational(lt.getCoefficient());
            if (co == null) throw new IllegalStateException("non-rational facet: " + lc);
            if (!co.isZero())
                terms.add(new Linterm1(lt.getVariable().toString(), ApronBridge.scalar(co.negate())));
        }
        Rational cst = ApronBridge.coeffToRational(lc.getCst());
        if (cst == null) throw new IllegalStateException("non-rational facet: " + lc);
        return new Lincons1(Lincons1.SUP,
                new Linexpr1(env, terms.toArray(new Linterm1[0]), ApronBridge.scalar(cst.negate())));
    }

    // -------------------------------------------------------------------------
    // Apron helpers
    // -------------------------------------------------------------------------

    private Environment ioEnv() {
        String[] v = new String[2 * n];
        for (int k = 0; k < n; k++) { v[k] = IN + k; v[n + k] = OUT + k; }
        return new Environment(new String[0], v);
    }

    /** Exact premise vector of a facet ({@code [i_0.., o_0.., const]}), or null if unreadable. */
    private Rational[] linconsToVec(Lincons1 lc) {
        Rational[] v = new Rational[2 * n + 1];
        java.util.Arrays.fill(v, Rational.ZERO);
        for (Linterm1 lt : lc.getLinterms()) {
            int idx = varIndex(lt.getVariable().toString());
            if (idx < 0) continue;
            Rational r = ApronBridge.coeffToRational(lt.getCoefficient());
            if (r == null) return null;
            v[idx] = r;
        }
        Rational cst = ApronBridge.coeffToRational(lc.getCst());
        if (cst == null) return null;
        v[2 * n] = cst;
        return v;
    }

    private int varIndex(String name) {
        if (name.startsWith(IN)) return Integer.parseInt(name.substring(IN.length()));
        if (name.startsWith(OUT)) return n + Integer.parseInt(name.substring(OUT.length()));
        return -1;
    }

    private static Rational[] negVec(Rational[] v) {
        Rational[] r = new Rational[v.length];
        for (int i = 0; i < v.length; i++) r[i] = v[i].negate();
        return r;
    }

    private static void zero(Rational[] row) {
        for (int i = 0; i < row.length; i++) row[i] = Rational.ZERO;
    }
}
