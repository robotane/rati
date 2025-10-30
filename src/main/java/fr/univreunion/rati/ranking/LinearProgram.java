package fr.univreunion.rati.ranking;

import java.util.ArrayList;
import java.util.List;

/**
 * An exact-rational linear program solved by a two-phase simplex with Bland's
 * anti-cycling rule.
 *
 * <p>Maximises {@code cᵀx} subject to a set of linear constraints
 * ({@code =}, {@code ≤}, {@code ≥}) over variables {@code x ≥ 0}. Everything is
 * computed over {@link Rational}, so the answer is exact — required because the
 * solution doubles as a Farkas/ranking certificate that must hold without
 * floating-point slack (see {@link FarkasRanking}).
 *
 * <p>Free variables (a template coefficient that may be negative) are handled by
 * the caller splitting them into a positive and a negative part, each {@code ≥ 0}.
 */
public final class LinearProgram {

    /** Constraint relation. */
    public enum Op { LE, GE, EQ }

    private static final class Row {
        final Rational[] a;     // coefficients over structural variables
        final Op op;
        final Rational rhs;
        Row(Rational[] a, Op op, Rational rhs) { this.a = a; this.op = op; this.rhs = rhs; }
    }

    private final int numVars;
    private final List<Row> rows = new ArrayList<Row>();
    private Rational[] objective;   // maximise objective·x; null ⇒ pure feasibility

    public LinearProgram(int numVars) {
        this.numVars = numVars;
    }

    /** Adds {@code coeffs·x  op  rhs}. {@code coeffs} length must be {@code numVars}. */
    public void addConstraint(Rational[] coeffs, Op op, Rational rhs) {
        if (coeffs.length != numVars) throw new IllegalArgumentException("coeff arity");
        rows.add(new Row(coeffs.clone(), op, rhs));
    }

    public void setObjective(Rational[] coeffs) {
        if (coeffs.length != numVars) throw new IllegalArgumentException("objective arity");
        this.objective = coeffs.clone();
    }

    /** Result of a solve: feasibility plus, when feasible, the optimal point and value. */
    public static final class Solution {
        public final boolean feasible;
        public final Rational[] x;          // length numVars (null when infeasible)
        public final Rational objective;    // optimum (null when infeasible / no objective)
        Solution(boolean feasible, Rational[] x, Rational objective) {
            this.feasible = feasible; this.x = x; this.objective = objective;
        }
    }

    // -------------------------------------------------------------------------
    // Two-phase simplex
    // -------------------------------------------------------------------------

    public Solution solve() {
        int m = rows.size();

        // Normalise every row to a non-negative right-hand side.
        Op[] op = new Op[m];
        Rational[] rhs = new Rational[m];
        Rational[][] a = new Rational[m][];
        for (int i = 0; i < m; i++) {
            Row r = rows.get(i);
            Rational[] ai = r.a.clone();
            Rational bi = r.rhs;
            Op oi = r.op;
            if (bi.isNegative()) {
                for (int j = 0; j < numVars; j++) ai[j] = ai[j].negate();
                bi = bi.negate();
                if (oi == Op.LE) oi = Op.GE; else if (oi == Op.GE) oi = Op.LE;
            }
            a[i] = ai; rhs[i] = bi; op[i] = oi;
        }

        // Column layout: [structural | slack/surplus | artificial].
        int nSlack = 0, nArt = 0;
        for (int i = 0; i < m; i++) {
            if (op[i] == Op.LE) nSlack++;
            else if (op[i] == Op.GE) { nSlack++; nArt++; }
            else nArt++;                     // EQ
        }
        int slackBase = numVars;
        int artBase = numVars + nSlack;
        int cols = numVars + nSlack + nArt;

        Rational[][] T = new Rational[m][cols + 1];
        int[] basis = new int[m];
        boolean[] isArtificial = new boolean[cols];
        for (int i = 0; i < m; i++)
            for (int j = 0; j <= cols; j++) T[i][j] = Rational.ZERO;

        int s = slackBase, art = artBase;
        for (int i = 0; i < m; i++) {
            for (int j = 0; j < numVars; j++) T[i][j] = a[i][j];
            T[i][cols] = rhs[i];
            switch (op[i]) {
                case LE:
                    T[i][s] = Rational.ONE; basis[i] = s; s++;
                    break;
                case GE:
                    T[i][s] = Rational.of(-1); s++;
                    T[i][art] = Rational.ONE; isArtificial[art] = true; basis[i] = art; art++;
                    break;
                default: // EQ
                    T[i][art] = Rational.ONE; isArtificial[art] = true; basis[i] = art; art++;
            }
        }

        boolean[] forbidden = new boolean[cols];   // columns barred from entering

        // ---- Phase 1: minimise Σ artificials  ⇔  maximise −Σ artificials ----
        if (nArt > 0) {
            Rational[] c1 = new Rational[cols];
            for (int j = 0; j < cols; j++) c1[j] = isArtificial[j] ? Rational.of(-1) : Rational.ZERO;
            Rational[] zrow = buildObjectiveRow(T, basis, c1, m, cols);
            if (!simplex(T, basis, zrow, forbidden, m, cols)) return infeasible();
            if (zrow[cols].isNegative()) return infeasible();   // Σ artificials > 0

            // Drive any artificial still in the basis out (or accept a redundant row).
            for (int i = 0; i < m; i++) {
                if (basis[i] >= artBase) {
                    int pc = -1;
                    for (int j = 0; j < artBase; j++)
                        if (!T[i][j].isZero()) { pc = j; break; }
                    if (pc >= 0) pivot(T, basis, null, m, cols, i, pc);
                }
            }
            for (int j = artBase; j < cols; j++) forbidden[j] = true;   // bar artificials in phase 2
        }

        if (objective == null) {
            return new Solution(true, extract(T, basis, m), null);
        }

        // ---- Phase 2: maximise the real objective ----
        Rational[] c2 = new Rational[cols];
        for (int j = 0; j < cols; j++) c2[j] = j < numVars ? objective[j] : Rational.ZERO;
        Rational[] zrow = buildObjectiveRow(T, basis, c2, m, cols);
        if (!simplex(T, basis, zrow, forbidden, m, cols)) {
            // Unbounded: should not occur for our bounded ranking LPs. Treat as no useful optimum.
            return new Solution(true, extract(T, basis, m), null);
        }
        return new Solution(true, extract(T, basis, m), zrow[cols]);
    }

    // -------------------------------------------------------------------------

    /** Builds the reduced-cost row for cost vector {@code c}, pricing out the basis. */
    private static Rational[] buildObjectiveRow(Rational[][] T, int[] basis,
                                                Rational[] c, int m, int cols) {
        Rational[] z = new Rational[cols + 1];
        for (int j = 0; j < cols; j++) z[j] = c[j].negate();   // zⱼ−cⱼ with z=0 initially
        z[cols] = Rational.ZERO;
        for (int i = 0; i < m; i++) {
            Rational cb = c[basis[i]];
            if (cb.isZero()) continue;
            for (int j = 0; j <= cols; j++) z[j] = z[j].add(cb.multiply(T[i][j]));
        }
        return z;
    }

    /**
     * Runs simplex iterations (maximise) until optimal. Returns false if unbounded.
     * Optimal when every non-forbidden reduced cost {@code z[j] ≥ 0}; entering
     * column and leaving row both chosen by Bland's rule (smallest index).
     */
    private static boolean simplex(Rational[][] T, int[] basis, Rational[] z,
                                   boolean[] forbidden, int m, int cols) {
        while (true) {
            int pc = -1;
            for (int j = 0; j < cols; j++) {
                if (forbidden[j]) continue;
                if (z[j].isNegative()) { pc = j; break; }     // Bland: first improving
            }
            if (pc < 0) return true;                          // optimal

            int pr = -1;
            Rational best = null;
            for (int i = 0; i < m; i++) {
                if (!T[i][pc].isPositive()) continue;
                Rational ratio = T[i][cols].divide(T[i][pc]);
                if (best == null || ratio.compareTo(best) < 0
                        || (ratio.compareTo(best) == 0 && basis[i] < basis[pr])) {
                    best = ratio; pr = i;
                }
            }
            if (pr < 0) return false;                         // unbounded
            pivot(T, basis, z, m, cols, pr, pc);
        }
    }

    /** Gauss-Jordan pivot at {@code (pr,pc)}; updates basis and (if given) z-row. */
    private static void pivot(Rational[][] T, int[] basis, Rational[] z,
                              int m, int cols, int pr, int pc) {
        Rational p = T[pr][pc];
        for (int j = 0; j <= cols; j++) T[pr][j] = T[pr][j].divide(p);
        for (int i = 0; i < m; i++) {
            if (i == pr) continue;
            Rational f = T[i][pc];
            if (f.isZero()) continue;
            for (int j = 0; j <= cols; j++) T[i][j] = T[i][j].subtract(f.multiply(T[pr][j]));
        }
        if (z != null) {
            Rational f = z[pc];
            if (!f.isZero())
                for (int j = 0; j <= cols; j++) z[j] = z[j].subtract(f.multiply(T[pr][j]));
        }
        basis[pr] = pc;
    }

    private Rational[] extract(Rational[][] T, int[] basis, int m) {
        Rational[] x = new Rational[numVars];
        for (int j = 0; j < numVars; j++) x[j] = Rational.ZERO;
        for (int i = 0; i < m; i++)
            if (basis[i] < numVars) x[basis[i]] = T[i][T[i].length - 1];
        return x;
    }

    private static Solution infeasible() {
        return new Solution(false, null, null);
    }
}
