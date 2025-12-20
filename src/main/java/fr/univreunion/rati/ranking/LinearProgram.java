package fr.univreunion.rati.ranking;

import java.math.BigInteger;
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

    /**
     * Selects the exact-arithmetic engine. {@code rational} (default) is the original
     * {@link #solveRational()}; {@code bareiss} is the fraction-free integer simplex
     * {@link #solveFractionFree()}. Both follow the <em>identical</em> Bland pivot
     * trajectory — every leaving pivot is on a strictly positive entry, so the
     * fraction-free determinant scale {@code D} stays positive and every sign /
     * min-ratio decision matches the rational tableau bit-for-bit — so they return
     * the same feasibility, point and optimum (validated: 0 verdict differences and
     * 0 inexact divisions over the corpus, all engine unit tests green).
     *
     * <p><b>Default is {@code rational}.</b> Bareiss keeps integer minors bounded by
     * Hadamard's inequality, so it bounds the worst-case exact-rational coefficient
     * blow-up — but that blow-up is not what dominates the slow methods. The
     * pathological ones (e.g. Diff.dif) are slow because of the sheer <em>number</em>
     * of Bland pivots on a hugely degenerate Farkas LP, which Bareiss does not reduce
     * (it stayed minutes-long there), while on the common case it is a wash. So it is
     * a sound, verdict-identical opt-in ({@code -Drati.exactArith=bareiss}) — a
     * worst-case coefficient bound, not the default. The real lever for the slow
     * methods is the LP's degeneracy (the free-variable pos/neg split), not the
     * arithmetic representation.
     */
    private static final boolean USE_BAREISS =
            "bareiss".equalsIgnoreCase(System.getProperty("rati.exactArith", "rational"));

    public Solution solve() {
        return USE_BAREISS ? solveFractionFree() : solveRational();
    }

    public Solution solveRational() {
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
     * Entering-column pricing rule. Bland's rule (first improving column) is proven
     * anti-cycling but pivots far too often on the large, highly-degenerate Farkas
     * LPs the ranking synthesiser builds (hundreds of λ/μ columns, almost all rows
     * equalities with rhs 0) — a single ranking LP could take seconds, dominated by
     * the exact-rational pivot arithmetic. Dantzig's rule (most-negative reduced
     * cost) slashes the pivot count there but can cycle, so the default hybrid prices
     * by Dantzig and only falls back to Bland once a run of degenerate (zero-progress)
     * pivots signals a stall — keeping the termination guarantee. {@code
     * -Drati.pricing=dantzig} selects that hybrid; the optimum and the certificate it
     * yields are identical to Bland's, since pricing changes only the pivot path, not
     * the solution.
     *
     * <p><b>Default is {@code bland}.</b> A corpus A/B showed Dantzig is <em>not</em>
     * a uniform win: it nearly halves the pivot count on some LPs (BubbleSort.sort
     * 14.4s→7.7s) but takes a pathological coefficient-blowup path on others
     * (Diff.dif 76s→691s, a 9× regression) that Bland's first-index rule avoids. The
     * disease is the exact-rational coefficient blowup, which pricing only reshuffles;
     * Dantzig is therefore an opt-in escape hatch, not the default.
     */
    private static final boolean PRICING_BLAND =
            !"dantzig".equalsIgnoreCase(System.getProperty("rati.pricing", "bland"));

    /**
     * Runs simplex iterations (maximise) until optimal. Returns false if unbounded.
     * Optimal when every non-forbidden reduced cost {@code z[j] ≥ 0}; the entering
     * column is priced per {@link #PRICING_BLAND} (Dantzig with Bland fallback, or
     * pure Bland), the leaving row by min-ratio with a smallest-basis-index tie-break.
     */
    private static boolean simplex(Rational[][] T, int[] basis, Rational[] z,
                                   boolean[] forbidden, int m, int cols) {
        boolean bland = PRICING_BLAND;     // pure-Bland mode never leaves Bland
        int stall = 0;
        // Flip to Bland for good after this many consecutive degenerate pivots —
        // long enough to let Dantzig clear ordinary degeneracy, bounded so a cycle
        // cannot persist (Bland's rule then guarantees termination).
        final int blandTrigger = 2 * (m + cols) + 64;
        while (true) {
            int pc = -1;
            if (bland) {
                for (int j = 0; j < cols; j++) {
                    if (forbidden[j]) continue;
                    if (z[j].isNegative()) { pc = j; break; }     // Bland: first improving
                }
            } else {
                Rational bestCost = null;
                for (int j = 0; j < cols; j++) {
                    if (forbidden[j]) continue;
                    if (z[j].isNegative() && (bestCost == null || z[j].compareTo(bestCost) < 0)) {
                        bestCost = z[j]; pc = j;                  // Dantzig: most negative
                    }
                }
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

            // Anti-cycling: a long run of degenerate pivots (zero min-ratio ⇒ no
            // objective progress) flips pricing to Bland, which cannot cycle.
            if (!bland) {
                if (best.isZero()) { if (++stall > blandTrigger) bland = true; }
                else stall = 0;
            }
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

    // =========================================================================
    // Fraction-free (Bareiss) two-phase simplex
    // -------------------------------------------------------------------------
    // The tableau is held as a BigInteger matrix M together with a positive scalar
    // D (the determinant of the current basis): the rational tableau entry is
    // M[i][j] / D. A basic column j (basis[k]=j) holds M[k][j]=D and 0 elsewhere, so
    // the basic value is M[k][cols]/D. Every pivot is on M[pr][pc] > 0 (the ratio
    // test forbids non-positive pivots), so D — a product of positive pivots — stays
    // positive. The fraction-free update
    //        M[i][j] ← (M[pr][pc]·M[i][j] − M[i][pc]·M[pr][j]) / D_old
    // is an exact integer division (Bareiss/Sylvester identity: each 2×2 minor is
    // divisible by the previous pivot) and keeps every entry a minor of the original
    // integer matrix, hence bounded by Hadamard's inequality — no coefficient
    // blow-up. With D > 0 the sign and min-ratio tests reproduce the rational
    // engine's decisions exactly, so this returns the same verdict, point and
    // optimum (see USE_BAREISS).
    // =========================================================================

    public Solution solveFractionFree() {
        int m = rows.size();

        // Normalise to non-negative rhs and clear denominators row-by-row: scaling a
        // constraint by a positive integer preserves it and leaves the simplex
        // trajectory invariant (row scaling cancels in every min-ratio and in the
        // reduced costs A_B^{-1}A), so the integer tableau ranks identically.
        Op[] op = new Op[m];
        BigInteger[] rhs = new BigInteger[m];
        BigInteger[][] a = new BigInteger[m][numVars];
        for (int i = 0; i < m; i++) {
            Row r = rows.get(i);
            Rational[] ai = r.a;
            Rational bi = r.rhs;
            Op oi = r.op;
            if (bi.isNegative()) {
                Rational[] neg = new Rational[numVars];
                for (int j = 0; j < numVars; j++) neg[j] = ai[j].negate();
                ai = neg; bi = bi.negate();
                if (oi == Op.LE) oi = Op.GE; else if (oi == Op.GE) oi = Op.LE;
            }
            BigInteger lcm = bi.denominator();
            for (int j = 0; j < numVars; j++) lcm = lcm(lcm, ai[j].denominator());
            for (int j = 0; j < numVars; j++) a[i][j] = scaleToInt(ai[j], lcm);
            rhs[i] = scaleToInt(bi, lcm);
            op[i] = oi;
        }

        int nSlack = 0, nArt = 0;
        for (int i = 0; i < m; i++) {
            if (op[i] == Op.LE) nSlack++;
            else if (op[i] == Op.GE) { nSlack++; nArt++; }
            else nArt++;
        }
        int slackBase = numVars;
        int artBase = numVars + nSlack;
        int cols = numVars + nSlack + nArt;

        BigInteger[][] M = new BigInteger[m][cols + 1];
        int[] basis = new int[m];
        boolean[] isArtificial = new boolean[cols];
        for (int i = 0; i < m; i++)
            for (int j = 0; j <= cols; j++) M[i][j] = BigInteger.ZERO;

        int s = slackBase, art = artBase;
        for (int i = 0; i < m; i++) {
            for (int j = 0; j < numVars; j++) M[i][j] = a[i][j];
            M[i][cols] = rhs[i];
            switch (op[i]) {
                case LE:
                    M[i][s] = BigInteger.ONE; basis[i] = s; s++;
                    break;
                case GE:
                    M[i][s] = BigInteger.valueOf(-1); s++;
                    M[i][art] = BigInteger.ONE; isArtificial[art] = true; basis[i] = art; art++;
                    break;
                default: // EQ
                    M[i][art] = BigInteger.ONE; isArtificial[art] = true; basis[i] = art; art++;
            }
        }

        boolean[] forbidden = new boolean[cols];
        BigInteger[] D = { BigInteger.ONE };   // determinant scale (positive)

        // ---- Phase 1: maximise −Σ artificials ----
        if (nArt > 0) {
            BigInteger[] c1 = new BigInteger[cols];
            for (int j = 0; j < cols; j++) c1[j] = isArtificial[j] ? BigInteger.valueOf(-1) : BigInteger.ZERO;
            BigInteger[] z = ffObjectiveRow(M, basis, c1, m, cols, D[0]);
            if (!ffSimplex(M, basis, z, forbidden, m, cols, D)) return infeasible();
            if (z[cols].signum() < 0) return infeasible();   // Σ artificials > 0

            for (int i = 0; i < m; i++) {
                if (basis[i] >= artBase) {
                    int pc = -1;
                    for (int j = 0; j < artBase; j++)
                        if (M[i][j].signum() != 0) { pc = j; break; }
                    if (pc >= 0) ffPivot(M, basis, null, m, cols, i, pc, D);
                }
            }
            for (int j = artBase; j < cols; j++) forbidden[j] = true;
        }

        if (objective == null) {
            return new Solution(true, ffExtract(M, basis, m, D[0]), null);
        }

        // ---- Phase 2: maximise the real objective (denominators cleared; the
        // optimum is divided back by gObj at the end) ----
        BigInteger gObj = BigInteger.ONE;
        for (int j = 0; j < numVars; j++) gObj = lcm(gObj, objective[j].denominator());
        BigInteger[] c2 = new BigInteger[cols];
        for (int j = 0; j < cols; j++)
            c2[j] = j < numVars ? scaleToInt(objective[j], gObj) : BigInteger.ZERO;
        BigInteger[] z = ffObjectiveRow(M, basis, c2, m, cols, D[0]);
        if (!ffSimplex(M, basis, z, forbidden, m, cols, D)) {
            return new Solution(true, ffExtract(M, basis, m, D[0]), null);   // unbounded
        }
        Rational opt = Rational.of(z[cols], D[0].multiply(gObj));
        return new Solution(true, ffExtract(M, basis, m, D[0]), opt);
    }

    /** Reduced-cost row scaled by {@code D}: {@code z[j] = Σ_i c[basis[i]]·M[i][j] − c[j]·D}. */
    private static BigInteger[] ffObjectiveRow(BigInteger[][] M, int[] basis,
                                               BigInteger[] c, int m, int cols, BigInteger D) {
        BigInteger[] z = new BigInteger[cols + 1];
        for (int j = 0; j < cols; j++) z[j] = c[j].multiply(D).negate();
        z[cols] = BigInteger.ZERO;
        for (int i = 0; i < m; i++) {
            BigInteger cb = c[basis[i]];
            if (cb.signum() == 0) continue;
            for (int j = 0; j <= cols; j++) z[j] = z[j].add(cb.multiply(M[i][j]));
        }
        return z;
    }

    /** Fraction-free simplex (maximise). Returns false if unbounded. Mirrors {@link #simplex}. */
    private static boolean ffSimplex(BigInteger[][] M, int[] basis, BigInteger[] z,
                                     boolean[] forbidden, int m, int cols, BigInteger[] D) {
        while (true) {
            int pc = -1;
            for (int j = 0; j < cols; j++) {
                if (forbidden[j]) continue;
                if (z[j].signum() < 0) { pc = j; break; }   // Bland: first improving (D>0 ⇒ sign exact)
            }
            if (pc < 0) return true;                         // optimal

            // Leaving row: min M[i][cols]/M[i][pc] over positive pivots; ratios share
            // the scale D so compare cross-multiplied; smallest-basis-index tie-break.
            int pr = -1;
            BigInteger bn = null, bd = null;   // best ratio bn/bd
            for (int i = 0; i < m; i++) {
                if (M[i][pc].signum() <= 0) continue;
                BigInteger n = M[i][cols], d = M[i][pc];
                if (pr < 0) { pr = i; bn = n; bd = d; continue; }
                int cmp = n.multiply(bd).compareTo(bn.multiply(d));   // n/d vs bn/bd (d,bd>0)
                if (cmp < 0 || (cmp == 0 && basis[i] < basis[pr])) { pr = i; bn = n; bd = d; }
            }
            if (pr < 0) return false;                        // unbounded
            ffPivot(M, basis, z, m, cols, pr, pc, D);
        }
    }

    /** Bareiss pivot at {@code (pr,pc)}; updates M, the z-row (if given), basis and {@code D}. */
    private static void ffPivot(BigInteger[][] M, int[] basis, BigInteger[] z,
                                int m, int cols, int pr, int pc, BigInteger[] D) {
        BigInteger p = M[pr][pc];           // > 0
        BigInteger dOld = D[0];
        for (int i = 0; i < m; i++) {
            if (i == pr) continue;          // pivot row is left unchanged
            BigInteger mipc = M[i][pc];
            if (mipc.signum() == 0) {
                // (p·M[i][j] − 0)/dOld = M[i][j]·(p/dOld); p/dOld is exact here too.
                for (int j = 0; j <= cols; j++) M[i][j] = exactDiv(p.multiply(M[i][j]), dOld);
            } else {
                for (int j = 0; j <= cols; j++)
                    M[i][j] = exactDiv(p.multiply(M[i][j]).subtract(mipc.multiply(M[pr][j])), dOld);
            }
        }
        if (z != null) {
            BigInteger zpc = z[pc];
            if (zpc.signum() == 0) {
                for (int j = 0; j <= cols; j++) z[j] = exactDiv(p.multiply(z[j]), dOld);
            } else {
                for (int j = 0; j <= cols; j++)
                    z[j] = exactDiv(p.multiply(z[j]).subtract(zpc.multiply(M[pr][j])), dOld);
            }
        }
        D[0] = p;
        basis[pr] = pc;

        // Normal simplex pivots are on a positive element (ratio test), so D stays
        // positive. Only the phase-1 drive-out can pivot on a negative entry, turning
        // D negative; negating D and every entry restores D > 0 while leaving every
        // rational value M/D unchanged — so the sign tests stay exact.
        if (D[0].signum() < 0) {
            D[0] = D[0].negate();
            for (int i = 0; i < m; i++)
                for (int j = 0; j <= cols; j++) M[i][j] = M[i][j].negate();
            if (z != null) for (int j = 0; j <= cols; j++) z[j] = z[j].negate();
        }
    }

    private Rational[] ffExtract(BigInteger[][] M, int[] basis, int m, BigInteger D) {
        Rational[] x = new Rational[numVars];
        for (int j = 0; j < numVars; j++) x[j] = Rational.ZERO;
        for (int i = 0; i < m; i++)
            if (basis[i] < numVars) x[basis[i]] = Rational.of(M[i][M[i].length - 1], D);
        return x;
    }

    /** {@code r·scale} as an exact integer ({@code scale} is a multiple of {@code r}'s denominator). */
    private static BigInteger scaleToInt(Rational r, BigInteger scale) {
        return r.numerator().multiply(scale).divide(r.denominator());
    }

    /** Bareiss division, exact by the Sylvester identity. {@code -Drati.checkExact} verifies it. */
    private static final boolean CHECK_EXACT = System.getProperty("rati.checkExact") != null;
    private static BigInteger exactDiv(BigInteger num, BigInteger den) {
        if (CHECK_EXACT) {
            BigInteger[] qr = num.divideAndRemainder(den);
            if (qr[1].signum() != 0)
                throw new ArithmeticException("Bareiss division not exact: " + num + " / " + den);
            return qr[0];
        }
        return num.divide(den);
    }

    private static BigInteger lcm(BigInteger a, BigInteger b) {
        if (a.signum() == 0 || b.signum() == 0) return BigInteger.ZERO;
        return a.divide(a.gcd(b)).multiply(b).abs();
    }
}
