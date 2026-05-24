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
 * <p>Free variables (a template coefficient that may be negative) can be declared
 * natively with {@link #markFree(int)}: a free variable is pre-pivoted into the
 * basis and kept there ("free stays basic"), so it is never pinned non-basic at 0
 * and never limits an entering column — the textbook treatment of an unrestricted
 * variable. This replaces the caller-side pos/neg split (two {@code ≥ 0} columns per
 * free coefficient) with a single column, halving the column count on the synthesiser's
 * large Farkas LPs. The feasibility and the optimum are identical to the split form
 * (a free variable spans the same value range either way); only the pivot trajectory —
 * hence any byte-level certificate hash — differs. By default no variable is free, so
 * a caller that does not call {@link #markFree} runs the original all-{@code ≥ 0} engine
 * bit-for-bit.
 */
public final class LinearProgram {

    /** Constraint relation. */
    public enum Op { LE, GE, EQ }

    /**
     * One constraint, stored sparse: only the nonzero structural coefficients, as
     * parallel arrays sorted by strictly increasing column index. The synthesiser's
     * Farkas LPs are huge and hollow — tens of thousands of λ/μ columns with a
     * handful of nonzeros per row — so materialising each row densely put the whole
     * heap into arrays of {@code Rational.ZERO} references (measured: 96% of a 1.5 GB
     * heap at OOM was {@code Rational[]}). Sparse rows store exactly the nonzeros.
     */
    private static final class Row {
        final int[] idx;        // strictly increasing column indices of the nonzeros
        final Rational[] val;   // parallel nonzero coefficients
        final Op op;
        final Rational rhs;
        Row(int[] idx, Rational[] val, Op op, Rational rhs) {
            this.idx = idx; this.val = val; this.op = op; this.rhs = rhs;
        }
        /** Dense structural-coefficient view (Bareiss engine only, opt-in path). */
        Rational[] dense(int numVars) {
            Rational[] a = new Rational[numVars];
            java.util.Arrays.fill(a, Rational.ZERO);
            for (int k = 0; k < idx.length; k++) a[idx[k]] = val[k];
            return a;
        }
    }

    private final int numVars;
    private final List<Row> rows = new ArrayList<Row>();
    private Rational[] objective;   // maximise objective·x; null ⇒ pure feasibility
    private final boolean[] free;   // free[j] ⇒ variable j is unrestricted in sign (default: none)
    private boolean anyFree;        // true once any variable is marked free

    public LinearProgram(int numVars) {
        this.numVars = numVars;
        this.free = new boolean[numVars];   // all false ⇒ every variable ≥ 0
    }

    /**
     * Marks structural variable {@code j} as free (unrestricted in sign) — see the class
     * doc. Idempotent. Must be called before {@link #solve()}; the choice does not affect
     * the rows, only how the solver treats column {@code j}.
     */
    public void markFree(int j) {
        if (j < 0 || j >= numVars) throw new IllegalArgumentException("free var index");
        free[j] = true; anyFree = true;
    }

    /** Adds {@code coeffs·x  op  rhs}. {@code coeffs} length must be {@code numVars}. */
    public void addConstraint(Rational[] coeffs, Op op, Rational rhs) {
        if (coeffs.length != numVars) throw new IllegalArgumentException("coeff arity");
        int nnz = 0;
        for (int j = 0; j < numVars; j++) if (!coeffs[j].isZero()) nnz++;
        int[] idx = new int[nnz];
        Rational[] val = new Rational[nnz];
        int k = 0;
        for (int j = 0; j < numVars; j++)
            if (!coeffs[j].isZero()) { idx[k] = j; val[k] = coeffs[j]; k++; }
        rows.add(new Row(idx, val, op, rhs));
    }

    /**
     * Sparse variant of {@link #addConstraint(Rational[], Op, Rational)}: the constraint's
     * nonzero coefficients as a column-index → value map (absent columns are 0; explicit
     * zero values are dropped). Entries are stored sorted by column index, so the engine's
     * scans — and hence the pivot trajectory and every verdict — are identical to feeding
     * the equivalent dense array. This is the path the ranking builders use: they assemble
     * rows as sparse maps already, and densifying them was the allocation the heap died on.
     */
    public void addConstraint(java.util.Map<Integer, Rational> coeffs, Op op, Rational rhs) {
        int nnz = 0;
        for (java.util.Map.Entry<Integer, Rational> e : coeffs.entrySet()) {
            int j = e.getKey().intValue();
            if (j < 0 || j >= numVars) throw new IllegalArgumentException("coeff index");
            if (!e.getValue().isZero()) nnz++;
        }
        int[] idx = new int[nnz];
        int k = 0;
        for (java.util.Map.Entry<Integer, Rational> e : coeffs.entrySet())
            if (!e.getValue().isZero()) idx[k++] = e.getKey().intValue();
        java.util.Arrays.sort(idx);
        Rational[] val = new Rational[nnz];
        for (int i = 0; i < nnz; i++) val[i] = coeffs.get(Integer.valueOf(idx[i]));
        rows.add(new Row(idx, val, op, rhs));
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

    /**
     * Cumulative budget, <em>per ranking attempt</em>, on exact-arithmetic <em>work</em> —
     * the running sum of {@code tableauRows × tableauCols} charged once per simplex pivot,
     * accumulated across every LP a single {@link FarkasRanking#prove} solves (it opens a
     * fresh window via {@link #beginProveWindow()}). When the window's work passes the
     * budget, the running solve aborts to {@link #infeasible()} and every later solve in
     * the same attempt aborts at once — so the whole attempt is bounded, not each LP.
     *
     * <p>Why work, not a pivot count, a per-LP cap, or a wall clock:
     * <ul>
     *   <li><b>vs pivot count</b> — the synthesiser's multi-predicate Farkas LPs blow up in
     *       tableau <em>area</em> (a many-location SCC with rich invariants reaches ~850
     *       rows × ~1600 free-split columns), so one solve grinds minutes of exact-rational
     *       pivoting yet at a pivot count (a few thousand) indistinguishable from a small
     *       loop that proves in milliseconds. Work = pivots × area separates them.</li>
     *   <li><b>vs a per-LP cap</b> — the relaxed ADFG round solves one LP per anchor
     *       transition (~a dozen on these SCCs); a per-LP cap is paid once per anchor and
     *       multiplies, so the attempt still runs minutes. The budget must span the attempt.</li>
     *   <li><b>vs a wall/CPU clock</b> — work is a deterministic function of the LP, so the
     *       abort point — hence every verdict — is byte-identical run to run and machine to
     *       machine; a time cap makes verdicts depend on load.</li>
     * </ul>
     * Measured over the Julia09 corpus: the hardest genuinely-provable method totals
     * ~8.2·10⁸ work, every other completing method ≤ ~6.6·10⁸, while the two pathological
     * Diff loops each exceed 3·10⁹ in a single non-terminating solve — so the {@code 1.5·10⁹}
     * default preserves every verdict (validated: byte-identical sweep) yet bounds the Diff
     * grind. Aborting only ever yields {@link #infeasible()}, which every caller reads as
     * "no proof via this step" — sound (never a false TERMINATES; the non-termination prover
     * re-checks each witness by exact substitution). {@code -Drati.workBudget=N} overrides
     * it; {@code 0} disables the cap.
     */
    public static final long WORK_BUDGET = Long.getLong("rati.workBudget", 1_500_000_000L);

    /**
     * All mutable budget counters, held <em>per thread</em>. RaTI was written for
     * single-threaded use (one process per proof), but bcterm now drives the engine
     * in-process from a parallel ranking cascade ({@code bcterm.rankParallel}). With the
     * counters as plain statics, one thread's {@link #endMphiWindow} would clear another
     * thread's open window mid-{@code solve()}, so the MΦRF pivot budget never fired and a
     * degenerate grind ran unbounded (Numerical3.main ≈ 60 s). Per-thread state restores the
     * budgets under concurrency without any locking. (Mirrors the per-thread Apron managers.)
     */
    private static final class Budget {
        long workSpent;        // per-attempt cumulative LP work
        long buildSpent;       // per-attempt cumulative LP-setup work
        long mphiSpent;        // pivot work charged inside the current MΦRF window
        boolean mphiActive;    // true between begin/endMphiWindow
    }
    private static final ThreadLocal<Budget> BUDGET = ThreadLocal.withInitial(Budget::new);
    private static Budget b() { return BUDGET.get(); }

    /**
     * Cumulative budget, <em>per ranking attempt</em>, on LP <em>setup</em> work — the
     * running sum of {@code tableauRows × tableauCols} charged once per {@link #solve()},
     * accumulated across every LP a single {@link FarkasRanking#prove} solves. This is the
     * cost {@link #WORK_BUDGET} does <em>not</em> see: each solve allocates the simplex
     * tableau and prices the initial objective row ({@link #buildObjectiveRow}) — O(rows ×
     * cols) of exact-rational work that runs <em>before the first pivot is charged</em>.
     * The relaxed ADFG round ({@link FarkasRanking#orientRoundRelaxed}) solves one LP per
     * <em>anchor</em> transition (a dozen-plus on a large SCC), and an anchor whose LP peels
     * nothing still pays full setup; on a many-hundred-location Kitten visitor body that
     * per-anchor setup grinds tens of seconds while almost no pivot is ever charged
     * (confirmed by a thread dump parked in {@link #buildObjectiveRow}).
     *
     * <p>Kept <em>separate</em> from {@code workSpent} on purpose: a pivot-bound but
     * genuinely-provable method must not have its proof forgone because setup ate the pivot
     * budget. Exhaustion throws {@link BuildBudgetExceeded}, caught in {@link
     * FarkasRanking#prove} and turned into a deterministic UNKNOWN — sound, since (as with
     * the pivot budget) abandoning the search only ever forgoes a proof, never fabricates a
     * false TERMINATES. {@code -Drati.buildBudget=N} overrides it; {@code 0} disables it.
     *
     * <p>Calibrated on the Julia09 corpus + dumped Kitten bodies (setup work measured per
     * attempt): the heaviest genuinely-provable method (KnapsackDP.SolveDP) totals
     * ≈2.1·10⁶, every other proof less, while a Kitten visitor grinder passes 1·10⁸ of pure
     * per-anchor setup. The {@code 10⁷} default clears every measured proof (≈5× margin)
     * yet bounds the grinder to a sub-second UNKNOWN.
     */
    public static final long BUILD_BUDGET = Long.getLong("rati.buildBudget", 10_000_000L);

    /** Thrown when an attempt exceeds {@link #WORK_BUDGET}; caught in {@link #solve()}. */
    private static final class BudgetExceeded extends RuntimeException {
        BudgetExceeded() { super(null, null, false, false); }   // stackless
    }

    /**
     * Thrown when an attempt's LP construction exceeds {@link #BUILD_BUDGET}. Unlike
     * {@link BudgetExceeded} (charged inside the solver and swallowed by {@link #solve()}),
     * this fires while {@link FarkasRanking}'s builder assembles rows, so it propagates out
     * of the build and is caught at the {@link FarkasRanking#prove} ranking loop.
     */
    static final class BuildBudgetExceeded extends RuntimeException {
        BuildBudgetExceeded() { super(null, null, false, false); }   // stackless
    }

    /**
     * Tier-local pivot budget for one multiphase (MΦRF) synthesis — the depth-1..d loop of
     * {@link MultiphaseRanking#rank}. Kept SEPARATE from {@link #WORK_BUDGET} because the two
     * tiers spend pivots at incomparable scales: a genuinely-hard <em>lexicographic</em> proof
     * (BubbleSort.sort ≈15 s) legitimately charges hundreds of millions of pivots, so the
     * global budget must stay high to clear it — but at that height it never bounds a
     * <em>degenerate MΦRF</em> grind (Numerical3's gcd charges ~5·10⁸ pivots over ~20 s on an
     * exact-rational nested-RF LP that admits no rank). Charging the MΦRF window against its
     * own, far tighter budget cuts that grind to a sub-second UNKNOWN (measured: a 5·10⁷ cap
     * turns gcd's 20 s MΦRF tier into ≈1 s) while leaving the lexicographic tier — and a real
     * MΦRF rank, which is found fast and charges few pivots — untouched. Sound: exhaustion
     * forgoes the step (→ UNKNOWN), never a false TERMINATES. {@code -Drati.mphiWorkBudget=N}
     * overrides; {@code 0} disables (MΦRF then sees only the global cap). Active only between
     * {@link #beginMphiWindow} and {@link #endMphiWindow}.
     */
    public static final long MPHI_WORK_BUDGET = Long.getLong("rati.mphiWorkBudget", 50_000_000L);

    /** Opens a fresh work-budget window for one ranking attempt (a {@link FarkasRanking#prove}). */
    public static void beginProveWindow() { Budget bd = b(); bd.workSpent = 0; bd.buildSpent = 0; }

    /** Opens a fresh MΦRF pivot-budget window (one {@link MultiphaseRanking#rank} call). */
    public static void beginMphiWindow() {
        Budget bd = b();
        bd.mphiSpent = 0; bd.mphiActive = MPHI_WORK_BUDGET > 0;
    }

    /** Closes the MΦRF pivot-budget window. */
    public static void endMphiWindow() { b().mphiActive = false; }

    /**
     * Charges {@code work} units of LP-setup effort (a solve's tableau area) and aborts the
     * attempt — via {@link BuildBudgetExceeded}, caught in {@link FarkasRanking#prove} —
     * once {@link #BUILD_BUDGET} is spent. Called once per {@link #solve()} so a relaxed
     * round that solves one zero-pivot LP per anchor on a huge SCC is bounded.
     */
    static void chargeBuild(long work) {
        if (BUILD_BUDGET <= 0) return;
        Budget bd = b();
        bd.buildSpent += work;
        if (bd.buildSpent > BUILD_BUDGET) throw new BuildBudgetExceeded();
    }

    /** Construction work charged so far in the current attempt (diagnostics). */
    static long buildSpent() { return b().buildSpent; }

    public Solution solve() {
        // The fraction-free (Bareiss) engine has no free-variable handling; when any
        // variable is free, fall back to the rational engine (which does). Bareiss is an
        // opt-in worst-case coefficient bound, not the measured default, so this only
        // affects the rare -Drati.exactArith=bareiss + native-free combination.
        boolean bareiss = USE_BAREISS && !anyFree;
        // No WORK_BUDGET<=0 shortcut around the try: chargePivot can still throw for
        // the tier-local MPHI_WORK_BUDGET while a multiphase window is open, and that
        // abort must degrade to an infeasible attempt, not escape as an engine error.
        try {
            return bareiss ? solveFractionFree() : solveRational();
        } catch (BudgetExceeded e) {
            return infeasible();
        }
    }

    /** Charges one pivot's worth of work and aborts the attempt if the budget is spent. */
    private static void chargePivot(int m, int cols) {
        Budget bd = b();
        long work = (long) m * cols;
        // Tier-local MΦRF budget (when a multiphase window is open): bounds a degenerate
        // nested-RF grind without raising the global cap that clears the lexicographic tier.
        if (bd.mphiActive) {
            bd.mphiSpent += work;
            if (bd.mphiSpent > MPHI_WORK_BUDGET) throw new BudgetExceeded();
        }
        if (WORK_BUDGET <= 0) return;
        bd.workSpent += work;
        if (bd.workSpent > WORK_BUDGET) throw new BudgetExceeded();
    }

    /**
     * One simplex-tableau row, sparse: parallel arrays of strictly increasing column
     * indices and their nonzero {@link Rational} values (stored zeros never appear; an
     * entry that cancels to zero during a pivot is dropped). Value-wise this is exactly
     * the dense row — {@link #get} returns {@link Rational#ZERO} for an absent column —
     * and every engine decision (entering scan, min-ratio, drive-out, extract) reads
     * values only, so the pivot trajectory is byte-identical to the dense tableau while
     * the storage is proportional to the nonzeros instead of {@code m × cols}.
     */
    private static final class SpRow {
        int[] idx;
        Rational[] val;
        int n;
        SpRow(int cap) { idx = new int[cap]; val = new Rational[cap]; }
        /** Appends {@code (j, v)}; callers append in strictly increasing column order. */
        void append(int j, Rational v) { idx[n] = j; val[n] = v; n++; }
        /** The value in column {@code j} ({@link Rational#ZERO} when absent). */
        Rational get(int j) {
            int lo = 0, hi = n - 1;
            while (lo <= hi) {
                int mid = (lo + hi) >>> 1;
                if (idx[mid] < j) lo = mid + 1;
                else if (idx[mid] > j) hi = mid - 1;
                else return val[mid];
            }
            return Rational.ZERO;
        }
    }

    /**
     * {@code row − f·prow} as a fresh sparse row (ordered merge), dropping entries that
     * cancel to exact zero. Arithmetic matches the dense update per column: both-present
     * {@code v − f·p}, prow-only {@code 0 − f·p}, row-only unchanged (the dense loop
     * skips zero pivot-row entries) — so every produced value, and hence every later
     * sign / ratio test, is identical to the dense engine's.
     */
    private static SpRow subtractScaled(SpRow row, Rational f, SpRow prow) {
        SpRow out = new SpRow(row.n + prow.n);
        int a = 0, b = 0;
        while (a < row.n || b < prow.n) {
            int ja = a < row.n ? row.idx[a] : Integer.MAX_VALUE;
            int jb = b < prow.n ? prow.idx[b] : Integer.MAX_VALUE;
            if (ja < jb) {
                out.append(ja, row.val[a]); a++;
            } else if (jb < ja) {
                out.append(jb, Rational.ZERO.subtract(f.multiply(prow.val[b]))); b++;
            } else {
                Rational v = row.val[a].subtract(f.multiply(prow.val[b]));
                if (!v.isZero()) out.append(ja, v);
                a++; b++;
            }
        }
        return out;
    }

    public Solution solveRational() {
        int m = rows.size();

        // Normalise every row to a non-negative right-hand side.
        Op[] op = new Op[m];
        Rational[] rhs = new Rational[m];
        boolean[] neg = new boolean[m];
        for (int i = 0; i < m; i++) {
            Row r = rows.get(i);
            Rational bi = r.rhs;
            Op oi = r.op;
            if (bi.isNegative()) {
                neg[i] = true;
                bi = bi.negate();
                if (oi == Op.LE) oi = Op.GE; else if (oi == Op.GE) oi = Op.LE;
            }
            rhs[i] = bi; op[i] = oi;
        }

        // Column layout: [structural | slack/surplus | artificial]; the rhs is carried
        // in-row as virtual column `cols`, exactly where the dense tableau kept it.
        int nSlack = 0, nArt = 0;
        for (int i = 0; i < m; i++) {
            if (op[i] == Op.LE) nSlack++;
            else if (op[i] == Op.GE) { nSlack++; nArt++; }
            else nArt++;                     // EQ
        }
        int slackBase = numVars;
        int artBase = numVars + nSlack;
        int cols = numVars + nSlack + nArt;

        // Setup charge: kept at the dense tableau's nominal O(m × cols) — NOT the sparse
        // engine's real O(nonzeros) cost — because the charge determines where an attempt
        // aborts (BUILD_BUDGET) and the abort points must stay byte-identical to the
        // calibrated dense engine's. See BUILD_BUDGET for why setup is charged at all.
        chargeBuild((long) m * cols);

        SpRow[] T = new SpRow[m];
        int[] basis = new int[m];
        boolean[] isArtificial = new boolean[cols];

        int s = slackBase, art = artBase;
        for (int i = 0; i < m; i++) {
            Row r = rows.get(i);
            // Appends stay strictly increasing: structural < numVars ≤ slack < art < cols.
            SpRow row = new SpRow(r.idx.length + 3);
            for (int k = 0; k < r.idx.length; k++)
                row.append(r.idx[k], neg[i] ? r.val[k].negate() : r.val[k]);
            switch (op[i]) {
                case LE:
                    row.append(s, Rational.ONE); basis[i] = s; s++;
                    break;
                case GE:
                    row.append(s, Rational.of(-1)); s++;
                    row.append(art, Rational.ONE); isArtificial[art] = true; basis[i] = art; art++;
                    break;
                default: // EQ
                    row.append(art, Rational.ONE); isArtificial[art] = true; basis[i] = art; art++;
            }
            if (!rhs[i].isZero()) row.append(cols, rhs[i]);
            T[i] = row;
        }

        boolean[] forbidden = new boolean[cols];   // columns barred from entering

        // Column-indexed free flags (a free structural variable is unrestricted in sign;
        // slacks/artificials never are). Null when nothing is free, which keeps the engine
        // on its original all-≥0 path bit-for-bit. The initial basis (slacks/artificials =
        // rhs ≥ 0, every structural at 0) is feasible even with free variables present —
        // 0 is a valid value for a free variable — so no pre-pivot is needed; the free
        // handling lives entirely in the entering/leaving rules of {@link #simplexFree}.
        boolean[] colFree = null;
        if (anyFree) {
            colFree = new boolean[cols];
            for (int j = 0; j < numVars; j++) colFree[j] = free[j];
        }

        // ---- Phase 1: minimise Σ artificials  ⇔  maximise −Σ artificials ----
        if (nArt > 0) {
            Rational[] c1 = new Rational[cols];
            for (int j = 0; j < cols; j++) c1[j] = isArtificial[j] ? Rational.of(-1) : Rational.ZERO;
            Rational[] zrow = buildObjectiveRow(T, basis, c1, m, cols);
            if (!simplex(T, basis, zrow, forbidden, colFree, m, cols)) return infeasible();
            if (zrow[cols].isNegative()) return infeasible();   // Σ artificials > 0

            // Drive any artificial still in the basis out (or accept a redundant row).
            // Sparse rows are sorted, so the first stored entry IS the dense scan's first
            // non-zero column; it qualifies iff it lands before the artificial block.
            for (int i = 0; i < m; i++) {
                if (basis[i] >= artBase) {
                    SpRow row = T[i];
                    if (row.n > 0 && row.idx[0] < artBase) pivot(T, basis, null, m, cols, i, row.idx[0]);
                }
            }
            for (int j = artBase; j < cols; j++) forbidden[j] = true;   // bar artificials in phase 2
        }

        if (objective == null) {
            return new Solution(true, extract(T, basis, m, cols), null);
        }

        // ---- Phase 2: maximise the real objective ----
        Rational[] c2 = new Rational[cols];
        for (int j = 0; j < cols; j++) c2[j] = j < numVars ? objective[j] : Rational.ZERO;
        Rational[] zrow = buildObjectiveRow(T, basis, c2, m, cols);
        if (!simplex(T, basis, zrow, forbidden, colFree, m, cols)) {
            // Unbounded: should not occur for our bounded ranking LPs. Treat as no useful optimum.
            return new Solution(true, extract(T, basis, m, cols), null);
        }
        return new Solution(true, extract(T, basis, m, cols), zrow[cols]);
    }

    // -------------------------------------------------------------------------

    /** Builds the reduced-cost row for cost vector {@code c}, pricing out the basis.
     *  The z-row itself stays dense — it is a single {@code cols+1} vector, and the
     *  entering scans read it by ascending index — only the tableau rows are sparse. */
    private static Rational[] buildObjectiveRow(SpRow[] T, int[] basis,
                                                Rational[] c, int m, int cols) {
        Rational[] z = new Rational[cols + 1];
        for (int j = 0; j < cols; j++) z[j] = c[j].negate();   // zⱼ−cⱼ with z=0 initially
        z[cols] = Rational.ZERO;
        for (int i = 0; i < m; i++) {
            Rational cb = c[basis[i]];
            if (cb.isZero()) continue;
            SpRow row = T[i];
            for (int k = 0; k < row.n; k++)   // the dense loop skipped zeros: same terms, same order
                z[row.idx[k]] = z[row.idx[k]].add(cb.multiply(row.val[k]));
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
     * Dispatches on {@code colFree}: when it is null (no variable is free) the original
     * all-{@code ≥0} engine {@link #simplexNonneg} runs unchanged (byte-identical); when
     * some column is free, {@link #simplexFree} runs the signed-direction variant.
     */
    private static boolean simplex(SpRow[] T, int[] basis, Rational[] z,
                                   boolean[] forbidden, boolean[] colFree, int m, int cols) {
        return colFree == null
                ? simplexNonneg(T, basis, z, forbidden, m, cols)
                : simplexFree(T, basis, z, forbidden, colFree, m, cols);
    }

    /**
     * All-{@code ≥0} simplex (every variable non-negative). Optimal when every non-forbidden
     * reduced cost {@code z[j] ≥ 0}; the entering column is priced per {@link #PRICING_BLAND}
     * (Dantzig with Bland fallback, or pure Bland), the leaving row by min-ratio with a
     * smallest-basis-index tie-break.
     */
    private static boolean simplexNonneg(SpRow[] T, int[] basis, Rational[] z,
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
                Rational tipc = T[i].get(pc);
                if (!tipc.isPositive()) continue;
                Rational ratio = T[i].get(cols).divide(tipc);
                if (best == null || ratio.compareTo(best) < 0
                        || (ratio.compareTo(best) == 0 && basis[i] < basis[pr])) {
                    best = ratio; pr = i;
                }
            }
            if (pr < 0) return false;                         // unbounded
            chargePivot(m, cols);
            pivot(T, basis, z, m, cols, pr, pc);

            // Anti-cycling: a long run of degenerate pivots (zero min-ratio ⇒ no
            // objective progress) flips pricing to Bland, which cannot cycle.
            if (!bland) {
                if (best.isZero()) { if (++stall > blandTrigger) bland = true; }
                else stall = 0;
            }
        }
    }

    /**
     * Simplex with free (unrestricted-in-sign) variables, flagged in {@code colFree}. It
     * differs from {@link #simplexNonneg} in exactly two rules, the textbook treatment of an
     * unrestricted variable:
     * <ul>
     *   <li><b>Entering</b> — a non-basic free variable sits at 0 (a feasible start) but is
     *       eligible to enter whenever its reduced cost is <em>non-zero</em>, in either
     *       direction: {@code z[j] < 0} ⇒ increase ({@code dir=+1}), {@code z[j] > 0} ⇒
     *       decrease ({@code dir=-1}). A {@code ≥0} variable enters only on {@code z[j] < 0}
     *       (increase), as before. Optimal ⇔ no eligible column remains.</li>
     *   <li><b>Leaving</b> — the ratio test bounds how far the entering variable moves so that
     *       every <em>non-free</em> basic variable stays {@code ≥0}; the limiting rows are
     *       those with {@code dir·T[i][pc] > 0}. A free basic variable has no lower bound, so
     *       its row never limits the move and it never leaves — once basic, it stays basic.</li>
     * </ul>
     * The Gauss-Jordan {@link #pivot} is direction-agnostic (for {@code dir=-1} the pivot is on
     * a negative entry, which the exact-rational pivot handles), and the resulting basic value
     * of a free variable may be negative — correct, and read straight out by {@link #extract}.
     * Bland's rule (smallest eligible index in, smallest basis index out) still bounds the pivot
     * count, so termination holds. Equivalent to the caller-side pos/neg split: same feasibility
     * and same optimum, one column per free coefficient instead of two.
     */
    private static boolean simplexFree(SpRow[] T, int[] basis, Rational[] z,
                                       boolean[] forbidden, boolean[] colFree, int m, int cols) {
        boolean bland = PRICING_BLAND;
        int stall = 0;
        final int blandTrigger = 2 * (m + cols) + 64;
        while (true) {
            int pc = -1, dir = 0;
            if (bland) {
                for (int j = 0; j < cols; j++) {
                    if (forbidden[j]) continue;
                    if (colFree[j]) {
                        if (!z[j].isZero()) { pc = j; dir = z[j].isNegative() ? 1 : -1; break; }
                    } else if (z[j].isNegative()) { pc = j; dir = 1; break; }
                }
            } else {
                // Dantzig: largest per-step objective gain |z[j]| among eligible columns.
                Rational bestGain = null;
                for (int j = 0; j < cols; j++) {
                    if (forbidden[j]) continue;
                    int d = 0;
                    if (colFree[j]) { if (!z[j].isZero()) d = z[j].isNegative() ? 1 : -1; }
                    else if (z[j].isNegative()) d = 1;
                    if (d == 0) continue;
                    Rational gain = d == 1 ? z[j].negate() : z[j];   // = |z[j]|
                    if (bestGain == null || gain.compareTo(bestGain) > 0) {
                        bestGain = gain; pc = j; dir = d;
                    }
                }
            }
            if (pc < 0) return true;                          // optimal

            // Leaving row: keep every non-free basic var ≥ 0 as the entering var moves by
            // t ≥ 0 in direction `dir`. Basic_i decreases at rate dir·T[i][pc]; rows where
            // that rate is positive limit t. Free-basic rows are skipped (no lower bound).
            int pr = -1;
            Rational best = null;
            for (int i = 0; i < m; i++) {
                if (colFree[basis[i]]) continue;             // free basic var never leaves
                Rational tipc = T[i].get(pc);
                Rational coef = dir == 1 ? tipc : tipc.negate();
                if (!coef.isPositive()) continue;
                Rational ratio = T[i].get(cols).divide(coef);
                if (best == null || ratio.compareTo(best) < 0
                        || (ratio.compareTo(best) == 0 && basis[i] < basis[pr])) {
                    best = ratio; pr = i;
                }
            }
            if (pr < 0) return false;                         // unbounded
            chargePivot(m, cols);
            pivot(T, basis, z, m, cols, pr, pc);

            if (!bland) {
                if (best.isZero()) { if (++stall > blandTrigger) bland = true; }
                else stall = 0;
            }
        }
    }

    /** Gauss-Jordan pivot at {@code (pr,pc)}; updates basis and (if given) z-row.
     *  Structurally sparse: the pivot row's stored entries ARE the nonzeros the dense
     *  update iterated (it skipped zeros), so dividing them, merging them into each
     *  affected row ({@link #subtractScaled}) and pricing them out of the z-row perform
     *  the same exact-rational operations in the same order — byte-identical basis,
     *  optimum and certificate — without ever touching an absent (zero) column. */
    private static void pivot(SpRow[] T, int[] basis, Rational[] z,
                              int m, int cols, int pr, int pc) {
        SpRow prow = T[pr];
        Rational p = prow.get(pc);
        for (int k = 0; k < prow.n; k++) prow.val[k] = prow.val[k].divide(p);   // nonzero/p ≠ 0
        for (int i = 0; i < m; i++) {
            if (i == pr) continue;
            Rational f = T[i].get(pc);
            if (f.isZero()) continue;
            T[i] = subtractScaled(T[i], f, prow);
        }
        if (z != null) {
            Rational f = z[pc];
            if (!f.isZero())
                for (int k = 0; k < prow.n; k++)
                    z[prow.idx[k]] = z[prow.idx[k]].subtract(f.multiply(prow.val[k]));
        }
        basis[pr] = pc;
    }

    private Rational[] extract(SpRow[] T, int[] basis, int m, int cols) {
        Rational[] x = new Rational[numVars];
        for (int j = 0; j < numVars; j++) x[j] = Rational.ZERO;
        for (int i = 0; i < m; i++)
            if (basis[i] < numVars) x[basis[i]] = T[i].get(cols);
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
            Rational[] ai = r.dense(numVars);   // Bareiss keeps its dense integer tableau
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

        // Setup cost (see solveRational): O(m × cols) tableau + objective-row work before
        // the first charged pivot. Bounds the per-anchor relaxed round on huge SCCs.
        chargeBuild((long) m * cols);

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
            chargePivot(m, cols);
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
