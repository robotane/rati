package fr.univreunion.rati.ranking;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

/** Exact two-phase simplex sanity checks (the engine under {@link FarkasRanking}). */
public class LinearProgramTest {

    private static Rational[] row(long... v) {
        Rational[] r = new Rational[v.length];
        for (int i = 0; i < v.length; i++) r[i] = Rational.of(v[i]);
        return r;
    }

    @Test
    public void maximiseWithUpperBounds() {
        // max x+y  s.t.  x+y ≤ 4, x ≤ 3, y ≤ 3, x,y ≥ 0  → 4
        LinearProgram lp = new LinearProgram(2);
        lp.addConstraint(row(1, 1), LinearProgram.Op.LE, Rational.of(4));
        lp.addConstraint(row(1, 0), LinearProgram.Op.LE, Rational.of(3));
        lp.addConstraint(row(0, 1), LinearProgram.Op.LE, Rational.of(3));
        lp.setObjective(row(1, 1));
        LinearProgram.Solution s = lp.solve();
        assertTrue(s.feasible);
        assertEquals(Rational.of(4), s.objective);
    }

    @Test
    public void infeasibleContradiction() {
        // x ≤ 1 ∧ x ≥ 2  → infeasible
        LinearProgram lp = new LinearProgram(1);
        lp.addConstraint(row(1), LinearProgram.Op.LE, Rational.of(1));
        lp.addConstraint(row(1), LinearProgram.Op.GE, Rational.of(2));
        assertFalse(lp.solve().feasible);
    }

    @Test
    public void equalityConstraint() {
        // max x  s.t.  x+y = 2, x ≤ 1  → x=1, y=1, opt=1
        LinearProgram lp = new LinearProgram(2);
        lp.addConstraint(row(1, 1), LinearProgram.Op.EQ, Rational.of(2));
        lp.addConstraint(row(1, 0), LinearProgram.Op.LE, Rational.of(1));
        lp.setObjective(row(1, 0));
        LinearProgram.Solution s = lp.solve();
        assertTrue(s.feasible);
        assertEquals(Rational.of(1), s.objective);
        assertEquals(Rational.of(1), s.x[0]);
        assertEquals(Rational.of(1), s.x[1]);
    }

    @Test
    public void feasibilityOnlyWithEqualities() {
        LinearProgram lp = new LinearProgram(2);
        lp.addConstraint(row(1, 1), LinearProgram.Op.EQ, Rational.of(2));
        lp.addConstraint(row(1, 0), LinearProgram.Op.LE, Rational.of(1));
        LinearProgram.Solution s = lp.solve();
        assertTrue(s.feasible);
    }

    @Test
    public void fractionalOptimum() {
        // max y  s.t.  2y ≤ 3  → 3/2
        LinearProgram lp = new LinearProgram(1);
        lp.addConstraint(row(2), LinearProgram.Op.LE, Rational.of(3));
        lp.setObjective(row(1));
        LinearProgram.Solution s = lp.solve();
        assertTrue(s.feasible);
        assertEquals(Rational.of(3, 2), s.objective);
    }

    // ---- Free (unrestricted-in-sign) variables: markFree ----

    @Test
    public void freeVarTakesNegativeValue() {
        // max x  s.t.  x + y = -3, x ≤ 5, y free  → x=5, y=-8 (impossible if y ≥ 0).
        LinearProgram lp = new LinearProgram(2);
        lp.addConstraint(row(1, 1), LinearProgram.Op.EQ, Rational.of(-3));
        lp.addConstraint(row(1, 0), LinearProgram.Op.LE, Rational.of(5));
        lp.markFree(1);
        lp.setObjective(row(1, 0));
        LinearProgram.Solution s = lp.solve();
        assertTrue(s.feasible);
        assertEquals(Rational.of(5), s.objective);
        assertEquals(Rational.of(5), s.x[0]);
        assertEquals(Rational.of(-8), s.x[1]);
    }

    @Test
    public void freeVarEntersDecreasing() {
        // max y  s.t.  x + y = 0, y ≤ 4, x free  → y=4, x=-4 (x enters in the − direction).
        LinearProgram lp = new LinearProgram(2);
        lp.addConstraint(row(1, 1), LinearProgram.Op.EQ, Rational.of(0));
        lp.addConstraint(row(0, 1), LinearProgram.Op.LE, Rational.of(4));
        lp.markFree(0);
        lp.setObjective(row(0, 1));
        LinearProgram.Solution s = lp.solve();
        assertTrue(s.feasible);
        assertEquals(Rational.of(4), s.objective);
        assertEquals(Rational.of(-4), s.x[0]);
        assertEquals(Rational.of(4), s.x[1]);
    }

    @Test
    public void freeVarStillRespectsContradiction() {
        // x = 1 ∧ x = 2 is infeasible even when x is free (no value satisfies both).
        LinearProgram lp = new LinearProgram(1);
        lp.addConstraint(row(1), LinearProgram.Op.EQ, Rational.of(1));
        lp.addConstraint(row(1), LinearProgram.Op.EQ, Rational.of(2));
        lp.markFree(0);
        assertFalse(lp.solve().feasible);
    }

    @Test
    public void freeVarMatchesPosNegSplit() {
        // The native free variable must give the same optimum as the caller-side pos/neg
        // split it replaces. Model the same problem both ways and compare.
        //   max t  s.t.  t ≤ 4,  c + t = 1,  c ≥ -10   (c free, t ≥ 0)
        // Native: variables [c (free), t].
        LinearProgram nat = new LinearProgram(2);
        nat.addConstraint(row(0, 1), LinearProgram.Op.LE, Rational.of(4));
        nat.addConstraint(row(1, 1), LinearProgram.Op.EQ, Rational.of(1));
        nat.addConstraint(row(1, 0), LinearProgram.Op.GE, Rational.of(-10));
        nat.markFree(0);
        nat.setObjective(row(0, 1));
        LinearProgram.Solution sn = nat.solve();

        // Split: variables [cPos, cNeg, t] with c = cPos − cNeg, all ≥ 0.
        LinearProgram split = new LinearProgram(3);
        split.addConstraint(row(0, 0, 1), LinearProgram.Op.LE, Rational.of(4));
        split.addConstraint(row(1, -1, 1), LinearProgram.Op.EQ, Rational.of(1));
        split.addConstraint(row(1, -1, 0), LinearProgram.Op.GE, Rational.of(-10));
        split.setObjective(row(0, 0, 1));
        LinearProgram.Solution ss = split.solve();

        assertTrue(sn.feasible);
        assertTrue(ss.feasible);
        assertEquals(ss.objective, sn.objective);
        // And the reconstructed free coefficient agrees.
        assertEquals(ss.x[0].subtract(ss.x[1]), sn.x[0]);
    }
}
