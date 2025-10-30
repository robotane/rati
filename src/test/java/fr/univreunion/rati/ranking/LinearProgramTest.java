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
}
