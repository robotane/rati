package fr.univreunion.rati.ranking;

import static org.junit.Assert.assertEquals;

import java.util.Random;

import org.junit.Test;

/**
 * Property test for the two exact simplex engines: {@link LinearProgram#solveRational()}
 * (the default) and {@link LinearProgram#solveFractionFree()} (the opt-in Bareiss engine,
 * {@code -Drati.exactArith=bareiss}). Their contract — see the {@code USE_BAREISS} doc —
 * is that both follow the identical Bland pivot trajectory, so on any LP they must agree
 * on feasibility, on the optimal point and on the optimum (or its absence, when the
 * objective is unbounded). The corpus validation showed 0 differences; this pins the
 * contract on randomly generated LPs so a future edit to either engine that breaks the
 * lockstep fails here instead of surfacing as a corpus verdict flip.
 *
 * <p>Free variables are excluded: the Bareiss engine has no {@code markFree} handling
 * ({@link LinearProgram#solve()} already falls back to the rational engine there).
 * The seed is fixed — the point is a broad deterministic sweep, not flaky fuzzing.
 */
public class SimplexEnginesPropertyTest {

    private static final int CASES = 500;

    @Test
    public void enginesAgreeOnRandomLps() {
        Random rnd = new Random(20260703L);
        for (int c = 0; c < CASES; c++) {
            int numVars = 1 + rnd.nextInt(5);
            int numRows = 1 + rnd.nextInt(7);
            boolean withObjective = rnd.nextBoolean();

            LinearProgram a = new LinearProgram(numVars);
            LinearProgram b = new LinearProgram(numVars);
            for (int i = 0; i < numRows; i++) {
                Rational[] coeffs = new Rational[numVars];
                boolean allZero = true;
                for (int j = 0; j < numVars; j++) {
                    coeffs[j] = Rational.of(rnd.nextInt(11) - 5);
                    if (!coeffs[j].isZero()) allZero = false;
                }
                if (allZero) coeffs[rnd.nextInt(numVars)] = Rational.of(1);
                LinearProgram.Op op = LinearProgram.Op.values()[rnd.nextInt(3)];
                Rational rhs = Rational.of(rnd.nextInt(21) - 10);
                a.addConstraint(coeffs.clone(), op, rhs);
                b.addConstraint(coeffs.clone(), op, rhs);
            }
            if (withObjective) {
                Rational[] obj = new Rational[numVars];
                for (int j = 0; j < numVars; j++) obj[j] = Rational.of(rnd.nextInt(11) - 5);
                a.setObjective(obj.clone());
                b.setObjective(obj.clone());
            }

            LinearProgram.Solution sr = a.solveRational();
            LinearProgram.Solution sf = b.solveFractionFree();

            String at = "case " + c + " (vars=" + numVars + ", rows=" + numRows
                    + ", obj=" + withObjective + ")";
            assertEquals(at + ": feasibility", sr.feasible, sf.feasible);
            if (!sr.feasible) continue;
            assertEquals(at + ": optimum", sr.objective, sf.objective);
            for (int j = 0; j < numVars; j++)
                assertEquals(at + ": x[" + j + "]", sr.x[j], sf.x[j]);
        }
    }
}
