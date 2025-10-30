package fr.univreunion.rati.ranking;

import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.List;

import org.junit.Test;

import fr.univreunion.rati.its.IntegerTransitionSystem;
import fr.univreunion.rati.its.ItsLinearConstraint;
import fr.univreunion.rati.its.ItsLinearConstraint.Op;
import fr.univreunion.rati.its.ItsLinearExpression;
import fr.univreunion.rati.its.ItsLocation;
import fr.univreunion.rati.its.ItsTransition;

/** ADFG lexicographic linear-ranking synthesis on hand-built transition systems. */
public class FarkasRankingTest {

    // ---- tiny DSL --------------------------------------------------------

    /** expr = c0 + Σ coeff·var, given as alternating (var,coeff) pairs then a trailing const. */
    private static ItsLinearExpression expr(long constant, Object... pairs) {
        ItsLinearExpression.Builder b = new ItsLinearExpression.Builder();
        b.addConstant(constant);
        for (int i = 0; i < pairs.length; i += 2) b.addTerm((String) pairs[i], (Long) pairs[i + 1]);
        return b.build();
    }

    private static ItsLinearConstraint ge(ItsLinearExpression lhs) { return new ItsLinearConstraint(lhs, Op.GE); }

    @Test
    public void singleCounterLoopTerminates() {
        // L(i) -> L(i-1)  guard i ≥ 1   (i.e. i-1 ≥ 0)
        ItsLocation l = new ItsLocation("L", Arrays.asList("I"));
        IntegerTransitionSystem its = new IntegerTransitionSystem("t", "L");
        its.addLocation(l);
        its.addTransition(new ItsTransition(l, l,
                Arrays.asList(ge(expr(-1, "I", 1L))),          // I - 1 ≥ 0
                Arrays.asList(expr(-1, "I", 1L))));            // I' = I - 1
        assertEquals(FarkasRanking.Verdict.TERMINATES, FarkasRanking.prove(its, "L"));
    }

    @Test
    public void lexicographicTwoComponentTerminates() {
        // L(x,y): t1 = decrease y (x fixed), t2 = decrease x (reset y := x).
        // No single linear function ranks both; the (x then y) lexicographic order does.
        ItsLocation l = new ItsLocation("L", Arrays.asList("X", "Y"));
        IntegerTransitionSystem its = new IntegerTransitionSystem("t", "L");
        its.addLocation(l);
        // t1: guard x ≥ 0 ∧ y ≥ 1,  x' = x, y' = y - 1
        its.addTransition(new ItsTransition(l, l,
                Arrays.asList(ge(expr(0, "X", 1L)), ge(expr(-1, "Y", 1L))),
                Arrays.asList(expr(0, "X", 1L), expr(-1, "Y", 1L))));
        // t2: guard x ≥ 1 ∧ y ≥ 0,  x' = x - 1, y' = x
        its.addTransition(new ItsTransition(l, l,
                Arrays.asList(ge(expr(-1, "X", 1L)), ge(expr(0, "Y", 1L))),
                Arrays.asList(expr(-1, "X", 1L), expr(0, "X", 1L))));
        assertEquals(FarkasRanking.Verdict.TERMINATES, FarkasRanking.prove(its, "L"));
    }

    @Test
    public void unboundedIncrementIsUnknown() {
        // L(x) -> L(x+1)  guard true  — diverges, no linear ranking function.
        ItsLocation l = new ItsLocation("L", Arrays.asList("X"));
        IntegerTransitionSystem its = new IntegerTransitionSystem("t", "L");
        its.addLocation(l);
        its.addTransition(new ItsTransition(l, l,
                java.util.Collections.<ItsLinearConstraint>emptyList(),
                Arrays.asList(expr(1, "X", 1L))));             // X' = X + 1
        assertEquals(FarkasRanking.Verdict.UNKNOWN, FarkasRanking.prove(its, "L"));
    }

    @Test
    public void identitySelfLoopIsUnknown() {
        // L(x) -> L(x)  guard true — stutter, no decrease.
        ItsLocation l = new ItsLocation("L", Arrays.asList("X"));
        IntegerTransitionSystem its = new IntegerTransitionSystem("t", "L");
        its.addLocation(l);
        its.addTransition(new ItsTransition(l, l,
                java.util.Collections.<ItsLinearConstraint>emptyList(),
                Arrays.asList(expr(0, "X", 1L))));
        assertEquals(FarkasRanking.Verdict.UNKNOWN, FarkasRanking.prove(its, "L"));
    }

    @Test
    public void twoLocationCycleTerminates() {
        // A(n) -> B(n) [n ≥ 1] ; B(n) -> A(n-1) — a 2-node SCC ranked by n.
        ItsLocation a = new ItsLocation("A", Arrays.asList("N"));
        ItsLocation b = new ItsLocation("B", Arrays.asList("N"));
        IntegerTransitionSystem its = new IntegerTransitionSystem("t", "A");
        its.addLocation(a); its.addLocation(b);
        its.addTransition(new ItsTransition(a, b,
                Arrays.asList(ge(expr(-1, "N", 1L))),
                Arrays.asList(expr(0, "N", 1L))));             // N' = N
        its.addTransition(new ItsTransition(b, a,
                Arrays.asList(ge(expr(0, "N", 1L))),           // length invariant N ≥ 0
                Arrays.asList(expr(-1, "N", 1L))));            // N' = N - 1
        assertEquals(FarkasRanking.Verdict.TERMINATES, FarkasRanking.prove(its, "A"));
    }

    @Test
    public void multiphaseLoop_rankedByMphiRF_notByLexicographic() {
        // Ben-Amram-Genaim loop (1): while (x ≥ -z) do x'=x+y, y'=y+z, z'=z-1.
        // No single/lexicographic LRF (y and z are unbounded below, so neither can
        // bound a ranking function); it has the MΦRF ⟨z+1, y+1, x⟩ of depth 3.
        ItsLocation l = new ItsLocation("L", Arrays.asList("X", "Y", "Z"));
        IntegerTransitionSystem its = new IntegerTransitionSystem("t", "L");
        its.addLocation(l);
        its.addTransition(new ItsTransition(l, l,
                Arrays.asList(ge(expr(0, "X", 1L, "Z", 1L))),       // X + Z ≥ 0  (x ≥ -z)
                Arrays.asList(expr(0, "X", 1L, "Y", 1L),            // X' = X + Y
                              expr(0, "Y", 1L, "Z", 1L),            // Y' = Y + Z
                              expr(-1, "Z", 1L))));                 // Z' = Z - 1
        // The MΦRF synthesiser proves it directly (no invariants needed here)…
        assertEquals(true, MultiphaseRanking.ranks(its.transitions(),
                new java.util.HashMap<String, java.util.List<ItsLinearConstraint>>()));
        // …and the full prover discharges it via the MΦRF fallback.
        assertEquals(FarkasRanking.Verdict.TERMINATES, FarkasRanking.prove(its, "L"));
    }

    @Test
    public void acyclicIsTrivallyTerminating() {
        // A -> B, no cycle: nothing to rank.
        ItsLocation a = new ItsLocation("A", Arrays.asList("N"));
        ItsLocation b = new ItsLocation("B", Arrays.asList("N"));
        IntegerTransitionSystem its = new IntegerTransitionSystem("t", "A");
        its.addLocation(a); its.addLocation(b);
        its.addTransition(new ItsTransition(a, b,
                java.util.Collections.<ItsLinearConstraint>emptyList(),
                Arrays.asList(expr(0, "N", 1L))));
        assertEquals(FarkasRanking.Verdict.TERMINATES, FarkasRanking.prove(its, "A"));
    }
}
