package fr.univreunion.rati.ranking;

import static org.junit.Assert.assertEquals;

import java.util.Arrays;

import org.junit.Test;

import fr.univreunion.rati.its.ItsLinearConstraint;
import fr.univreunion.rati.its.ItsLinearConstraint.Op;
import fr.univreunion.rati.its.ItsLinearExpression;
import fr.univreunion.rati.its.ItsLocation;
import fr.univreunion.rati.its.ItsTransition;

/**
 * Disjunctive termination (transition invariants) on the canonical multiphase loop
 * that has neither a single/lexicographic LRF nor a MΦRF — {@code while (x>0 || y>0)
 * { if (x>0) x-- else y-- }} — proved by the union of the two well-founded relations
 * {@code R_1 = {x≥0 ∧ Δx≥1}} and {@code R_2 = {y≥0 ∧ Δy≥1}}.
 */
public class DisjunctiveTerminationTest {

    private static ItsLinearExpression expr(long constant, Object... pairs) {
        ItsLinearExpression.Builder b = new ItsLinearExpression.Builder();
        b.addConstant(constant);
        for (int i = 0; i < pairs.length; i += 2) b.addTerm((String) pairs[i], (Long) pairs[i + 1]);
        return b.build();
    }
    private static ItsLinearConstraint ge(ItsLinearExpression e) { return new ItsLinearConstraint(e, Op.GE); }

    @Test
    public void multiphaseLoop_provedByTransitionInvariant() {
        ItsLocation l = new ItsLocation("L", Arrays.asList("X", "Y"));
        // τ_A:  x ≥ 1,  x' = x-1, y' = y
        ItsTransition a = new ItsTransition(l, l,
                Arrays.asList(ge(expr(-1, "X", 1L))),
                Arrays.asList(expr(-1, "X", 1L), expr(0, "Y", 1L)));
        // τ_B:  x ≤ 0 ∧ y ≥ 1,  x' = x, y' = y-1
        ItsTransition b = new ItsTransition(l, l,
                Arrays.asList(ge(expr(0, "X", -1L)), ge(expr(-1, "Y", 1L))),
                Arrays.asList(expr(0, "X", 1L), expr(-1, "Y", 1L)));
        assertEquals(true, DisjunctiveTermination.terminates(Arrays.asList(a, b)));
    }

    @Test
    public void nonTerminatingIncrement_notProved() {
        // L(x) -> L(x+1) : diverges; no disjunctively well-founded transition invariant.
        ItsLocation l = new ItsLocation("L", Arrays.asList("X"));
        ItsTransition t = new ItsTransition(l, l,
                java.util.Collections.<ItsLinearConstraint>emptyList(),
                Arrays.asList(expr(1, "X", 1L)));
        assertEquals(false, DisjunctiveTermination.terminates(Arrays.asList(t)));
    }
}
