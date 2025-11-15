package fr.univreunion.rati.ranking;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.junit.Test;

import apron.Abstract1;
import apron.Environment;
import apron.Lincons1;
import apron.Manager;
import apron.Polka;

import fr.univreunion.rati.its.ItsLinearConstraint;
import fr.univreunion.rati.its.ItsLinearConstraint.Op;
import fr.univreunion.rati.its.ItsLinearExpression;
import fr.univreunion.rati.its.ItsLocation;
import fr.univreunion.rati.its.ItsTransition;

/**
 * Exactness of the ITS ↔ Apron bridge on coefficients that the old conversion
 * silently corrupted: an {@code (int)} cast truncates anything past 2³¹ and
 * {@code toDouble + Math.round} anything past 2⁵³. Each test uses such a value
 * and asserts the behaviour only an exact path can produce.
 */
public class ApronBridgeTest {

    private static final long BIG = 1L << 32;   // past int range, exact in long

    private static ItsLinearExpression expr(long constant, Object... pairs) {
        ItsLinearExpression.Builder b = new ItsLinearExpression.Builder();
        b.addConstant(constant);
        for (int i = 0; i < pairs.length; i += 2) b.addTerm((String) pairs[i], (Long) pairs[i + 1]);
        return b.build();
    }

    @Test
    public void bigCoefficient_roundTripsExactly() throws Exception {
        // 2³²·X − 2³² ≥ 0 (i.e. X ≥ 1). The old (int) cast turned 2³² into 0,
        // making the polyhedron "−0 ≥ 0" garbage. Exact read-back must yield a
        // single constraint equivalent to X ≥ 1: k·X − k ≥ 0 with k > 0.
        Manager man = new Polka(false);
        Environment env = new Environment(new String[0], new String[]{"X"});
        ItsLinearConstraint c = new ItsLinearConstraint(expr(-BIG, "X", BIG), Op.GE);
        Abstract1 a = new Abstract1(man, env)
                .meetCopy(man, new Lincons1[]{ApronBridge.toLincons(env, c)});

        List<ItsLinearConstraint> back = ApronBridge.toConstraints(man, a);
        assertEquals(1, back.size());
        ItsLinearConstraint r = back.get(0);
        assertEquals(Op.GE, r.op());
        long k = r.lhs().coefficient("X");
        assertTrue(k > 0);
        assertEquals(-k, r.lhs().constant());
    }

    @Test
    public void isInfeasible_doesNotInventInfeasibilityOnBigCoefficients() {
        // Guard 2³²·X − 1 ≥ 0 is satisfiable (X ≥ 1). With the truncating cast it
        // became 0·X − 1 ≥ 0 — bottom — and the transition was wrongly PRUNED
        // from its SCC, a path to a false TERMINATES.
        ItsLocation l = new ItsLocation("L", Arrays.asList("X"));
        ItsTransition t = new ItsTransition(l, l,
                Arrays.asList(new ItsLinearConstraint(expr(-1, "X", BIG), Op.GE)),
                Arrays.asList(expr(0, "X", 1L)));
        assertFalse(ItsInvariants.isInfeasible(t));
    }

    @Test
    public void isInfeasible_stillDetectsRealContradictions() {
        // X ≥ 1 ∧ −X ≥ 0 is empty; the exact path must keep finding it.
        ItsLocation l = new ItsLocation("L", Arrays.asList("X"));
        ItsTransition t = new ItsTransition(l, l,
                Arrays.asList(
                        new ItsLinearConstraint(expr(-1, "X", 1L), Op.GE),
                        new ItsLinearConstraint(expr(0, "X", -1L), Op.GE)),
                Arrays.asList(expr(0, "X", 1L)));
        assertTrue(ItsInvariants.isInfeasible(t));
    }

    @Test
    public void entailsNonNegative_exactBeyondIntRange() {
        // Premise X − (2³²+1) ≥ 0 entails X ≥ 0. The old (int) casts mangled the
        // premise's constant, losing the entailment (or worse, flipping one).
        List<ItsLinearExpression> premises =
                Collections.singletonList(expr(-(BIG + 1), "X", 1L));
        Map<String, Long> rho = new LinkedHashMap<String, Long>();
        rho.put("X", 1L);
        assertTrue(ItsInvariants.entailsNonNegative(premises, rho, 0));
        // Control: X ≥ 0 does not entail X − 5 ≥ 0.
        List<ItsLinearExpression> weak = Collections.singletonList(expr(0, "X", 1L));
        assertFalse(ItsInvariants.entailsNonNegative(weak, rho, -5));
    }
}
