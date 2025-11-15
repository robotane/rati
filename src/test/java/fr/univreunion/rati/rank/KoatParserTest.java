package fr.univreunion.rati.rank;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.junit.Test;

import fr.univreunion.rati.its.IntegerTransitionSystem;
import fr.univreunion.rati.its.ItsLinearConstraint;
import fr.univreunion.rati.its.ItsLinearExpression;
import fr.univreunion.rati.its.ItsLocation;
import fr.univreunion.rati.its.ItsTransition;
import fr.univreunion.rati.its.KoatPrinter;
import fr.univreunion.rati.ranking.FarkasRanking;

/**
 * {@link KoatParser} is the inverse of {@link KoatPrinter}: this verifies the
 * expression/constraint grammar and a full print → parse → prove round-trip,
 * so the standalone solver reads exactly what the BCTerm pipeline writes.
 */
public class KoatParserTest {

    // ---- expression grammar ------------------------------------------------

    @Test
    public void parsesSignedMultiTermExpression() {
        ItsLinearExpression e = KoatParser.parseExpr("LI2 - LO2 - 1");
        assertEquals(1L, e.coefficient("LI2"));
        assertEquals(-1L, e.coefficient("LO2"));
        assertEquals(-1L, e.constant());
    }

    @Test
    public void parsesLeadingNegativeAndCoefficients() {
        ItsLinearExpression e = KoatParser.parseExpr("-LI0 + 2*LO0 + 3");
        assertEquals(-1L, e.coefficient("LI0"));
        assertEquals(2L, e.coefficient("LO0"));
        assertEquals(3L, e.constant());
    }

    @Test
    public void parsesZeroAndBareVariable() {
        assertTrue(KoatParser.parseExpr("0").isConstant());
        assertEquals(0L, KoatParser.parseExpr("0").constant());
        ItsLinearExpression v = KoatParser.parseExpr("LO1");
        assertEquals(1L, v.coefficient("LO1"));
        assertEquals(0L, v.constant());
    }

    @Test
    public void parsesConstraintWithRhsZero() {
        ItsLinearConstraint c = KoatParser.parseConstraint("LI2 - LO2 - 1 >= 0");
        assertEquals(ItsLinearConstraint.Op.GE, c.op());
        assertEquals(1L, c.lhs().coefficient("LI2"));
        assertEquals(-1L, c.lhs().coefficient("LO2"));
        assertEquals(-1L, c.lhs().constant());
    }

    @Test
    public void roundTripExpressionThroughToString() {
        // toString() output must parse back to the same coefficients.
        ItsLinearExpression e = new ItsLinearExpression.Builder()
                .addTerm("LI0", -1).addTerm("SO3", 2).addConstant(-5).build();
        ItsLinearExpression back = KoatParser.parseExpr(e.toString());
        assertEquals(-1L, back.coefficient("LI0"));
        assertEquals(2L, back.coefficient("SO3"));
        assertEquals(-5L, back.constant());
    }

    // ---- operator coverage + malformed-token rejection (R1) ----------------

    @Test
    public void parsesLessEqualBySwappingSides() {
        // A <= B  ≡  B - A >= 0. (legal KoAT/termCOMP; must not mis-split on '=')
        ItsLinearConstraint c = KoatParser.parseConstraint("LI0 <= LO0");
        assertEquals(ItsLinearConstraint.Op.GE, c.op());
        assertEquals(-1L, c.lhs().coefficient("LI0"));
        assertEquals(1L, c.lhs().coefficient("LO0"));
    }

    @Test
    public void parsesStrictLessBySwappingSides() {
        // A < B  ≡  B - A > 0.
        ItsLinearConstraint c = KoatParser.parseConstraint("LI0 < 5");
        assertEquals(ItsLinearConstraint.Op.GT, c.op());
        assertEquals(-1L, c.lhs().coefficient("LI0"));
        assertEquals(5L, c.lhs().constant());
    }

    @Test
    public void unspacedMinusParsesToTheRealForm_notAPhantomVariable() {
        // No spaces around the minus: the old spaced-operator splitter could only
        // reject this (the phantom-variable hazard); the tokenising parser reads
        // the intended linear form instead. See KoatExprTest for the full grammar.
        fr.univreunion.rati.its.ItsLinearExpression e = KoatParser.parseExpr("LI2-LO2-1");
        assertEquals(1L, e.coefficient("LI2"));
        assertEquals(-1L, e.coefficient("LO2"));
        assertEquals(-1L, e.constant());
        assertEquals(2, e.variables().size());
    }

    @Test(expected = IllegalArgumentException.class)
    public void rejectsStrayComparisonFragmentAsVariable() {
        // "A <" (e.g. a mis-split operator) is not a valid identifier.
        KoatParser.parseExpr("A <");
    }

    // ---- full print → parse → prove round-trip -----------------------------

    @Test
    public void roundTripDownCounterTerminates() {
        // loop: while (i >= 1) i = i - 1;  ranks by rho = i.
        // The real entry is "b_start"; KoatPrinter adds its own synthetic
        // "koat_init -> b_start" wrapper rule (so the start has no in-edge).
        IntegerTransitionSystem its = new IntegerTransitionSystem("t", "");
        List<String> vars = Arrays.asList("LI0");
        ItsLocation start = new ItsLocation("b_start", vars);
        ItsLocation loop = new ItsLocation("loop", vars);
        its.addLocation(start);
        its.addLocation(loop);
        // b_start -> loop : identity
        its.addTransition(new ItsTransition(start, loop,
                Collections.<ItsLinearConstraint>emptyList(),
                Arrays.asList(ItsLinearExpression.variable("LI0"))));
        // loop -> loop : guard (LI0 - 1 >= 0), update LI0 := LI0 - 1
        ItsLinearConstraint guard = new ItsLinearConstraint(
                new ItsLinearExpression.Builder().addTerm("LI0", 1).addConstant(-1).build(),
                ItsLinearConstraint.Op.GE);
        ItsLinearExpression dec =
                new ItsLinearExpression.Builder().addTerm("LI0", 1).addConstant(-1).build();
        its.addTransition(new ItsTransition(loop, loop,
                Arrays.asList(guard), Arrays.asList(dec)));

        String koat = KoatPrinter.print(its, "b_start");
        KoatParser.Parsed parsed = KoatParser.parse(koat);

        assertEquals("koat_init", parsed.start);
        assertNotNull(parsed.its.location("loop"));
        // synthetic koat_init->b_start rule + the two original rules.
        assertEquals(3, parsed.its.transitions().size());

        FarkasRanking.Certificate cert =
                FarkasRanking.proveWithCertificate(parsed.its, parsed.start);
        assertEquals(FarkasRanking.Verdict.TERMINATES, cert.verdict);
        assertEquals(1, cert.sccs.size());
        assertTrue("ADFG lexicographic-linear certificate expected",
                cert.sccs.get(0).method.contains("ADFG"));
        assertTrue("a ranking-function component should be recorded",
                cert.sccs.get(0).rounds.size() >= 1);
    }

    @Test
    public void verdictMatchesDirectProve() {
        // proveWithCertificate must agree with the existing prove() on the verdict.
        IntegerTransitionSystem its = new IntegerTransitionSystem("t", "");
        List<String> vars = Arrays.asList("LI0");
        ItsLocation start = new ItsLocation("b_start", vars);
        ItsLocation loop = new ItsLocation("loop", vars);
        its.addLocation(start);
        its.addLocation(loop);
        its.addTransition(new ItsTransition(start, loop,
                Collections.<ItsLinearConstraint>emptyList(),
                Arrays.asList(ItsLinearExpression.variable("LI0"))));
        // unbounded loop: no decrease — must stay UNKNOWN.
        its.addTransition(new ItsTransition(loop, loop,
                Collections.<ItsLinearConstraint>emptyList(),
                Arrays.asList(ItsLinearExpression.variable("LI0"))));
        String koat = KoatPrinter.print(its, "b_start");
        KoatParser.Parsed parsed = KoatParser.parse(koat);
        FarkasRanking.Verdict direct = FarkasRanking.prove(parsed.its, "koat_init");
        FarkasRanking.Certificate cert = FarkasRanking.proveWithCertificate(parsed.its, "koat_init");
        assertEquals(direct, cert.verdict);
    }
}
