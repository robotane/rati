package fr.univreunion.rati.rank;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import org.junit.Test;

import fr.univreunion.rati.its.ItsLinearConstraint;
import fr.univreunion.rati.its.ItsLinearExpression;

/**
 * The tokenising expression parser: spaced and unspaced operators must parse to
 * the same linear form, non-affine products must raise {@link
 * KoatParser.NonlinearException}, and garbage must be rejected loudly — never
 * silently turned into a phantom variable.
 */
public class KoatExprTest {

    @Test
    public void spacedAndUnspacedParseTheSame() {
        ItsLinearExpression spaced = KoatParser.parseExpr("LI2 - LO2 - 1");
        ItsLinearExpression packed = KoatParser.parseExpr("LI2-LO2-1");
        assertEquals(spaced.coefficient("LI2"), packed.coefficient("LI2"));
        assertEquals(spaced.coefficient("LO2"), packed.coefficient("LO2"));
        assertEquals(spaced.constant(), packed.constant());
        assertEquals(1L, packed.coefficient("LI2"));
        assertEquals(-1L, packed.coefficient("LO2"));
        assertEquals(-1L, packed.constant());
    }

    @Test
    public void coefficientsBothSidesAndConstants() {
        assertEquals(2L, KoatParser.parseExpr("2*A+3").coefficient("A"));
        assertEquals(3L, KoatParser.parseExpr("2*A+3").constant());
        assertEquals(2L, KoatParser.parseExpr("A*2").coefficient("A"));
        assertEquals(-1L, KoatParser.parseExpr("-A").coefficient("A"));
        assertEquals(6L, KoatParser.parseExpr("2*3").constant());
        assertEquals(6L, KoatParser.parseExpr("2*3*B").coefficient("B"));
        assertEquals(0L, KoatParser.parseExpr("0").constant());
        assertEquals(1L, KoatParser.parseExpr("- -A").coefficient("A"));   // double sign folds
    }

    @Test
    public void unspacedConstraintParses() {
        ItsLinearConstraint c = KoatParser.parseConstraint("A-1>=0");
        assertEquals(ItsLinearConstraint.Op.GE, c.op());
        assertEquals(1L, c.lhs().coefficient("A"));
        assertEquals(-1L, c.lhs().constant());
    }

    @Test
    public void nonlinearProductRejectedAsNonlinear() {
        try {
            KoatParser.parseExpr("A*B");
            fail("A*B must be non-affine");
        } catch (KoatParser.NonlinearException expected) { /* ok */ }
        try {
            KoatParser.parseExpr("2*A*B");
            fail("2*A*B must be non-affine");
        } catch (KoatParser.NonlinearException expected) { /* ok */ }
    }

    @Test
    public void garbageRejectedLoudly() {
        String[] bad = { "A B", "A &", "A +", "*A", "2A + (" };
        for (String s : bad) {
            try {
                KoatParser.parseExpr(s);
                fail("must reject '" + s + "'");
            } catch (IllegalArgumentException expected) {
                assertTrue(expected.getMessage().contains("'" + s + "'")
                        || expected.getMessage().contains("malformed"));
            }
        }
    }

    @Test
    public void unspacedRuleParsesEndToEnd() {
        String koat = "(GOAL COMPLEXITY)\n"
                + "(STARTTERM (FUNCTIONSYMBOLS f))\n"
                + "(VAR A)\n"
                + "(RULES\n"
                + "  f(A) -> f(A-1) :|: A-1>=0\n"
                + ")\n";
        KoatParser.Parsed parsed = KoatParser.parse(koat);
        assertEquals(1, parsed.its.transitions().size());
        assertEquals(1, parsed.its.transitions().get(0).constraints().size());
        // The countdown loop must still be proved terminating.
        assertEquals(fr.univreunion.rati.ranking.FarkasRanking.Verdict.TERMINATES,
                fr.univreunion.rati.ranking.FarkasRanking.prove(parsed.its, "f"));
    }
}
