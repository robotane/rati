package fr.univreunion.rati.ranking;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import fr.univreunion.rati.rank.KoatParser;

/**
 * Locks the behaviour of the cheap, no-Apron SCT fail-fast tier
 * ({@link SizeChangeTermination}) of the "pure Julia" path-length cascade.
 *
 * <p>The fixtures are the worked CLP(PL) examples of §7 of Spoto-Mesnard-Payet
 * TOPLAS 2010, encoded in the KoAT input format (input = {@code LI*}, output =
 * {@code LO*}, guards relate the two). They pin both what SCT <em>proves</em>
 * cheaply (the lexicographic loop — its canonical win) and what it correctly
 * <em>punts</em> to the heavyweight polyhedral/Farkas tier (the {@code div2}
 * halving and the {@code gcd} subtraction loops, which need convex polyhedra /
 * per-SCC global ranking and call-contexts — exactly the handoff's tier split).
 * A punt is sound: SCT reports UNKNOWN, never a false TERMINATES.
 */
public class SizeChangeTerminationTest {

    private static SizeChangeTermination.Result run(String koat) {
        KoatParser.Parsed p = KoatParser.parse(koat);
        return SizeChangeTermination.analyze(p.its, p.start);
    }

    /** A single strictly-decreasing counter: SCT proves it instantly. */
    @Test
    public void singleDecreasingCounterTerminates() {
        String koat =
            "(GOAL COMPLEXITY)\n" +
            "(STARTTERM (FUNCTIONSYMBOLS koat_init))\n" +
            "(VAR LI0 LI1)\n" +
            "(RULES\n" +
            "  koat_init(LI0, LI1) -> p(LI0, LI1)\n" +
            "  p(LI0, LI1) -> p(LO0, LI1) :|: -LI0 + LO0 + 1 = 0 && LI0 >= 1\n" +
            ")\n";
        SizeChangeTermination.Result r = run(koat);
        assertEquals(SizeChangeTermination.Verdict.TERMINATES, r.verdict);
        assertEquals(1, r.sccProved);
        assertNull(r.blockingScc);
    }

    /**
     * §7 lexicographic loop: clause 1 strictly decreases the first argument while
     * the second is unconstrained; clause 2 keeps the first equal and strictly
     * decreases the second. No single affine function ranks it, but SCT does —
     * every idempotent self-graph has an in-situ strict thread. This is the tier
     * the bounded-monotonicity domain exists for, captured here without Apron.
     */
    @Test
    public void lexicographicLoopTerminates() {
        String koat =
            "(GOAL COMPLEXITY)\n" +
            "(STARTTERM (FUNCTIONSYMBOLS koat_init))\n" +
            "(VAR LI0 LI1)\n" +
            "(RULES\n" +
            "  koat_init(LI0, LI1) -> lex(LI0, LI1)\n" +
            // clause 1: LO0 <= LI0 - 1 (x1 strictly down), LO0,LO1 >= 0
            "  lex(LI0, LI1) -> lex(LO0, LO1) :|: LI0 - LO0 - 1 >= 0 && LO0 >= 0 && LO1 >= 0\n" +
            // clause 2: LO0 = LI0 (x1 equal), LO1 <= LI1 - 1 (x2 strictly down)
            "  lex(LI0, LI1) -> lex(LO0, LO1) :|: LI0 - LO0 = 0 && LI1 - LO1 - 1 >= 0 && LO1 >= 0\n" +
            ")\n";
        SizeChangeTermination.Result r = run(koat);
        assertEquals("lexicographic loop must be an SCT win",
                SizeChangeTermination.Verdict.TERMINATES, r.verdict);
        assertEquals(1, r.sccProved);
    }

    /**
     * A pure identity loop {@code p(x) -> p(x)} never decreases: SCT must NOT
     * prove it (the idempotent self-graph has only a non-strict thread). The
     * caller stays UNKNOWN, which is the sound outcome (the loop is genuinely
     * non-terminating).
     */
    @Test
    public void identityLoopIsPunted() {
        String koat =
            "(GOAL COMPLEXITY)\n" +
            "(STARTTERM (FUNCTIONSYMBOLS koat_init))\n" +
            "(VAR LI0)\n" +
            "(RULES\n" +
            "  koat_init(LI0) -> p(LI0)\n" +
            "  p(LI0) -> p(LO0) :|: LI0 - LO0 = 0\n" +
            ")\n";
        SizeChangeTermination.Result r = run(koat);
        assertEquals(SizeChangeTermination.Verdict.UNKNOWN, r.verdict);
        assertTrue("at least one SCC blocked the proof", r.blockingScc != null);
    }

    /**
     * §7 {@code div2}: {@code div2(x) :- x = 2*x', x >= 1, div2(x')}. The decrease
     * needs the non-unit relation {@code x = 2*x'} (convex polyhedra, tier 1) which
     * the cheap difference-bound arc extraction deliberately drops. SCT therefore
     * punts (UNKNOWN) — this is the documented hand-off to the polyhedral tier, not
     * a bug.
     */
    @Test
    public void halvingLoopIsPuntedToPolyhedralTier() {
        String koat =
            "(GOAL COMPLEXITY)\n" +
            "(STARTTERM (FUNCTIONSYMBOLS koat_init))\n" +
            "(VAR LI0)\n" +
            "(RULES\n" +
            "  koat_init(LI0) -> div2(LI0)\n" +
            "  div2(LI0) -> div2(LO0) :|: LI0 - 2*LO0 = 0 && LI0 >= 1\n" +
            ")\n";
        SizeChangeTermination.Result r = run(koat);
        assertEquals(SizeChangeTermination.Verdict.UNKNOWN, r.verdict);
    }

    /**
     * §7 {@code gcd}: the two-predicate subtraction loop. The recursive binding
     * {@code x1' = x1 - x2} is a multi-variable update the difference-bound
     * extractor cannot turn into an arc, so SCT punts to the per-SCC global affine
     * tier (rati) — exactly the handoff's tier-3 case. Sound UNKNOWN.
     */
    @Test
    public void gcdSubtractionLoopIsPuntedToGlobalTier() {
        String koat =
            "(GOAL COMPLEXITY)\n" +
            "(STARTTERM (FUNCTIONSYMBOLS koat_init))\n" +
            "(VAR LI0 LI1)\n" +
            "(RULES\n" +
            "  koat_init(LI0, LI1) -> gcd(LI0, LI1)\n" +
            "  gcd(LI0, LI1) -> gcd2(LO0, LO1) :|: LI0 - LO0 = 0 && LI1 - LO1 = 0 && LI0 >= 1 && LI1 >= 1\n" +
            "  gcd2(LI0, LI1) -> gcd(LO0, LO1) :|: LI0 - LI1 - 1 >= 0 && LI0 - LI1 - LO0 = 0 && LI1 - LO1 = 0\n" +
            "  gcd2(LI0, LI1) -> gcd(LO0, LO1) :|: LI1 - LI0 - 1 >= 0 && LI0 - LO0 = 0 && LI1 - LI0 - LO1 = 0\n" +
            ")\n";
        SizeChangeTermination.Result r = run(koat);
        assertEquals(SizeChangeTermination.Verdict.UNKNOWN, r.verdict);
    }

    /** Acyclic systems have no non-trivial SCC: vacuously SCT-terminating. */
    @Test
    public void acyclicSystemTerminatesVacuously() {
        String koat =
            "(GOAL COMPLEXITY)\n" +
            "(STARTTERM (FUNCTIONSYMBOLS koat_init))\n" +
            "(VAR LI0)\n" +
            "(RULES\n" +
            "  koat_init(LI0) -> a(LI0)\n" +
            "  a(LI0) -> b(LO0) :|: LI0 - LO0 - 1 >= 0\n" +
            ")\n";
        SizeChangeTermination.Result r = run(koat);
        assertEquals(SizeChangeTermination.Verdict.TERMINATES, r.verdict);
        assertEquals(0, r.sccTotal);
    }
}
