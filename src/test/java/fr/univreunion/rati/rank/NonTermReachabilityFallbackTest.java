package fr.univreunion.rati.rank;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.math.BigInteger;

import org.junit.Test;

import fr.univreunion.rati.ranking.FarkasRanking;
import fr.univreunion.rati.ranking.NonTermination;

/**
 * Existential-prefix reachability. A loop is reached through a transition that
 * havocs the loop's guard variable — {@code b_run(t, p) -> b_loop(t, q)}, where
 * {@code q} is a fresh unconstrained update variable. This is the shape a
 * divergent-call inlining produces when the callee's field-ghost local is havoced
 * at the call edge (bcterm's {@code bcterm.havocCalleeLocals}): the loop
 * {@code while (p >= 1)} diverges for the receiver whose field is positive.
 *
 * <p>The composed reachability search fixes the nondeterministic prefix update
 * {@code q} to 0 — sound, but it thereby assumes {@code p == 0} at the loop entry
 * and misses the recurrent set. The existential fallback re-solves the prefix as an
 * SSA system in which {@code q} is chosen, finding the reachable {@code p >= 1}.
 * With the fallback disabled ({@code rati.noReachFallback}) the same system is only
 * UNKNOWN, which pins the fallback as exactly what recovers the proof.
 */
public class NonTermReachabilityFallbackTest {

    private static final String KOAT =
            "(GOAL COMPLEXITY)\n"
          + "(STARTTERM (FUNCTIONSYMBOLS koat_init))\n"
          + "(VAR t p)\n"
          + "(RULES\n"
          + "  koat_init(t, p) -> b_run(t, p)\n"
          + "  b_run(t, p) -> b_loop(t, q)\n"
          + "  b_loop(t, p) -> b_loop(t, p) :|: p - 1 >= 0\n"
          + ")\n";

    @Test
    public void loopReachedViaHavocedPrefix_disproved() {
        KoatParser.Parsed parsed = KoatParser.parse(KOAT);
        FarkasRanking.Certificate cert =
                FarkasRanking.proveWithCertificate(parsed.its, parsed.start);

        assertEquals("a loop reachable only for a chosen prefix value must be disproved",
                FarkasRanking.Verdict.NONTERMINATES, cert.verdict);
        NonTermination.Witness w = cert.nonTermination;
        assertNotNull(w);
        assertEquals("b_loop", w.location);
        assertFalse("the loop is reached through the havocing prefix", w.path.isEmpty());
        assertEquals(parsed.start, w.path.get(0).source().name());
        // The witness must choose the havoced variable so the loop guard holds — the
        // whole point: the composed search would have pinned it to 0.
        assertTrue("state entering the loop must satisfy p >= 1",
                w.headState.get("p").compareTo(BigInteger.ONE) >= 0);
    }

    @Test
    public void withoutFallback_theSameLoopIsOnlyUnknown() {
        String prop = "rati.noReachFallback";
        String saved = System.getProperty(prop);
        System.setProperty(prop, "true");
        try {
            KoatParser.Parsed parsed = KoatParser.parse(KOAT);
            FarkasRanking.Certificate cert =
                    FarkasRanking.proveWithCertificate(parsed.its, parsed.start);
            assertNotEquals("composed-only reachability cannot reach the recurrent set",
                    FarkasRanking.Verdict.NONTERMINATES, cert.verdict);
        } finally {
            if (saved == null) System.clearProperty(prop); else System.setProperty(prop, saved);
        }
    }
}
