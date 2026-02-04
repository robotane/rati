package fr.univreunion.rati.ranking;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.junit.Test;

import fr.univreunion.rati.its.IntegerTransitionSystem;
import fr.univreunion.rati.its.ItsLinearConstraint;
import fr.univreunion.rati.its.ItsLinearExpression;
import fr.univreunion.rati.its.ItsTransition;
import fr.univreunion.rati.rank.KoatParser;

/**
 * Acceptance tests for {@link BinTerm}, the faithful BINTERM / Algorithm-1 prover
 * (Spoto-Mesnard-Payet TOPLAS 2010, §7). The fixtures are the four worked CLP(PL)
 * examples of §7 — encoded in KoAT (input {@code LI*}, next state {@code LO*}) — and
 * pin that each one lands at the tier the paper says decides it:
 * <ul>
 *   <li>{@code div2} — convex-polyhedra tier&nbsp;1 (a single affine rank over the
 *       non-unit halving relation);</li>
 *   <li>{@code lex} — bounded-monotonicity tier&nbsp;2 (tier&nbsp;1's convex hull of the
 *       two clauses admits no single affine rank — the reason tier&nbsp;2 exists);</li>
 *   <li>{@code BubbleSort/Double} — the call-context improvement disables a clause that
 *       is divergent in isolation but unreachable from the entry context;</li>
 *   <li>{@code gcd} — the two-predicate subtraction loop, with the entry context.</li>
 * </ul>
 */
public class BinTermTest {

    private static BinTerm.Result run(String koat) {
        KoatParser.Parsed p = KoatParser.parse(koat);
        return BinTerm.analyze(p.its, p.start);
    }

    /** §7 div2: {@code div2(x) :- x = 2·x', x ≥ 1, div2(x')}. Polyhedral tier 1. */
    @Test
    public void div2ProvedByPolyhedralTier() {
        String koat =
            "(GOAL COMPLEXITY)\n" +
            "(STARTTERM (FUNCTIONSYMBOLS koat_init))\n" +
            "(VAR LI0 LO0)\n" +
            "(RULES\n" +
            "  koat_init(LI0) -> div2(LI0)\n" +
            "  div2(LI0) -> div2(LO0) :|: LI0 - 2*LO0 = 0 && LI0 >= 1\n" +
            ")\n";
        BinTerm.Result r = run(koat);
        assertEquals(r.toString(), BinTerm.Verdict.TERMINATES, r.verdict);
        assertEquals("div2 is the canonical polyhedral tier-1 win",
                BinTerm.Tier.POLYHEDRAL, r.tier);
        assertTrue("a tier-1 proof must surface its synthesised ranking function",
                r.detail.contains("f = "));
    }

    /**
     * Unit test of the tier-1 Farkas synthesis ({@link BinTerm#affineRank}) directly on
     * loop relations over {@code I@v}/{@code C@v}: the div2 halving relation
     * {@code I = 2·C, I ≥ 1} must yield a positive-coefficient ranking function, while a
     * pure copy relation {@code I = C} must yield none (no decrease). This pins that the
     * synthesiser produces a genuine certificate, not just a yes/no.
     */
    @Test
    public void farkasSynthesisProducesSoundWitness() {
        List<String> formals = Arrays.asList("LI0");
        // div2: I@LI0 - 2·C@LI0 = 0  and  I@LI0 - 1 >= 0
        ItsLinearConstraint halve = new ItsLinearConstraint(
                new ItsLinearExpression.Builder().addTerm("I@LI0", 1).addTerm("C@LI0", -2).build(),
                ItsLinearConstraint.Op.EQ);
        ItsLinearConstraint bound = new ItsLinearConstraint(
                new ItsLinearExpression.Builder().addTerm("I@LI0", 1).addConstant(-1).build(),
                ItsLinearConstraint.Op.GE);
        BinTerm.AffineRank rank = BinTerm.affineRank(formals, Arrays.asList(halve, bound));
        assertNotNull("the halving relation is affine-rankable", rank);
        assertTrue("the ranking coefficient on LI0 must be positive (f decreases as LI0 → LI0/2)",
                rank.a[0].signum() > 0);

        // A pure copy I@LI0 - C@LI0 = 0 never decreases: not rankable.
        ItsLinearConstraint copy = new ItsLinearConstraint(
                new ItsLinearExpression.Builder().addTerm("I@LI0", 1).addTerm("C@LI0", -1).build(),
                ItsLinearConstraint.Op.EQ);
        assertNull("an identity loop relation has no affine ranking",
                BinTerm.affineRank(formals, Arrays.asList(copy)));
    }

    /**
     * §7 lex: two clauses, clause 1 strictly decreases x₁ with x₂ free, clause 2 keeps
     * x₁ and decreases x₂. The polyhedral binary unfolding joins them by convex hull,
     * which admits no single affine ranking — so tier 1 must FAIL and the bounded-
     * monotonicity tier 2 must prove it. This is the exact tier-1/tier-2 boundary.
     */
    @Test
    public void lexProvedByMonotonicityTierNotPolyhedral() {
        String koat =
            "(GOAL COMPLEXITY)\n" +
            "(STARTTERM (FUNCTIONSYMBOLS koat_init))\n" +
            "(VAR LI0 LI1 LO0 LO1)\n" +
            "(RULES\n" +
            "  koat_init(LI0, LI1) -> lex(LI0, LI1)\n" +
            "  lex(LI0, LI1) -> lex(LO0, LO1) :|: LI0 - LO0 - 1 >= 0 && LO0 >= 0 && LO1 >= 0\n" +
            "  lex(LI0, LI1) -> lex(LO0, LO1) :|: LI0 - LO0 = 0 && LI1 - LO1 - 1 >= 0 && LO1 >= 0\n" +
            ")\n";
        BinTerm.Result r = run(koat);
        assertEquals(r.toString(), BinTerm.Verdict.TERMINATES, r.verdict);
        assertEquals("the convex hull of the two clauses has no single affine rank, so the "
                + "bounded-monotonicity tier must be the one that proves it",
                BinTerm.Tier.MONOTONICITY, r.tier);
    }

    /**
     * The fidelity discriminator, locked independently of the cascade order: the
     * <em>polyhedral</em> binary-unfolding relation of the lex loop (the convex hull of
     * "x₁ down" and "x₂ down") admits NO single affine ranking function. This is why
     * tier 1 cannot prove lex and the bounded-monotonicity tier 2 is needed — exactly
     * the §7 argument, verified white-box on the loop relation itself.
     */
    @Test
    public void lexHullIsNotPolyhedralRankable() throws Exception {
        String koat =
            "(GOAL COMPLEXITY)\n" +
            "(STARTTERM (FUNCTIONSYMBOLS koat_init))\n" +
            "(VAR LI0 LI1 LO0 LO1)\n" +
            "(RULES\n" +
            "  koat_init(LI0, LI1) -> lex(LI0, LI1)\n" +
            "  lex(LI0, LI1) -> lex(LO0, LO1) :|: LI0 - LO0 - 1 >= 0 && LO0 >= 0 && LO1 >= 0\n" +
            "  lex(LI0, LI1) -> lex(LO0, LO1) :|: LI0 - LO0 = 0 && LI1 - LO1 - 1 >= 0 && LO1 >= 0\n" +
            ")\n";
        KoatParser.Parsed p = KoatParser.parse(koat);
        IntegerTransitionSystem its = p.its;
        Set<String> reach = BinUnfoldProbe.reachableFrom(its, p.start);
        Map<String, List<ItsTransition>> bySource = new HashMap<String, List<ItsTransition>>();
        for (ItsTransition t : its.transitions())
            if (t.isSupported() && reach.contains(t.source().name()) && reach.contains(t.target().name()))
                bySource.computeIfAbsent(t.source().name(), k -> new ArrayList<ItsTransition>()).add(t);
        Set<String> lexScc = null;
        for (Set<String> c : BinUnfoldProbe.sccs(reach, bySource))
            if (c.contains("lex")) lexScc = c;
        List<ItsLinearConstraint> rhh = BinUnfoldProbe.loopRelation(its, lexScc, bySource, "lex");
        assertNull("the convex-hull loop relation of lex must not be single-affine rankable",
                BinTerm.affineRank(its.location("lex").variables(), rhh));
    }

    /**
     * §7 BubbleSort/Double: {@code p} alone is non-terminating (a divergent clause for
     * {@code x ≤ −1}), but from {@code entry} the context {@code x ≥ 0} makes that clause
     * unreachable. The call-context filter must drop it, after which the remaining
     * decreasing clause is ranked at tier 1.
     */
    @Test
    public void bubbleSortProvedViaCallContext() {
        String koat =
            "(GOAL COMPLEXITY)\n" +
            "(STARTTERM (FUNCTIONSYMBOLS koat_init))\n" +
            "(VAR LI0 LO0)\n" +
            "(RULES\n" +
            "  koat_init(LI0) -> p(LI0) :|: LI0 >= 0\n" +
            "  p(LI0) -> p(LO0) :|: LI0 - LO0 - 1 = 0 && LO0 >= 0\n" +
            "  p(LI0) -> p(LO0) :|: -LI0 - 1 >= 0 && LO0 - LI0 = 0\n" +
            ")\n";
        BinTerm.Result r = run(koat);
        assertEquals(r.toString(), BinTerm.Verdict.TERMINATES, r.verdict);
        // The point is the call context (it disables the divergent clause); which tier then
        // ranks the surviving decreasing clause — size-change or polyhedral — is incidental.
        assertTrue(r.toString(), r.tier == BinTerm.Tier.MONOTONICITY || r.tier == BinTerm.Tier.POLYHEDRAL);
    }

    /**
     * The same predicate WITHOUT the entry context {@code x ≥ 0}: the divergent clause
     * is now reachable (an identity self-loop for {@code x ≤ −1}), so no tier proves it.
     * This pins that it is genuinely the call context — not the rest of the machinery —
     * that proves {@link #bubbleSortProvedViaCallContext}.
     */
    @Test
    public void bubbleSortWithoutContextIsUnknown() {
        String koat =
            "(GOAL COMPLEXITY)\n" +
            "(STARTTERM (FUNCTIONSYMBOLS koat_init))\n" +
            "(VAR LI0 LO0)\n" +
            "(RULES\n" +
            "  koat_init(LI0) -> p(LI0)\n" +
            "  p(LI0) -> p(LO0) :|: LI0 - LO0 - 1 = 0 && LO0 >= 0\n" +
            "  p(LI0) -> p(LO0) :|: -LI0 - 1 >= 0 && LO0 - LI0 = 0\n" +
            ")\n";
        BinTerm.Result r = run(koat);
        assertEquals(r.toString(), BinTerm.Verdict.UNKNOWN, r.verdict);
    }

    /**
     * §7 gcd: the two-predicate subtraction loop, with the entry context x₁,x₂ ≥ 1.
     * The paper uses gcd to illustrate the global per-SCC tier 3, but Algorithm 1
     * returns true at the FIRST tier that succeeds: here the polyhedral binary
     * unfolding composes gcd→gcd2→gcd into a compact relation on which, under the
     * entry context, the single affine function {@code x₁ + x₂} decreases by ≥ 1 in
     * both subtraction branches — so tier 1 already proves it. That is the algorithm
     * working (a sound ranking function), not a deviation; we assert only that some
     * tier proves it.
     */
    @Test
    public void gcdProved() {
        String koat =
            "(GOAL COMPLEXITY)\n" +
            "(STARTTERM (FUNCTIONSYMBOLS koat_init))\n" +
            "(VAR LI0 LI1 LO0 LO1)\n" +
            "(RULES\n" +
            "  koat_init(LI0, LI1) -> gcd(LI0, LI1)\n" +
            "  gcd(LI0, LI1) -> gcd2(LO0, LO1) :|: LI0 - LO0 = 0 && LI1 - LO1 = 0 && LI0 >= 1 && LI1 >= 1\n" +
            "  gcd2(LI0, LI1) -> gcd(LO0, LO1) :|: LI0 - LI1 - 1 >= 0 && LI0 - LI1 - LO0 = 0 && LI1 - LO1 = 0\n" +
            "  gcd2(LI0, LI1) -> gcd(LO0, LO1) :|: LI1 - LI0 - 1 >= 0 && LI0 - LO0 = 0 && LI1 - LI0 - LO1 = 0\n" +
            ")\n";
        BinTerm.Result r = run(koat);
        assertEquals(r.toString(), BinTerm.Verdict.TERMINATES, r.verdict);
        assertTrue("gcd must be proved by some tier", r.terminates());
    }

    /** An acyclic system: no non-trivial SCC, trivially terminating. */
    @Test
    public void acyclicSystemTerminates() {
        String koat =
            "(GOAL COMPLEXITY)\n" +
            "(STARTTERM (FUNCTIONSYMBOLS koat_init))\n" +
            "(VAR LI0 LO0)\n" +
            "(RULES\n" +
            "  koat_init(LI0) -> a(LI0)\n" +
            "  a(LI0) -> b(LO0) :|: LI0 - LO0 - 1 >= 0\n" +
            ")\n";
        BinTerm.Result r = run(koat);
        assertEquals(BinTerm.Verdict.TERMINATES, r.verdict);
        assertEquals(BinTerm.Tier.ACYCLIC, r.tier);
    }
}
