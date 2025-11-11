package fr.univreunion.rati.ranking;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.junit.Test;

import fr.univreunion.rati.its.IntegerTransitionSystem;
import fr.univreunion.rati.its.ItsLinearConstraint;
import fr.univreunion.rati.its.ItsLinearConstraint.Op;
import fr.univreunion.rati.its.ItsLinearExpression;
import fr.univreunion.rati.its.ItsLocation;
import fr.univreunion.rati.its.ItsTransition;

/**
 * Recurrent-set non-termination proving ({@link NonTermination} via
 * {@link FarkasRanking}): inductive-guard loops (NT1) must yield a verified
 * NONTERMINATES witness, terminating systems must keep their TERMINATES verdict,
 * and loops whose divergence the engine cannot certify must stay UNKNOWN.
 */
public class NonTerminationTest {

    private static ItsLinearExpression expr(long constant, Object... pairs) {
        ItsLinearExpression.Builder b = new ItsLinearExpression.Builder();
        b.addConstant(constant);
        for (int i = 0; i < pairs.length; i += 2) b.addTerm((String) pairs[i], (Long) pairs[i + 1]);
        return b.build();
    }
    private static ItsLinearConstraint ge(ItsLinearExpression e) { return new ItsLinearConstraint(e, Op.GE); }
    private static ItsLinearConstraint gt(ItsLinearExpression e) { return new ItsLinearConstraint(e, Op.GT); }

    // -------------------------------------------------------------------------
    // NT1: the loop guard itself is inductive
    // -------------------------------------------------------------------------

    @Test
    public void guardedIncrement_nonterminating_withWitness() {
        // L(x): x ≥ 0 -> L(x+1) — guard x ≥ 0 is preserved by x' = x+1.
        ItsLocation l = new ItsLocation("L", Arrays.asList("X"));
        IntegerTransitionSystem its = new IntegerTransitionSystem("t", "L");
        its.addLocation(l);
        its.addTransition(new ItsTransition(l, l,
                Arrays.asList(ge(expr(0, "X", 1L))),
                Arrays.asList(expr(1, "X", 1L))));
        FarkasRanking.Certificate cert = FarkasRanking.proveWithCertificate(its, "L");
        assertEquals(FarkasRanking.Verdict.NONTERMINATES, cert.verdict);
        NonTermination.Witness w = cert.nonTermination;
        assertNotNull(w);
        assertEquals("L", w.location);
        assertTrue(w.path.isEmpty());                       // entry is the loop head
        assertEquals(1, w.cycle.size());
        // The witness state must satisfy the loop guard: X ≥ 0.
        assertTrue(w.headState.get("X").signum() >= 0);
    }

    @Test
    public void strictGuard_tightenedNotRelaxed() {
        // L(x): x > 0 -> L(2x) — recurrent on x ≥ 1; the witness must respect the
        // strict guard (x ≥ 1, not the unsound relaxation x ≥ 0, where 2x stutters at 0).
        ItsLocation l = new ItsLocation("L", Arrays.asList("X"));
        IntegerTransitionSystem its = new IntegerTransitionSystem("t", "L");
        its.addLocation(l);
        its.addTransition(new ItsTransition(l, l,
                Arrays.asList(gt(expr(0, "X", 1L))),
                Arrays.asList(expr(0, "X", 2L))));
        FarkasRanking.Certificate cert = FarkasRanking.proveWithCertificate(its, "L");
        assertEquals(FarkasRanking.Verdict.NONTERMINATES, cert.verdict);
        assertTrue(cert.nonTermination.headState.get("X").signum() > 0);
    }

    @Test
    public void twoLocationCycle_nonterminating() {
        // A(n): n ≥ 1 -> B(n+1) ; B(n) -> A(n) — composed self-loop at A keeps n ≥ 1.
        ItsLocation a = new ItsLocation("A", Arrays.asList("N"));
        ItsLocation b = new ItsLocation("B", Arrays.asList("N"));
        IntegerTransitionSystem its = new IntegerTransitionSystem("t", "A");
        its.addLocation(a); its.addLocation(b);
        its.addTransition(new ItsTransition(a, b,
                Arrays.asList(ge(expr(-1, "N", 1L))),
                Arrays.asList(expr(1, "N", 1L))));
        its.addTransition(new ItsTransition(b, a,
                Collections.<ItsLinearConstraint>emptyList(),
                Arrays.asList(expr(0, "N", 1L))));
        assertEquals(FarkasRanking.Verdict.NONTERMINATES, FarkasRanking.prove(its, "A"));
    }

    @Test
    public void loopBehindGuardedPrefix_reachabilityWitnessFound() {
        // start(x) -> L(x) only when x ≥ 5; L(x): x ≥ 1 -> L(x+1).
        // Zero entry values fail the prefix guard, so the LP must find e.g. x = 5.
        ItsLocation s = new ItsLocation("start", Arrays.asList("X"));
        ItsLocation l = new ItsLocation("L", Arrays.asList("X"));
        IntegerTransitionSystem its = new IntegerTransitionSystem("t", "start");
        its.addLocation(s); its.addLocation(l);
        its.addTransition(new ItsTransition(s, l,
                Arrays.asList(ge(expr(-5, "X", 1L))),
                Arrays.asList(expr(0, "X", 1L))));
        its.addTransition(new ItsTransition(l, l,
                Arrays.asList(ge(expr(-1, "X", 1L))),
                Arrays.asList(expr(1, "X", 1L))));
        FarkasRanking.Certificate cert = FarkasRanking.proveWithCertificate(its, "start");
        assertEquals(FarkasRanking.Verdict.NONTERMINATES, cert.verdict);
        NonTermination.Witness w = cert.nonTermination;
        assertEquals(1, w.path.size());
        assertTrue(w.entryState.get("X").compareTo(BigInteger.valueOf(5)) >= 0);
    }

    @Test
    public void deterministicUpdateSolvedFromGuardEquality() {
        // KoAT style: L(x) -> L(z) :|: z - x - 1 = 0 && x ≥ 0  (z fresh, solved to x+1).
        ItsLocation l = new ItsLocation("L", Arrays.asList("X"));
        IntegerTransitionSystem its = new IntegerTransitionSystem("t", "L");
        its.addLocation(l);
        its.addTransition(new ItsTransition(l, l,
                Arrays.asList(
                        new ItsLinearConstraint(expr(-1, "Z", 1L, "X", -1L), Op.EQ),
                        ge(expr(0, "X", 1L))),
                Arrays.asList(ItsLinearExpression.variable("Z"))));
        assertEquals(FarkasRanking.Verdict.NONTERMINATES, FarkasRanking.prove(its, "L"));
    }

    // -------------------------------------------------------------------------
    // No false NO: terminating / undecided systems
    // -------------------------------------------------------------------------

    @Test
    public void terminatingCountdown_stillTerminates() {
        // L(x): x ≥ 1 -> L(x-1) — ranked; the non-termination stage must not run it down.
        ItsLocation l = new ItsLocation("L", Arrays.asList("X"));
        IntegerTransitionSystem its = new IntegerTransitionSystem("t", "L");
        its.addLocation(l);
        its.addTransition(new ItsTransition(l, l,
                Arrays.asList(ge(expr(-1, "X", 1L))),
                Arrays.asList(expr(-1, "X", 1L))));
        assertEquals(FarkasRanking.Verdict.TERMINATES, FarkasRanking.prove(its, "L"));
    }

    @Test
    public void unreachableDivergentLoop_staysUnprovable() {
        // L(x): x ≥ 0 ∧ −x ≥ 1 -> L(x+1): infeasible guard — the loop never fires,
        // so the system terminates (the SCC is dropped as infeasible upstream).
        ItsLocation l = new ItsLocation("L", Arrays.asList("X"));
        IntegerTransitionSystem its = new IntegerTransitionSystem("t", "L");
        its.addLocation(l);
        its.addTransition(new ItsTransition(l, l,
                Arrays.asList(ge(expr(0, "X", 1L)), ge(expr(-1, "X", -1L))),
                Arrays.asList(expr(1, "X", 1L))));
        assertEquals(FarkasRanking.Verdict.TERMINATES, FarkasRanking.prove(its, "L"));
    }

    @Test
    public void disprovalRespectsWitnessVerification() {
        // L(x,y): x ≥ 0 -> L(x+y, y) — diverges only from y ≥ 0, a fact no guard,
        // invariant or bounded strengthening supplies here (G ∧ G∘s adds x+ky ≥ 0
        // forever without converging), so UNKNOWN is the honest outcome — never a
        // wrong TERMINATES, and only a *verified* NONTERMINATES would do.
        ItsLocation l = new ItsLocation("L", Arrays.asList("X", "Y"));
        IntegerTransitionSystem its = new IntegerTransitionSystem("t", "L");
        its.addLocation(l);
        its.addTransition(new ItsTransition(l, l,
                Arrays.asList(ge(expr(0, "X", 1L))),
                Arrays.asList(expr(0, "X", 1L, "Y", 1L), expr(0, "Y", 1L))));
        FarkasRanking.Verdict v = FarkasRanking.prove(its, "L");
        assertTrue(v == FarkasRanking.Verdict.UNKNOWN || v == FarkasRanking.Verdict.NONTERMINATES);
    }

    @Test
    public void guardBudgetOverflow_bailsInsteadOfTruncating() {
        // 70 distinct guard constraints (X + i ≥ 0) exceed the determinisation
        // budget. The loop actually diverges, but the engine must REFUSE the step
        // (UNKNOWN) rather than truncate its guard: a truncated guard enlarges the
        // relation, and a witness on the enlarged step could certify a run the
        // real system does not have — a false NONTERMINATES on other inputs.
        ItsLocation l = new ItsLocation("L", Arrays.asList("X"));
        IntegerTransitionSystem its = new IntegerTransitionSystem("t", "L");
        its.addLocation(l);
        List<ItsLinearConstraint> guard = new java.util.ArrayList<ItsLinearConstraint>();
        for (long i = 0; i < 70; i++) guard.add(ge(expr(i, "X", 1L)));
        its.addTransition(new ItsTransition(l, l, guard,
                Arrays.asList(expr(1, "X", 1L))));
        assertEquals(FarkasRanking.Verdict.UNKNOWN, FarkasRanking.prove(its, "L"));
    }

    // -------------------------------------------------------------------------
    // NT2: strengthening and invariant-seeded candidates
    // -------------------------------------------------------------------------

    @Test
    public void strengthening_convergesInOneRound() {
        // L(x,y): x ≥ 1 -> L(y, y) — guard x ≥ 1 is not inductive (x' = y is
        // unbounded), but one G ← G ∧ G∘s round adds y ≥ 1, which closes the set:
        // {x ≥ 1, y ≥ 1} is recurrent.
        ItsLocation l = new ItsLocation("L", Arrays.asList("X", "Y"));
        IntegerTransitionSystem its = new IntegerTransitionSystem("t", "L");
        its.addLocation(l);
        its.addTransition(new ItsTransition(l, l,
                Arrays.asList(ge(expr(-1, "X", 1L))),
                Arrays.asList(expr(0, "Y", 1L), expr(0, "Y", 1L))));
        FarkasRanking.Certificate cert = FarkasRanking.proveWithCertificate(its, "L");
        assertEquals(FarkasRanking.Verdict.NONTERMINATES, cert.verdict);
        // Both coordinates of the witness must sit in the strengthened set.
        assertTrue(cert.nonTermination.headState.get("X").compareTo(BigInteger.ONE) >= 0);
        assertTrue(cert.nonTermination.headState.get("Y").compareTo(BigInteger.ONE) >= 0);
    }

    @Test
    public void invariantSeed_suppliesTheMissingFact() {
        // init(x,y) -> L(x, 3) ; L(x,y): x ≥ 0 -> L(x+y, y). The guard alone
        // diverges under strengthening (x + ky ≥ 0 forever); the polyhedral
        // invariant y = 3 at L closes it: {x ≥ 0, y = 3} is recurrent.
        ItsLocation init = new ItsLocation("init", Arrays.asList("X", "Y"));
        ItsLocation l = new ItsLocation("L", Arrays.asList("X", "Y"));
        IntegerTransitionSystem its = new IntegerTransitionSystem("t", "init");
        its.addLocation(init); its.addLocation(l);
        its.addTransition(new ItsTransition(init, l,
                Collections.<ItsLinearConstraint>emptyList(),
                Arrays.asList(expr(0, "X", 1L), expr(3))));
        its.addTransition(new ItsTransition(l, l,
                Arrays.asList(ge(expr(0, "X", 1L))),
                Arrays.asList(expr(0, "X", 1L, "Y", 1L), expr(0, "Y", 1L))));
        FarkasRanking.Certificate cert = FarkasRanking.proveWithCertificate(its, "init");
        assertEquals(FarkasRanking.Verdict.NONTERMINATES, cert.verdict);
        assertEquals(BigInteger.valueOf(3), cert.nonTermination.headState.get("Y"));
    }

    // -------------------------------------------------------------------------
    // Witness exactness: replayable by hand
    // -------------------------------------------------------------------------

    @Test
    public void witnessStateReplaysOneIteration() {
        // L(x,y): x ≥ 1 -> L(x+y, y+1) is NOT guard-inductive in general; but
        // L(x): x ≥ 2 -> L(3x − 4): x' − 2 = 3(x − 2) + 2·... check: x≥2 ⇒ 3x−4 ≥ 2 ⟺ 3x ≥ 6 ✓.
        ItsLocation l = new ItsLocation("L", Arrays.asList("X"));
        IntegerTransitionSystem its = new IntegerTransitionSystem("t", "L");
        its.addLocation(l);
        its.addTransition(new ItsTransition(l, l,
                Arrays.asList(ge(expr(-2, "X", 1L))),
                Arrays.asList(expr(-4, "X", 3L))));
        FarkasRanking.Certificate cert = FarkasRanking.proveWithCertificate(its, "L");
        assertEquals(FarkasRanking.Verdict.NONTERMINATES, cert.verdict);
        // Replay: x₀ ≥ 2 and x₁ = 3x₀ − 4 must satisfy the guard again.
        BigInteger x0 = cert.nonTermination.headState.get("X");
        BigInteger x1 = x0.multiply(BigInteger.valueOf(3)).subtract(BigInteger.valueOf(4));
        assertTrue(x0.compareTo(BigInteger.valueOf(2)) >= 0);
        assertTrue(x1.compareTo(BigInteger.valueOf(2)) >= 0);
    }
}
