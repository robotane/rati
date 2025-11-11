package fr.univreunion.rati.ranking;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fr.univreunion.rati.its.IntegerTransitionSystem;
import fr.univreunion.rati.its.ItsLinearConstraint;
import fr.univreunion.rati.its.ItsLinearExpression;
import fr.univreunion.rati.its.ItsLocation;
import fr.univreunion.rati.its.ItsTransition;

/**
 * Non-termination prover for an {@link IntegerTransitionSystem}: searches an
 * unranked SCC for a <em>recurrent set</em> — a set of states {@code G} closed
 * under one loop iteration and reachable from the entry — which witnesses an
 * infinite run (Gupta et al., POPL 2008; closed recurrence sets of Chen et al.,
 * TACAS 2014; the inductive-guard criterion is Frohn &amp; Giesl, FMCAD 2019).
 *
 * <p>The search underapproximates, the verdict is exact:
 * <ol>
 *   <li><b>determinisation</b> — each transition's update variables are solved
 *       from the guard equalities (coefficient ±1, so values stay integral);
 *       leftover nondeterministic variables are <em>fixed to 0</em>, restricting
 *       the relation to a subset of its behaviours — sound for disproving;</li>
 *   <li><b>cycle enumeration</b> — simple cycles of the SCC are composed into
 *       explicit self-loops {@code guard(x) ∧ x' = s(x)} by exact substitution;</li>
 *   <li><b>recurrence</b> — a candidate {@code G} (the loop guard, optionally
 *       strengthened) is checked inductive, {@code G(x) ⊨ G(s(x))}, by Farkas'
 *       lemma over the exact-rational {@link LinearProgram};</li>
 *   <li><b>reachability</b> — a concrete integer entry state whose (determinised)
 *       run reaches {@code G} is synthesised by LP + rounding and then
 *       <em>re-verified by substitution</em> in {@link BigInteger} arithmetic.</li>
 * </ol>
 *
 * <p>Soundness: strict guards are tightened to their exact integer form
 * ({@code e > 0  ⇒  e − 1 ≥ 0}) — never relaxed, unlike the ranking side where
 * enlarging the guard is the conservative direction. A returned {@link Witness}
 * is a machine-checked certificate: the witness state satisfies every constraint
 * on its path, lands in {@code G}, and {@code G} is Farkas-certified inductive,
 * so the verdict NONTERMINATES holds <em>of the ITS as given</em>. (A front-end
 * whose ITS over-approximates a program must not propagate NO to that program.)
 * Every failure path returns {@code null} — never an unsound claim.
 */
public final class NonTermination {

    private static final boolean DEBUG = Boolean.getBoolean("rati.ntDebug");

    /** Bound on the length (in transitions) of an enumerated simple cycle. */
    private static final int MAX_CYCLE_LEN = 8;
    /** Bound on the number of cycles enumerated per head location. */
    private static final int MAX_CYCLES_PER_HEAD = 16;
    /** Bound on the size of a candidate recurrent set (constraint count). */
    private static final int MAX_CONSTRAINTS = 64;
    /** Bound on the strengthening rounds {@code G ← G ∧ G∘s} (stage NT2). */
    private static final int MAX_STRENGTHEN = 8;

    private NonTermination() {}

    // -------------------------------------------------------------------------
    // Public face
    // -------------------------------------------------------------------------

    /**
     * A verified non-termination witness: from {@link #entryState}, the
     * (determinised) {@link #path} reaches {@link #headState} at
     * {@link #location}, which lies in the inductive {@link #recurrentSet};
     * iterating {@link #cycle} therefore never leaves it.
     */
    public static final class Witness {
        public final String location;
        /** Rendered constraints of the recurrent set, over {@code location}'s formals. */
        public final List<String> recurrentSet;
        /** The looping transitions, in firing order starting at {@code location}. */
        public final List<ItsTransition> cycle;
        /** The entry → {@code location} transitions (empty when the entry is the head). */
        public final List<ItsTransition> path;
        /**
         * The determinised cycle step, rendered ({@code X' = …} per formal). This
         * records the nondeterministic choices the witness commits to (solved and
         * zeroed update variables), so the certificate replays without consulting
         * the search: iterating exactly this step from {@link #headState} stays in
         * {@link #recurrentSet} forever.
         */
        public final List<String> loopStep;
        public final Map<String, BigInteger> entryState;
        public final Map<String, BigInteger> headState;

        Witness(String location, List<String> recurrentSet, List<ItsTransition> cycle,
                List<ItsTransition> path, List<String> loopStep,
                Map<String, BigInteger> entryState, Map<String, BigInteger> headState) {
            this.location = location;
            this.recurrentSet = recurrentSet;
            this.cycle = cycle;
            this.path = path;
            this.loopStep = loopStep;
            this.entryState = entryState;
            this.headState = headState;
        }
    }

    /**
     * Tries to disprove termination of the SCC given by {@code sccTransitions}.
     * Returns a verified {@link Witness}, or {@code null} when none is found
     * (which proves nothing). {@code invariants} may be null; they only seed
     * candidate sets — every candidate is re-verified exactly, so a wrong
     * invariant can never produce a wrong witness.
     */
    public static Witness disprove(IntegerTransitionSystem its, String entry,
            List<ItsTransition> sccTransitions,
            Map<String, List<ItsLinearConstraint>> invariants) {
        try {
            return new NonTermination().run(its, entry, sccTransitions, invariants);
        } catch (ArithmeticException e) {
            return null;   // coefficient overflow somewhere — give up, sound
        }
    }

    // -------------------------------------------------------------------------
    // Search driver
    // -------------------------------------------------------------------------

    private Witness run(IntegerTransitionSystem its, String entry,
            List<ItsTransition> sccTransitions,
            Map<String, List<ItsLinearConstraint>> invariants) {
        // Supported intra-SCC transitions, grouped by source.
        Map<String, List<ItsTransition>> bySrc = new LinkedHashMap<String, List<ItsTransition>>();
        Set<String> heads = new java.util.TreeSet<String>();
        for (ItsTransition t : sccTransitions) {
            if (!t.isSupported()) continue;
            bySrc.computeIfAbsent(t.source().name(), k -> new ArrayList<ItsTransition>()).add(t);
            heads.add(t.source().name());
        }

        for (String head : heads) {
            List<List<ItsTransition>> cycles = enumerateCycles(head, bySrc);
            cycles.sort((a, b) -> Integer.compare(a.size(), b.size()));   // cheap candidates first
            for (List<ItsTransition> cycle : cycles) {
                Step s = stepOfCycle(cycle);
                if (s == null) continue;
                List<Cons> g = recurrentSet(s, invariants == null ? null : invariants.get(head));
                if (g == null) continue;
                if (DEBUG) System.err.println("[nonterm] head " + head + ": recurrent set "
                        + render(g, s.src.variables()));
                Witness w = witness(its, entry, s, g, cycle);
                if (w != null) return w;
                if (DEBUG) System.err.println("[nonterm]   ...but no reachable integer witness");
            }
        }
        return null;
    }

    /** Simple cycles from {@code head} back to itself (bounded DFS, no repeated interior node). */
    private static List<List<ItsTransition>> enumerateCycles(String head,
            Map<String, List<ItsTransition>> bySrc) {
        List<List<ItsTransition>> cycles = new ArrayList<List<ItsTransition>>();
        Deque<ItsTransition> stack = new ArrayDeque<ItsTransition>();
        dfsCycles(head, head, stack, new HashSet<String>(), bySrc, cycles);
        return cycles;
    }

    private static void dfsCycles(String cur, String head, Deque<ItsTransition> stack,
            Set<String> visited, Map<String, List<ItsTransition>> bySrc,
            List<List<ItsTransition>> cycles) {
        if (stack.size() >= MAX_CYCLE_LEN) return;
        for (ItsTransition t : bySrc.getOrDefault(cur, java.util.Collections.emptyList())) {
            if (cycles.size() >= MAX_CYCLES_PER_HEAD) return;
            String tgt = t.target().name();
            if (tgt.equals(head)) {
                List<ItsTransition> cycle = new ArrayList<ItsTransition>(stack);
                java.util.Collections.reverse(cycle);   // ArrayDeque pushes to the front
                cycle.add(t);
                cycles.add(cycle);
            } else if (!visited.contains(tgt)) {
                visited.add(tgt);
                stack.push(t);
                dfsCycles(tgt, head, stack, visited, bySrc, cycles);
                stack.pop();
                visited.remove(tgt);
            }
        }
    }

    // -------------------------------------------------------------------------
    // Exact linear forms over a location's formals (by position)
    // -------------------------------------------------------------------------

    /** {@code Σ c[i]·x_i + k} over the positions of some location's formals. */
    private static final class LinForm {
        final long[] c;
        final long k;
        LinForm(long[] c, long k) { this.c = c; this.k = k; }

        boolean isConstant() {
            for (long v : c) if (v != 0) return false;
            return true;
        }

        LinForm negate() {
            long[] n = new long[c.length];
            for (int i = 0; i < c.length; i++) n[i] = Math.negateExact(c[i]);
            return new LinForm(n, Math.negateExact(k));
        }

        /** This form with each input substituted by {@code inner[i]} (over {@code inArity} positions). */
        LinForm compose(LinForm[] inner, int inArity) {
            long[] rc = new long[inArity];
            long rk = k;
            for (int i = 0; i < c.length; i++) {
                if (c[i] == 0) continue;
                for (int v = 0; v < inArity; v++)
                    rc[v] = Math.addExact(rc[v], Math.multiplyExact(c[i], inner[i].c[v]));
                rk = Math.addExact(rk, Math.multiplyExact(c[i], inner[i].k));
            }
            return new LinForm(rc, rk);
        }

        BigInteger eval(BigInteger[] x) {
            BigInteger r = BigInteger.valueOf(k);
            for (int i = 0; i < c.length; i++)
                if (c[i] != 0) r = r.add(BigInteger.valueOf(c[i]).multiply(x[i]));
            return r;
        }

        String render(List<String> names) {
            StringBuilder sb = new StringBuilder();
            for (int i = 0; i < c.length; i++) {
                if (c[i] == 0) continue;
                long mag = Math.abs(c[i]);
                if (sb.length() == 0) { if (c[i] < 0) sb.append('-'); }
                else sb.append(c[i] < 0 ? " - " : " + ");
                if (mag != 1) sb.append(mag).append('*');
                sb.append(names.get(i));
            }
            if (k != 0 || sb.length() == 0) {
                if (sb.length() == 0) sb.append(k);
                else sb.append(k < 0 ? " - " : " + ").append(Math.abs(k));
            }
            return sb.toString();
        }

        String key() {
            StringBuilder sb = new StringBuilder();
            for (long v : c) sb.append(v).append(',');
            return sb.append(';').append(k).toString();
        }
    }

    /** {@code f ≥ 0} (or {@code f = 0} when {@code eq}); strict forms are pre-tightened over ℤ. */
    private static final class Cons {
        final LinForm f;
        final boolean eq;
        Cons(LinForm f, boolean eq) { this.f = f; this.eq = eq; }
        String key() { return (eq ? "=" : ">") + f.key(); }
    }

    /**
     * A determinised transition: from a state {@code x} over {@code src}'s
     * formals, the step is enabled iff every {@code guard} constraint holds, and
     * then moves to the state {@code update(x)} over {@code tgt}'s formals.
     */
    private static final class Step {
        final ItsLocation src, tgt;
        final LinForm[] update;   // one per tgt formal, each over src's positions
        final List<Cons> guard;   // over src's positions
        Step(ItsLocation src, ItsLocation tgt, LinForm[] update, List<Cons> guard) {
            this.src = src; this.tgt = tgt; this.update = update; this.guard = guard;
        }
    }

    // -------------------------------------------------------------------------
    // Determinisation: ItsTransition → Step
    // -------------------------------------------------------------------------

    /**
     * Turns {@code t} into an explicit {@link Step}, or {@code null} when that
     * fails. Update variables defined by a guard equality with coefficient ±1
     * over already-known variables are solved exactly (±1 keeps them integral);
     * any leftover fresh variable is fixed to 0 — a sound restriction of the
     * relation. Residual guard constraints are kept (with the fixed values
     * substituted), so the step never fires where the original could not.
     */
    private static Step determinize(ItsTransition t) {
        if (!t.isSupported()) return null;
        List<String> formals = t.source().variables();
        Set<String> formalSet = new HashSet<String>(formals);

        // Name-based working copies of the guard, strict forms tightened (e > 0 ⇒ e − 1 ≥ 0).
        List<Map<String, Long>> coeffs = new ArrayList<Map<String, Long>>();
        List<Long> consts = new ArrayList<Long>();
        List<Boolean> eqs = new ArrayList<Boolean>();
        for (ItsLinearConstraint c : t.constraints()) {
            coeffs.add(new LinkedHashMap<String, Long>(c.lhs().coefficients()));
            long k = c.lhs().constant();
            if (c.op() == ItsLinearConstraint.Op.GT) k = Math.subtractExact(k, 1);
            consts.add(k);
            eqs.add(c.op() == ItsLinearConstraint.Op.EQ);
        }

        // Solve fresh variables from equalities: v = −(rest)/a needs a = ±1 and
        // every other variable of the row already known (a formal or solved fresh).
        Map<String, Map<String, Long>> solC = new HashMap<String, Map<String, Long>>();
        Map<String, Long> solK = new HashMap<String, Long>();
        Set<Integer> consumed = new HashSet<Integer>();
        boolean progress = true;
        while (progress) {
            progress = false;
            for (int i = 0; i < coeffs.size(); i++) {
                if (consumed.contains(i) || !eqs.get(i)) continue;
                String cand = null;
                int unknowns = 0;
                for (String v : coeffs.get(i).keySet())
                    if (!formalSet.contains(v) && !solC.containsKey(v)) { unknowns++; cand = v; }
                if (unknowns != 1) continue;
                long a = coeffs.get(i).get(cand);
                if (a != 1 && a != -1) continue;
                // cand = −(rest)/a, with solved fresh variables expanded away.
                Map<String, Long> rc = new HashMap<String, Long>();
                long rk = consts.get(i);
                for (Map.Entry<String, Long> e : coeffs.get(i).entrySet()) {
                    if (e.getKey().equals(cand)) continue;
                    if (solC.containsKey(e.getKey())) {
                        long m = e.getValue();
                        for (Map.Entry<String, Long> s : solC.get(e.getKey()).entrySet())
                            accumulate(rc, s.getKey(), Math.multiplyExact(m, s.getValue()));
                        rk = Math.addExact(rk, Math.multiplyExact(m, solK.get(e.getKey())));
                    } else {
                        accumulate(rc, e.getKey(), e.getValue());
                    }
                }
                if (a == 1) { negateInPlace(rc); rk = Math.negateExact(rk); }
                solC.put(cand, rc);
                solK.put(cand, rk);
                consumed.add(i);
                progress = true;
            }
        }

        // Positional residual guard: expand solved variables, drop the rest (fixed to 0).
        List<Cons> guard = new ArrayList<Cons>();
        Set<String> seen = new HashSet<String>();
        for (int i = 0; i < coeffs.size(); i++) {
            if (consumed.contains(i)) continue;
            LinForm f = toPositional(coeffs.get(i), consts.get(i), formals, solC, solK);
            if (!addCons(f, eqs.get(i), guard, seen)) return null;   // dead or over budget
        }

        // Updates: same expansion, one form per target formal.
        List<ItsLinearExpression> upd = t.updates();
        LinForm[] update = new LinForm[upd.size()];
        for (int j = 0; j < upd.size(); j++)
            update[j] = toPositional(upd.get(j).coefficients(), upd.get(j).constant(),
                    formals, solC, solK);

        return new Step(t.source(), t.target(), update, guard);
    }

    /**
     * Adds {@code f OP 0} to a step guard unless trivially true. Returns false —
     * the step must be ABANDONED — when the constraint is constant-false (the
     * step never fires) or the budget is exhausted: silently dropping a guard
     * constraint would enlarge the step's relation, and a witness riding on an
     * enlarged step could claim a run the real system does not have (a false
     * NONTERMINATES). Bailing out is the sound reaction to both.
     */
    private static boolean addCons(LinForm f, boolean eq, List<Cons> guard, Set<String> seen) {
        if (f.isConstant()) return eq ? f.k == 0 : f.k >= 0;
        Cons c = new Cons(f, eq);
        if (!seen.add(c.key())) return true;                  // duplicate: already enforced
        if (guard.size() >= MAX_CONSTRAINTS) return false;    // over budget: abandon the step
        guard.add(c);
        return true;
    }

    /** A name-based linear form, rewritten over {@code formals}' positions via the solved map. */
    private static LinForm toPositional(Map<String, Long> coeffs, long cst, List<String> formals,
            Map<String, Map<String, Long>> solC, Map<String, Long> solK) {
        Map<String, Long> flat = new HashMap<String, Long>();
        long k = cst;
        for (Map.Entry<String, Long> e : coeffs.entrySet()) {
            if (solC.containsKey(e.getKey())) {
                long m = e.getValue();
                for (Map.Entry<String, Long> s : solC.get(e.getKey()).entrySet())
                    accumulate(flat, s.getKey(), Math.multiplyExact(m, s.getValue()));
                k = Math.addExact(k, Math.multiplyExact(m, solK.get(e.getKey())));
            } else {
                accumulate(flat, e.getKey(), e.getValue());
            }
        }
        long[] c = new long[formals.size()];
        for (int i = 0; i < formals.size(); i++) {
            Long v = flat.get(formals.get(i));
            if (v != null) c[i] = v;
        }
        // Variables in `flat` that are neither formals nor solved are unsolved
        // fresh variables: dropping their terms is exactly the "fix to 0" choice.
        return new LinForm(c, k);
    }

    private static void accumulate(Map<String, Long> m, String var, long add) {
        long n = Math.addExact(m.getOrDefault(var, 0L), add);
        if (n == 0) m.remove(var); else m.put(var, n);
    }

    private static void negateInPlace(Map<String, Long> m) {
        for (Map.Entry<String, Long> e : m.entrySet()) e.setValue(Math.negateExact(e.getValue()));
    }

    // -------------------------------------------------------------------------
    // Exact step composition
    // -------------------------------------------------------------------------

    /** Sequential composition {@code a; b} (requires {@code a.tgt} = {@code b.src}); null if dead. */
    private static Step compose(Step a, Step b) {
        int inArity = a.src.arity();
        List<Cons> guard = new ArrayList<Cons>();
        Set<String> seen = new HashSet<String>();
        for (Cons c : a.guard)
            if (!addCons(c.f, c.eq, guard, seen)) return null;
        for (Cons c : b.guard)
            if (!addCons(c.f.compose(a.update, inArity), c.eq, guard, seen)) return null;
        LinForm[] update = new LinForm[b.update.length];
        for (int j = 0; j < b.update.length; j++)
            update[j] = b.update[j].compose(a.update, inArity);
        return new Step(a.src, b.tgt, update, guard);
    }

    /** Identity step at {@code loc} (used as the seed of path composition). */
    private static Step identity(ItsLocation loc) {
        int n = loc.arity();
        LinForm[] u = new LinForm[n];
        for (int j = 0; j < n; j++) {
            long[] c = new long[n];
            c[j] = 1;
            u[j] = new LinForm(c, 0);
        }
        return new Step(loc, loc, u, new ArrayList<Cons>());
    }

    /** Composes a cycle's transitions into one self-loop step at its head, or null. */
    private static Step stepOfCycle(List<ItsTransition> cycle) {
        Step s = null;
        for (ItsTransition t : cycle) {
            Step d = determinize(t);
            if (d == null) return null;
            s = s == null ? d : compose(s, d);
            if (s == null) return null;
        }
        return s;
    }

    // -------------------------------------------------------------------------
    // Recurrent-set search on one self-loop step
    // -------------------------------------------------------------------------

    /**
     * Searches an inductive set for the self-loop {@code s}: a constraint list
     * {@code G ⊇ s.guard} with {@code G(x) ⊨ G(s(x))} (Farkas-certified).
     *
     * <p>Stage NT1: the guard itself (the Frohn–Giesl criterion). Stage NT2:
     * when a candidate is not inductive, it is strengthened with the violated
     * post-constraints — {@code G ← G ∧ G∘s}, a bounded descending iteration
     * towards the greatest closed recurrence set (Chen et al.) — and the guard
     * is also retried conjoined with the location's polyhedral invariant, whose
     * facts (established before the loop) the guard often lacks. Invariants only
     * seed the search; inductiveness is re-proved exactly, so an imprecise
     * invariant can never produce a wrong witness. Returns null when no
     * candidate becomes inductive within the bounds.
     */
    private static List<Cons> recurrentSet(Step s, List<ItsLinearConstraint> invariantAtHead) {
        List<Cons> guardSeed = dedupe(s.guard);
        List<Cons> g = strengthen(guardSeed, s);
        if (g != null) return g;

        List<Cons> inv = invariantCons(invariantAtHead, s.src.variables());
        if (inv.isEmpty()) return null;
        List<Cons> seeded = new ArrayList<Cons>(guardSeed);
        Set<String> seen = new HashSet<String>();
        for (Cons c : seeded) seen.add(c.key());
        for (Cons c : inv) if (seen.add(c.key()) && seeded.size() < MAX_CONSTRAINTS) seeded.add(c);
        if (seeded.size() == guardSeed.size()) return null;   // invariant added nothing
        return strengthen(seeded, s);
    }

    /**
     * Bounded descending iteration: repeatedly conjoins the candidate with its
     * own image constraints until it is inductive (returned) or the bounds are
     * hit (null). Every added constraint is a consequence of "stay one more
     * iteration", so the final set is a subset of the seed — still inside the
     * guard, as recurrence requires.
     */
    private static List<Cons> strengthen(List<Cons> seed, Step s) {
        int n = s.src.arity();
        List<Cons> g = new ArrayList<Cons>(seed);
        Set<String> seen = new HashSet<String>();
        for (Cons c : g) seen.add(c.key());
        for (int round = 0; round <= MAX_STRENGTHEN; round++) {
            List<Cons> missing = new ArrayList<Cons>();
            for (Cons c : g) {
                LinForm post = c.f.compose(s.update, n);
                boolean held = entails(g, post) && (!c.eq || entails(g, post.negate()));
                if (!held) missing.add(new Cons(post, c.eq));
            }
            if (missing.isEmpty()) return g;
            boolean grew = false;
            for (Cons c : missing) {
                if (c.f.isConstant()) {
                    if (c.eq ? c.f.k != 0 : c.f.k < 0) return null;   // G dies after one step
                    continue;
                }
                if (seen.add(c.key()) && g.size() < MAX_CONSTRAINTS) { g.add(c); grew = true; }
            }
            if (!grew) return null;   // constraint cap reached without convergence
        }
        return null;
    }

    /** The location invariant as positional constraints (strict forms tightened), skipping aliens. */
    private static List<Cons> invariantCons(List<ItsLinearConstraint> inv, List<String> formals) {
        List<Cons> out = new ArrayList<Cons>();
        if (inv == null) return out;
        Map<String, Integer> pos = new HashMap<String, Integer>();
        for (int i = 0; i < formals.size(); i++) pos.put(formals.get(i), i);
        nextConstraint:
        for (ItsLinearConstraint c : inv) {
            long[] coef = new long[formals.size()];
            for (Map.Entry<String, Long> e : c.lhs().coefficients().entrySet()) {
                Integer i = pos.get(e.getKey());
                if (i == null) continue nextConstraint;   // not over the formals: unusable
                coef[i] = e.getValue();
            }
            long k = c.lhs().constant();
            if (c.op() == ItsLinearConstraint.Op.GT) k = Math.subtractExact(k, 1);
            out.add(new Cons(new LinForm(coef, k), c.op() == ItsLinearConstraint.Op.EQ));
        }
        return out;
    }

    private static List<Cons> dedupe(List<Cons> cs) {
        List<Cons> out = new ArrayList<Cons>();
        Set<String> seen = new HashSet<String>();
        for (Cons c : cs) if (seen.add(c.key())) out.add(c);
        return out;
    }

    /**
     * Farkas entailment, exact: do {@code λ ≥ 0, λ₀ ≥ 0} exist with
     * {@code e = Σ λᵢ·pᵢ + λ₀} (equality premises get a free, pos−neg split
     * multiplier)? Then {@code e ≥ 0} wherever all premises hold. Complete over
     * ℚ for satisfiable premise sets; an unsatisfiable candidate is harmless
     * because the reachability stage must exhibit a concrete point in it anyway.
     */
    private static boolean entails(List<Cons> premises, LinForm e) {
        if (e.isConstant()) return e.k >= 0;
        int n = e.c.length;
        // Variable layout: one λ per premise (two for an equality), then λ₀.
        int vars = 0;
        for (Cons p : premises) vars += p.eq ? 2 : 1;
        int lam0 = vars++;
        LinearProgram lp = new LinearProgram(vars);
        for (int v = 0; v < n; v++) {
            Rational[] row = zeros(vars);
            int idx0 = 0;
            for (Cons p : premises) {
                row[idx0++] = Rational.of(p.f.c[v]);
                if (p.eq) row[idx0++] = Rational.of(Math.negateExact(p.f.c[v]));
            }
            lp.addConstraint(row, LinearProgram.Op.EQ, Rational.of(e.c[v]));
        }
        Rational[] row = zeros(vars);
        int idx = 0;
        for (Cons p : premises) {
            row[idx++] = Rational.of(p.f.k);
            if (p.eq) row[idx++] = Rational.of(Math.negateExact(p.f.k));
        }
        row[lam0] = Rational.ONE;
        lp.addConstraint(row, LinearProgram.Op.EQ, Rational.of(e.k));
        return lp.solve().feasible;
    }

    private static Rational[] zeros(int n) {
        Rational[] r = new Rational[n];
        for (int i = 0; i < n; i++) r[i] = Rational.ZERO;
        return r;
    }

    // -------------------------------------------------------------------------
    // Reachability: a concrete integer entry state whose run lands in G
    // -------------------------------------------------------------------------

    /**
     * Builds the full witness: a BFS path entry → head, its exact composition,
     * and an integer entry point satisfying the path guards with its image in
     * {@code G}. Every numeric fact is re-checked by BigInteger substitution
     * before the witness is returned.
     */
    private Witness witness(IntegerTransitionSystem its, String entry, Step loop,
            List<Cons> g, List<ItsTransition> cycle) {
        List<ItsTransition> path = bfsPath(its, entry, loop.src.name());
        if (path == null) return null;

        ItsLocation entryLoc = its.location(entry);
        Step sigma = identity(entryLoc);
        for (ItsTransition t : path) {
            Step d = determinize(t);
            if (d == null) return null;
            sigma = compose(sigma, d);
            if (sigma == null) return null;
        }

        // Constraint system over the entry formals: path guards + G at the image.
        int n = entryLoc.arity();
        List<Cons> sys = new ArrayList<Cons>(sigma.guard);
        for (Cons c : g) sys.add(new Cons(c.f.compose(sigma.update, n), c.eq));

        BigInteger[] x0 = findIntegerPoint(sys, n);
        if (x0 == null) return null;

        // Exact replay (defence in depth): path feasible, head in G, one loop step stays in G.
        if (!satisfies(sigma.guard, x0)) return null;
        BigInteger[] h = evalUpdate(sigma.update, x0);
        if (!satisfies(g, h)) return null;
        if (!satisfies(loop.guard, h)) return null;
        if (!satisfies(g, evalUpdate(loop.update, h))) return null;

        return new Witness(loop.src.name(), render(g, loop.src.variables()), cycle, path,
                renderStep(loop), stateMap(entryLoc.variables(), x0),
                stateMap(loop.src.variables(), h));
    }

    /** The determinised self-loop update as {@code X' = …} lines, over the head's formals. */
    private static List<String> renderStep(Step loop) {
        List<String> names = loop.src.variables();
        List<String> out = new ArrayList<String>();
        for (int j = 0; j < loop.update.length; j++)
            out.add(names.get(j) + "' = " + loop.update[j].render(names));
        return out;
    }

    /** Shortest entry → target path over supported transitions (empty when equal), or null. */
    private static List<ItsTransition> bfsPath(IntegerTransitionSystem its, String entry, String target) {
        if (entry.equals(target)) return new ArrayList<ItsTransition>();
        Map<String, ItsTransition> pred = new HashMap<String, ItsTransition>();
        Deque<String> work = new ArrayDeque<String>();
        Set<String> seen = new HashSet<String>();
        seen.add(entry);
        work.add(entry);
        while (!work.isEmpty()) {
            String cur = work.poll();
            for (ItsTransition t : its.transitions()) {
                if (!t.isSupported() || !t.source().name().equals(cur)) continue;
                String nxt = t.target().name();
                if (!seen.add(nxt)) continue;
                pred.put(nxt, t);
                if (nxt.equals(target)) {
                    LinkedList<ItsTransition> path = new LinkedList<ItsTransition>();
                    for (String at = target; !at.equals(entry); at = path.getFirst().source().name())
                        path.addFirst(pred.get(at));
                    return path;
                }
                work.add(nxt);
            }
        }
        return null;
    }

    /** An integer point of {@code sys} ({@code n} variables): zero, then LP vertex + roundings. */
    private static BigInteger[] findIntegerPoint(List<Cons> sys, int n) {
        BigInteger[] zero = new BigInteger[n];
        java.util.Arrays.fill(zero, BigInteger.ZERO);
        if (satisfies(sys, zero)) return zero;
        if (n == 0) return null;

        // Free variables as pos − neg splits; pure rational feasibility.
        LinearProgram lp = new LinearProgram(2 * n);
        for (Cons c : sys) {
            Rational[] row = new Rational[2 * n];
            for (int i = 0; i < n; i++) {
                row[2 * i] = Rational.of(c.f.c[i]);
                row[2 * i + 1] = Rational.of(c.f.c[i]).negate();
            }
            lp.addConstraint(row, c.eq ? LinearProgram.Op.EQ : LinearProgram.Op.GE,
                    Rational.of(c.f.k).negate());
        }
        LinearProgram.Solution sol = lp.solve();
        if (!sol.feasible || sol.x == null) return null;

        Rational[] q = new Rational[n];
        for (int i = 0; i < n; i++) q[i] = sol.x[2 * i].subtract(sol.x[2 * i + 1]);
        // The vertex itself, then uniform nearest / floor / ceil roundings.
        BigInteger[][] candidates = { roundEach(q, 0), roundEach(q, -1), roundEach(q, 1) };
        for (BigInteger[] cand : candidates)
            if (cand != null && satisfies(sys, cand)) return cand;
        return null;
    }

    /** Rounds each rational: mode 0 nearest, −1 floor, +1 ceil. */
    private static BigInteger[] roundEach(Rational[] q, int mode) {
        BigInteger[] r = new BigInteger[q.length];
        for (int i = 0; i < q.length; i++) {
            BigInteger num = q[i].numerator(), den = q[i].denominator();   // den > 0
            BigInteger[] dr = num.divideAndRemainder(den);
            BigInteger fl = dr[1].signum() < 0 ? dr[0].subtract(BigInteger.ONE) : dr[0];
            if (mode < 0) r[i] = fl;
            else if (mode > 0) r[i] = dr[1].signum() == 0 ? dr[0] : fl.add(BigInteger.ONE);
            else {   // nearest: floor(q + 1/2)
                BigInteger twice = num.multiply(BigInteger.valueOf(2)).add(den);
                BigInteger[] d2 = twice.divideAndRemainder(den.multiply(BigInteger.valueOf(2)));
                r[i] = d2[1].signum() < 0 ? d2[0].subtract(BigInteger.ONE) : d2[0];
            }
        }
        return r;
    }

    private static boolean satisfies(List<Cons> cs, BigInteger[] x) {
        for (Cons c : cs) {
            BigInteger v = c.f.eval(x);
            if (c.eq ? v.signum() != 0 : v.signum() < 0) return false;
        }
        return true;
    }

    private static BigInteger[] evalUpdate(LinForm[] update, BigInteger[] x) {
        BigInteger[] r = new BigInteger[update.length];
        for (int j = 0; j < update.length; j++) r[j] = update[j].eval(x);
        return r;
    }

    private static Map<String, BigInteger> stateMap(List<String> names, BigInteger[] x) {
        Map<String, BigInteger> m = new LinkedHashMap<String, BigInteger>();
        for (int i = 0; i < names.size(); i++) m.put(names.get(i), x[i]);
        return m;
    }

    private static List<String> render(List<Cons> g, List<String> names) {
        List<String> out = new ArrayList<String>();
        for (Cons c : g) out.add(c.f.render(names) + (c.eq ? " = 0" : " >= 0"));
        return out;
    }
}
