package fr.univreunion.rati.its;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Summarises an {@link IntegerTransitionSystem} onto its <em>local</em> variables
 * by composing the per-basic-block transition graph of each method and
 * existentially eliminating the operand-<b>stack</b> variables ({@code SI*},
 * {@code SO*}) from the state.
 *
 * <p><b>Why.</b> The path-length export cuts at basic-block granularity and
 * exposes the JVM operand stack as explicit state variables, because a value is
 * threaded across blocks through the stack ({@code SO0} of one block becomes
 * {@code SI0} of the next). RaTI's exact rational Farkas LP then carries those
 * stack dimensions through a large strongly-connected component, and on a few
 * programs (Ackermann, Numerical3) the coefficients blow up into huge bignums —
 * the LP grinds for tens of seconds. Yet the termination argument lives entirely
 * in the <em>locals</em>: collapsing a method's block graph into direct edges
 * between its recursion heads, over locals only, is the dimensionality cap of
 * Spoto-Mesnard-Payet TOPLAS 2010 §8 ("the path-length of the highest variables
 * is not approximated"). This is exactly the shape of the hand-built
 * {@code (m,n)} Ackermann that RaTI proves in 0.14 s instead of grinding.
 *
 * <p><b>Soundness.</b> Two exact-over-the-rationals operations are used:
 * relation composition (eliminating an intermediate location's variables) and
 * projection (eliminating the stack variables). Both <em>over</em>-approximate
 * the original system, so "the projected system terminates" implies "the
 * original terminates" — the sound direction. Because the result has at least
 * the original's runs, a ranking proof on it is sound; a non-termination witness
 * on it may be spurious, so the caller must downgrade NONTERMINATES to UNKNOWN
 * when this transform is enabled (see {@code RankMain}).
 *
 * <p><b>Robustness.</b> All-or-nothing: on any structural anomaly (an unsupported
 * transition, a {@code long} coefficient overflow, or a blow-up past the safety
 * caps) it returns the <em>original</em> system unchanged, so a failure degrades
 * to "no speed-up", never to a corrupt ITS. A composed edge whose guard is
 * infeasible is dropped (removing an unreachable edge preserves behaviour).
 */
public final class StackProjection {

    private StackProjection() {}

    /** Prefix for the post-state (target) copy of a variable in a relation. */
    private static final String POST = "P#";
    /** Prefix for the mid-state variables introduced when composing two relations. */
    private static final String MID = "M#";

    /** Safety caps: fall back if a single guard or the edge set blows up. */
    private static final int MAX_ROWS = 4000;
    private static final int MAX_EDGES = 6000;

    private static boolean isStackBase(String v) {
        return !v.isEmpty() && v.charAt(0) == 'S';     // SI*, SO*
    }

    private static boolean isLocalArg(String v) {
        return v.startsWith("LI");                     // source/target local formal arg
    }

    private static boolean isAux(String v) {
        return v.startsWith("LO") || v.startsWith("SO");   // block output vars
    }

    /**
     * Returns a system equivalent-or-over-approximating {@code its} with the
     * operand stack eliminated from the state, or {@code its} itself if the
     * transform is not safely applicable.
     */
    public static IntegerTransitionSystem project(IntegerTransitionSystem its) {
        try {
            return projectOrThrow(its);
        } catch (Fallback f) {
            return its;
        } catch (RuntimeException e) {
            return its;                                 // never corrupt the analysis
        }
    }

    private static final class Fallback extends RuntimeException {
        Fallback(String m) { super(m); }
    }

    private static final class Infeasible extends RuntimeException {}

    // ----- a transition relation over pre/post (and transient mid) variables --

    /** A relation {@code src(pre) -> tgt(post)} as a conjunction of {@link Row}s. */
    private static final class Rel {
        final String src, tgt;
        final List<Row> rows;
        final int cost;
        Rel(String src, String tgt, List<Row> rows, int cost) {
            this.src = src; this.tgt = tgt; this.rows = rows; this.cost = cost;
        }
    }

    private static IntegerTransitionSystem projectOrThrow(IntegerTransitionSystem its) {
        if (its.hasUnsupportedTransition()) throw new Fallback("unsupported transition");

        // Uniform local state vector (LI* in order); require all locations to agree.
        List<String> keptLocals = null;
        boolean anyStack = false;
        for (ItsLocation l : its.locations()) {
            List<String> locals = localsOf(l.variables());
            if (keptLocals == null) keptLocals = locals;
            else if (!keptLocals.equals(locals)) throw new Fallback("non-uniform locals");
            for (String v : l.variables()) if (isStackBase(v)) anyStack = true;
        }
        if (keptLocals == null) throw new Fallback("no locations");
        if (!anyStack) throw new Fallback("no stack vars");

        String entry = its.entryLocation();
        Set<String> reachable = reachableFrom(its, entry);

        // 1. Each transition becomes a clean relation over pre (LI*,SI*) and
        //    post (P#LI*,P#SI*); the block output vars (LO*,SO*) are eliminated.
        List<Rel> edges = new ArrayList<Rel>();
        for (ItsTransition t : its.transitions()) {
            if (!reachable.contains(t.source().name())) continue;
            edges.add(toRel(t));
        }

        // 2. Choose a cut-set (feedback vertex set incl. entry) and eliminate every
        //    other location by composing its in-edges with its out-edges.
        Set<String> cut = cutSet(entry, reachable, edges);
        edges = eliminateLocations(edges, cut);

        // 3. Project the stack out of every surviving edge: eliminate pre SI* and
        //    post P#SI*, leaving a relation purely over locals.
        IntegerTransitionSystem out = new IntegerTransitionSystem(its.name(), entry);
        Map<String, ItsLocation> newLoc = new LinkedHashMap<String, ItsLocation>();
        for (String name : cut) {
            ItsLocation src = its.location(name);
            List<String> locals = src != null ? localsOf(src.variables()) : keptLocals;
            ItsLocation nl = new ItsLocation(name, locals);
            newLoc.put(name, nl);
            out.addLocation(nl);
        }
        for (Rel r : edges) {
            ItsTransition pt = rebuild(r, newLoc, keptLocals);
            if (pt != null) out.addTransition(pt);
        }
        return out;
    }

    private static List<String> localsOf(List<String> vars) {
        List<String> r = new ArrayList<String>();
        for (String v : vars) if (isLocalArg(v)) r.add(v);
        return r;
    }

    private static Set<String> reachableFrom(IntegerTransitionSystem its, String start) {
        Set<String> seen = new LinkedHashSet<String>();
        Deque<String> q = new ArrayDeque<String>();
        seen.add(start); q.add(start);
        while (!q.isEmpty()) {
            String cur = q.poll();
            for (ItsTransition t : its.transitions())
                if (t.source().name().equals(cur) && seen.add(t.target().name()))
                    q.add(t.target().name());
        }
        return seen;
    }

    /** Build the clean pre/post relation of a single transition. */
    private static Rel toRel(ItsTransition t) {
        List<String> tgtArgs = t.target().variables();
        if (t.updates().size() != tgtArgs.size()) throw new Fallback("update/arity mismatch");
        List<Row> rows = new ArrayList<Row>();
        for (ItsLinearConstraint c : t.constraints()) rows.add(Row.of(c));
        for (int k = 0; k < tgtArgs.size(); k++)
            rows.add(Row.fromUpdate(POST + tgtArgs.get(k), t.updates().get(k)));
        // Eliminate the block output vars (LO*, SO*); keep pre (LI*,SI*) and post (P#…).
        Set<String> aux = new LinkedHashSet<String>();
        for (Row r : rows) for (String v : r.coef.keySet()) if (isAux(v)) aux.add(v);
        rows = eliminateAll(rows, aux);
        return new Rel(t.source().name(), t.target().name(), rows, Math.max(1, t.cost()));
    }

    // ----- location elimination ----------------------------------------------

    /** A feedback vertex set containing {@code entry}: keep it minimal-ish, greedily. */
    private static Set<String> cutSet(String entry, Set<String> nodes, List<Rel> edges) {
        Set<String> cut = new LinkedHashSet<String>();
        cut.add(entry);
        while (true) {
            List<String> cycle = findCycle(nodes, edges, cut);
            if (cycle == null) return cut;
            // Add the cycle node (other than entry) with the highest total degree.
            String best = null; int bestDeg = -1;
            for (String n : cycle) {
                if (cut.contains(n)) continue;
                int deg = 0;
                for (Rel e : edges) if (e.src.equals(n) || e.tgt.equals(n)) deg++;
                if (deg > bestDeg) { bestDeg = deg; best = n; }
            }
            if (best == null) throw new Fallback("cycle through cut only");
            cut.add(best);
        }
    }

    /** Finds a cycle among nodes outside {@code cut}, or null if that subgraph is acyclic. */
    private static List<String> findCycle(Set<String> nodes, List<Rel> edges, Set<String> cut) {
        Map<String, List<String>> succ = new LinkedHashMap<String, List<String>>();
        for (String n : nodes) if (!cut.contains(n)) succ.put(n, new ArrayList<String>());
        for (Rel e : edges)
            if (!cut.contains(e.src) && !cut.contains(e.tgt) && succ.containsKey(e.src))
                succ.get(e.src).add(e.tgt);
        Set<String> visiting = new LinkedHashSet<String>();
        Set<String> done = new LinkedHashSet<String>();
        Deque<String> stack = new ArrayDeque<String>();
        for (String s : succ.keySet()) {
            List<String> c = dfsCycle(s, succ, visiting, done, stack);
            if (c != null) return c;
        }
        return null;
    }

    private static List<String> dfsCycle(String u, Map<String, List<String>> succ,
            Set<String> visiting, Set<String> done, Deque<String> stack) {
        if (done.contains(u)) return null;
        if (visiting.contains(u)) {
            List<String> cyc = new ArrayList<String>();
            for (String x : stack) { cyc.add(x); if (x.equals(u)) break; }
            return cyc;
        }
        visiting.add(u); stack.push(u);
        for (String v : succ.getOrDefault(u, java.util.Collections.<String>emptyList())) {
            List<String> c = dfsCycle(v, succ, visiting, done, stack);
            if (c != null) return c;
        }
        stack.pop(); visiting.remove(u); done.add(u);
        return null;
    }

    /** Eliminate every non-cut location by composing its in-edges with its out-edges. */
    private static List<Rel> eliminateLocations(List<Rel> edges, Set<String> cut) {
        Set<String> toGo = new LinkedHashSet<String>();
        for (Rel e : edges) {
            if (!cut.contains(e.src)) toGo.add(e.src);
            if (!cut.contains(e.tgt)) toGo.add(e.tgt);
        }
        for (String L : toGo) {
            List<Rel> in = new ArrayList<Rel>(), outE = new ArrayList<Rel>(), rest = new ArrayList<Rel>();
            for (Rel e : edges) {
                boolean si = e.src.equals(L), ti = e.tgt.equals(L);
                if (si && ti) throw new Fallback("self-loop on non-cut location");
                if (ti) in.add(e);
                else if (si) outE.add(e);
                else rest.add(e);
            }
            List<Rel> next = rest;
            for (Rel a : in)
                for (Rel b : outE)
                    next.add(compose(a, b));
            if (next.size() > MAX_EDGES) throw new Fallback("edge blow-up");
            edges = next;
        }
        return edges;
    }

    /** Compose {@code a: A->L} with {@code b: L->B} into {@code A->B}, eliminating L's state. */
    private static Rel compose(Rel a, Rel b) {
        List<Row> rows = new ArrayList<Row>();
        // a's post (P#x) becomes the mid state (M#x); a's pre (LI*,SI*) stays.
        for (Row r : a.rows) rows.add(renamePrefix(r, POST, MID));
        // b's pre (LI*,SI*) becomes the mid state (M#…); b's post (P#x) stays.
        for (Row r : b.rows) rows.add(renamePreToMid(r));
        Set<String> mid = new LinkedHashSet<String>();
        for (Row r : rows) for (String v : r.coef.keySet()) if (v.startsWith(MID)) mid.add(v);
        List<Row> composed;
        try {
            composed = eliminateAll(rows, mid);
        } catch (Infeasible inf) {
            // The two steps cannot be chained: contribute nothing (drop the path).
            composed = null;
        }
        if (composed == null) return new Rel(a.src, b.tgt, infeasibleRows(), a.cost + b.cost);
        return new Rel(a.src, b.tgt, composed, a.cost + b.cost);
    }

    /** A guard that is unsatisfiable, so the edge is dropped on rebuild. */
    private static List<Row> infeasibleRows() {
        Row r = new Row();
        r.op = ItsLinearConstraint.Op.GE;
        r.cst = BigInteger.valueOf(-1);                 // -1 >= 0  is false
        List<Row> l = new ArrayList<Row>();
        l.add(r);
        return l;
    }

    private static Row renamePrefix(Row r, String from, String to) {
        Row n = new Row(); n.op = r.op; n.cst = r.cst;
        for (Map.Entry<String, BigInteger> e : r.coef.entrySet()) {
            String k = e.getKey();
            if (k.startsWith(from)) k = to + k.substring(from.length());
            n.add(k, e.getValue());
        }
        return n;
    }

    private static Row renamePreToMid(Row r) {
        Row n = new Row(); n.op = r.op; n.cst = r.cst;
        for (Map.Entry<String, BigInteger> e : r.coef.entrySet()) {
            String k = e.getKey();
            if (k.startsWith("LI") || k.startsWith("SI")) k = MID + k;   // a pre var of b
            n.add(k, e.getValue());
        }
        return n;
    }

    // ----- rebuild a projected transition over locals only -------------------

    private static ItsTransition rebuild(Rel r, Map<String, ItsLocation> newLoc,
            List<String> keptLocals) {
        // Project the stack out: eliminate pre SI* and post P#SI*.
        Set<String> stack = new LinkedHashSet<String>();
        for (Row row : r.rows)
            for (String v : row.coef.keySet()) {
                String base = v.startsWith(POST) ? v.substring(POST.length()) : v;
                if (isStackBase(base)) stack.add(v);
            }
        List<Row> rows;
        try {
            rows = eliminateAll(r.rows, stack);
        } catch (Infeasible inf) {
            return null;
        }

        ItsLocation src = newLoc.get(r.src), tgt = newLoc.get(r.tgt);
        if (src == null || tgt == null) throw new Fallback("dangling edge");

        // P#LI_k -> fresh nondeterministic output LO_k; one update per target local.
        List<ItsLinearExpression> updates = new ArrayList<ItsLinearExpression>();
        Map<String, String> rename = new LinkedHashMap<String, String>();
        for (String arg : tgt.variables()) {                 // already locals only
            String outVar = "LO" + arg.substring(2);          // LI<k> -> LO<k>
            rename.put(POST + arg, outVar);
            updates.add(ItsLinearExpression.variable(outVar));
        }
        if (updates.size() != tgt.arity()) throw new Fallback("projected arity mismatch");

        List<ItsLinearConstraint> guard = new ArrayList<ItsLinearConstraint>();
        for (Row row : rows) {
            ItsLinearConstraint c = row.toConstraint(rename);
            if (c != null) guard.add(c);
        }
        return new ItsTransition(src, tgt, guard, updates, Math.max(1, r.cost), true);
    }

    // ----- generic Fourier-Motzkin / Gaussian elimination over Rows ----------

    private static List<Row> eliminateAll(List<Row> rows, Set<String> elim) {
        Set<String> remaining = new LinkedHashSet<String>(elim);
        while (true) {
            String pick = choose(rows, remaining);
            if (pick == null) return rows;
            rows = eliminateVar(rows, pick);
            remaining.remove(pick);
            if (rows.size() > MAX_ROWS) throw new Fallback("guard blow-up");
        }
    }

    private static String choose(List<Row> rows, Set<String> remaining) {
        String anyPresent = null;
        for (String v : remaining) {
            boolean inEq = false, present = false;
            for (Row r : rows) {
                if (r.coef.containsKey(v)) {
                    present = true;
                    if (r.op == ItsLinearConstraint.Op.EQ) { inEq = true; break; }
                }
            }
            if (inEq) return v;
            if (present && anyPresent == null) anyPresent = v;
        }
        return anyPresent;
    }

    private static List<Row> eliminateVar(List<Row> rows, String v) {
        List<Row> without = new ArrayList<Row>();
        Row pivotEq = null;
        List<Row> withV = new ArrayList<Row>();
        for (Row r : rows) {
            if (!r.coef.containsKey(v)) { without.add(r); continue; }
            if (pivotEq == null && r.op == ItsLinearConstraint.Op.EQ) pivotEq = r;
            else withV.add(r);
        }
        if (pivotEq != null) return substitute(without, withV, pivotEq, v);
        return fourierMotzkin(without, withV, v);
    }

    private static List<Row> substitute(List<Row> out, List<Row> withV, Row pivotEq, String v) {
        BigInteger a = pivotEq.coef.get(v);
        if (a.signum() < 0) { pivotEq = pivotEq.scale(BigInteger.valueOf(-1)); a = a.negate(); }
        for (Row r : withV) {
            BigInteger b = r.coef.get(v);
            Row r2 = r.combine(a, pivotEq, b.negate());      // a*r - b*pivotEq, a>0
            r2.op = r.op;
            r2.normalize();
            r2.classifyTrivial();
            if (!r2.dropped) out.add(r2);
        }
        return out;
    }

    private static List<Row> fourierMotzkin(List<Row> out, List<Row> withV, String v) {
        List<Row> pos = new ArrayList<Row>(), neg = new ArrayList<Row>();
        for (Row r : withV) {
            if (r.op == ItsLinearConstraint.Op.EQ) throw new Fallback("eq in FM");
            if (r.coef.get(v).signum() > 0) pos.add(r); else neg.add(r);
        }
        for (Row p : pos) {
            BigInteger ap = p.coef.get(v);                   // > 0
            for (Row n : neg) {
                BigInteger bn = n.coef.get(v).negate();      // > 0
                Row r2 = p.combine(bn, n, ap);               // bn*p + ap*n, cancels v
                r2.op = (p.op == ItsLinearConstraint.Op.GT || n.op == ItsLinearConstraint.Op.GT)
                        ? ItsLinearConstraint.Op.GT : ItsLinearConstraint.Op.GE;
                r2.normalize();
                r2.classifyTrivial();
                if (!r2.dropped) out.add(r2);
            }
        }
        return out;                                          // unpaired one-sided bounds: drop
    }

    // ----- working row representation ----------------------------------------

    private static final class Row {
        final Map<String, BigInteger> coef = new LinkedHashMap<String, BigInteger>();
        BigInteger cst = BigInteger.ZERO;
        ItsLinearConstraint.Op op;
        boolean dropped = false;

        static Row of(ItsLinearConstraint c) {
            Row r = new Row();
            ItsLinearExpression e = c.lhs();
            for (Map.Entry<String, Long> t : e.coefficients().entrySet())
                r.coef.put(t.getKey(), BigInteger.valueOf(t.getValue()));
            r.cst = BigInteger.valueOf(e.constant());
            r.op = c.op();
            return r;
        }

        /** The equality {@code primed - update = 0}. */
        static Row fromUpdate(String primed, ItsLinearExpression update) {
            Row r = new Row();
            r.op = ItsLinearConstraint.Op.EQ;
            r.coef.put(primed, BigInteger.ONE);
            for (Map.Entry<String, Long> t : update.coefficients().entrySet())
                r.add(t.getKey(), BigInteger.valueOf(-t.getValue()));
            r.cst = BigInteger.valueOf(-update.constant());
            return r;
        }

        void add(String v, BigInteger c) {
            if (c.signum() == 0) return;
            BigInteger n = coef.getOrDefault(v, BigInteger.ZERO).add(c);
            if (n.signum() == 0) coef.remove(v); else coef.put(v, n);
        }

        Row scale(BigInteger m) {
            Row r = new Row();
            r.op = op;
            for (Map.Entry<String, BigInteger> e : coef.entrySet())
                r.coef.put(e.getKey(), e.getValue().multiply(m));
            r.cst = cst.multiply(m);
            return r;
        }

        Row combine(BigInteger m1, Row other, BigInteger m2) {
            Row r = new Row();
            for (Map.Entry<String, BigInteger> e : coef.entrySet())
                r.add(e.getKey(), e.getValue().multiply(m1));
            for (Map.Entry<String, BigInteger> e : other.coef.entrySet())
                r.add(e.getKey(), e.getValue().multiply(m2));
            r.cst = cst.multiply(m1).add(other.cst.multiply(m2));
            return r;
        }

        void normalize() {
            BigInteger g = cst.abs();
            for (BigInteger c : coef.values()) g = g.gcd(c.abs());
            if (g.signum() != 0 && !g.equals(BigInteger.ONE)) {
                for (Map.Entry<String, BigInteger> e : coef.entrySet())
                    e.setValue(e.getValue().divide(g));
                cst = cst.divide(g);
            }
        }

        void classifyTrivial() {
            if (!coef.isEmpty()) return;
            int s = cst.signum();
            switch (op) {
                case EQ: if (s != 0) throw new Infeasible(); break;
                case GE: if (s < 0) throw new Infeasible(); break;
                case GT: if (s <= 0) throw new Infeasible(); break;
            }
            dropped = true;
        }

        ItsLinearConstraint toConstraint(Map<String, String> rename) {
            if (coef.isEmpty()) return null;             // trivially-true survivor
            ItsLinearExpression.Builder b = new ItsLinearExpression.Builder();
            for (Map.Entry<String, BigInteger> e : coef.entrySet())
                b.addTerm(rename.getOrDefault(e.getKey(), e.getKey()), toLong(e.getValue()));
            b.addConstant(toLong(cst));
            return new ItsLinearConstraint(b.build(), op);
        }

        private static long toLong(BigInteger b) {
            if (b.bitLength() > 62) throw new Fallback("coefficient overflow");
            return b.longValueExact();
        }
    }
}
