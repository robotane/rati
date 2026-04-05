package fr.univreunion.rati.ranking;

import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import apron.Abstract1;
import apron.ApronException;
import apron.Environment;
import apron.Lincons1;
import apron.Linexpr1;
import apron.Manager;

import fr.univreunion.rati.its.IntegerTransitionSystem;
import fr.univreunion.rati.its.ItsLinearConstraint;
import fr.univreunion.rati.its.ItsLinearExpression;
import fr.univreunion.rati.its.ItsLocation;
import fr.univreunion.rati.its.ItsTransition;
import fr.univreunion.rati.rank.KoatParser;

/**
 * §9-step-4 make-or-break experiment for the "pure Julia" path-length redesign
 * Computes the <em>binary-unfolding closure</em> of a
 * path-length ITS — the principled, widened version of {@code StackProjection.chain()}
 * (Codish &amp; Taboch 1999, Def 5.4; abstract domain = convex polyhedra, LUB =
 * convex hull, widening for the fixpoint) — and reports whether it CONVERGES
 * cheaply and stays BOUNDED on a grinder SCC (the gating risk, handoff §11),
 * vs. the parallel-edge blow-up that left {@code chain()} still capping.
 *
 * <p>This is a diagnostic probe, not production code. It does NOT touch the
 * verdict pipeline. Run:
 * <pre>
 *   java -Djava.library.path=lib -cp rati.jar \
 *        fr.univreunion.rati.probe.BinUnfoldProbe &lt;file.koat&gt; [--entry F]
 * </pre>
 *
 * <h2>What it computes</h2>
 * For each non-trivial SCC of the reachable ITS it picks a feedback vertex set
 * (FVS = loop headers; every cycle passes through one). For each header {@code h}
 * it runs a forward <em>relational</em> abstract interpretation over the SCC:
 * each location carries a polyhedron over {@code I@*} (h's call-time args, frozen)
 * and {@code C@*} (the current point's args), joined with convex hull and widened.
 * The relation flowing back into {@code h} is the loop summary
 * {@code R_hh ⊆ (I, C)} — the compact {@code p→p} binary recursive clause the
 * paper's tier-1/2 local affine ranking would consume.
 *
 * <p>It then applies a cheap, SOUND 1-D rankability witness: {@code h} is
 * "rankable here" if some single variable {@code v} satisfies
 * {@code R_hh ⊨ C@v ≤ I@v − 1} (strict decrease) and {@code R_hh ⊨ I@v ≥ 0}
 * (bounded below). This is sufficient (a real implementation does a full affine
 * LP), so the reported rankable count is a LOWER bound on what tier-1/2 proves.
 */
public final class BinUnfoldProbe {

    /** This thread's polyhedra manager (per-thread for race-free in-process use). */
    private static Manager man() { return ApronManagers.polka(); }
    private static final int WIDEN_DELAY = 3;
    private static final long PER_HEADER_MS = 20_000;

    private BinUnfoldProbe() {}

    private static String onlyFilter = null;
    private static boolean dump = false;

    public static void main(String[] args) throws Exception {
        String file = null, entry = null;
        for (int i = 0; i < args.length; i++) {
            if (args[i].equals("--entry") && i + 1 < args.length) entry = args[++i];
            else if (args[i].equals("--only") && i + 1 < args.length) onlyFilter = args[++i];
            else if (args[i].equals("--dump")) dump = true;
            else if (file == null) file = args[i];
        }
        if (file == null) { System.err.println("usage: BinUnfoldProbe <file.koat> [--entry F] [--only SUB] [--dump]"); System.exit(2); }

        String text = new String(Files.readAllBytes(Paths.get(file)), StandardCharsets.UTF_8);
        KoatParser.Parsed parsed = KoatParser.parse(text);
        IntegerTransitionSystem its = parsed.its;
        String start = entry != null ? entry : parsed.start;

        System.out.println("=== BinUnfoldProbe: " + Paths.get(file).getFileName() + " ===");
        System.out.println("locations=" + its.locations().size()
                + " transitions=" + its.transitions().size() + " entry=" + start);

        Set<String> reachable = reachableFrom(its, start);
        System.out.println("reachable=" + reachable.size());

        // Adjacency over reachable, supported transitions only.
        Map<String, List<ItsTransition>> bySource = new HashMap<String, List<ItsTransition>>();
        for (ItsTransition t : its.transitions()) {
            if (!t.isSupported()) continue;
            String s = t.source().name(), d = t.target().name();
            if (!reachable.contains(s) || !reachable.contains(d)) continue;
            bySource.computeIfAbsent(s, k -> new ArrayList<ItsTransition>()).add(t);
        }

        List<Set<String>> sccs = sccs(reachable, bySource);
        List<Set<String>> nonTrivial = new ArrayList<Set<String>>();
        for (Set<String> c : sccs) if (isCyclic(c, bySource)) nonTrivial.add(c);
        nonTrivial.sort((a, b) -> Integer.compare(b.size(), a.size()));
        System.out.println("nonTrivialSCCs=" + nonTrivial.size()
                + " sizes=" + sizes(nonTrivial));

        long t0 = System.nanoTime();
        int totalHeaders = 0, totalRankable = 0, totalClauses = 0;
        long maxConstr = 0;
        for (int ci = 0; ci < nonTrivial.size(); ci++) {
            Set<String> scc = nonTrivial.get(ci);
            int edgeCount = 0;
            for (String s : scc)
                for (ItsTransition t : bySource.getOrDefault(s, Collections.emptyList()))
                    if (scc.contains(t.target().name())) edgeCount++;
            List<String> fvs = feedbackVertexSet(scc, bySource);
            System.out.println("\nSCC#" + ci + ": locations=" + scc.size()
                    + " transitions=" + edgeCount + " FVS=" + fvs.size() + " " + fvs);

            for (String h : fvs) {
                if (onlyFilter != null && !h.contains(onlyFilter)) continue;
                totalHeaders++;
                HeaderResult r = closeHeader(its, scc, bySource, h);
                totalClauses += r.converged ? 1 : 0;
                maxConstr = Math.max(maxConstr, r.numConstraints);
                if (r.rankable) totalRankable++;
                System.out.printf("  %-58s iters=%-4d ms=%-6d constraints=%-4d %s%s%n",
                        truncate(h, 58), r.iterations, r.millis, r.numConstraints,
                        r.converged ? "" : "[BUDGET] ",
                        r.rankable ? "RANKABLE(" + r.rankVar + ")" : "unranked");
            }
        }
        long ms = (System.nanoTime() - t0) / 1_000_000;
        System.out.println("\n=== SUMMARY ===");
        System.out.println("headers(loops)=" + totalHeaders
                + " converged=" + totalClauses
                + " rankable(1-D witness)=" + totalRankable
                + " maxConstraints=" + maxConstr
                + " closureWallMs=" + ms);
    }

    // ------------------------------------------------------------------ closure

    private static final class HeaderResult {
        int iterations; long millis; long numConstraints;
        boolean converged; boolean rankable; String rankVar = "";
    }

    /** The widened binary-unfolding loop relation R_hh plus the closure metrics. */
    private static final class Closure {
        final Abstract1 loopRel; final int iterations; final boolean converged; final long millis;
        Closure(Abstract1 loopRel, int iterations, boolean converged, long millis) {
            this.loopRel = loopRel; this.iterations = iterations;
            this.converged = converged; this.millis = millis;
        }
    }

    /**
     * The polyhedral binary-unfolding loop relation R_hh for header {@code h}, as
     * ITS constraints over {@code I@v} (h's call-time arguments) and {@code C@v}
     * (h's arguments on its next visit). Returns {@code null} when the relation is
     * ⊥ (h has no actual loop iteration — vacuously fine for termination). This is
     * the compact {@code p→p} binary recursive clause Algorithm 1's tier-1 local
     * affine ranking consumes (Spoto-Mesnard-Payet TOPLAS 2010, §7, lines 1-2).
     */
    static List<ItsLinearConstraint> loopRelation(IntegerTransitionSystem its, Set<String> scc,
            Map<String, List<ItsTransition>> bySource, String h) throws ApronException {
        return loopRelation(its, scc, bySource, h, PER_HEADER_MS);
    }

    /**
     * As {@link #loopRelation(IntegerTransitionSystem, Set, Map, String)} but with an
     * explicit wall-clock cap {@code perHeaderMs} on the closure — the bounded-proof
     * lever (handoff §8b.A): a caller that wants a <em>fast</em> tier-1 caps the cost of
     * the widened polyhedral closure and treats a partial relation as "tier-1
     * inconclusive". Sound: a budget-truncated R_hh is a (weaker) over-approximation, so
     * a ranking found over it is still valid and a failure just falls through.
     */
    static List<ItsLinearConstraint> loopRelation(IntegerTransitionSystem its, Set<String> scc,
            Map<String, List<ItsTransition>> bySource, String h, long perHeaderMs) throws ApronException {
        Abstract1 loopRel = closeHeaderRel(its, scc, bySource, h, perHeaderMs).loopRel;
        try {
            if (loopRel.isBottom(man())) return null;
            return ApronBridge.toConstraints(man(), loopRel);
        } finally {
            loopRel.dispose();   // read back into constraints — the native relation is now dead
        }
    }

    /** Runs the widened forward relational closure from {@code h} and returns R_hh. */
    private static Closure closeHeaderRel(IntegerTransitionSystem its, Set<String> scc,
            Map<String, List<ItsTransition>> bySource, String h) throws ApronException {
        return closeHeaderRel(its, scc, bySource, h, PER_HEADER_MS);
    }

    /** As {@link #closeHeaderRel(IntegerTransitionSystem, Set, Map, String)} with a closure time cap. */
    private static Closure closeHeaderRel(IntegerTransitionSystem its, Set<String> scc,
            Map<String, List<ItsTransition>> bySource, String h, long perHeaderMs) throws ApronException {
        long start = System.currentTimeMillis();
        List<String> hf = its.location(h).variables();
        String[] iSide = pref("I@", hf);

        // Rel[loc] : polyhedron over (I@hf ∪ C@locFormals). ⊥ initially, identity at h.
        Map<String, Abstract1> rel = new HashMap<String, Abstract1>();
        for (String loc : scc) rel.put(loc, new Abstract1(man(), envIC(iSide, its.location(loc)), true));
        rel.put(h, identity(iSide, hf));

        Map<String, Integer> visits = new HashMap<String, Integer>();
        Deque<String> work = new ArrayDeque<String>();
        Set<String> inWork = new HashSet<String>();
        work.add(h); inWork.add(h);
        int budget = 400 * Math.max(1, scc.size());
        int iters = 0;
        while (!work.isEmpty() && budget-- > 0) {
            if (System.currentTimeMillis() - start > perHeaderMs) break;
            iters++;
            String loc = work.poll(); inWork.remove(loc);
            Abstract1 src = rel.get(loc);
            if (src.isBottom(man())) continue;
            for (ItsTransition t : bySource.getOrDefault(loc, Collections.emptyList())) {
                String tgt = t.target().name();
                if (!scc.contains(tgt)) continue;
                Abstract1 post = relPost(src, t, iSide);
                Abstract1 old = rel.get(tgt);
                Abstract1 joined = old.joinCopy(man(), post);
                post.dispose();   // consumed by the join — dead, never aliased
                int v = visits.getOrDefault(tgt, 0) + 1; visits.put(tgt, v);
                if (v > WIDEN_DELAY) joined = ApronBridge.supersede(joined, old.widening(man(), joined));
                if (!joined.isIncluded(man(), old)) {
                    rel.put(tgt, joined);
                    if (inWork.add(tgt)) work.add(tgt);
                } else {
                    joined.dispose();   // not propagated — dead
                }
            }
        }
        boolean converged = work.isEmpty() && (System.currentTimeMillis() - start <= perHeaderMs);

        // R_hh = ⊔ over in-edges (src -> h) of relPost(Rel[src], edge). The ≥1-step
        // loop relation: h's call-time args (I@) related to h's next-visit args (C@).
        Abstract1 loopRel = new Abstract1(man(), envIC(iSide, its.location(h)), true);
        for (String s : scc)
            for (ItsTransition t : bySource.getOrDefault(s, Collections.emptyList()))
                if (t.target().name().equals(h) && !rel.get(s).isBottom(man())) {
                    Abstract1 pi = relPost(rel.get(s), t, iSide);   // fresh copy (relPost returns a copy)
                    loopRel = ApronBridge.supersede(loopRel, loopRel.joinCopy(man(), pi));
                    pi.dispose();
                }
        // The fixpoint relations are now folded into loopRel (through copies); free them here on
        // the proof thread rather than leaving the whole map to the Cleaner. loopRel escapes in
        // the Closure and is disposed by the caller after read-back; it is never a map value.
        for (Abstract1 v : rel.values()) if (v != null) v.dispose();
        return new Closure(loopRel, iters, converged, System.currentTimeMillis() - start);
    }

    /** Forward relational closure from header {@code h} over {@code scc}; returns R_hh metrics. */
    private static HeaderResult closeHeader(IntegerTransitionSystem its, Set<String> scc,
            Map<String, List<ItsTransition>> bySource, String h) throws ApronException {
        HeaderResult res = new HeaderResult();
        List<String> hf = its.location(h).variables();
        Closure cl = closeHeaderRel(its, scc, bySource, h);
        Abstract1 loopRel = cl.loopRel;
        res.iterations = cl.iterations;
        res.converged = cl.converged;

        res.numConstraints = loopRel.isBottom(man()) ? 0 : ApronBridge.toConstraints(man(), loopRel).size();
        res.millis = cl.millis;

        if (dump && !loopRel.isBottom(man())) {
            System.out.println("  --- R_hh for " + h + " ---");
            int shown = 0, decreasing = 0;
            for (ItsLinearConstraint c : ApronBridge.toConstraints(man(), loopRel)) {
                // count how many constraints witness a per-variable strict decrease C@v < I@v
                String s = c.toString();
                if (shown++ < 50) System.out.println("    " + s);
            }
            for (String v : hf) {
                Map<String, BigInteger> dec = new LinkedHashMap<String, BigInteger>();
                dec.put("I@" + v, BigInteger.ONE); dec.put("C@" + v, BigInteger.valueOf(-1));
                Map<String, BigInteger> eq = new LinkedHashMap<String, BigInteger>();
                eq.put("I@" + v, BigInteger.ONE); eq.put("C@" + v, BigInteger.valueOf(-1));
                boolean strictDown = entails(loopRel, dec, BigInteger.valueOf(-1));
                // frame copy: both I@v−C@v≥0 and C@v−I@v≥0 entailed
                Map<String, BigInteger> up = new LinkedHashMap<String, BigInteger>();
                up.put("C@" + v, BigInteger.ONE); up.put("I@" + v, BigInteger.valueOf(-1));
                boolean copy = entails(loopRel, eq, BigInteger.ZERO) && entails(loopRel, up, BigInteger.ZERO);
                if (strictDown) { System.out.println("    [STRICT↓] " + v); decreasing++; }
                else if (!copy) System.out.println("    [varies]  " + v);
            }
            System.out.println("    (variables with no line above are frame-copies C@v = I@v; strict↓ count=" + decreasing + ")");
        }

        // Cheap 1-D rankability witness over R_hh.
        if (!loopRel.isBottom(man())) {
            for (String v : hf) {
                Map<String, BigInteger> dec = new LinkedHashMap<String, BigInteger>();
                dec.put("I@" + v, BigInteger.ONE); dec.put("C@" + v, BigInteger.valueOf(-1));
                Map<String, BigInteger> pos = new LinkedHashMap<String, BigInteger>();
                pos.put("I@" + v, BigInteger.ONE);
                if (entails(loopRel, dec, BigInteger.valueOf(-1))   // I@v − C@v − 1 ≥ 0
                 && entails(loopRel, pos, BigInteger.ZERO)) {       // I@v ≥ 0
                    res.rankable = true; res.rankVar = v; break;
                }
            }
        }
        loopRel.dispose();   // read into HeaderResult (counts only) — native relation now dead
        return res;
    }

    /** Relational post-image of {@code rel} (over I@* ∪ C@srcFormals) through {@code t}. */
    private static Abstract1 relPost(Abstract1 rel, ItsTransition t, String[] iSide) throws ApronException {
        List<String> sv = t.source().variables();
        List<String> tv = t.target().variables();

        // 1. Rename rel's C@srcFormals back to the raw guard names (LI0, SI0, …).
        String[] cFrom = pref("C@", sv);
        // a may alias the caller's rel (when sv is empty); guard the first dispose so we free
        // only a copy we made, never the input. Every step after is a fresh copy (supersede).
        Abstract1 a = sv.isEmpty() ? rel : rel.renameCopy(man(), cFrom.clone(), sv.toArray(new String[0]));

        // 2. Full env: I@* ∪ raw src formals ∪ guard/update vars ∪ fresh res.
        Set<String> names = new LinkedHashSet<String>();
        Collections.addAll(names, iSide);
        names.addAll(sv);
        for (ItsLinearConstraint c : t.constraints()) names.addAll(c.lhs().variables());
        for (ItsLinearExpression e : t.updates()) names.addAll(e.variables());
        String[] resv = new String[tv.size()];
        for (int j = 0; j < resv.length; j++) { resv[j] = "__r" + j; names.add(resv[j]); }
        Environment full = new Environment(new String[0], names.toArray(new String[0]));
        Abstract1 aFull = a.changeEnvironmentCopy(man(), full, false);
        ApronBridge.disposeUnless(a, rel);   // free the rename copy if we made one; never rel
        a = aFull;

        // 3. Meet guard, bind res_j = update_j.
        List<Lincons1> cons = new ArrayList<Lincons1>();
        for (ItsLinearConstraint c : t.constraints()) cons.add(ApronBridge.toLincons(full, c));
        for (int j = 0; j < resv.length; j++) cons.add(ApronBridge.bindEq(full, resv[j], t.updates().get(j)));
        if (!cons.isEmpty()) a = ApronBridge.supersede(a, a.meetCopy(man(), cons.toArray(new Lincons1[0])));

        // 4. Project to I@* ∪ res*, rename res_j → C@tgtFormals_j.
        Set<String> keep = new LinkedHashSet<String>();
        Collections.addAll(keep, iSide);
        Collections.addAll(keep, resv);
        a = ApronBridge.supersede(a, a.changeEnvironmentCopy(man(), new Environment(new String[0], keep.toArray(new String[0])), true));
        if (resv.length > 0) a = ApronBridge.supersede(a, a.renameCopy(man(), resv.clone(), pref("C@", tv)));
        return ApronBridge.supersede(a, a.changeEnvironmentCopy(man(), envIC(iSide, t.target()), false));
    }

    // --------------------------------------------------------------- Apron util

    private static Environment envIC(String[] iSide, ItsLocation loc) {
        Set<String> n = new LinkedHashSet<String>();
        Collections.addAll(n, iSide);
        Collections.addAll(n, pref("C@", loc.variables()));
        return new Environment(new String[0], n.toArray(new String[0]));
    }

    private static Abstract1 identity(String[] iSide, List<String> hf) throws ApronException {
        Set<String> n = new LinkedHashSet<String>();
        Collections.addAll(n, iSide);
        Collections.addAll(n, pref("C@", hf));
        Environment env = new Environment(new String[0], n.toArray(new String[0]));
        Abstract1 a = new Abstract1(man(), env);
        List<Lincons1> cons = new ArrayList<Lincons1>();
        for (String v : hf) {
            Map<String, BigInteger> terms = new LinkedHashMap<String, BigInteger>();
            terms.put("I@" + v, BigInteger.ONE);
            terms.put("C@" + v, BigInteger.valueOf(-1));
            cons.add(new Lincons1(Lincons1.EQ, ApronBridge.linexpr(env, terms, BigInteger.ZERO)));
        }
        if (cons.isEmpty()) return a;
        Abstract1 met = a.meetCopy(man(), cons.toArray(new Lincons1[0]));
        a.dispose();   // the ⊤ seed is superseded by the meet — dead
        return met;
    }

    /**
     * True if {@code a ⊨ (Σterms + c ≥ 0)}, via {@code a ∧ (Σterms + c ≤ −1)} empty.
     * Exact over ℤ: the non-strict negation {@code −(Σterms) − c − 1 ≥ 0} avoids the
     * loose Polka domain silently relaxing a strict inequality.
     */
    private static boolean entails(Abstract1 a, Map<String, BigInteger> terms, BigInteger c) throws ApronException {
        Map<String, BigInteger> neg = new LinkedHashMap<String, BigInteger>();
        for (Map.Entry<String, BigInteger> e : terms.entrySet()) neg.put(e.getKey(), e.getValue().negate());
        Linexpr1 le = ApronBridge.linexpr(a.getEnvironment(), neg, c.negate().subtract(BigInteger.ONE));
        Abstract1 m = a.meetCopy(man(), new Lincons1(Lincons1.SUPEQ, le));   // a is the caller's — not disposed
        boolean bot = m.isBottom(man());
        m.dispose();
        return bot;
    }

    private static String[] pref(String p, List<String> vs) {
        String[] a = new String[vs.size()];
        for (int i = 0; i < a.length; i++) a[i] = p + vs.get(i);
        return a;
    }

    // --------------------------------------------------------------- graph util

    static Set<String> reachableFrom(IntegerTransitionSystem its, String entry) {
        Map<String, List<String>> adj = new HashMap<String, List<String>>();
        for (ItsTransition t : its.transitions())
            adj.computeIfAbsent(t.source().name(), k -> new ArrayList<String>()).add(t.target().name());
        Set<String> seen = new HashSet<String>();
        Deque<String> dq = new ArrayDeque<String>();
        if (entry != null) { dq.add(entry); seen.add(entry); }
        while (!dq.isEmpty()) {
            for (String n : adj.getOrDefault(dq.poll(), Collections.emptyList()))
                if (seen.add(n)) dq.add(n);
        }
        return seen;
    }

    static boolean isCyclic(Set<String> scc, Map<String, List<ItsTransition>> bySource) {
        if (scc.size() > 1) return true;
        String only = scc.iterator().next();
        for (ItsTransition t : bySource.getOrDefault(only, Collections.emptyList()))
            if (t.target().name().equals(only)) return true;
        return false;
    }

    /** Tarjan SCCs over the reachable sub-graph. */
    static List<Set<String>> sccs(Set<String> nodes, Map<String, List<ItsTransition>> bySource) {
        Map<String, Integer> index = new HashMap<String, Integer>();
        Map<String, Integer> low = new HashMap<String, Integer>();
        Set<String> onStack = new HashSet<String>();
        Deque<String> stack = new ArrayDeque<String>();
        List<Set<String>> out = new ArrayList<Set<String>>();
        int[] counter = {0};
        for (String n : nodes)
            if (!index.containsKey(n))
                strongConnect(n, nodes, bySource, index, low, onStack, stack, out, counter);
        return out;
    }

    private static void strongConnect(String v, Set<String> nodes,
            Map<String, List<ItsTransition>> bySource, Map<String, Integer> index,
            Map<String, Integer> low, Set<String> onStack, Deque<String> stack,
            List<Set<String>> out, int[] counter) {
        // Iterative Tarjan (the grinder SCCs are deep — recursion would overflow).
        Deque<String> dfs = new ArrayDeque<String>();
        Deque<Integer> it = new ArrayDeque<Integer>();
        dfs.push(v); it.push(0);
        Map<String, List<String>> succ = new HashMap<String, List<String>>();
        while (!dfs.isEmpty()) {
            String u = dfs.peek();
            if (!index.containsKey(u)) {
                index.put(u, counter[0]); low.put(u, counter[0]); counter[0]++;
                stack.push(u); onStack.add(u);
                List<String> ss = new ArrayList<String>();
                for (ItsTransition t : bySource.getOrDefault(u, Collections.emptyList()))
                    if (nodes.contains(t.target().name())) ss.add(t.target().name());
                succ.put(u, ss);
            }
            List<String> ss = succ.get(u);
            int i = it.pop();
            if (i < ss.size()) {
                it.push(i + 1);
                String w = ss.get(i);
                if (!index.containsKey(w)) { dfs.push(w); it.push(0); }
                else if (onStack.contains(w)) low.put(u, Math.min(low.get(u), index.get(w)));
            } else {
                if (low.get(u).equals(index.get(u))) {
                    Set<String> comp = new LinkedHashSet<String>();
                    String w;
                    do { w = stack.pop(); onStack.remove(w); comp.add(w); } while (!w.equals(u));
                    out.add(comp);
                }
                dfs.pop();
                if (!dfs.isEmpty()) { String p = dfs.peek(); low.put(p, Math.min(low.get(p), low.get(u))); }
            }
        }
    }

    /**
     * Greedy feedback vertex set: repeatedly remove the node with the largest
     * {@code indeg·outdeg} inside the still-cyclic residual, until acyclic. The
     * removed nodes form a set hitting every cycle (loop headers).
     */
    static List<String> feedbackVertexSet(Set<String> scc, Map<String, List<ItsTransition>> bySource) {
        Set<String> live = new LinkedHashSet<String>(scc);
        List<String> fvs = new ArrayList<String>();
        while (true) {
            // residual SCCs over live
            Map<String, List<ItsTransition>> resAdj = new HashMap<String, List<ItsTransition>>();
            for (String s : live) {
                List<ItsTransition> keep = new ArrayList<ItsTransition>();
                for (ItsTransition t : bySource.getOrDefault(s, Collections.emptyList()))
                    if (live.contains(t.target().name())) keep.add(t);
                resAdj.put(s, keep);
            }
            List<Set<String>> rs = sccs(live, resAdj);
            Set<String> cyclic = null;
            for (Set<String> c : rs) if (isCyclic(c, resAdj)) { cyclic = c; break; }
            if (cyclic == null) break;
            // pick max indeg*outdeg within this cyclic component
            Map<String, Integer> indeg = new HashMap<String, Integer>();
            Map<String, Integer> outdeg = new HashMap<String, Integer>();
            for (String s : cyclic) {
                int o = 0;
                for (ItsTransition t : resAdj.getOrDefault(s, Collections.emptyList()))
                    if (cyclic.contains(t.target().name())) { o++; indeg.merge(t.target().name(), 1, Integer::sum); }
                outdeg.put(s, o);
            }
            String best = null; long bestScore = -1;
            for (String s : cyclic) {
                long score = (long) outdeg.getOrDefault(s, 0) * indeg.getOrDefault(s, 0);
                if (score > bestScore) { bestScore = score; best = s; }
            }
            if (best == null) best = cyclic.iterator().next();
            fvs.add(best); live.remove(best);
        }
        return fvs;
    }

    private static String sizes(List<Set<String>> cs) {
        StringBuilder sb = new StringBuilder("[");
        for (int i = 0; i < cs.size() && i < 8; i++) { if (i > 0) sb.append(','); sb.append(cs.get(i).size()); }
        if (cs.size() > 8) sb.append(",…");
        return sb.append("]").toString();
    }

    private static String truncate(String s, int n) { return s.length() <= n ? s : s.substring(0, n - 1) + "…"; }
}
