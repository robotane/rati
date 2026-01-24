package fr.univreunion.rati.ranking;

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

import fr.univreunion.rati.its.IntegerTransitionSystem;
import fr.univreunion.rati.its.ItsLinearConstraint;
import fr.univreunion.rati.its.ItsLinearExpression;
import fr.univreunion.rati.its.ItsTransition;
import fr.univreunion.rati.rank.KoatParser;

/**
 * §9-step-5/6 prototype for the "pure Julia" path-length redesign. The cheap, PTIME, <em>no-Apron</em> fail-fast layer the
 * BinUnfoldProbe result pointed at: <strong>size-change termination</strong>
 * (Lee, Jones &amp; Ben-Amram, POPL 2001) over the path-length ITS.
 *
 * <p>Rationale:
 * the widened polyhedral binary-unfolding closure CONVERGES but is too slow
 * (~8s/header on a 72-dim rational Polka) and collapses to ~TOP on grinders, so
 * the polyhedral tier is NOT where the time budget lives. The fail-fast layer
 * must be a cheap abstraction that bails in milliseconds when nothing decreases
 * (Family-A) and ranks real loops without native LP. SCT is exactly that: arcs
 * are 3-valued ({@code none}/{@code ↓=}/{@code ↓}) difference facts, composition
 * is boolean-matrix multiplication, the decision is "every idempotent self-graph
 * has an in-situ strict thread".
 *
 * <h2>Soundness</h2>
 * An arc {@code x_i → y_j} is emitted ONLY when the transition relation provably
 * entails the (non-)strict decrease — extracted from genuine two-variable
 * difference constraints closed by Floyd-Warshall. Missing an arc can only make
 * us FAIL to prove termination (report not-SCT ⇒ caller stays UNKNOWN), never
 * wrongly prove it. So the extraction is conservative = sound.
 *
 * <p>Diagnostic probe; does NOT touch the verdict pipeline. Run:
 * <pre>
 *   java -cp rati.jar fr.univreunion.rati.ranking.SctProbe &lt;file.koat&gt; [--entry F] [--dump]
 * </pre>
 * (No {@code -Djava.library.path} needed — this layer never loads Apron.)
 */
public final class SctProbe {

    /** Arc strengths, ordered: none &lt; non-strict (↓=) &lt; strict (↓). */
    private static final byte NONE = 0, GTE = 1, GT = 2;

    private static final long INF = Long.MAX_VALUE / 4;
    private static final int MAX_CLOSURE = Integer.getInteger("sct.maxClosure", 200_000);
    private static final long CLOSURE_MS = Long.getLong("sct.closureMs", 30_000);

    private static boolean dump = false;

    private SctProbe() {}

    public static void main(String[] args) throws Exception {
        String file = null, entry = null;
        for (int i = 0; i < args.length; i++) {
            if (args[i].equals("--entry") && i + 1 < args.length) entry = args[++i];
            else if (args[i].equals("--dump")) dump = true;
            else if (file == null) file = args[i];
        }
        if (file == null) { System.err.println("usage: SctProbe <file.koat> [--entry F] [--dump]"); System.exit(2); }

        String text = new String(Files.readAllBytes(Paths.get(file)), StandardCharsets.UTF_8);
        KoatParser.Parsed parsed = KoatParser.parse(text);
        IntegerTransitionSystem its = parsed.its;
        String start = entry != null ? entry : parsed.start;

        System.out.println("=== SctProbe: " + Paths.get(file).getFileName() + " ===");
        System.out.println("locations=" + its.locations().size()
                + " transitions=" + its.transitions().size() + " entry=" + start);

        Set<String> reachable = reachableFrom(its, start);
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
        System.out.println("reachable=" + reachable.size()
                + " nonTrivialSCCs=" + nonTrivial.size() + " sizes=" + sizes(nonTrivial));

        long t0 = System.nanoTime();
        int sccTerm = 0, sccUnknown = 0, sccBudget = 0;
        for (int ci = 0; ci < nonTrivial.size(); ci++) {
            Set<String> scc = nonTrivial.get(ci);

            // Base size-change graphs: one per supported transition inside the SCC.
            List<Scg> base = new ArrayList<Scg>();
            int strictArcs = 0;
            for (String s : scc)
                for (ItsTransition t : bySource.getOrDefault(s, Collections.emptyList()))
                    if (scc.contains(t.target().name())) {
                        Scg g = build(t);
                        base.add(g);
                        strictArcs += g.countStrict();
                    }

            long cs = System.currentTimeMillis();
            ClosureResult cr = decide(base);
            long ms = System.currentTimeMillis() - cs;

            String verdict = cr.budgetHit ? "BUDGET" : (cr.terminating ? "SCT-TERMINATES" : "not-SCT");
            if (cr.budgetHit) sccBudget++;
            else if (cr.terminating) sccTerm++;
            else sccUnknown++;
            System.out.printf("  SCC#%-2d loc=%-4d baseSCGs=%-4d strictArcs=%-4d closure=%-6d ms=%-5d %s%n",
                    ci, scc.size(), base.size(), strictArcs, cr.closureSize, ms, verdict);
            if (dump && !cr.terminating && !cr.budgetHit && ci < 3)
                System.out.println("    witness idempotent w/o strict thread: " + cr.witness);
        }
        long total = (System.nanoTime() - t0) / 1_000_000;
        System.out.println("\n=== SUMMARY ===");
        System.out.println("SCCs: SCT-terminates=" + sccTerm
                + " not-SCT(UNKNOWN)=" + sccUnknown + " budget=" + sccBudget
                + " sctWallMs=" + total);
    }

    // ------------------------------------------------------------- SCG model

    /** A size-change graph for a call {@code src(x⃗) -> tgt(y⃗)}: arcs x_i ⇒ y_j. */
    private static final class Scg {
        final String src, tgt;
        final byte[][] m;            // m[i][j] ∈ {NONE,GTE,GT}, i over src formals, j over tgt formals
        final int ni, nj;
        private String key;          // lazily-cached canonical key
        Scg(String src, String tgt, byte[][] m) {
            this.src = src; this.tgt = tgt; this.m = m;
            this.ni = m.length; this.nj = ni == 0 ? 0 : m[0].length;
        }
        int countStrict() {
            int c = 0;
            for (byte[] row : m) for (byte v : row) if (v == GT) c++;
            return c;
        }
        String key() {
            if (key == null) {
                StringBuilder sb = new StringBuilder(src).append('|').append(tgt).append('|');
                for (byte[] row : m) for (byte v : row) sb.append((char) ('0' + v));
                key = sb.toString();
            }
            return key;
        }
    }

    /** Compose {@code a:p→q} with {@code b:q→r} into {@code p→r} (boolean-matrix, 3-valued). */
    private static Scg compose(Scg a, Scg b) {
        byte[][] r = new byte[a.ni][b.nj];
        for (int i = 0; i < a.ni; i++) {
            byte[] ai = a.m[i];
            for (int k = 0; k < a.nj; k++) {       // k over q's formals = b's source side
                byte aik = ai[k];
                if (aik == NONE) continue;
                byte[] bk = b.m[k];
                for (int j = 0; j < b.nj; j++) {
                    byte bkj = bk[j];
                    if (bkj == NONE) continue;
                    byte s = (aik == GT || bkj == GT) ? GT : GTE;
                    if (s > r[i][j]) r[i][j] = s;
                }
            }
        }
        return new Scg(a.src, b.tgt, r);
    }

    private static boolean sameMatrix(Scg a, Scg b) {
        if (a.ni != b.ni || a.nj != b.nj) return false;
        for (int i = 0; i < a.ni; i++)
            for (int j = 0; j < a.nj; j++)
                if (a.m[i][j] != b.m[i][j]) return false;
        return true;
    }

    // --------------------------------------------------------- SCT decision

    private static final class ClosureResult {
        boolean terminating; boolean budgetHit; int closureSize; String witness = "";
    }

    /**
     * Transitive closure of {@code base} under composition, then the SCT test:
     * SCT-terminating iff every idempotent self-graph {@code G:p→p} (G∘G = G) has
     * an in-situ strict thread {@code G[i][i] = ↓}.
     */
    private static ClosureResult decide(List<Scg> base) {
        ClosureResult res = new ClosureResult();
        Map<String, Scg> all = new LinkedHashMap<String, Scg>();
        Map<String, List<Scg>> bySrc = new HashMap<String, List<Scg>>();
        Map<String, List<Scg>> byTgt = new HashMap<String, List<Scg>>();
        Deque<Scg> work = new ArrayDeque<Scg>();
        for (Scg g : base) if (all.putIfAbsent(g.key(), g) == null) { index(g, bySrc, byTgt); work.add(g); }

        long start = System.currentTimeMillis();
        while (!work.isEmpty()) {
            if (all.size() > MAX_CLOSURE || System.currentTimeMillis() - start > CLOSURE_MS) {
                res.budgetHit = true; break;
            }
            Scg g = work.poll();
            // g:p→q composed after any h:x→p, and before any h:q→y. Snapshot the
            // adjacency lists first: add() appends to these very lists.
            List<Scg> pre = byTgt.get(g.src);
            List<Scg> post = bySrc.get(g.tgt);
            Scg[] preA = pre == null ? new Scg[0] : pre.toArray(new Scg[0]);
            Scg[] postA = post == null ? new Scg[0] : post.toArray(new Scg[0]);
            for (Scg h : preA) add(compose(h, g), all, bySrc, byTgt, work);
            for (Scg h : postA) add(compose(g, h), all, bySrc, byTgt, work);
        }
        res.closureSize = all.size();

        if (!res.budgetHit) {
            res.terminating = true;
            for (Scg g : all.values()) {
                if (!g.src.equals(g.tgt)) continue;
                if (!sameMatrix(g, compose(g, g))) continue;   // idempotent only
                boolean strictThread = false;
                int n = Math.min(g.ni, g.nj);
                for (int i = 0; i < n; i++) if (g.m[i][i] == GT) { strictThread = true; break; }
                if (!strictThread) { res.terminating = false; res.witness = g.src; break; }
            }
        }
        return res;
    }

    private static void add(Scg g, Map<String, Scg> all, Map<String, List<Scg>> bySrc,
            Map<String, List<Scg>> byTgt, Deque<Scg> work) {
        if (all.putIfAbsent(g.key(), g) == null) { index(g, bySrc, byTgt); work.add(g); }
    }

    private static void index(Scg g, Map<String, List<Scg>> bySrc, Map<String, List<Scg>> byTgt) {
        bySrc.computeIfAbsent(g.src, k -> new ArrayList<Scg>()).add(g);
        byTgt.computeIfAbsent(g.tgt, k -> new ArrayList<Scg>()).add(g);
    }

    // ----------------------------------------------------- arc extraction (DBM)

    /**
     * Builds the size-change graph of a transition by a cheap syntactic DBM:
     * collect genuine two-variable (and one-variable-vs-0) difference facts from
     * the guard, Floyd-Warshall close them, then read off arcs {@code x_i ⇒ y_j}
     * from the bound on {@code (binding of y_j) − x_i}. Conservative = sound.
     */
    private static Scg build(ItsTransition t) {
        List<String> sf = t.source().variables();
        List<String> tf = t.target().variables();
        List<ItsLinearExpression> upd = t.updates();

        // DBM node set: source formals ∪ guard vars ∪ update-expr vars ∪ ZERO.
        LinkedHashMap<String, Integer> idx = new LinkedHashMap<String, Integer>();
        idx.put("#0", 0);                              // the constant-0 node
        for (String v : sf) idx.putIfAbsent(v, idx.size());
        for (ItsLinearConstraint c : t.constraints()) for (String v : c.lhs().variables()) idx.putIfAbsent(v, idx.size());
        for (ItsLinearExpression e : upd) for (String v : e.variables()) idx.putIfAbsent(v, idx.size());
        int n = idx.size();
        long[][] d = new long[n][n];
        for (long[] row : d) java.util.Arrays.fill(row, INF);
        for (int i = 0; i < n; i++) d[i][i] = 0;

        // dbm[a][b] = upper bound on (a − b). Feed difference facts from the guard.
        for (ItsLinearConstraint c : t.constraints()) addConstraint(c, idx, d);
        // Floyd-Warshall min-plus closure.
        for (int k = 0; k < n; k++)
            for (int i = 0; i < n; i++) {
                if (d[i][k] >= INF) continue;
                for (int j = 0; j < n; j++)
                    if (d[k][j] < INF && d[i][k] + d[k][j] < d[i][j]) d[i][j] = d[i][k] + d[k][j];
            }

        byte[][] m = new byte[sf.size()][tf.size()];
        for (int j = 0; j < tf.size(); j++) {
            // y_j is bound to update expr e_j; usable only if e_j = w + const (single var).
            ItsLinearExpression e = upd.get(j);
            String w; long cst;
            if (e.variables().size() == 1) {
                w = e.variables().iterator().next();
                if (e.coefficient(w) != 1) continue;   // only unit-coefficient bindings
                cst = e.constant();
            } else if (e.variables().isEmpty()) {
                w = "#0"; cst = e.constant();           // y_j = const ⇒ compare const vs x_i via #0
            } else continue;                            // multi-var binding: no arc (sound)
            Integer wi = idx.get(w);
            if (wi == null) continue;
            for (int i = 0; i < sf.size(); i++) {
                Integer xi = idx.get(sf.get(i));
                if (xi == null) continue;
                long bound = d[wi][xi];                  // UB on (w − x_i); y_j − x_i ≤ bound + cst
                if (bound >= INF) continue;
                long yb = bound + cst;
                if (yb <= -1) m[i][j] = GT;
                else if (yb <= 0) m[i][j] = GTE;
            }
        }
        Scg g = new Scg(t.source().name(), t.target().name(), m);
        if (dump) System.out.println("    SCG " + g.src + "->" + g.tgt + " strict=" + g.countStrict()
                + " gte=" + (countArcs(m) - g.countStrict()));
        return g;
    }

    private static int countArcs(byte[][] m) {
        int c = 0; for (byte[] r : m) for (byte v : r) if (v != NONE) c++; return c;
    }

    /**
     * Adds the difference facts of {@code lhs OP 0} to the DBM. Only one- and
     * two-variable forms with unit coefficients yield a fact; anything else is
     * dropped (sound — fewer arcs). GT becomes "≥ 1" over ℤ.
     */
    private static void addConstraint(ItsLinearConstraint c, Map<String, Integer> idx, long[][] d) {
        Map<String, Long> terms = c.lhs().coefficients();
        long k0 = c.lhs().constant();
        switch (c.op()) {
            case EQ:                       // lhs = 0  ⇔  lhs ≥ 0 ∧ −lhs ≥ 0
                ge(terms, k0, idx, d);
                ge(negate(terms), -k0, idx, d);
                break;
            case GE: ge(terms, k0, idx, d); break;
            case GT: ge(terms, k0 - 1, idx, d); break;   // lhs > 0 ⇒ lhs − 1 ≥ 0 over ℤ
            default: break;
        }
    }

    /** Feeds {@code Σterms + k0 ≥ 0} into the DBM, for one/two-variable unit forms. */
    private static void ge(Map<String, Long> terms, long k0, Map<String, Integer> idx, long[][] d) {
        int z = idx.get("#0");
        if (terms.size() == 1) {
            Map.Entry<String, Long> e = terms.entrySet().iterator().next();
            long co = e.getValue(); Integer a = idx.get(e.getKey());
            if (a == null) return;
            if (co == 1) rel(z, a, k0, d);          // a ≥ −k0 ⇒ (#0 − a) ≤ k0
            else if (co == -1) rel(a, z, k0, d);    // a ≤ k0  ⇒ (a − #0) ≤ k0
        } else if (terms.size() == 2) {
            java.util.Iterator<Map.Entry<String, Long>> it = terms.entrySet().iterator();
            Map.Entry<String, Long> e1 = it.next(), e2 = it.next();
            long c1 = e1.getValue(), c2 = e2.getValue();
            Integer a = idx.get(e1.getKey()), b = idx.get(e2.getKey());
            if (a == null || b == null) return;
            if (c1 == 1 && c2 == -1) rel(b, a, k0, d);   // a − b + k0 ≥ 0 ⇒ (b − a) ≤ k0
            else if (c1 == -1 && c2 == 1) rel(a, b, k0, d);
        }
    }

    private static Map<String, Long> negate(Map<String, Long> t) {
        Map<String, Long> r = new LinkedHashMap<String, Long>();
        for (Map.Entry<String, Long> e : t.entrySet()) r.put(e.getKey(), -e.getValue());
        return r;
    }

    /** Tightens dbm[a][b] (upper bound on a − b) to {@code min(old, bound)}. */
    private static void rel(int a, int b, long bound, long[][] d) {
        if (bound < d[a][b]) d[a][b] = bound;
    }

    // --------------------------------------------------------- graph utilities

    private static Set<String> reachableFrom(IntegerTransitionSystem its, String entry) {
        Map<String, List<String>> adj = new HashMap<String, List<String>>();
        for (ItsTransition t : its.transitions())
            adj.computeIfAbsent(t.source().name(), k -> new ArrayList<String>()).add(t.target().name());
        Set<String> seen = new HashSet<String>();
        Deque<String> dq = new ArrayDeque<String>();
        if (entry != null) { dq.add(entry); seen.add(entry); }
        while (!dq.isEmpty())
            for (String n : adj.getOrDefault(dq.poll(), Collections.emptyList()))
                if (seen.add(n)) dq.add(n);
        return seen;
    }

    private static boolean isCyclic(Set<String> scc, Map<String, List<ItsTransition>> bySource) {
        if (scc.size() > 1) return true;
        String only = scc.iterator().next();
        for (ItsTransition t : bySource.getOrDefault(only, Collections.emptyList()))
            if (t.target().name().equals(only)) return true;
        return false;
    }

    private static List<Set<String>> sccs(Set<String> nodes, Map<String, List<ItsTransition>> bySource) {
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

    private static String sizes(List<Set<String>> cs) {
        StringBuilder sb = new StringBuilder("[");
        for (int i = 0; i < cs.size() && i < 8; i++) { if (i > 0) sb.append(','); sb.append(cs.get(i).size()); }
        if (cs.size() > 8) sb.append(",…");
        return sb.append("]").toString();
    }
}
