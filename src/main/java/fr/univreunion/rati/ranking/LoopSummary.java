package fr.univreunion.rati.ranking;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import apron.Abstract1;
import apron.ApronException;
import apron.Environment;
import apron.Lincons1;
import apron.Manager;

import fr.univreunion.rati.its.ItsLinearConstraint;
import fr.univreunion.rati.its.ItsLinearExpression;
import fr.univreunion.rati.its.ItsLocation;
import fr.univreunion.rati.its.ItsTransition;

/**
 * Cut-point loop summarisation for an SCC: composes the SCC's transitions into
 * summary self-loops (and cut-point-to-cut-point edges) by eliminating the
 * intermediate locations, so a ranking function only has to be bounded where an
 * invariant actually holds.
 *
 * <p>This is the "control-flow / transition composition" layer iRankFinder relies
 * on. The bare {@link FarkasRanking} per-transition method fails on a multi-block
 * loop (a CFG diamond, or nested loops) because boundedness is required at every
 * block, including blocks where the loop counter is unconstrained. Summarising the
 * SCC to its cut-points — locations carrying a self-loop — keeps the whole loop
 * body's guard on a single transition, where the counter bound is present.
 *
 * <p>Soundness: by the cut-point theorem an SCC terminates iff its cut-point
 * summary graph does. Each composition is the exact relational composition of two
 * transition relations (existential projection of the shared mid-state), computed
 * over Apron convex polyhedra; a composition that is empty (a dead path) is
 * dropped. The summary is returned as ordinary {@link ItsTransition}s so the
 * existing lexicographic ranker consumes them unchanged.
 */
public final class LoopSummary {

    /** Bail-out: composition can blow up multiplicatively; above this, give up (sound: caller ranks the raw SCC). */
    private static final int MAX_EDGES = 600;

    private final Manager man = ApronManagers.POLKA;

    private LoopSummary() {}

    /**
     * Summarises {@code sccTrans} (the intra-SCC transitions) to its cut-points.
     * Returns the summary transitions, or {@code sccTrans} unchanged if composition
     * is not beneficial (single self-looping location) or blows past {@link #MAX_EDGES}.
     */
    public static List<ItsTransition> summarize(List<ItsTransition> sccTrans) {
        try {
            return new LoopSummary().run(sccTrans);
        } catch (ApronException e) {
            return sccTrans;   // sound fallback: rank the raw transitions
        }
    }

    // -------------------------------------------------------------------------

    /** A working edge: a transition relation over {@code __ri_*} (source) / {@code __ro_*} (target). */
    private static final class Edge {
        final ItsLocation src, tgt;
        final Abstract1 rel;
        Edge(ItsLocation src, ItsLocation tgt, Abstract1 rel) { this.src = src; this.tgt = tgt; this.rel = rel; }
        boolean selfLoop() { return src.name().equals(tgt.name()); }
    }

    private List<ItsTransition> run(List<ItsTransition> sccTrans) throws ApronException {
        List<Edge> edges = new ArrayList<Edge>();
        Set<String> nodes = new LinkedHashSet<String>();
        Map<String, ItsLocation> locByName = new java.util.HashMap<String, ItsLocation>();
        for (ItsTransition t : sccTrans) {
            edges.add(new Edge(t.source(), t.target(), relationOf(t)));
            nodes.add(t.source().name()); nodes.add(t.target().name());
            locByName.put(t.source().name(), t.source());
            locByName.put(t.target().name(), t.target());
        }
        if (nodes.size() <= 1) return sccTrans;   // already a single self-looping location

        // Eliminate every location that has no self-loop, re-routing its in/out edges.
        while (true) {
            String victim = pickEliminable(nodes, edges);
            if (victim == null) break;            // only self-looping cut-points remain
            List<Edge> in = new ArrayList<Edge>(), out = new ArrayList<Edge>(), rest = new ArrayList<Edge>();
            for (Edge e : edges) {
                boolean si = e.src.name().equals(victim), ti = e.tgt.name().equals(victim);
                if (ti && !si) in.add(e);
                else if (si && !ti) out.add(e);
                else if (!si) rest.add(e);        // untouched (victim has no self-loop ⇒ no si&&ti)
            }
            for (Edge u : in) for (Edge w : out) {
                Abstract1 composed = compose(u.rel, u.tgt.arity(), w.rel, w.tgt.arity());
                if (!composed.isBottom(man)) rest.add(new Edge(u.src, w.tgt, composed));
            }
            edges = rest;
            nodes.remove(victim);
            if (edges.size() > MAX_EDGES) return sccTrans;   // blow-up ⇒ sound bail
        }

        List<ItsTransition> out = new ArrayList<ItsTransition>();
        for (Edge e : edges) out.add(toTransition(e));
        return out;
    }

    /** A location with at least one non-self in/out edge but no self-loop is eliminable. */
    private static String pickEliminable(Set<String> nodes, List<Edge> edges) {
        for (String v : nodes) {
            boolean hasSelf = false;
            for (Edge e : edges)
                if (e.src.name().equals(v) && e.tgt.name().equals(v)) { hasSelf = true; break; }
            if (!hasSelf) return v;
        }
        return null;
    }

    // -------------------------------------------------------------------------
    // Apron relation algebra
    // -------------------------------------------------------------------------

    private static final String IN = "__ri", OUT = "__ro", MID = "__rm";

    /** Transition relation as a polyhedron over {@code __ri_i} (source) and {@code __ro_j} (target). */
    private Abstract1 relationOf(ItsTransition t) throws ApronException {
        List<String> src = t.source().variables();
        int q = t.target().arity();

        Set<String> names = new LinkedHashSet<String>(src);
        for (ItsLinearConstraint c : t.constraints()) names.addAll(c.lhs().variables());
        for (ItsLinearExpression e : t.updates()) names.addAll(e.variables());
        String[] ro = new String[q];
        for (int j = 0; j < q; j++) { ro[j] = OUT + j; names.add(ro[j]); }

        Environment env = new Environment(new String[0], names.toArray(new String[0]));
        List<Lincons1> cs = new ArrayList<Lincons1>();
        for (ItsLinearConstraint c : t.constraints()) cs.add(ApronBridge.toLincons(env, c));
        for (int j = 0; j < q; j++) cs.add(ApronBridge.bindEq(env, ro[j], t.updates().get(j)));
        Abstract1 a = new Abstract1(man, env).meetCopy(man, cs.toArray(new Lincons1[0]));

        // Keep only source formals + ro_j, then rename source formals to __ri_i.
        String[] keep = concat(src.toArray(new String[0]), ro);
        a = a.changeEnvironmentCopy(man, new Environment(new String[0], keep), true);
        String[] ri = new String[src.size()];
        for (int i = 0; i < ri.length; i++) ri[i] = IN + i;
        if (!src.isEmpty()) a = a.renameCopy(man, src.toArray(new String[0]), ri);
        return a;
    }

    /** Relational composition: {@code r1} (over ri/ro, target arity {@code r}) then {@code r2} (ri arity {@code r}). */
    private Abstract1 compose(Abstract1 r1, int r, Abstract1 r2, int q) throws ApronException {
        int p = arityOfPrefix(r1, IN);
        // r1.ro_k -> __rm_k ; r2.ri_k -> __rm_k
        Abstract1 a1 = renamePrefix(r1, OUT, MID, r);
        Abstract1 a2 = renamePrefix(r2, IN, MID, r);

        List<String> joint = new ArrayList<String>();
        for (int i = 0; i < p; i++) joint.add(IN + i);
        for (int k = 0; k < r; k++) joint.add(MID + k);
        for (int j = 0; j < q; j++) joint.add(OUT + j);
        Environment je = new Environment(new String[0], joint.toArray(new String[0]));
        Abstract1 met = a1.changeEnvironmentCopy(man, je, false)
                          .meetCopy(man, a2.changeEnvironmentCopy(man, je, false));

        List<String> keep = new ArrayList<String>();
        for (int i = 0; i < p; i++) keep.add(IN + i);
        for (int j = 0; j < q; j++) keep.add(OUT + j);
        return met.changeEnvironmentCopy(man, new Environment(new String[0], keep.toArray(new String[0])), true);
    }

    /** Converts a relation edge back to an {@link ItsTransition} for the lexicographic ranker. */
    private ItsTransition toTransition(Edge e) throws ApronException {
        List<String> src = e.src.variables();
        int q = e.tgt.arity();
        // __ri_i -> source formal name ; __ro_j -> z_j (fresh update vars).
        Abstract1 a = e.rel;
        String[] riFrom = new String[src.size()], riTo = src.toArray(new String[0]);
        for (int i = 0; i < src.size(); i++) riFrom[i] = IN + i;
        if (src.size() > 0) a = a.renameCopy(man, riFrom, riTo);
        String[] roFrom = new String[q], roTo = new String[q];
        for (int j = 0; j < q; j++) { roFrom[j] = OUT + j; roTo[j] = "z" + j; }
        if (q > 0) a = a.renameCopy(man, roFrom, roTo);

        // Exact read-back; a conjunct beyond the long model is dropped, which
        // ENLARGES the summary relation — sound here, because the summary is only
        // ever used to PROVE termination of a superset of the real relation.
        List<ItsLinearConstraint> cons = ApronBridge.toConstraints(man, a);
        List<ItsLinearExpression> updates = new ArrayList<ItsLinearExpression>();
        for (int j = 0; j < q; j++) updates.add(ItsLinearExpression.variable("z" + j));
        return new ItsTransition(e.src, e.tgt, cons, updates);
    }

    // -------------------------------------------------------------------------
    // Apron helpers
    // -------------------------------------------------------------------------

    private int arityOfPrefix(Abstract1 a, String prefix) throws ApronException {
        int n = 0;
        for (apron.Var v : a.getEnvironment().getVars()) if (v.toString().startsWith(prefix)) n++;
        return n;
    }

    private Abstract1 renamePrefix(Abstract1 a, String from, String to, int n) throws ApronException {
        if (n == 0) return a;
        String[] f = new String[n], t = new String[n];
        for (int k = 0; k < n; k++) { f[k] = from + k; t[k] = to + k; }
        return a.renameCopy(man, f, t);
    }

    private static String[] concat(String[] a, String[] b) {
        String[] r = new String[a.length + b.length];
        System.arraycopy(a, 0, r, 0, a.length);
        System.arraycopy(b, 0, r, a.length, b.length);
        return r;
    }
}
