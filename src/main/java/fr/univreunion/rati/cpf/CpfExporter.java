package fr.univreunion.rati.cpf;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fr.univreunion.rati.its.IntegerTransitionSystem;
import fr.univreunion.rati.its.ItsLinearConstraint;
import fr.univreunion.rati.its.ItsLinearExpression;
import fr.univreunion.rati.its.ItsLocation;
import fr.univreunion.rati.its.ItsTransition;
import fr.univreunion.rati.ranking.FarkasRanking;
import fr.univreunion.rati.ranking.FarkasRanking.Certificate;
import fr.univreunion.rati.ranking.FarkasRanking.RankRound;
import fr.univreunion.rati.ranking.FarkasRanking.SccProof;
import fr.univreunion.rati.ranking.FarkasRanking.Verdict;
import fr.univreunion.rati.ranking.ItsInvariants;

/**
 * Serialises a RaTI termination proof of an integer transition system as a CPF 3.x
 * <em>LTS termination certificate</em> that the Isabelle/HOL-verified certifier CeTA
 * re-checks. The exporter targets exactly the structure validated end-to-end against
 * the CeTA 3.8 binary (see {@code solvers/ceta/examples/two_block_loop_inv.proof.xml}):
 *
 * <pre>
 *   ltsTerminationProof
 *     newInvariants( per-location invariants ; impact cover graph )   ← from ItsInvariants
 *       switchToCooperationTermination( cut points = loop heads )
 *         sccDecomposition
 *           sccWithProof( sharp SCC )
 *             transitionRemoval( ρ, bound 0, remove peeled )*  → empty sccDecomposition
 * </pre>
 *
 * <p>The path-length ITS uses input variables {@code LI*,SI*} for a location's pre-state
 * and fresh output variables {@code LO*,SO*} (constrained by the guard) for its
 * post-state; in CPF these map to a single global variable per slot, unprimed for the
 * pre-state and {@code <post>} for the post-state.
 *
 * <p><b>Scope.</b> Returns {@code null} (not exportable) rather than emit an unsound or
 * malformed certificate when the proof rests on a technique whose CeTA encoding is not
 * implemented here — a loop-summary / multiphase / disjunctive SCC (no per-transition
 * ranking rounds), or a transition mentioning a variable outside the {@code LI/SI/LO/SO}
 * universe. A {@code null} only forgoes certification; it can never certify a wrong
 * result (CeTA is the check). CeTA certifies that the emitted ITS terminates, not the
 * bytecode→ITS abstraction that produced it.
 */
public final class CpfExporter {

    private CpfExporter() {}

    /** Signals a proof shape this exporter does not encode; turns into a {@code null} certificate. */
    private static final class NotExportable extends RuntimeException {
        NotExportable(String msg) { super(msg); }
    }

    /**
     * Exports a CPF LTS termination certificate for the sub-ITS reachable from
     * {@code entry}, or {@code null} when the certificate ({@code TERMINATES} required)
     * is not of an exportable shape.
     */
    public static String export(IntegerTransitionSystem its, String entry, Certificate cert) {
        if (cert == null || cert.verdict != Verdict.TERMINATES) return null;
        try {
            return new CpfExporter().build(its, entry, cert);
        } catch (NotExportable e) {
            return null;
        }
    }

    /** Convenience: prove with a certificate and export in one step. */
    public static String proveAndExport(IntegerTransitionSystem its, String entry) {
        return export(its, entry, FarkasRanking.proveWithCertificate(its, entry));
    }

    // -- per-export state ----------------------------------------------------

    private Set<String> reachable;
    private List<String> stateVars;
    private Map<String, String> outToState;            // LO0 -> LI0, SO1 -> SI1
    private Map<ItsTransition, String> tid;            // non-split transition -> its single id
    private List<Emit> edges;                          // emitted transitions, in id order
    /** For each MΦRF SCC: phase i (1-based) -> the ids of that SCC's phase-i sub-transitions. */
    private Map<SccProof, List<List<String>>> mphiPlan;

    /**
     * One emitted LTS transition: an ITS transition {@code t} optionally restricted
     * by extra phase-region conjuncts {@code regions} (empty for an un-split edge).
     * A MΦRF cyclic transition is emitted as {@code depth} such {@code Emit}s, one
     * per phase region; every other reachable transition is emitted once with no
     * region.
     */
    private static final class Emit {
        final ItsTransition t;
        final String id;
        final List<Region> regions;
        Emit(ItsTransition t, String id, List<Region> regions) {
            this.t = t; this.id = id; this.regions = regions;
        }
    }

    /** A phase-region conjunct over the source pre-state: {@code f ≥ 1} or {@code f ≤ 0}. */
    private static final class Region {
        final long[] f;          // coefficients [c_0,…,c_{n−1}, constant] over stateVars
        final boolean geOne;     // true ⇒ f ≥ 1 ; false ⇒ f ≤ 0
        Region(long[] f, boolean geOne) { this.f = f; this.geOne = geOne; }
    }

    private String build(IntegerTransitionSystem its, String entry, Certificate cert) {
        reachable = reachableFrom(its, entry);
        stateVars = stateVariables(its, entry);
        outToState = new LinkedHashMap<String, String>();
        for (String v : stateVars) outToState.put(outputName(v), v);

        buildEdges(its, cert);

        Map<String, List<ItsLinearConstraint>> invariants =
                ItsInvariants.compute(its, entry, reachable);

        StringBuilder sb = new StringBuilder();
        sb.append("<?xml version=\"1.0\"?>\n");
        sb.append("<certificationProblem xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\"")
          .append(" xsi:noNamespaceSchemaLocation=\"cpf3.xsd\">\n");
        sb.append("  <cpfVersion>3.0</cpfVersion>\n");
        sb.append("  <lookupTables><ruleTable/></lookupTables>\n");
        emitInput(sb, entry);
        sb.append("  <property><termination/></property>\n");
        sb.append("  <answer><yes/></answer>\n");
        sb.append("  <proof>\n");
        sb.append("    <ltsTerminationProof>\n");
        emitProofBody(sb, its, entry, cert, invariants);
        sb.append("    </ltsTerminationProof>\n");
        sb.append("  </proof>\n");
        sb.append("  <metaInformation><toolInfos>")
          .append("<toolInfo>RaTI</toolInfo><toolInfo>CeTA export</toolInfo>")
          .append("</toolInfos></metaInformation>\n");
        sb.append("</certificationProblem>\n");
        return sb.toString();
    }

    /**
     * Builds the emitted-transition list, splitting every cyclic transition of a
     * MΦRF SCC into its {@code depth} phase regions (each carrying the original
     * relation plus {@code f_1≤0 ∧ … ∧ f_{i−1}≤0 ∧ (i<d ? f_i≥1 : true)}) and
     * leaving every other reachable transition un-split. Records, per MΦRF SCC, the
     * sub-transition ids grouped by phase for the ordered {@code transitionRemoval}.
     */
    private void buildEdges(IntegerTransitionSystem its, Certificate cert) {
        edges = new ArrayList<Emit>();
        tid = new IdentityHashMap<ItsTransition, String>();
        mphiPlan = new LinkedHashMap<SccProof, List<List<String>>>();

        // location -> the MΦRF SCC it belongs to (if any).
        Map<String, SccProof> mphiByLoc = new LinkedHashMap<String, SccProof>();
        for (SccProof s : cert.sccs)
            if (s.multiphase != null)
                for (String loc : s.locations) mphiByLoc.put(loc, s);
        for (SccProof s : cert.sccs)
            if (s.multiphase != null) {
                List<List<String>> phases = new ArrayList<List<String>>();
                for (int i = 0; i < s.multiphase.depth; i++) phases.add(new ArrayList<String>());
                mphiPlan.put(s, phases);
            }

        int n = 0;
        for (ItsTransition t : its.transitions()) {
            String src = t.source().name(), tgt = t.target().name();
            if (!reachable.contains(src)) continue;
            SccProof s = mphiByLoc.get(src);
            boolean cyclicInMphi = s != null && s == mphiByLoc.get(tgt);
            if (!cyclicInMphi) {
                String id = "t" + (n++);
                tid.put(t, id);
                edges.add(new Emit(t, id, java.util.Collections.<Region>emptyList()));
                continue;
            }
            // Split this cyclic transition by the MΦRF phase regions of its source.
            int d = s.multiphase.depth;
            List<List<String>> phases = mphiPlan.get(s);
            for (int i = 1; i <= d; i++) {
                List<Region> regions = new ArrayList<Region>();
                for (int j = 1; j < i; j++)                       // f_j(src) ≤ 0
                    regions.add(new Region(phaseCoeffs(s, j, src), false));
                if (i < d)                                        // f_i(src) ≥ 1
                    regions.add(new Region(phaseCoeffs(s, i, src), true));
                String id = "t" + (n++) + "_p" + i;
                edges.add(new Emit(t, id, regions));
                phases.get(i - 1).add(id);
            }
        }
    }

    /** Phase-{@code i} (1-based) component {@code f_i} of a MΦRF SCC at a location. */
    private static long[] phaseCoeffs(SccProof s, int i, String loc) {
        long[] c = s.multiphase.phase.get(i - 1).get(loc);
        if (c == null) throw new NotExportable("MΦRF phase " + i + " missing at " + loc);
        return c;
    }

    // -- input LTS -----------------------------------------------------------

    private void emitInput(StringBuilder sb, String entry) {
        sb.append("  <input>\n    <lts>\n");
        sb.append("      <initial><locationId>").append(esc(entry)).append("</locationId></initial>\n");
        for (Emit em : edges) {
            ItsTransition t = em.t;
            sb.append("      <transition>\n");
            sb.append("        <transitionId>").append(em.id).append("</transitionId>\n");
            sb.append("        <source><locationId>").append(esc(t.source().name())).append("</locationId></source>\n");
            sb.append("        <target><locationId>").append(esc(t.target().name())).append("</locationId></target>\n");
            sb.append("        <formula>\n");
            emitTransitionFormula(sb, em);
            sb.append("        </formula>\n");
            sb.append("      </transition>\n");
        }
        sb.append("    </lts>\n  </input>\n");
    }

    /**
     * The transition relation = its guard (LI→pre, LO→post), any non-identity update,
     * plus the phase-region conjuncts that restrict a MΦRF split sub-transition.
     */
    private void emitTransitionFormula(StringBuilder sb, Emit em) {
        ItsTransition t = em.t;
        sb.append("          <conjunction>\n");
        for (ItsLinearConstraint c : t.constraints()) emitConstraint(sb, c);
        for (Region r : em.regions) emitRegion(sb, r);
        // Updates: target formal i receives updates[i]. The common case updates[i] = LO_i
        // is the identity (post = the guard's output variable) and is already carried by
        // the guard; emit an explicit eq only for a non-trivial update expression.
        List<String> targetFormals = t.target().variables();
        List<ItsLinearExpression> u = t.updates();
        for (int i = 0; i < u.size() && i < targetFormals.size(); i++) {
            ItsLinearExpression e = u.get(i);
            if (isOutputVarOf(e, targetFormals.get(i))) continue;        // identity post = LO_i
            sb.append("            <eq><post><variableId>").append(esc(targetFormals.get(i)))
              .append("</variableId></post>");
            emitExpr(sb, e);
            sb.append("</eq>\n");
        }
        sb.append("          </conjunction>\n");
    }

    /** A phase-region conjunct over the source pre-state: {@code 1 ≤ f} or {@code f ≤ 0}. */
    private void emitRegion(StringBuilder sb, Region r) {
        sb.append("            <leq>");
        if (r.geOne) { sb.append("<constant>1</constant>"); emitAffineSum(sb, r.f); }
        else         { emitAffineSum(sb, r.f); sb.append("<constant>0</constant>"); }
        sb.append("</leq>\n");
    }

    /** Emits {@code Σ c_i·formal_i + const} over the pre-state {@code stateVars} as a {@code <sum>}. */
    private void emitAffineSum(StringBuilder sb, long[] coeffs) {
        sb.append("<sum>");
        for (int i = 0; i < stateVars.size() && i < coeffs.length - 1; i++)
            if (coeffs[i] != 0) emitTerm(sb, coeffs[i], "<variableId>" + esc(stateVars.get(i)) + "</variableId>");
        sb.append("<constant>").append(coeffs[coeffs.length - 1]).append("</constant>");
        sb.append("</sum>");
    }

    /** True iff {@code e} is exactly the single output variable {@code outputName(formal)}. */
    private boolean isOutputVarOf(ItsLinearExpression e, String formal) {
        return e.constant() == 0 && e.coefficients().size() == 1
                && e.coefficient(outputName(formal)) == 1;
    }

    private void emitConstraint(StringBuilder sb, ItsLinearConstraint c) {
        sb.append("            ");
        switch (c.op()) {
            case EQ:  sb.append("<eq>");   emitExpr(sb, c.lhs()); sb.append("<constant>0</constant></eq>");   break;
            case GE:  sb.append("<leq><constant>0</constant>");  emitExpr(sb, c.lhs()); sb.append("</leq>");  break;
            case GT:  sb.append("<less><constant>0</constant>"); emitExpr(sb, c.lhs()); sb.append("</less>"); break;
            default:  throw new NotExportable("operator " + c.op());
        }
        sb.append('\n');
    }

    /** Emits {@code c0 + Σ c_v·v} as a CPF {@code <sum>}; v is a pre var or a {@code <post>}. */
    private void emitExpr(StringBuilder sb, ItsLinearExpression e) {
        sb.append("<sum>");
        for (Map.Entry<String, Long> term : e.coefficients().entrySet())
            emitTerm(sb, term.getValue(), varRef(term.getKey()));
        sb.append("<constant>").append(e.constant()).append("</constant>");
        sb.append("</sum>");
    }

    /** A CPF reference to an ITS variable: pre {@code <variableId>} or post {@code <post>}. */
    private String varRef(String v) {
        if (stateVars.contains(v)) return "<variableId>" + esc(v) + "</variableId>";
        String state = outToState.get(v);
        if (state != null) return "<post><variableId>" + esc(state) + "</variableId></post>";
        throw new NotExportable("variable outside LI/SI/LO/SO universe: " + v);
    }

    private static void emitTerm(StringBuilder sb, long coeff, String varInner) {
        if (coeff == 1) sb.append(varInner);
        else sb.append("<product><constant>").append(coeff).append("</constant>").append(varInner).append("</product>");
    }

    // -- proof body ----------------------------------------------------------

    private void emitProofBody(StringBuilder sb, IntegerTransitionSystem its, String entry,
            Certificate cert, Map<String, List<ItsLinearConstraint>> invariants) {
        // Acyclic reachable graph (no non-trivial SCC): no infinite run, but CeTA's
        // <trivial/> only discharges a transition-free LTS, so switch to a cooperation
        // program (one cut point at the entry) and let the empty sccDecomposition delete
        // the acyclic transitions. No invariants are needed.
        if (cert.sccs.isEmpty()) {
            sb.append("      <switchToCooperationTermination>\n        <cutPoints>\n");
            emitCutPoint(sb, entry);
            sb.append("        </cutPoints>\n        <sccDecomposition/>\n");
            sb.append("      </switchToCooperationTermination>\n");
            return;
        }
        // Every recorded SCC must be exportable: either the direct ADFG path
        // (per-transition rounds) or a surfaced MΦRF (phase-split chain).
        for (SccProof scc : cert.sccs)
            if (scc.cpfRounds.isEmpty() && scc.multiphase == null)
                throw new NotExportable("SCC proved by a non-exportable technique: " + scc.method);

        sb.append("      <newInvariants>\n");
        emitInvariants(sb, invariants);
        emitImpact(sb, its, entry, invariants);
        emitCooperation(sb, its, cert);
        sb.append("      </newInvariants>\n");
    }

    private void emitInvariants(StringBuilder sb, Map<String, List<ItsLinearConstraint>> invariants) {
        sb.append("        <invariants>\n");
        for (String loc : reachable) {
            sb.append("          <invariant><location><locationId>").append(esc(loc))
              .append("</locationId></location><formula>");
            emitConjunction(sb, invariants.get(loc));
            sb.append("</formula></invariant>\n");
        }
        sb.append("        </invariants>\n");
    }

    /** Conjunction of a location's invariant constraints (empty conjunction = true). */
    private void emitConjunction(StringBuilder sb, List<ItsLinearConstraint> inv) {
        if (inv == null || inv.isEmpty()) { sb.append("<conjunction/>"); return; }
        sb.append("<conjunction>");
        for (ItsLinearConstraint c : inv) {
            StringBuilder t = new StringBuilder();
            emitConstraint(t, c);
            sb.append(t.toString().trim());
        }
        sb.append("</conjunction>");
    }

    /**
     * An impact cover graph proving the invariants inductive: one node per reachable
     * location (the node id is the location name), the entry node marked initial, and a
     * child per outgoing transition pointing at the target location's node (cycles close
     * by pointing back to an existing node). CeTA re-checks node.inv ∧ transition ⊨
     * child.inv, so the invariants must genuinely hold.
     */
    private void emitImpact(StringBuilder sb, IntegerTransitionSystem its, String entry,
            Map<String, List<ItsLinearConstraint>> invariants) {
        sb.append("        <impact>\n          <initial>").append(esc(entry)).append("</initial>\n          <nodes>\n");
        for (String loc : reachable) {
            sb.append("            <node>\n");
            if (loc.equals(entry)) sb.append("              <initial/>\n");
            sb.append("              <nodeId>").append(esc(loc)).append("</nodeId>\n");
            sb.append("              <invariant>");
            emitConjunction(sb, invariants.get(loc));
            sb.append("</invariant>\n");
            sb.append("              <location><locationId>").append(esc(loc)).append("</locationId></location>\n");
            sb.append("              <children>\n");
            for (Emit em : edges)
                if (em.t.source().name().equals(loc))
                    sb.append("                <child><transitionId>").append(em.id)
                      .append("</transitionId><nodeId>").append(esc(em.t.target().name())).append("</nodeId></child>\n");
            sb.append("              </children>\n            </node>\n");
        }
        sb.append("          </nodes>\n        </impact>\n");
    }

    private void emitCooperation(StringBuilder sb, IntegerTransitionSystem its, Certificate cert) {
        // Cut points must be a feedback vertex set of each SCC (CeTA rejects the
        // construction otherwise — "graph not acyclic"). The whole SCC is trivially such
        // a set, and is robust to nested loops where a single loop head leaves an inner
        // cycle uncut; the per-location ρ are emitted for every SCC location anyway.
        Set<String> cuts = new LinkedHashSet<String>();
        for (SccProof scc : cert.sccs) cuts.addAll(scc.locations);
        sb.append("        <switchToCooperationTermination>\n          <cutPoints>\n");
        for (String loc : cuts) emitCutPoint(sb, loc);
        sb.append("          </cutPoints>\n");
        sb.append("          <sccDecomposition>\n");
        for (SccProof scc : cert.sccs) emitSccProof(sb, scc);
        sb.append("          </sccDecomposition>\n");
        sb.append("        </switchToCooperationTermination>\n");
    }

    private void emitCutPoint(StringBuilder sb, String loc) {
        sb.append("            <cutPoint>\n");
        sb.append("              <locationId>").append(esc(loc)).append("</locationId>\n");
        sb.append("              <skipId>skip_").append(esc(loc)).append("</skipId>\n");
        sb.append("              <skipFormula><conjunction>");
        for (String v : stateVars)
            sb.append("<eq><post><variableId>").append(esc(v)).append("</variableId></post><variableId>")
              .append(esc(v)).append("</variableId></eq>");
        sb.append("</conjunction></skipFormula>\n");
        sb.append("            </cutPoint>\n");
    }

    private void emitSccProof(StringBuilder sb, SccProof scc) {
        sb.append("            <sccWithProof>\n              <scc>");
        for (String loc : scc.locations)
            sb.append("<locationDuplicate>").append(esc(loc)).append("</locationDuplicate>");
        sb.append("</scc>\n");
        if (!scc.cpfRounds.isEmpty()) emitTransitionRemovalChain(sb, scc, 0);
        else emitMphiChain(sb, scc, 1);
        sb.append("            </sccWithProof>\n");
    }

    /** One {@code transitionRemoval} per peeling round, closing with an empty sccDecomposition. */
    private void emitTransitionRemovalChain(StringBuilder sb, SccProof scc, int round) {
        if (round >= scc.cpfRounds.size()) { sb.append("              <sccDecomposition/>\n"); return; }
        RankRound r = scc.cpfRounds.get(round);
        sb.append("              <transitionRemoval>\n                <rankingFunctions>\n");
        for (String loc : scc.locations) {
            long[] coeffs = r.rho.get(loc);
            sb.append("                  <rankingFunction><location><locationDuplicate>").append(esc(loc))
              .append("</locationDuplicate></location><expression>");
            emitRankExpr(sb, loc, coeffs);
            sb.append("</expression></rankingFunction>\n");
        }
        sb.append("                </rankingFunctions>\n");
        sb.append("                <bound><constant>0</constant></bound>\n");
        sb.append("                <remove>");
        for (ItsTransition t : r.removed) {
            String id = tid.get(t);
            if (id == null) throw new NotExportable("peeled transition outside the reachable set");
            sb.append("<transitionDuplicate>").append(id).append("</transitionDuplicate>");
        }
        sb.append("</remove>\n");
        emitTransitionRemovalChain(sb, scc, round + 1);
        sb.append("              </transitionRemoval>\n");
    }

    /**
     * One {@code transitionRemoval} per MΦRF phase, removing phase {@code i}'s
     * sub-transitions by ranking with {@code f_i} (bound 0) and recursing on the
     * remaining phases; the innermost closes with an empty sccDecomposition. Each
     * round is a valid linear entailment: in phase {@code i}'s region {@code f_i ≥ 1}
     * (boundedness) and {@code f_i} strictly decreases, while on every later phase
     * {@code f_1≤0 ∧ … ∧ f_{i−1}≤0} makes (13_i) force {@code Δf_i ≥ 1 ≥ 0}
     * (non-increasing) — exactly what CeTA re-checks.
     */
    private void emitMphiChain(StringBuilder sb, SccProof scc, int phase) {
        if (phase > scc.multiphase.depth) { sb.append("              <sccDecomposition/>\n"); return; }
        List<String> ids = mphiPlan.get(scc).get(phase - 1);
        Map<String, long[]> f = scc.multiphase.phase.get(phase - 1);
        sb.append("              <transitionRemoval>\n                <rankingFunctions>\n");
        for (String loc : scc.locations) {
            sb.append("                  <rankingFunction><location><locationDuplicate>").append(esc(loc))
              .append("</locationDuplicate></location><expression>");
            emitRankExpr(sb, loc, f.get(loc));
            sb.append("</expression></rankingFunction>\n");
        }
        sb.append("                </rankingFunctions>\n");
        sb.append("                <bound><constant>0</constant></bound>\n");
        sb.append("                <remove>");
        for (String id : ids) sb.append("<transitionDuplicate>").append(id).append("</transitionDuplicate>");
        sb.append("</remove>\n");
        emitMphiChain(sb, scc, phase + 1);
        sb.append("              </transitionRemoval>\n");
    }

    /** Ranking expression {@code Σ c_i·formal_i + const} over a location's pre-state formals. */
    private void emitRankExpr(StringBuilder sb, String loc, long[] coeffs) {
        if (coeffs == null) { sb.append("<constant>0</constant>"); return; }
        emitAffineSum(sb, coeffs);
    }

    // -- helpers -------------------------------------------------------------

    /** The output (post-state) variable name for an input formal: LI0→LO0, SI1→SO1. */
    private static String outputName(String stateVar) {
        if (stateVar.length() >= 2 && stateVar.charAt(1) == 'I')
            return stateVar.charAt(0) + "O" + stateVar.substring(2);
        return stateVar + "'";   // fallback; such a name simply won't match any guard var
    }

    private static Set<String> reachableFrom(IntegerTransitionSystem its, String start) {
        Set<String> seen = new LinkedHashSet<String>();
        Deque<String> q = new ArrayDeque<String>();
        seen.add(start); q.add(start);
        while (!q.isEmpty()) {
            String cur = q.poll();
            for (ItsTransition t : its.transitions())
                if (t.source().name().equals(cur) && seen.add(t.target().name())) q.add(t.target().name());
        }
        return seen;
    }

    private static List<String> stateVariables(IntegerTransitionSystem its, String start) {
        ItsLocation s = its.location(start);
        if (s != null && !s.variables().isEmpty()) return s.variables();
        for (ItsLocation l : its.locations()) if (!l.variables().isEmpty()) return l.variables();
        return new ArrayList<String>();
    }

    private static String esc(String s) {
        return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;");
    }
}
