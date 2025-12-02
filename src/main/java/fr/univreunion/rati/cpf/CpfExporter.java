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
    private Map<ItsTransition, String> tid;            // stable transition ids
    private List<ItsTransition> edges;                 // reachable transitions, in id order

    private String build(IntegerTransitionSystem its, String entry, Certificate cert) {
        reachable = reachableFrom(its, entry);
        stateVars = stateVariables(its, entry);
        outToState = new LinkedHashMap<String, String>();
        for (String v : stateVars) outToState.put(outputName(v), v);

        edges = new ArrayList<ItsTransition>();
        tid = new IdentityHashMap<ItsTransition, String>();
        for (ItsTransition t : its.transitions()) {
            if (!reachable.contains(t.source().name())) continue;
            tid.put(t, "t" + edges.size());
            edges.add(t);
        }

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

    // -- input LTS -----------------------------------------------------------

    private void emitInput(StringBuilder sb, String entry) {
        sb.append("  <input>\n    <lts>\n");
        sb.append("      <initial><locationId>").append(esc(entry)).append("</locationId></initial>\n");
        for (ItsTransition t : edges) {
            sb.append("      <transition>\n");
            sb.append("        <transitionId>").append(tid.get(t)).append("</transitionId>\n");
            sb.append("        <source><locationId>").append(esc(t.source().name())).append("</locationId></source>\n");
            sb.append("        <target><locationId>").append(esc(t.target().name())).append("</locationId></target>\n");
            sb.append("        <formula>\n");
            emitTransitionFormula(sb, t);
            sb.append("        </formula>\n");
            sb.append("      </transition>\n");
        }
        sb.append("    </lts>\n  </input>\n");
    }

    /** The transition relation = its guard (LI→pre, LO→post) plus any non-identity update. */
    private void emitTransitionFormula(StringBuilder sb, ItsTransition t) {
        sb.append("          <conjunction>\n");
        for (ItsLinearConstraint c : t.constraints()) emitConstraint(sb, c);
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
        // Every recorded SCC must come from the direct ADFG path (per-transition rounds).
        for (SccProof scc : cert.sccs)
            if (scc.cpfRounds.isEmpty())
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
            for (ItsTransition t : edges)
                if (t.source().name().equals(loc))
                    sb.append("                <child><transitionId>").append(tid.get(t))
                      .append("</transitionId><nodeId>").append(esc(t.target().name())).append("</nodeId></child>\n");
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
        emitTransitionRemovalChain(sb, scc, 0);
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

    /** Ranking expression {@code Σ c_i·formal_i + const} over a location's pre-state formals. */
    private void emitRankExpr(StringBuilder sb, String loc, long[] coeffs) {
        if (coeffs == null) { sb.append("<constant>0</constant>"); return; }
        List<String> formals = stateVars;            // uniform across locations
        sb.append("<sum>");
        for (int i = 0; i < formals.size() && i < coeffs.length - 1; i++)
            if (coeffs[i] != 0) emitTerm(sb, coeffs[i], "<variableId>" + esc(formals.get(i)) + "</variableId>");
        sb.append("<constant>").append(coeffs[coeffs.length - 1]).append("</constant>");
        sb.append("</sum>");
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
