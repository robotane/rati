package fr.univreunion.rati.its;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Prints an {@link IntegerTransitionSystem} in the KoAT / KITTeL integer
 * transition-system format. This single format is dual-use: it is the input
 * format of <b>iRankFinder</b> (for ranking-function termination proofs) and of
 * <b>KoAT</b> (for complexity bounds), both read by genericparser.
 *
 * <p>Output shape:
 * <pre>
 * (GOAL COMPLEXITY)
 * (STARTTERM (FUNCTIONSYMBOLS &lt;entry&gt;))
 * (VAR LI0 LI1 SI0 ...)
 * (RULES
 *   src(LI0,LI1,SI0) -&gt; tgt(LO0,LO1,SO0) :|: LI0 - LO0 - 1 = 0 &amp;&amp; LI1 &gt;= 0
 *   ...
 * )
 * </pre>
 *
 * <p>The state variables (VAR) are the locations' formal arguments
 * {@code LI*,SI*}; a transition's {@link ItsTransition#updates() updates} pass the
 * block's output variables {@code LO*,SO*} as the next state, and the guard
 * relates the two. The update variables are fresh (not declared in VAR), which
 * the parser treats as nondeterministic — exactly the relational step a
 * path-length relation needs (an output may be bounded, not determined).
 *
 * <p>{@link #print(IntegerTransitionSystem, String)} prints only the part of a
 * (whole-program) system reachable from a chosen start functor, so analysing one
 * method does not emit every other method's transitions.
 */
public final class KoatPrinter {

    private KoatPrinter() {}

    /** Prints the whole system, starting from {@link IntegerTransitionSystem#entryLocation()}. */
    public static String print(IntegerTransitionSystem its) {
        return print(its, its.entryLocation());
    }

    /** A synthetic initial location, guaranteed to have no incoming edge (KoAT requires it). */
    private static final String INIT = "koat_init";

    /** Prints the sub-system reachable from {@code startFunctor}. */
    public static String print(IntegerTransitionSystem its, String startFunctor) {
        Set<String> reachable = reachableFrom(its, startFunctor);
        List<String> vars = stateVariables(its, startFunctor);
        String args = String.join(", ", vars);

        // KoAT requires the initial location to have NO incoming transition. The
        // real entry block is often a loop head (it has a back-edge), so we start
        // from a fresh location koat_init whose only rule enters the real start.
        // A system whose start IS koat_init was already wrapped (RatiItsBridge adds
        // the same synthetic entry): re-emitting the rule here would print a spurious
        // "koat_init -> koat_init" identity self-loop — an unrankable phantom SCC
        // that poisons any re-parse of the printed text (the dumpRatiDir round-trip).
        StringBuilder sb = new StringBuilder();
        sb.append("(GOAL COMPLEXITY)\n");
        sb.append("(STARTTERM (FUNCTIONSYMBOLS ").append(INIT).append("))\n");
        sb.append("(VAR ").append(String.join(" ", vars)).append(")\n");
        sb.append("(RULES\n");
        if (!INIT.equals(startFunctor)) {
            sb.append("  ").append(INIT).append('(').append(args).append(") -> ")
              .append(startFunctor).append('(').append(args).append(")\n");
        }
        for (ItsTransition t : its.transitions()) {
            if (reachable.contains(t.source().name())) sb.append("  ").append(rule(t)).append('\n');
        }
        sb.append(")\n");
        return sb.toString();
    }

    /** Location names reachable from {@code start} by following transitions. */
    private static Set<String> reachableFrom(IntegerTransitionSystem its, String start) {
        Set<String> seen = new LinkedHashSet<String>();
        Deque<String> q = new ArrayDeque<String>();
        seen.add(start);
        q.add(start);
        while (!q.isEmpty()) {
            String cur = q.poll();
            for (ItsTransition t : its.transitions()) {
                if (t.source().name().equals(cur) && seen.add(t.target().name())) {
                    q.add(t.target().name());
                }
            }
        }
        return seen;
    }

    /** The state variables = the start location's formal args (all locations uniform). */
    private static List<String> stateVariables(IntegerTransitionSystem its, String start) {
        ItsLocation s = its.location(start);
        if (s != null && !s.variables().isEmpty()) return s.variables();
        for (ItsLocation l : its.locations()) {
            if (!l.variables().isEmpty()) return l.variables();
        }
        return java.util.Collections.<String>emptyList();
    }

    private static String rule(ItsTransition t) {
        StringBuilder sb = new StringBuilder();
        sb.append(t.source().name()).append('(')
          .append(String.join(", ", t.source().variables())).append(')');
        sb.append(" -> ").append(t.target().name()).append('(');
        List<ItsLinearExpression> u = t.updates();
        for (int i = 0; i < u.size(); i++) {
            if (i > 0) sb.append(", ");
            sb.append(u.get(i));
        }
        sb.append(')');
        List<ItsLinearConstraint> g = t.constraints();
        if (!g.isEmpty()) {
            sb.append(" :|: ");
            for (int i = 0; i < g.size(); i++) {
                if (i > 0) sb.append(" && ");
                sb.append(g.get(i));
            }
        }
        return sb.toString();
    }
}
