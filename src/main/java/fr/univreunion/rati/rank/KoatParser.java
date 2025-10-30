package fr.univreunion.rati.rank;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import fr.univreunion.rati.its.IntegerTransitionSystem;
import fr.univreunion.rati.its.ItsLinearConstraint;
import fr.univreunion.rati.its.ItsLinearExpression;
import fr.univreunion.rati.its.ItsLocation;
import fr.univreunion.rati.its.ItsTransition;

/**
 * Reads an {@link IntegerTransitionSystem} from the KoAT / KITTeL integer
 * transition-system text format — the exact inverse of {@link
 * fr.univreunion.rati.its.KoatPrinter}. This makes the in-house ranking solver
 * a standalone tool: it consumes the same {@code .koat} files iRankFinder / KoAT
 * do, so any front-end able to emit KoAT can be ranked without going through the
 * BCTerm bytecode pipeline.
 *
 * <p>Accepted shape (whitespace-tolerant, one rule per line):
 * <pre>
 * (GOAL COMPLEXITY)                       % ignored
 * (STARTTERM (FUNCTIONSYMBOLS koat_init)) % start functor
 * (VAR LI0 LI1 SI0 ...)                   % uniform state variables
 * (RULES
 *   src(LI0, LI1, SI0) -&gt; tgt(LO0, LI1 - 1, SO0) :|: LI0 - LO0 - 1 = 0 &amp;&amp; LI1 &gt;= 0
 *   ...
 * )
 * </pre>
 *
 * <p>All locations share the {@code (VAR …)} list as their formal arguments
 * (KoatPrinter emits a uniform frame); a rule's right-hand arguments are the
 * transition {@link ItsTransition#updates() updates} and the {@code :|:} part its
 * guard. Update variables not in {@code (VAR …)} are fresh / nondeterministic,
 * exactly the relational step a path-length relation needs.
 */
public final class KoatParser {

    private KoatParser() {}

    /** The parsed system plus the start functor declared by {@code (STARTTERM …)}. */
    public static final class Parsed {
        public final IntegerTransitionSystem its;
        public final String start;
        Parsed(IntegerTransitionSystem its, String start) {
            this.its = its;
            this.start = start;
        }
    }

    private static final Pattern VAR =
            Pattern.compile("\\(VAR\\s+([^)]*)\\)");
    private static final Pattern STARTTERM =
            Pattern.compile("\\(STARTTERM\\s*\\(FUNCTIONSYMBOLS\\s+([^)\\s]+)\\s*\\)\\s*\\)");

    /** Parses the whole KoAT text. */
    public static Parsed parse(String text) {
        List<String> vars = new ArrayList<String>();
        Matcher vm = VAR.matcher(text);
        if (vm.find()) {
            for (String v : vm.group(1).trim().split("\\s+")) {
                if (!v.isEmpty()) vars.add(v);
            }
        }
        String start = null;
        Matcher sm = STARTTERM.matcher(text);
        if (sm.find()) start = sm.group(1).trim();

        IntegerTransitionSystem its =
                new IntegerTransitionSystem("parsed", start == null ? "" : start);

        // Pass 1: each location's formal arguments are the args on its OWN source
        // side — locations may have different arities (the (VAR …) list is only the
        // universe of variable names, the fallback for a sink that is never a
        // source). KoatPrinter emits a uniform frame, but general KoAT/termCOMP ITSs
        // give each function symbol its own parameters.
        Map<String, List<String>> formals = new LinkedHashMap<String, List<String>>();
        for (String raw : text.split("\\R")) {
            String line = stripComment(raw).trim();
            int arrow = line.indexOf("->");
            if (arrow < 0 || (line.startsWith("(") && !looksLikeRule(line))) continue;
            String lhs = line.substring(0, arrow).trim();
            String name = functorName(lhs);
            if (name != null && !formals.containsKey(name)) {
                formals.put(name, splitArgs(functorArgs(lhs)));
            }
        }
        // A location that only ever appears as a TARGET (a sink — no outgoing rule)
        // has no source side, so size its formals by the ARITY it is called with,
        // not the (VAR …) universe: calling m1(B) when m1 is a sink must give m1
        // arity 1, else the transition's update count mismatches the target arity
        // (an IndexOutOfBounds in the invariant post-image). A sink's formal NAMES
        // are irrelevant (it has no outgoing transitions).
        for (String raw : text.split("\\R")) {
            String line = stripComment(raw).trim();
            int arrow = line.indexOf("->");
            if (arrow < 0 || (line.startsWith("(") && !looksLikeRule(line))) continue;
            for (String targetAtom : unwrapTargets(line.substring(arrow + 2).trim())) {
                String name = functorName(targetAtom);
                if (name == null || formals.containsKey(name)) continue;
                int arity = splitArgs(functorArgs(targetAtom)).size();
                List<String> generic = new ArrayList<String>();
                for (int k = 0; k < arity; k++) generic.add(k < vars.size() ? vars.get(k) : "v" + k);
                formals.put(name, generic);
            }
        }

        // Pass 2: build the transitions.
        Map<String, ItsLocation> locs = new LinkedHashMap<String, ItsLocation>();
        for (String raw : text.split("\\R")) {
            String line = stripComment(raw).trim();
            if (line.isEmpty() || !line.contains("->")) continue;
            if (line.startsWith("(") && !looksLikeRule(line)) continue;
            for (ItsTransition t : parseRule(line, formals, vars, locs)) its.addTransition(t);
        }
        for (ItsLocation l : locs.values()) its.addLocation(l);
        return new Parsed(its, start);
    }

    private static boolean looksLikeRule(String line) {
        int arrow = line.indexOf("->");
        return arrow > 0 && line.indexOf('(') >= 0 && line.indexOf('(') < arrow;
    }

    private static String stripComment(String line) {
        // KITTeL/KoAT line comments are not emitted by KoatPrinter, but tolerate
        // a leading-% comment line.
        int pct = line.indexOf('%');
        return pct >= 0 ? line.substring(0, pct) : line;
    }

    /**
     * Parses one {@code src(args) -> RHS [:|: guard]} rule into one or more
     * transitions. The RHS is either a single target {@code tgt(args)} (as
     * KoatPrinter emits) or a KoAT/KITTeL cost wrapper
     * {@code Com_n(t1(a1), …, tn(an))} — n successor calls. For termination each
     * {@code Com_n} successor is a separate transition from {@code src} with the
     * same guard (the standard ITS encoding: all reachable loops must be ranked).
     */
    private static List<ItsTransition> parseRule(String line,
            Map<String, List<String>> formals, List<String> vars,
            Map<String, ItsLocation> locs) {
        List<ItsTransition> out = new ArrayList<ItsTransition>();
        String head = line;
        String guardPart = null;
        int gi = line.indexOf(":|:");
        if (gi >= 0) {
            head = line.substring(0, gi);
            guardPart = line.substring(gi + 3);
        }
        int arrow = head.indexOf("->");
        if (arrow < 0) return out;
        String lhs = head.substring(0, arrow).trim();
        String rhs = head.substring(arrow + 2).trim();

        String srcName = functorName(lhs);
        if (srcName == null) return out;
        ItsLocation src = location(srcName, formals, vars, locs);
        List<ItsLinearConstraint> guard;
        boolean guardLinear = true;
        try {
            guard = parseGuard(guardPart);
        } catch (NonlinearException nl) {
            // A non-affine guard cannot be modelled: drop it (empty guard = always
            // enabled) but keep the rule as UNSUPPORTED so the loop is not silently
            // lost (which would be unsound). The prover returns UNKNOWN.
            guard = new ArrayList<ItsLinearConstraint>();
            guardLinear = false;
        }

        for (String targetAtom : unwrapTargets(rhs)) {
            String tgtName = functorName(targetAtom);
            if (tgtName == null) continue;
            ItsLocation tgt = location(tgtName, formals, vars, locs);
            if (!guardLinear) { out.add(new ItsTransition(src, tgt, guard, 1, false)); continue; }
            try {
                List<ItsLinearExpression> updates = new ArrayList<ItsLinearExpression>();
                for (String arg : splitArgs(functorArgs(targetAtom))) updates.add(parseExpr(arg));
                out.add(new ItsTransition(src, tgt, guard, updates));
            } catch (NonlinearException nl) {
                // A non-affine update (e.g. a(A*B)): not expressible as a linear
                // relation. Keep it as an UNSUPPORTED transition with the guard
                // preserved — the prover then stays sound (UNKNOWN) unless the
                // guard is independently infeasible, in which case the transition
                // can never fire and is pruned regardless of its update.
                out.add(new ItsTransition(src, tgt, guard, 1, false));
            }
        }
        return out;
    }

    /** A non-affine sub-term ({@code var*var}, {@code a*b*c}) that has no linear model. */
    static final class NonlinearException extends RuntimeException {
        NonlinearException(String term) { super("non-linear term: " + term); }
    }

    private static List<ItsLinearConstraint> parseGuard(String guardPart) {
        List<ItsLinearConstraint> guard = new ArrayList<ItsLinearConstraint>();
        if (guardPart != null) {
            for (String c : guardPart.split("&&")) {
                String cc = c.trim();
                if (!cc.isEmpty()) guard.add(parseConstraint(cc));
            }
        }
        return guard;
    }

    /**
     * Target atoms of a RHS: {@code Com_n(t1, …, tn)} → the n atoms; an unwrapped
     * {@code tgt(args)} → a singleton.
     */
    private static List<String> unwrapTargets(String rhs) {
        String s = rhs.trim();
        if (s.startsWith("Com_")) {
            int p = s.indexOf('(');
            int q = s.lastIndexOf(')');
            if (p > 0 && q > p) return splitTopLevel(s.substring(p + 1, q));
        }
        List<String> single = new ArrayList<String>();
        if (!s.isEmpty()) single.add(s);
        return single;
    }

    /** Splits a comma list at paren depth 0 (the inner atoms keep their own args). */
    private static List<String> splitTopLevel(String s) {
        List<String> out = new ArrayList<String>();
        int depth = 0, start = 0;
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (c == '(') depth++;
            else if (c == ')') depth--;
            else if (c == ',' && depth == 0) {
                String t = s.substring(start, i).trim();
                if (!t.isEmpty()) out.add(t);
                start = i + 1;
            }
        }
        String t = s.substring(start).trim();
        if (!t.isEmpty()) out.add(t);
        return out;
    }

    private static ItsLocation location(String name, Map<String, List<String>> formals,
            List<String> vars, Map<String, ItsLocation> locs) {
        ItsLocation l = locs.get(name);
        if (l == null) {
            List<String> f = formals.get(name);   // its own source-side params; VAR list for a sink
            l = new ItsLocation(name, new ArrayList<String>(f != null ? f : vars));
            locs.put(name, l);
        }
        return l;
    }

    /** {@code name(args)} → {@code name}. */
    private static String functorName(String atom) {
        int p = atom.indexOf('(');
        if (p < 0) return atom.trim().isEmpty() ? null : atom.trim();
        return atom.substring(0, p).trim();
    }

    /** {@code name(a, b)} → {@code "a, b"} (empty when no args). */
    private static String functorArgs(String atom) {
        int p = atom.indexOf('(');
        int q = atom.lastIndexOf(')');
        if (p < 0 || q < 0 || q <= p) return "";
        return atom.substring(p + 1, q);
    }

    /** Splits a top-level comma list (our expressions contain no parens/commas). */
    private static List<String> splitArgs(String args) {
        List<String> out = new ArrayList<String>();
        if (args.trim().isEmpty()) return out;
        for (String a : args.split(",")) {
            String t = a.trim();
            if (!t.isEmpty()) out.add(t);
        }
        return out;
    }

    /** Parses {@code <lhs> <op> <rhs>} into a {@code (lhs - rhs) OP 0} constraint. */
    static ItsLinearConstraint parseConstraint(String s) {
        ItsLinearConstraint.Op op;
        String opSym;
        if (s.contains(">=")) { op = ItsLinearConstraint.Op.GE; opSym = ">="; }
        else if (s.contains("=")) { op = ItsLinearConstraint.Op.EQ; opSym = "="; }
        else if (s.contains(">")) { op = ItsLinearConstraint.Op.GT; opSym = ">"; }
        else throw new IllegalArgumentException("no comparison operator in constraint: " + s);

        int idx = s.indexOf(opSym);
        String lhs = s.substring(0, idx).trim();
        String rhs = s.substring(idx + opSym.length()).trim();

        ItsLinearExpression le = parseExpr(lhs);
        ItsLinearExpression re = parseExpr(rhs);
        // Combine into (lhs - rhs) OP 0.
        ItsLinearExpression.Builder b = new ItsLinearExpression.Builder();
        b.addConstant(le.constant() - re.constant());
        for (Map.Entry<String, Long> e : le.coefficients().entrySet())
            b.addTerm(e.getKey(), e.getValue());
        for (Map.Entry<String, Long> e : re.coefficients().entrySet())
            b.addTerm(e.getKey(), -e.getValue());
        return new ItsLinearConstraint(b.build(), op);
    }

    /**
     * Parses a linear expression like {@code -LI0 + LO0}, {@code LI2 - LO2 - 1},
     * {@code 2*LI0 + 3}, {@code LO1} or {@code 0} — the {@link
     * ItsLinearExpression#toString()} grammar. Terms are separated by {@code +}/
     * {@code -} (a leading {@code -} is a sign), a term is {@code [coeff*]var} or a
     * bare integer.
     */
    static ItsLinearExpression parseExpr(String expr) {
        ItsLinearExpression.Builder b = new ItsLinearExpression.Builder();
        String s = expr.trim();
        if (s.isEmpty()) return b.build();
        // Normalise separators: " - " becomes " + -", " + " stays, so a split on
        // " + " yields signed tokens; a leading "-term" keeps its sign.
        s = s.replace(" - ", " + -").replace(" + ", " + ");
        for (String tok : s.split(" \\+ ")) {
            String t = tok.trim();
            if (t.isEmpty()) continue;
            long sign = 1;
            while (t.startsWith("-") || t.startsWith("+")) {
                if (t.startsWith("-")) sign = -sign;
                t = t.substring(1).trim();
            }
            if (t.isEmpty()) continue;
            int star = t.indexOf('*');
            if (star >= 0) {
                String left = t.substring(0, star).trim();
                String right = t.substring(star + 1).trim();
                // Accept coeff*var, var*coeff and const*const; reject var*var and
                // products of three or more factors (non-affine — no linear model).
                if (right.indexOf('*') >= 0) throw new NonlinearException(t);
                if (isInteger(left) && !isInteger(right)) b.addTerm(right, sign * Long.parseLong(left));
                else if (isInteger(right) && !isInteger(left)) b.addTerm(left, sign * Long.parseLong(right));
                else if (isInteger(left) && isInteger(right))
                    b.addConstant(sign * Long.parseLong(left) * Long.parseLong(right));
                else throw new NonlinearException(t);
            } else if (isInteger(t)) {
                b.addConstant(sign * Long.parseLong(t));
            } else {
                b.addTerm(t, sign);
            }
        }
        return b.build();
    }

    private static boolean isInteger(String s) {
        if (s.isEmpty()) return false;
        for (int i = 0; i < s.length(); i++) {
            if (!Character.isDigit(s.charAt(i))) return false;
        }
        return true;
    }
}
