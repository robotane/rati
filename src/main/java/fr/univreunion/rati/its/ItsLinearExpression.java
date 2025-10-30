package fr.univreunion.rati.its;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

/**
 * An integer linear expression {@code c0 + Σ c_v · v} over named variables.
 *
 * <p>This is the structured counterpart of the textual constraints that
 * {@link fr.univreunion.rati.clp.PolyToClp} renders for cTI: instead of a
 * Prolog string it keeps the coefficients explicitly, so backends that consume
 * an Integer Transition System (iRankFinder, KoAT) can read the relation
 * symbolically rather than re-parsing text. Immutable; build with
 * {@link Builder} or the static factories.
 */
public final class ItsLinearExpression {

    private final Map<String, Long> terms;   // variable -> non-zero coefficient
    private final long constant;

    private ItsLinearExpression(Map<String, Long> terms, long constant) {
        this.terms = Collections.unmodifiableMap(terms);
        this.constant = constant;
    }

    public static ItsLinearExpression constant(long c) {
        return new ItsLinearExpression(new LinkedHashMap<String, Long>(), c);
    }

    public static ItsLinearExpression variable(String name) {
        Map<String, Long> t = new LinkedHashMap<String, Long>();
        t.put(name, 1L);
        return new ItsLinearExpression(t, 0L);
    }

    /** Coefficient of {@code var} (0 if absent). */
    public long coefficient(String var) {
        Long c = terms.get(var);
        return c == null ? 0L : c.longValue();
    }

    public long constant() { return constant; }

    /** Variables with a non-zero coefficient (insertion order). */
    public Set<String> variables() { return terms.keySet(); }

    /** True when there are no variable terms (a pure integer). */
    public boolean isConstant() { return terms.isEmpty(); }

    public Map<String, Long> coefficients() { return terms; }

    /** Builds {@code lhs OP 0}-style expressions term by term, folding zeros. */
    public static final class Builder {
        private final Map<String, Long> terms = new LinkedHashMap<String, Long>();
        private long constant = 0L;

        public Builder addTerm(String var, long coeff) {
            if (coeff == 0) return this;
            long n = (terms.containsKey(var) ? terms.get(var) : 0L) + coeff;
            if (n == 0) terms.remove(var); else terms.put(var, n);
            return this;
        }

        public Builder addConstant(long c) { constant += c; return this; }

        public ItsLinearExpression build() {
            return new ItsLinearExpression(new LinkedHashMap<String, Long>(terms), constant);
        }
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        boolean first = true;
        for (Map.Entry<String, Long> e : terms.entrySet()) {
            long c = e.getValue();
            long mag = Math.abs(c);
            if (first) { if (c < 0) sb.append('-'); first = false; }
            else sb.append(c < 0 ? " - " : " + ");
            if (mag == 1) sb.append(e.getKey());
            else sb.append(mag).append('*').append(e.getKey());
        }
        if (constant != 0 || first) {
            long mag = Math.abs(constant);
            if (first) sb.append(constant < 0 ? "-" + mag : Long.toString(mag));
            else sb.append(constant < 0 ? " - " : " + ").append(mag);
        }
        return sb.toString();
    }
}
