package fr.univreunion.rati.its;

import apron.Lincons1;

/**
 * A linear constraint {@code lhs OP 0} where {@code OP ∈ {=, ≥, >}}.
 *
 * <p>Mirrors the three Apron constraint kinds our path-length polyhedra ever
 * produce ({@code Lincons1.EQ}, {@code Lincons1.SUPEQ}, {@code Lincons1.SUP});
 * see {@link fr.univreunion.rati.ranking.ApronBridge}. Keeping the comparison
 * structured (rather than as Prolog text) lets ITS backends read the relation
 * directly.
 */
public final class ItsLinearConstraint {

    /** Comparison operator of a constraint {@code lhs OP 0}. */
    public enum Op {
        EQ("="), GE(">="), GT(">");
        private final String symbol;
        Op(String symbol) { this.symbol = symbol; }
        public String symbol() { return symbol; }
    }

    private final ItsLinearExpression lhs;
    private final Op op;

    public ItsLinearConstraint(ItsLinearExpression lhs, Op op) {
        this.lhs = lhs;
        this.op = op;
    }

    public ItsLinearExpression lhs() { return lhs; }
    public Op op() { return op; }

    /** Maps an Apron constraint kind to an {@link Op}, or {@code null} for EQMOD/DISEQ. */
    public static Op opFromApron(int kind) {
        if (kind == Lincons1.EQ)    return Op.EQ;
        if (kind == Lincons1.SUPEQ) return Op.GE;
        if (kind == Lincons1.SUP)   return Op.GT;
        return null;
    }

    @Override
    public String toString() {
        return lhs + " " + op.symbol() + " 0";
    }
}
