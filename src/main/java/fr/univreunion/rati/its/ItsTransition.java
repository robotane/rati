package fr.univreunion.rati.its;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * A transition {@code source --[guard]--> target} of an
 * {@link IntegerTransitionSystem}, with an integer {@link #cost()}.
 *
 * <p>A transition is the standard relational step {@code f(x⃗) -> g(u⃗) :|: guard}:
 * <ul>
 *   <li>{@link #source()}/{@link #target()} are the two locations;</li>
 *   <li>{@link #updates()} are the expressions passed to the target's formal
 *       arguments (the "next state"), one per target argument — e.g. the block's
 *       output variables {@code LO0, SO0, …};</li>
 *   <li>{@link #constraints()} are the guard: linear relations over the source
 *       variables {@code LI0,SI0,…} and the update variables {@code LO0,SO0,…}
 *       (so {@code -LI2 + LO2 + 1 = 0} means the target's argument fed by
 *       {@code LO2} equals {@code LI2 - 1}).</li>
 * </ul>
 *
 * <p>A transition can be flagged {@link #isSupported() unsupported} when the
 * originating CLP(PL) clause cannot be faithfully expressed as a single
 * source→target step. The ITS keeps it as an explicit marker so termination
 * backends stay sound by returning UNKNOWN rather than silently dropping it.
 */
public final class ItsTransition {

    private final ItsLocation source;
    private final ItsLocation target;
    private final List<ItsLinearConstraint> constraints;
    private final List<ItsLinearExpression> updates;
    private final int cost;
    private final boolean supported;

    /** Full constructor. {@code updates.size()} must equal {@code target.arity()}. */
    public ItsTransition(ItsLocation source, ItsLocation target,
                         List<ItsLinearConstraint> constraints,
                         List<ItsLinearExpression> updates, int cost, boolean supported) {
        this.source = source;
        this.target = target;
        this.constraints = Collections.unmodifiableList(constraints);
        this.updates = Collections.unmodifiableList(updates);
        this.cost = cost;
        this.supported = supported;
    }

    /** Supported, unit-cost transition with explicit updates. */
    public ItsTransition(ItsLocation source, ItsLocation target,
                         List<ItsLinearConstraint> constraints,
                         List<ItsLinearExpression> updates) {
        this(source, target, constraints, updates, 1, true);
    }

    /** Supported, unit-cost transition with identity updates (target's own vars). */
    public ItsTransition(ItsLocation source, ItsLocation target,
                         List<ItsLinearConstraint> constraints) {
        this(source, target, constraints, identity(target), 1, true);
    }

    /** Unit-cost transition with identity updates and an explicit supported flag. */
    public ItsTransition(ItsLocation source, ItsLocation target,
                         List<ItsLinearConstraint> constraints, int cost, boolean supported) {
        this(source, target, constraints, identity(target), cost, supported);
    }

    private static List<ItsLinearExpression> identity(ItsLocation target) {
        List<ItsLinearExpression> u = new ArrayList<ItsLinearExpression>();
        for (String v : target.variables()) u.add(ItsLinearExpression.variable(v));
        return u;
    }

    public ItsLocation source() { return source; }
    public ItsLocation target() { return target; }
    public List<ItsLinearConstraint> constraints() { return constraints; }

    /** Expressions bound to the target's formal arguments (the next state). */
    public List<ItsLinearExpression> updates() { return updates; }

    public int cost() { return cost; }

    /** False when the source clause could not be faithfully modelled (see class doc). */
    public boolean isSupported() { return supported; }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(source.name()).append('(').append(String.join(", ", source.variables())).append(')');
        sb.append(" -> ").append(target.name()).append('(');
        for (int i = 0; i < updates.size(); i++) {
            if (i > 0) sb.append(", ");
            sb.append(updates.get(i));
        }
        sb.append(')');
        if (cost != 1) sb.append("  [cost=").append(cost).append(']');
        if (!supported) sb.append("  [UNSUPPORTED]");
        if (!constraints.isEmpty()) {
            sb.append("\n    { ");
            for (int i = 0; i < constraints.size(); i++) {
                if (i > 0) sb.append(", ");
                sb.append(constraints.get(i));
            }
            sb.append(" }");
        }
        return sb.toString();
    }
}
