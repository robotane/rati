package fr.univreunion.rati.its;

import java.util.Collections;
import java.util.List;

/**
 * A location (program point) of an {@link IntegerTransitionSystem}.
 *
 * <p>One location per CLP(PL) block predicate: its {@link #variables()} are the
 * predicate's formal arguments in order (e.g. {@code [LI0, LI1, SI0]}), the same
 * names the path-length export uses for a block's input locals/stack.
 */
public final class ItsLocation {

    private final String name;
    private final List<String> variables;

    public ItsLocation(String name, List<String> variables) {
        this.name = name;
        this.variables = Collections.unmodifiableList(variables);
    }

    public String name() { return name; }

    /** Formal argument names, in order. */
    public List<String> variables() { return variables; }

    public int arity() { return variables.size(); }

    @Override
    public String toString() {
        return name + "(" + String.join(", ", variables) + ")";
    }
}
