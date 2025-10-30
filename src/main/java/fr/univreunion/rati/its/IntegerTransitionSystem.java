package fr.univreunion.rati.its;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * An Integer Transition System: the structured pivot between BCTerm's
 * path-length analyses and the termination/complexity backends.
 *
 * <p>It is a faithful factorisation of the CLP(PL) export (Spoto-Mesnard-Payet
 * TOPLAS 2010, Def 53): every block predicate becomes an {@link ItsLocation}
 * and every clause {@code H :- C, B} becomes an {@link ItsTransition} from
 * {@code H}'s location to {@code B}'s, guarded by {@code C}. A terminal fact
 * {@code H :- C.} contributes a location with no outgoing transition. From this
 * one representation we print:
 * <ul>
 *   <li>CLP(PL) for cTI (round-trips the existing export, validating the IR);</li>
 *   <li>an iRankFinder integer-transition-system for ranking-function synthesis;</li>
 *   <li>a KoAT system for complexity bounds.</li>
 * </ul>
 *
 * <p>Soundness: an ITS over-approximates the program's path-length behaviour, so
 * "the ITS terminates" implies "the program terminates" — the sound direction.
 * Clauses that cannot be modelled as a single source→target step are kept as
 * {@link ItsTransition#isSupported() unsupported} transitions so backends report
 * UNKNOWN instead of dropping them.
 */
public final class IntegerTransitionSystem {

    private final String name;
    private final String entryLocation;
    private final Map<String, ItsLocation> locations = new LinkedHashMap<String, ItsLocation>();
    private final List<ItsTransition> transitions = new ArrayList<ItsTransition>();

    /**
     * @param name          a label for the system (e.g. the method functor)
     * @param entryLocation name of the location the analysis starts from
     */
    public IntegerTransitionSystem(String name, String entryLocation) {
        this.name = name;
        this.entryLocation = entryLocation;
    }

    public String name() { return name; }
    public String entryLocation() { return entryLocation; }

    public ItsLocation addLocation(ItsLocation loc) {
        locations.put(loc.name(), loc);
        return loc;
    }

    public ItsLocation location(String name) { return locations.get(name); }
    public Collection<ItsLocation> locations() { return locations.values(); }

    public void addTransition(ItsTransition t) {
        // Register endpoint locations defensively so the system is self-contained.
        locations.put(t.source().name(), t.source());
        locations.put(t.target().name(), t.target());
        transitions.add(t);
    }

    public List<ItsTransition> transitions() { return transitions; }

    /** True if any transition is flagged unsupported (forces a sound UNKNOWN). */
    public boolean hasUnsupportedTransition() {
        for (ItsTransition t : transitions) if (!t.isSupported()) return true;
        return false;
    }

    /** Human-readable dump (the debug printer of the ITS pipeline). */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("ITS ").append(name).append("  (entry: ").append(entryLocation).append(")\n");
        sb.append("locations:\n");
        for (ItsLocation l : locations.values()) sb.append("  ").append(l).append('\n');
        sb.append("transitions:\n");
        for (ItsTransition t : transitions) sb.append("  ").append(t).append('\n');
        return sb.toString();
    }
}
