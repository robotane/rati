package fr.univreunion.rati.ranking;

import apron.Manager;
import apron.Polka;

/**
 * Per-thread Apron polyhedra managers.
 *
 * <p>An Apron {@link Manager} is a stateless configuration handle: it carries the
 * domain choice (here convex polyhedra, {@code Polka}) and nothing tied to a
 * particular {@code Abstract1}/{@code Environment}, so a single instance is reused
 * across every operation on a thread. The binding holds the native domain only
 * through a {@code long ptr} freed by {@code finalize()}, so creating a fresh
 * {@code Polka} per call (per ITS transition, in the worst case) accumulated
 * unbounded native Apron/GMP memory — the wrappers stay tiny on the Java heap, the
 * GC almost never runs, and the finalizers that release the native polyhedra never
 * fire. Reusing one manager per domain per thread keeps the native footprint to the
 * polyhedra of the method actually being analysed.
 *
 * <p>The manager is held in a {@link ThreadLocal}, not a single shared static, so an
 * embedding analyser can rank several methods <em>concurrently in one JVM</em> — the
 * mode BCTerm uses when it calls the engine in-process from its parallel ranking
 * cascade, where the former forked model gave each method its own process and thus
 * its own manager. The underlying Polka domain is not safe under concurrent
 * operations, so two threads sharing one manager could corrupt native state; a
 * per-thread manager makes concurrent proofs race-free while preserving the
 * "one manager reused across every operation" memory win (the native footprint is
 * bounded by the number of ranking threads — a handful — not by per-call creation).
 * The standalone CLI ({@code RankMain}) is single-threaded, so it allocates exactly
 * one manager per domain, exactly as before.
 */
final class ApronManagers {

    /** Loose (non-strict) convex polyhedra — the default invariant/summary domain. */
    private static final ThreadLocal<Manager> POLKA =
            ThreadLocal.withInitial(() -> new Polka(false));

    /** Strict convex polyhedra — needed where a {@code f < 0} complement must be exact. */
    private static final ThreadLocal<Manager> POLKA_STRICT =
            ThreadLocal.withInitial(() -> new Polka(true));

    /** This thread's loose-polyhedra manager (created on first use). */
    static Manager polka() { return POLKA.get(); }

    /** This thread's strict-polyhedra manager (created on first use). */
    static Manager polkaStrict() { return POLKA_STRICT.get(); }

    private ApronManagers() {}
}
