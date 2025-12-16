package fr.univreunion.rati.ranking;

import apron.Manager;
import apron.Polka;

/**
 * Shared Apron polyhedra managers.
 *
 * <p>An Apron {@link Manager} is a stateless configuration handle: it carries the
 * domain choice (here convex polyhedra, {@code Polka}) and nothing tied to a
 * particular {@code Abstract1}/{@code Environment}, so a single instance is reused
 * across every operation. The binding holds the native domain only through a
 * {@code long ptr} freed by {@code finalize()}, so creating a fresh {@code Polka}
 * per call (per ITS transition, in the worst case) accumulated unbounded native
 * Apron/GMP memory — the wrappers stay tiny on the Java heap, the GC almost never
 * runs, and the finalizers that release the native polyhedra never fire. Sharing
 * one manager per domain keeps the native footprint to the polyhedra of the
 * method actually being analysed.
 *
 * <p>Single-threaded use only (the whole RaTI pipeline is sequential), so no
 * synchronisation is needed.
 */
final class ApronManagers {

    /** Loose (non-strict) convex polyhedra — the default invariant/summary domain. */
    static final Manager POLKA = new Polka(false);

    /** Strict convex polyhedra — needed where a {@code f < 0} complement must be exact. */
    static final Manager POLKA_STRICT = new Polka(true);

    private ApronManagers() {}
}
