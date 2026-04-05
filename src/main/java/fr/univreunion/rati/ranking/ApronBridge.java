package fr.univreunion.rati.ranking;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import apron.Abstract1;
import apron.ApronException;
import apron.Coeff;
import apron.Environment;
import apron.Lincons1;
import apron.Linexpr1;
import apron.Linterm1;
import apron.Manager;
import apron.MpqScalar;
import apron.Scalar;
import gmp.Mpq;

import fr.univreunion.rati.its.ItsLinearConstraint;
import fr.univreunion.rati.its.ItsLinearExpression;

/**
 * The single, <em>exact</em> bridge between the ITS constraint model and Apron.
 *
 * <p>Apron's Java binding stores every scalar as a GMP rational ({@link
 * MpqScalar}), so both directions can be lossless: constraints are built with
 * {@code BigInteger}-backed scalars (never an {@code (int)} cast, which silently
 * truncates a {@code long} coefficient) and read back through {@link
 * #coeffToRational} (never {@code toDouble} + {@code Math.round}, which silently
 * corrupts anything beyond 2⁵³).
 *
 * <p>Reading back ({@link #toConstraints}) may still meet a value that does not
 * fit the {@code long}-coefficient ITS model after integer scaling; such a
 * conjunct is <b>dropped</b>, which <em>weakens</em> the constraint set. Every
 * caller must only use the result where weakening is the sound direction:
 * a weaker invariant premise, a larger summarised relation to rank, a smaller
 * premise set for a Farkas synthesis. Never feed a dropped-conjunct read-back to
 * a use where a smaller polyhedron is assumed.
 */
final class ApronBridge {

    private ApronBridge() {}

    // -------------------------------------------------------------------------
    // Native lifetime — free dead intermediates on the proof thread
    // -------------------------------------------------------------------------

    /**
     * Frees the superseded intermediate {@code old} on THIS (the proof) thread and returns
     * its replacement {@code neo}. The chained Apron transfers in the ranking tiers
     * ({@code meetCopy}, {@code changeEnvironmentCopy}, {@code joinCopy}, {@code renameCopy},
     * {@code widening}) each allocate a fresh native polyhedron and leave the previous one
     * dead. Left to the GC those are freed asynchronously by the JVM {@code Cleaner} daemon,
     * which calls into the per-thread {@code Polka} manager while a proof may still be
     * mid-operation on the same manager — and NewPolka is not safe under concurrent
     * operations (see {@link ApronManagers}), so an async free racing a live op can corrupt
     * native state. Disposing each dead intermediate synchronously, on the proof thread,
     * keeps it off the Cleaner's queue (deterministic same-thread free) and bounds the live
     * native footprint. Apply ONLY to a value that neither escapes nor aliases a still-live
     * one; use {@link #disposeUnless} when the value may alias a protected input.
     */
    static Abstract1 supersede(Abstract1 old, Abstract1 neo) {
        if (old != null) old.dispose();
        return neo;
    }

    /** Disposes {@code x} unless it is {@code null} or is the protected {@code keep} — the
     *  guard for a chain whose first link may alias an input ({@code a = cond ? in : in.copy()}).
     *  {@code Abstract1.dispose()} is idempotent, so a double call is a safe no-op. */
    static void disposeUnless(Abstract1 x, Abstract1 keep) {
        if (x != null && x != keep) x.dispose();
    }

    // -------------------------------------------------------------------------
    // ITS → Apron (always exact)
    // -------------------------------------------------------------------------

    /** {@code c} as an Apron constraint over {@code env}, exactly. */
    static Lincons1 toLincons(Environment env, ItsLinearConstraint c) {
        int kind = c.op() == ItsLinearConstraint.Op.EQ ? Lincons1.EQ
                 : c.op() == ItsLinearConstraint.Op.GT ? Lincons1.SUP : Lincons1.SUPEQ;
        return new Lincons1(kind, linexpr(env, bigTerms(c.lhs(), false),
                BigInteger.valueOf(c.lhs().constant())));
    }

    /** {@code expr ≥ 0} over {@code env}, exactly. */
    static Lincons1 geLincons(Environment env, ItsLinearExpression expr) {
        return new Lincons1(Lincons1.SUPEQ, linexpr(env, bigTerms(expr, false),
                BigInteger.valueOf(expr.constant())));
    }

    /** {@code var − expr = 0} over {@code env}, exactly. */
    static Lincons1 bindEq(Environment env, String var, ItsLinearExpression expr) {
        Map<String, BigInteger> terms = bigTerms(expr, true);
        BigInteger own = terms.getOrDefault(var, BigInteger.ZERO);
        terms.put(var, own.add(BigInteger.ONE));
        return new Lincons1(Lincons1.EQ,
                linexpr(env, terms, BigInteger.valueOf(expr.constant()).negate()));
    }

    /** {@code Σ terms·v + cst} as a {@link Linexpr1}, exactly. */
    static Linexpr1 linexpr(Environment env, Map<String, BigInteger> terms, BigInteger cst) {
        List<Linterm1> ts = new ArrayList<Linterm1>();
        for (Map.Entry<String, BigInteger> e : terms.entrySet())
            if (e.getValue().signum() != 0)
                ts.add(new Linterm1(e.getKey(), new MpqScalar(e.getValue())));
        return new Linexpr1(env, ts.toArray(new Linterm1[0]), new MpqScalar(cst));
    }

    /** An exact rational scalar. */
    static MpqScalar scalar(Rational r) {
        return new MpqScalar(r.numerator(), r.denominator());
    }

    private static Map<String, BigInteger> bigTerms(ItsLinearExpression e, boolean negated) {
        Map<String, BigInteger> m = new LinkedHashMap<String, BigInteger>();
        for (Map.Entry<String, Long> t : e.coefficients().entrySet()) {
            BigInteger v = BigInteger.valueOf(t.getValue());
            m.put(t.getKey(), negated ? v.negate() : v);
        }
        return m;
    }

    // -------------------------------------------------------------------------
    // Apron → ITS / rationals (exact, or an explicit refusal — never a rounding)
    // -------------------------------------------------------------------------

    /** The exact rational value of {@code c}, or {@code null} when it is not a finite rational. */
    static Rational coeffToRational(Coeff c) {
        if (!(c instanceof MpqScalar)) {
            // DoubleScalar / MpfrScalar / Interval never occur with Polka, but a
            // silent 0 (the old behaviour) would corrupt the constraint: refuse.
            return null;
        }
        if (((Scalar) c).isInfty() != 0) return null;
        Mpq q = ((MpqScalar) c).get();
        return Rational.of(q.getNum().bigIntegerValue(), q.getDen().bigIntegerValue());
    }

    /**
     * Reads {@code a} back as ITS constraints over its own variable names,
     * exactly: each row is scaled by the (positive) lcm of its denominators, so
     * the inequality is preserved. A row whose scaled values do not fit a
     * {@code long} — or whose scalars are not plain rationals — is dropped,
     * which only ever <em>weakens</em> the result (see class doc). Pure-constant
     * facets are dropped too (they carry no variable information).
     */
    static List<ItsLinearConstraint> toConstraints(Manager man, Abstract1 a) throws ApronException {
        List<ItsLinearConstraint> out = new ArrayList<ItsLinearConstraint>();
        if (a.isBottom(man) || a.isTop(man)) return out;
        nextRow:
        for (Lincons1 lc : a.toLincons(man)) {
            ItsLinearConstraint.Op op = ItsLinearConstraint.opFromApron(lc.getKind());
            if (op == null) continue;
            List<String> vars = new ArrayList<String>();
            List<Rational> coefs = new ArrayList<Rational>();
            for (Linterm1 lt : lc.getLinterms()) {
                Rational r = coeffToRational(lt.getCoefficient());
                if (r == null) continue nextRow;
                if (!r.isZero()) { vars.add(lt.getVariable().toString()); coefs.add(r); }
            }
            Rational cst = coeffToRational(lc.getCst());
            if (cst == null || vars.isEmpty()) continue;

            BigInteger d = cst.denominator();
            for (Rational r : coefs) d = lcm(d, r.denominator());
            ItsLinearExpression.Builder b = new ItsLinearExpression.Builder();
            try {
                for (int i = 0; i < vars.size(); i++)
                    b.addTerm(vars.get(i), scaledLong(coefs.get(i), d));
                b.addConstant(scaledLong(cst, d));
            } catch (ArithmeticException overflow) {
                continue;   // beyond the long model: drop the conjunct (weakens)
            }
            out.add(new ItsLinearConstraint(b.build(), op));
        }
        return out;
    }

    /** {@code r·d} as an exact {@code long} ({@code d} a multiple of {@code r}'s denominator). */
    private static long scaledLong(Rational r, BigInteger d) {
        return r.numerator().multiply(d.divide(r.denominator())).longValueExact();
    }

    private static BigInteger lcm(BigInteger a, BigInteger b) {
        return a.divide(a.gcd(b)).multiply(b);
    }
}
