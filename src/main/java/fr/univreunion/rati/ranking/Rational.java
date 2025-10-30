package fr.univreunion.rati.ranking;

import java.math.BigInteger;

/**
 * An exact rational number {@code num/den} (always in lowest terms, {@code den > 0}).
 *
 * <p>The in-house linear-ranking synthesiser ({@link FarkasRanking}) runs an exact
 * simplex ({@link LinearProgram}) over these to avoid the floating-point
 * unsoundness a ranking certificate cannot tolerate: a ranking function must
 * <em>provably</em> decrease, so the Farkas multipliers and template coefficients
 * are computed in exact arithmetic.
 */
public final class Rational implements Comparable<Rational> {

    public static final Rational ZERO = new Rational(BigInteger.ZERO, BigInteger.ONE);
    public static final Rational ONE  = new Rational(BigInteger.ONE, BigInteger.ONE);

    private final BigInteger num;   // normalised: gcd(|num|,den)=1
    private final BigInteger den;   // > 0

    private Rational(BigInteger num, BigInteger den) {
        this.num = num;
        this.den = den;
    }

    public static Rational of(long n) {
        return new Rational(BigInteger.valueOf(n), BigInteger.ONE);
    }

    public static Rational of(long n, long d) {
        return of(BigInteger.valueOf(n), BigInteger.valueOf(d));
    }

    public static Rational of(BigInteger n, BigInteger d) {
        if (d.signum() == 0) throw new ArithmeticException("rational with zero denominator");
        if (d.signum() < 0) { n = n.negate(); d = d.negate(); }
        BigInteger g = n.gcd(d);
        if (g.signum() != 0 && !g.equals(BigInteger.ONE)) { n = n.divide(g); d = d.divide(g); }
        return new Rational(n, d);
    }

    public Rational add(Rational o) {
        return of(num.multiply(o.den).add(o.num.multiply(den)), den.multiply(o.den));
    }

    public Rational subtract(Rational o) {
        return of(num.multiply(o.den).subtract(o.num.multiply(den)), den.multiply(o.den));
    }

    public Rational multiply(Rational o) {
        return of(num.multiply(o.num), den.multiply(o.den));
    }

    public Rational divide(Rational o) {
        if (o.num.signum() == 0) throw new ArithmeticException("division by zero");
        return of(num.multiply(o.den), den.multiply(o.num));
    }

    public Rational negate() {
        return new Rational(num.negate(), den);
    }

    public int signum() { return num.signum(); }
    public boolean isZero() { return num.signum() == 0; }
    public boolean isNegative() { return num.signum() < 0; }
    public boolean isPositive() { return num.signum() > 0; }

    public BigInteger numerator() { return num; }
    public BigInteger denominator() { return den; }

    @Override
    public int compareTo(Rational o) {
        return num.multiply(o.den).compareTo(o.num.multiply(den));
    }

    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof Rational)) return false;
        Rational o = (Rational) obj;
        return num.equals(o.num) && den.equals(o.den);
    }

    @Override
    public int hashCode() {
        return 31 * num.hashCode() + den.hashCode();
    }

    @Override
    public String toString() {
        return den.equals(BigInteger.ONE) ? num.toString() : num + "/" + den;
    }
}
