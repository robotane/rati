# RaTI

**RaTI** (Ranking-based Termination Inference) is a **termination and
non-termination prover for integer transition systems (ITS)**: it reads a system
in the [KoAT](https://github.com/aprove-developers/KoAT2-Releases) / KITTeL text
format and answers `TERMINATES` (with a ranking-function certificate),
`NONTERMINATES` (with a recurrent-set witness) or `UNKNOWN`.

The engine is language-agnostic — it only consumes an ITS, so any front-end that
can emit KoAT (bytecode, EVM/Wasm, hand-written models) can be proved terminating
with it.

## What it does

Given an ITS — locations with integer variables, and guarded transitions
`src(x⃗) -> tgt(e⃗) :|: guard` — `RaTI` proves every reachable loop (SCC)
well-founded by searching, in order:

1. **Lexicographic linear ranking** (Alias–Darte–Feautrier–Gonnord, SAS 2010):
   Farkas-encoded bounded/decrease implications, maximal-strict peeling, in exact
   rational arithmetic.
2. **Polyhedral invariants** (Apron, widening + narrowing) injected as extra
   premises — the boundedness facts per-transition guards lack.
3. **Cut-point loop summarisation** (exact relational composition) for
   diamonds / nested loops.
4. **Multiphase ranking** (MΦRF, Ben-Amram–Genaim, CAV 2017).
5. **Disjunctive termination** (transition invariants, Podelski–Rybalchenko,
   LICS 2004) as a last resort.

An SCC no ranking technique covers is then attacked from the other side —
**non-termination by recurrent sets** (Gupta et al., POPL 2008):

6. the SCC's simple cycles are **determinised** (update variables solved exactly
   from the guard equalities; leftover nondeterminism fixed — a sound
   under-approximation) and composed into explicit self-loops;
7. a candidate set `G` — the loop guard (Frohn–Giesl, FMCAD 2019), strengthened
   by the bounded descending iteration `G ← G ∧ G∘s` (closed recurrence,
   Chen et al., TACAS 2014) and/or the polyhedral invariant — is checked
   **inductive by Farkas' lemma in exact rational arithmetic**;
8. a **concrete integer entry state** reaching `G` is synthesised (LP + rounding)
   and **re-verified by `BigInteger` substitution**: only then is `NONTERMINATES`
   answered, with the recurrent set, the cycle, the path and the witness state.

A found ranking is a sound proof, a verified recurrent set a sound disproof; an
undecided loop yields `UNKNOWN` (never a false verdict either way). Strict guards
are tightened to their exact integer form (`e > 0 ⇒ e − 1 ≥ 0`) on the
non-termination side — never relaxed. Note that `NONTERMINATES` is a statement
about the ITS *as given*: a front-end whose ITS over-approximates a program may
propagate `TERMINATES` to that program, but never `NONTERMINATES`.

## Build

Apron (the polyhedra library, JNI) is not on Maven Central, so its jars ship in
`lib-repo/` (a project-local Maven repository) and its native libraries in `lib/`
— `mvn package` works out of the box, no setup step:

```bash
mvn package                # runs tests, builds target/rati.jar
```

Requirements: JDK 8+ and Maven. The native libs in `lib/` are Linux x86-64
(`libjapron.so`, `libjgmp.so`); on another platform, drop in matching Apron/GMP
native builds.

## Usage

```bash
# Apron is JNI → point java.library.path at the native libs in lib/
LD_LIBRARY_PATH=lib java -Djava.library.path=lib -jar target/rati.jar <file.koat> [--entry F] [--quiet]
```

- `--entry <functor>` — start location (default: the `(STARTTERM …)` in the file);
- `--quiet` — print only the verdict (no certificate);
- exit code `0` = TERMINATES, `1` = UNKNOWN, `2` = usage / I/O error,
  `3` = NONTERMINATES.

A handy alias:

```bash
alias rati='LD_LIBRARY_PATH=lib java -Djava.library.path=lib -jar target/rati.jar'
rati examples/nested_loops.koat
```

### Example

```
$ rati examples/nested_loops.koat
TERMINATES
certificate:
  SCC [b_nested_2, b_nested_3, b_nested_4, b_nested_5, b_nested_6]: lexicographic linear (ADFG, loop summary)
    lexicographic component 1:
      rho(b_nested_5) = 2*LI0 - 2*LI2 - 2
      rho(b_nested_6) = 2*LI0 - 2*LI2 - 3
    lexicographic component 2:
      rho(b_nested_5) = LI1 - LI3 - 1
      rho(b_nested_6) = 0
```

The certificate lists, per loop SCC, the technique used and — for the
lexicographic-linear path — the synthesised ranking function ρ at each location,
one component per peeling round (here a 2-component lexicographic order: the outer
counter, then the inner).

A non-termination certificate is a replayable witness:

```
$ rati examples/nonterminating.koat
NONTERMINATES
certificate (non-termination):
  location: b_main_count_sub_neg_2
  recurrent set: { LI0 >= 0, LI3 - 1 >= 0 }
  cycle: b_main_count_sub_neg_2 -> b_main_count_sub_neg_3 -> b_main_count_sub_neg_2
  determinised step: LI0' = LI0, LI1' = LI1, LI2' = LI2 + LI3, LI3' = LI3 + 1, LI4' = 0, LI5' = 0, SI0' = 0, SI1' = 0
  path: koat_init -> b_main_count_sub_neg_1 -> b_main_count_sub_neg_2
  entry state: LI0 = 0, LI1 = 0, LI2 = 0, LI3 = 0, LI4 = 0, LI5 = 0, SI0 = 0, SI1 = 0
  state entering the loop: LI0 = 0, LI1 = -1, LI2 = 0, LI3 = 10, LI4 = 0, LI5 = 0, SI0 = 0, SI1 = 0
```

— from the entry state, the path reaches the loop head inside the recurrent set,
which one cycle iteration provably never leaves.

`examples/` holds a few ready inputs (`nested_loops`, `upcounter_bounded`
terminating; `nonterminating` disproved).

## Input format

The KoAT / KITTeL ITS format (the one `KoatPrinter` emits and that KoAT /
iRankFinder read):

```
(GOAL COMPLEXITY)
(STARTTERM (FUNCTIONSYMBOLS koat_init))
(VAR LI0 LI1 SI0)
(RULES
  koat_init(LI0, LI1, SI0) -> b_loop(LI0, LI1, SI0)
  b_loop(LI0, LI1, SI0) -> b_loop(LI0 - 1, LI1, SI0) :|: LI0 - 1 >= 0
)
```

The `(VAR …)` names are every location's formal arguments; a rule's right-hand
arguments are the update expressions and the `:|:` part the guard
(`lhs OP 0`, `OP ∈ {=, >=, >}`). Update variables not in `(VAR …)` are
nondeterministic — the relational step a path-length / abstract-domain relation
needs.

## Library use

```java
IntegerTransitionSystem its = KoatParser.parse(text).its;
FarkasRanking.Certificate c = FarkasRanking.proveWithCertificate(its, "koat_init");
// c.verdict ∈ {TERMINATES, NONTERMINATES, UNKNOWN};
// c.sccs = per-SCC ranking certificate; c.nonTermination = recurrent-set witness
```

## Layout

```
src/main/java/fr/univreunion/rati/
  its/        ITS data model (IntegerTransitionSystem, ItsLocation, ItsTransition,
              ItsLinearConstraint, ItsLinearExpression, KoatPrinter)
  ranking/    the prover: FarkasRanking, LinearProgram, Rational, ItsInvariants,
              LoopSummary, MultiphaseRanking, DisjunctiveTermination, NonTermination
  rank/       CLI: KoatParser, RankMain
lib/          Apron/GMP native libraries (JNI)
lib-repo/     Apron/GMP jars as a project-local Maven repository
examples/     sample .koat inputs
```

`DecouplingArchitectureTest` enforces that the engine never depends on any
bytecode-analysis code, keeping it front-end-agnostic.

## References

- Alias, Darte, Feautrier, Gonnord — *Multi-dimensional Rankings, Program
  Termination, and Complexity Bounds of Flowchart Programs*, SAS 2010.
- Ben-Amram, Genaim — *Multiphase-Linear Ranking Functions and their Relation to
  Recurrent Sets*, CAV 2017.
- Podelski, Rybalchenko — *Transition Invariants*, LICS 2004.
- Gupta, Henzinger, Majumdar, Rybalchenko, Xu — *Proving Non-Termination*,
  POPL 2008.
- Chen, Cook, Fuhs, Nimkar, O'Hearn — *Proving Nontermination via Safety*,
  TACAS 2014.
- Frohn, Giesl — *Proving Non-Termination via Loop Acceleration*, FMCAD 2019.
- Apron — <https://antoinemine.github.io/Apron/doc/> (LGPL).

## Licence

RaTI's own source is under the Apache License 2.0 (see `LICENSE` / `NOTICE`).
Apron / GMP (bundled native libs and jars) are LGPL — see their upstream licences.
