/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.EllipticDivisibilitySequence.Descent
public import TauCeti.NumberTheory.EllipticDivisibilitySequence.Universal
import TauCeti.NumberTheory.EllipticDivisibilitySequence.Ext

/-!
# A normalised EDS is an elliptic net

`normEDS b c d` is defined by the doubling recursion, so it satisfies that recursion by
construction. This file draws the consequence: it satisfies the full **four**-index elliptic
relation, for arbitrary `b`, `c`, `d` in any commutative ring. Being an elliptic *sequence* is
the last index held at `0`.

Knowing that, one specialisation can be identified outright: `normEDS 2 3 2` is the identity
sequence. Its base values are `1, 2, 3, 4`, `id` is an elliptic sequence too, and
`IsEllipticSequence.ext` makes two elliptic sequences agreeing at `1, 2, 3, 4` equal given that
the first two values are nonzerodivisors — here `1` and `2` in `ℤ`. `Universal.lean` records this
identity as what `universalNormEDS_ne_zero` and `universalNormEDS_mem_nonZeroDivisors` rest on,
and had it down as blocked on that extensionality principle; `Ext.lean` supplies it.

The `ℤ` statement is the one with consumers, but it is not the general one: applying the unique
ring map out of `ℤ` gives `normEDS (2 : R) 3 2 = Int.cast` over every commutative ring, and both
are stated below.

The three-index statement is the first half of the TODO Mathlib records at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:70`, "prove that `normEDS` satisfies
`IsEllipticDvdSequence`". That predicate is `IsEllipticSequence ∧ IsDvdSequence`; the second
conjunct needs a general `normEDS_mul_complEDS`, of which Mathlib has only the `k = 2` case, and
is left to its own slice.

The net is what the invariant layer needs. `IsEllipticNet.invarNum_mul_invarDenom` takes an
`IsEllipticNet` hypothesis — its cross-multiplication identity is proved from the relation at four
free indices, not three — so stopping at the sequence would leave that consumer inapplicable to
`normEDS`. Applied to `isEllipticNet_normEDS` it gives, writing `W` for `normEDS b c d`,

`invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m`

for every `b`, `c`, `d`, `s`, `m` and `n`.

That is **weaker** than index-independence of an invariant ratio, which needs the denominators
invertible and so does not hold over a general commutative ring; `Invariant.lean` states the
distinction where the identity is proved.

## Main results

* `isEllipticNet_normEDS`: `IsEllipticNet (normEDS b c d)`, with no hypothesis on the parameters.
* `isEllipticSequence_normEDS`: its `s = 0` case.
* `normEDS_two_three_two_eq_intCast`: `normEDS (2 : R) 3 2 = Int.cast` over any commutative ring.
* `normEDS_two_three_two_eq_id`: its `R = ℤ` case, `normEDS (2 : ℤ) 3 2 = id`. Kept as a named
  theorem rather than left to the general form because it is what the universal-parameter
  arguments consume — they specialise at `(2, 3, 2)` in `ℤ`. Only the general form is `@[simp]`:
  tagging both makes `normEDS 2 3 2` rewrite to `Int.cast`, so the `ℤ` left-hand side is no longer
  in normal form and `simpNF` fails the build.

The first consumer this unlocks is `IsEllipticNet.invarNum_mul_invarDenom`, which callers can
apply to `isEllipticNet_normEDS` directly; it is deliberately not restated here as a
specialisation.

The `s = 0` case is kept as a named theorem rather than left to `.isEllipticSequence` at each
use: `IsEllipticSequence` is the predicate Mathlib defines, `IsEllipticDvdSequence` is
`IsEllipticSequence ∧ IsDvdSequence`, and so this is the term discharging the first conjunct of
the TODO cited above. Three files already name it as the fact they rest on —
`Universal.lean`, `ReducedInvariant.lean` and
`AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Invariant.lean`.

## Implementation notes

The direct argument needs `normEDS b c d 2 = b` to be a nonzerodivisor, which is a genuine
constraint on `b`. It is avoided by proving the statement over `ℤ[B, C, D]` first, where the
second term is the indeterminate `X B` and is a nonzerodivisor because a polynomial ring over a
domain is a domain, and then transporting along `aeval`. Every `normEDS b c d` is such a
specialisation of `universalNormEDS`, which is what `normEDS_eq_aeval` says, so the hypothesis
survives only in the private helper, applied once at the indeterminates.

`Universal.lean` records `universalNormEDS_ne_zero` and `universalNormEDS_mem_nonZeroDivisors`
as belonging with "whichever slice ports" the fact proved here. They are still not ported: they
rest on `normEDS 2 3 2 = id`, which is `normEDS_two_three_two_eq_id` below. The extensionality
principle
that identity needs is `IsEllipticSequence.ext`, which this repository now has, so the obstacle
recorded for those two is gone; what remains is the work itself.

## Provenance

Adapted from D. K. Angdinata's `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`
in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`),
declarations `IsEllSequence.normEDS_of_mem_nonZeroDivisors` and `IsEllSequence.normEDS`. That
file's header reads `Authors: David Kurniadi Angdinata`; following this repository's convention for
adapted material the upstream authorship is credited here rather than in the copyright header. J.
Xu is acknowledged for the surrounding LutzNagell development — he authors `Universal.lean` and
co-authors `DivisionPolynomialOmega.lean` at the same revision — as context for this port, not as
an author of the declarations above.

The net strengthening here adapts one further declaration of that same file, `net_normEDS`, and
`normEDS_two_three_two_eq_id` below adapts its `normEDS_two_three_two` (`:1236`), renamed to state
its conclusion. That declaration is byte-identical at the roadmap's NagellLutz pin
(`dev/modular-curves @ 9fec8eba7652`, `:1235`); the revision named above is used throughout so
that this file cites one source revision rather than two.

Its proof is the source's, with `IsEllipticSequence.id` in place of the deprecated
`isEllSequence_id` alias, and the four base-value hypotheses discharged by `simp` rather than by
`simp only` followed by `exacts`.

The source proves the hypothesis-carrying version from its own descent development; here that step
is `Descent.lean`'s `IsEllipticNet.of_rel`, fed the two recurrences in relator form, so the helper
is six lines rather than a file. The universal transport is the source's argument, with
`normEDS_eq_aeval` in place of its inline rewriting.
-/

public section

open scoped nonZeroDivisors
open MvPolynomial NormEDSParam

variable {R : Type*} [CommRing R] {b c d : R}

/-- **A normalised EDS is an elliptic net, given that `b` is a nonzerodivisor.** Superseded by
`isEllipticNet_normEDS`, which carries no hypothesis; this is the form that transports.

The two recurrences are supplied in relator form, which is what `IsEllipticNet.of_rel` consumes;
`rel_odd` and `rel_even` turn each into the equation `normEDS_odd` and `normEDS_even` state. -/
private theorem isEllipticNet_normEDS_of_mem (hb : b ∈ R⁰) :
    IsEllipticNet (normEDS b c d) := by
  refine IsEllipticNet.of_rel (fun k ↦ normEDS_neg b c d k) (normEDS_zero b c d)
    (by simp [normEDS_one]) (by simpa [normEDS_two] using hb) (fun m _ ↦ ?_) fun m _ ↦ ?_
  · rw [IsEllipticNet.rel_odd]
    simp only [normEDS_one, one_pow, mul_one]
    linear_combination normEDS_odd b c d m
  -- `linear_combination` needs `normEDS _ _ _ 2` and `… 1` as `b` and `1` before it can match.
  · rw [IsEllipticNet.rel_even]
    simp only [normEDS_one, normEDS_two, one_pow, mul_one]
    linear_combination normEDS_even b c d m

/-- **A normalised EDS is an elliptic net**, for arbitrary `b`, `c`, `d` over any commutative
ring. In particular no nonzerodivisor hypothesis is needed on the parameters. -/
theorem isEllipticNet_normEDS (b c d : R) : IsEllipticNet (normEDS b c d) := by
  -- Supply the defining equation rather than leaving it to `isDefEq`: `universalNormEDS`'s body
  -- is not exposed, so unification cannot cheaply see it as `normEDS (X B) (X C) (X D)`.
  have huniv : IsEllipticNet (universalNormEDS : ℤ → MvPolynomial NormEDSParam ℤ) := by
    have hfun : (universalNormEDS : ℤ → MvPolynomial NormEDSParam ℤ)
        = normEDS (X B) (X C) (X D) := funext universalNormEDS_apply
    rw [hfun]
    exact isEllipticNet_normEDS_of_mem (mem_nonZeroDivisors_of_ne_zero (X_ne_zero B))
  intro p q r s
  -- `map_rel` is stated for `f ∘ W`, `normEDS_eq_aeval` for the eta-expanded lambda.
  rw [normEDS_eq_aeval (b := b) (c := c) (d := d), ← Function.comp_def,
    ← IsEllipticNet.map_rel, huniv, map_zero]

/-- **A normalised EDS is an elliptic sequence**, the last index of the net held at `0`. -/
theorem isEllipticSequence_normEDS (b c d : R) : IsEllipticSequence (normEDS b c d) :=
  (isEllipticNet_normEDS b c d).isEllipticSequence

/-- **`normEDS 2 3 2` is the identity sequence on `ℤ`.** -/
theorem normEDS_two_three_two_eq_id : normEDS (2 : ℤ) 3 2 = id := by
  refine (isEllipticSequence_normEDS 2 3 2).ext IsEllipticSequence.id ?_ ?_ ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp

/-- **`normEDS 2 3 2` is the integer cast, over any commutative ring.** The identity on `ℤ`
transported along the unique ring map out of it. -/
@[simp]
theorem normEDS_two_three_two_eq_intCast (R : Type*) [CommRing R] :
    normEDS (2 : R) 3 2 = Int.cast := by
  funext n
  have h := map_normEDS (f := Int.castRingHom R) (b := (2 : ℤ)) (c := 3) (d := 2) n
  rw [normEDS_two_three_two_eq_id] at h
  simpa using h.symm
