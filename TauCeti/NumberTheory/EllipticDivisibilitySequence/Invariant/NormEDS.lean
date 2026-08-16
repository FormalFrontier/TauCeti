/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.EllipticDivisibilitySequence.Invariant.Basic
public import TauCeti.NumberTheory.EllipticDivisibilitySequence.NormEDS

/-!
# The invariant of a normalised EDS

For an elliptic net `W`, `invarNum_mul_invarDenom` gives the **cross-multiplied** identity
`invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m`. Over a general
`CommRing` that is all it gives: a denominator may vanish or be a zero divisor, so there is no
quotient to call constant — `Invariant/Basic.lean` makes the same caveat. A normalised EDS is an
elliptic net unconditionally (`isEllipticNet_normEDS`), so evaluating at the single index `n = 2`
yields the stated cross-multiplied identity for every other index.

## Main results

* `invarNum_normEDS_one_two`, `invarDenom_normEDS_one_two`: at `s = 1`, `n = 2` the numerator is
  `(d + b ^ 4) * b` and the denominator is `c * b`.
* `invarNum_normEDS_one_mul_eq_invarDenom_mul`: the cross-multiplied consequence,
  `invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b ^ 4)`, for every `m`
  and with no hypothesis on `b`, `c`, `d`.

## Implementation notes

Instantiating `invarNum_mul_invarDenom` at `(s, m, n) = (1, m, 2)` and substituting the two values
above gives the target multiplied through by `b`:

`(invarNum (normEDS b c d) 1 m * c) * b = (invarDenom (normEDS b c d) 1 m * (d + b ^ 4)) * b`

Cancelling that `b` needs `b` to be a nonzerodivisor, which is **not** implied by
`isEllipticNet_normEDS` being unconditional — that is a fact about the net property, not about
cancellation. The hypothesis is therefore discharged the same way `NormEDS.lean` discharges it for
`isEllipticNet_normEDS`: prove the statement over `MvPolynomial NormEDSParam ℤ`, where the
indeterminate `X B` *is* a nonzerodivisor, then specialise along `aeval`. The private
`invarNum_normEDS_one_mul_eq_invarDenom_mul_of_mem` is the hypothesis-carrying form, and exists
only to be specialised.

**Neither evaluation is a simp lemma**, and the two have different reasons. `invarDenom_def` and
`invarNum_def` are themselves `@[simp]`, so at equal priority they expand the left-hand sides
first: neither is in simp normal form, and tagging either would fail `simpNF`. For the denominator
that is the whole story, and it costs nothing — plain `simp` reaches `c * b` unaided. The numerator
is a genuine rewrite the default set does not perform: its proof needs `ring` after the expansions,
so `simp` alone does not normalise `invarNum (normEDS b c d) 1 2` to `(d + b ^ 4) * b`. Raising it
to `@[simp high]`, the escape `ReducedInvariant.lean` uses for its own numerator lemma, is what is
declined here: a module importing both this file and `ReducedInvariant.lean` would then carry two
`simp high` lemmas rewriting `invarNum (normEDS b c d) 1 2` to different normal forms, since
`invarNum_normEDS_one_eq_reducedInvarNum_mul` fires for every `m`, including `2`. That clash is a
fact about the consumer's environment rather than this module's, which is why it is recorded here
rather than left to be rediscovered. Both stay useful as rewrites named explicitly, which is how
the proof below uses them.

## Provenance

Adapted from D. K. Angdinata's
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at `dev/modular-curves @ 9fec8eba7652` — the revision
`TauCetiRoadmap/EllipticCurves/README.md` pins for the NagellLutz project. Source declarations
`invarNum_normEDS_two` (`:977`), `invarDenom_normEDS_two` (`:980`),
`invar₂_normEDS_of_mem_nonZeroDivisors` (`:1485`) and `invar₂_normEDS` (`:1492`). That file's
header reads `Authors: David Kurniadi Angdinata`; following this repository's convention for
adapted material the upstream authorship is credited here rather than in the copyright header.

All four are renamed here. The source's `invar₂_normEDS` advertises an index `2` that its statement
never mentions — the `2` enters only through the proof — so it is
`invarNum_normEDS_one_mul_eq_invarDenom_mul` below, describing the conclusion, and its
hypothesis-carrying helper is `…_of_mem`, matching `isEllipticNet_normEDS_of_mem`. The two
evaluations gain the first index: `invarNum` and `invarDenom` take two, and the source's `…_two`
names only the second, so `…_one_two` is what distinguishes them from an evaluation at some other
`s`. The source's `invar_normEDS` step needs no declaration at all: it is this repository's
`invarNum_mul_invarDenom` applied to `isEllipticNet_normEDS`.

## Placement

`Invariant/Basic.lean` states the invariant of a general elliptic net and the cross-multiplication
identity it satisfies; this file is its specialisation to `normEDS`. They share the `Invariant`
subject directory rather than sitting flat beside each other, so that further specialisations have
somewhere to go.
-/

public section

open MvPolynomial NormEDSParam

open scoped nonZeroDivisors

namespace IsEllipticNet

variable {R : Type*} [CommRing R] {b c d : R}

/-- The numerator of the invariant of `normEDS b c d` at `s = 1`, `n = 2`: it is `(d + b ^ 4) * b`.

Not a simp lemma; neither is its denominator counterpart, and the module's implementation notes
say why. -/
theorem invarNum_normEDS_one_two (b c d : R) :
    invarNum (normEDS b c d) 1 2 = (d + b ^ 4) * b := by
  simp only [invarNum_def, mul_one, Int.reduceAdd, normEDS_four, Int.reduceSub, normEDS_one,
    one_pow, normEDS_three, sub_self, normEDS_zero, mul_zero, add_zero, normEDS_two]
  ring

/-- The denominator of the invariant of `normEDS b c d` at `s = 1`, `n = 2`: it is `c * b`. -/
theorem invarDenom_normEDS_one_two (b c d : R) : invarDenom (normEDS b c d) 1 2 = c * b := by
  simp

/-- `invarNum_normEDS_one_mul_eq_invarDenom_mul` under a nonzerodivisor hypothesis on `b`, which
the unconditional form discharges by specialising from the universal parameters. -/
private theorem invarNum_normEDS_one_mul_eq_invarDenom_mul_of_mem (hb : b ∈ R⁰) (m : ℤ) :
    invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b ^ 4) := by
  rw [← mul_cancel_right_mem_nonZeroDivisors hb]
  have h := invarNum_mul_invarDenom (isEllipticNet_normEDS b c d) 1 m 2
  rw [invarNum_normEDS_one_two, invarDenom_normEDS_one_two] at h
  linear_combination h

/-- **The cross-multiplied invariant identity at `s = 1`**, for every `m` and with no hypothesis on
`b`, `c`, `d`.

It is an identity between products, not a statement that a quotient is constant: over a general
`CommRing` a denominator may vanish or be a zero divisor, and if `c` and `d + b ^ 4` both vanish
the equation holds vacuously. `Invariant/Basic.lean` makes the same distinction where
`invarNum_mul_invarDenom` is proved. -/
theorem invarNum_normEDS_one_mul_eq_invarDenom_mul (b c d : R) (m : ℤ) :
    invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b ^ 4) := by
  have huniv := invarNum_normEDS_one_mul_eq_invarDenom_mul_of_mem
    (b := (X B : MvPolynomial NormEDSParam ℤ)) (c := X C) (d := X D)
    (mem_nonZeroDivisors_of_ne_zero (X_ne_zero (R := ℤ) B)) m
  have key := congr(aeval (NormEDSParam.rec b c d) $huniv)
  -- `universalNormEDS`'s body is unexposed here, so the rewrite under `invarNum` needs the named
  -- equation; `universalNormEDS_def` is stated at the level of functions for exactly that reason.
  rw [normEDS_eq_aeval (b := b) (c := c) (d := d), ← Function.comp_def, ← map_invarNum,
    ← map_invarDenom, universalNormEDS_def]
  simpa only [map_mul, map_add, map_pow, aeval_X] using key

end IsEllipticNet
