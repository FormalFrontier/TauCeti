/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.NumDen

/-!
# What the reduced denominator of a fraction measures

Over a unique factorization domain `R` with fraction field `K`, Mathlib's `IsFractionRing.num` and
`IsFractionRing.den` write `x : K` as a fraction in lowest terms. This file records what `den`
measures: it is exactly the obstruction to `x` being integral, in the sense that scaling `x` by
`d : R` lands in the image of `R` **precisely** when `den x` divides `d`.

## Main results

* `IsFractionRing.den_dvd_iff_isInteger_mul`: `den x ∣ d ↔ IsLocalization.IsInteger R (d * x)`.

The forward direction holds for any denominator; the converse is where being in *lowest terms*
matters, and it is the reason this is an `Iff` rather than a one-way bound.

Mathlib's existing `den` API answers adjacent questions — `isInteger_of_isUnit_den` when the
denominator is a unit, `isUnit_den_iff` for the converse of that, `num_mul_den_eq_num_iff_eq` for
the defining relation — but none of them relates divisibility of `den` to integrality of a multiple.

The statement is in the `*`-form `algebraMap R K d * x` rather than the `•`-form `d • x` that
Mathlib's `isInteger_smul` uses. The two are equal (`Algebra.smul_def`), and the choice follows the
consumers: a denominator bound is applied with `d` a numeral, where `IsInteger R (4 * x)` needs no
rewriting and the `•`-form would need `algebraMap_smul` at every call site.
-/

public section

namespace IsFractionRing

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The reduced denominator is exactly the obstruction to integrality**: `d * x` lies in the
image of `R` if and only if `den x` divides `d`.

The forward direction is a bound on how far `x` is from being integral, and holds for any `d` that
`den x` divides. The converse needs the fraction to be in lowest terms: `d * x = s` clears to
`d * num x = s * den x`, so `den x ∣ d * num x`, and `num x` and `den x` being relatively prime
leaves `den x ∣ d`. -/
theorem den_dvd_iff_isInteger_mul {x : K} {d : R} :
    (den R x : R) ∣ d ↔ IsLocalization.IsInteger R (algebraMap R K d * x) := by
  have hx : x * algebraMap R K (den R x : R) = algebraMap R K (num R x) :=
    (num_mul_den_eq_num_iff_eq (A := R) (x := x) (y := x)).2 rfl
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e * num R x, ?_⟩
    rw [he, map_mul, map_mul, ← hx]
    ring
  · rintro ⟨s, hs⟩
    have hR : d * num R x = s * (den R x : R) := by
      refine IsFractionRing.injective R K ?_
      rw [map_mul, map_mul, ← hx, ← mul_assoc, hs]
    exact (num_den_reduced R x).symm.dvd_of_dvd_mul_right ⟨s, by rw [hR, mul_comm]⟩

end IsFractionRing
