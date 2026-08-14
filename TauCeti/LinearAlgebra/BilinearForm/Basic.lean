/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# A form that is both symmetric and alternating

Away from characteristic two a bilinear form cannot be both symmetric and alternating without
being zero: symmetry and alternation give `B x y = B y x` and `B x y = -B y x`, so `2 * B x y = 0`,
and cancelling the `2` leaves `B x y = 0`.

That cancellation is all the hypothesis on the ring there is: `2` has to be regular, and nothing
is asked of any other element, so the statement covers rings with zero divisors elsewhere.  Over a
field, or over any domain, `IsRegular.of_ne_zero` supplies the hypothesis from `(2 : R) ≠ 0`.

## Main results

* `TauCeti.BilinForm.eq_zero_of_isSymm_of_isAlt`: a symmetric alternating form over a ring in which
  `2` is regular is zero.
* `TauCeti.BilinForm.IsSymm.toQuadraticMap_add`: polarization identity for the quadratic form
  associated to a symmetric bilinear form.
* `TauCeti.BilinForm.IsSymm.toQuadraticMap_sub`: subtraction polarization identity for the quadratic
  form associated to a symmetric bilinear form.
-/

public section

namespace TauCeti

open LinearMap (BilinForm)
open QuadraticMap (polar)

namespace BilinForm

/-- **Away from characteristic two a symmetric alternating form is zero**: symmetry and alternation
force `2 * B x y = 0`, and a regular `2` cancels. -/
theorem eq_zero_of_isSymm_of_isAlt {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (h2 : IsLeftRegular (2 : R)) {B : BilinForm R M} (hsymm : B.IsSymm)
    (halt : B.IsAlt) : B = 0 := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  have hzero : (2 : R) * B x y = 2 * 0 := by
    rw [mul_zero]
    linear_combination hsymm.eq x y - halt.neg_eq x y
  simpa using h2 hzero

/-- Polarization identity for the quadratic form associated to a symmetric bilinear form. -/
theorem _root_.LinearMap.BilinForm.IsSymm.toQuadraticMap_add {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {B : BilinForm R M} (hB : B.IsSymm) (x y : M) :
    B.toQuadraticMap (x + y) = B.toQuadraticMap x + B.toQuadraticMap y + 2 * B x y := by
  have hpolar : polar B.toQuadraticMap x y = 2 * B x y := by
    rw [LinearMap.BilinMap.polar_toQuadraticMap, hB.eq y x, two_mul]
  rw [← hpolar, polar]
  abel

/-- Subtraction polarization identity for the quadratic form associated to a symmetric
bilinear form. -/
theorem _root_.LinearMap.BilinForm.IsSymm.toQuadraticMap_sub {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {B : BilinForm R M} (hB : B.IsSymm) (x y : M) :
    B.toQuadraticMap (x - y) = B.toQuadraticMap x + B.toQuadraticMap y - 2 * B x y := by
  rw [sub_eq_add_neg, hB.toQuadraticMap_add, B.toQuadraticMap.map_neg, map_neg, mul_neg,
    sub_eq_add_neg]

end BilinForm

end TauCeti
