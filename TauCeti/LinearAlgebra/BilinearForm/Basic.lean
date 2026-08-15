/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Basic properties of bilinear forms and quadratic maps

This module collects foundational properties of bilinear forms and their associated
quadratic maps that complement Mathlib's basic bilinear and quadratic form APIs.

Specifically, it covers two core algebraic features of symmetric bilinear forms:

1. **Symmetric alternating forms vanish away from characteristic two**:
   A bilinear form that is both symmetric and alternating must be zero. Symmetry and
   alternation give `B x y = B y x` and `B x y = -B y x`, which implies `2 * B x y = 0`.
   Whenever `2` is regular in the scalar ring, cancelling `2` leaves `B x y = 0`.
   That regularity hypothesis covers any domain where `2 ≠ 0` as well as rings with
   zero divisors elsewhere.

2. **Polarization identities for symmetric bilinear forms**:
   For any symmetric bilinear form `B`, the associated quadratic map `B.toQuadraticMap`
   satisfies the standard additive and subtractive polarization identities expressing
   `B.toQuadraticMap (x + y)` and `B.toQuadraticMap (x - y)` in terms of `B.toQuadraticMap x`,
   `B.toQuadraticMap y`, and `2 * B x y`.

These results live together here as foundational, lightweight utilities on bilinear forms
and quadratic maps, shared by downstream consumers such as integral lattices and Lie algebra
weight modules without imposing heavier structural dependencies.

## Main results

* `TauCeti.BilinForm.eq_zero_of_isSymm_of_isAlt`: a symmetric alternating form over a ring
  in which `2` is regular is zero.
* `LinearMap.BilinForm.IsSymm.toQuadraticMap_add`: additive polarization identity for the
  quadratic map associated to a symmetric bilinear form.
* `LinearMap.BilinForm.IsSymm.toQuadraticMap_sub`: subtractive polarization identity for the
  quadratic map associated to a symmetric bilinear form.
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
theorem _root_.LinearMap.BilinForm.IsSymm.toQuadraticMap_add {R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] {B : BilinForm R M} (hB : B.IsSymm) (x y : M) :
    B.toQuadraticMap (x + y) = B.toQuadraticMap x + B.toQuadraticMap y + 2 * B x y := by
  simp only [LinearMap.BilinMap.toQuadraticMap_apply, map_add, LinearMap.add_apply]
  rw [hB.eq y x, two_mul]
  simp only [add_comm, add_left_comm]

/-- Subtraction polarization identity for the quadratic form associated to a symmetric
bilinear form. -/
theorem _root_.LinearMap.BilinForm.IsSymm.toQuadraticMap_sub {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {B : BilinForm R M} (hB : B.IsSymm) (x y : M) :
    B.toQuadraticMap (x - y) = B.toQuadraticMap x + B.toQuadraticMap y - 2 * B x y := by
  rw [sub_eq_add_neg, hB.toQuadraticMap_add, B.toQuadraticMap.map_neg, map_neg, mul_neg,
    sub_eq_add_neg]

end BilinForm

end TauCeti
