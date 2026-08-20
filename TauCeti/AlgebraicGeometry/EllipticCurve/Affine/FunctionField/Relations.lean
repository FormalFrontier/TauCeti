/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Finrank

/-!
# Relations in the function field of a Weierstrass curve

This file records two general facts about the function field `F(W)` of an affine Weierstrass
curve. The Weierstrass equation holds after mapping the coordinates into `F(W)`, and every
function is a rational function of `x` plus another rational function of `x` times `y`.

## Main results

* `WeierstrassCurve.Affine.mk_Y_mul_add_eq`: the Weierstrass equation, read in the function field.
* `WeierstrassCurve.Affine.exists_ratFunc_add_mul_mk_Y`: every function is `A + B y` with `A` and
  `B` rational functions of `x`.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0** (the function field, places, and divisors).
These are general function-field relations used to characterize the place at infinity.
-/

public section

open Polynomial WeierstrassCurve

open scoped Polynomial.Bivariate RatFunc

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F]

section Relation

variable (W : WeierstrassCurve.Affine F)

/-- **The Weierstrass equation, in the function field**:
`y * (y + (a₁X + a₃)) = X³ + a₂X² + a₄X + a₆`. Grouping the two left-hand terms as a product is
useful when comparing the pole orders of `x` and `y`. -/
theorem mk_Y_mul_add_eq :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) *
        (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)
          + algebraMap F[X] W.FunctionField (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃))
      = algebraMap F[X] W.FunctionField
          (Polynomial.X ^ 3 + Polynomial.C W.a₂ * Polynomial.X ^ 2
            + Polynomial.C W.a₄ * Polynomial.X + Polynomial.C W.a₆) := by
  have hY : CoordinateRing.mk W Y * (CoordinateRing.mk W Y
      + algebraMap F[X] W.CoordinateRing (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃))
      = algebraMap F[X] W.CoordinateRing (Polynomial.X ^ 3 + Polynomial.C W.a₂ * Polynomial.X ^ 2
          + Polynomial.C W.a₄ * Polynomial.X + Polynomial.C W.a₆) := by
    rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_C, ← map_add, ← map_mul]
    exact AdjoinRoot.mk_eq_mk.mpr ⟨1, by rw [polynomial]; ring1⟩
  rw [IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField,
    IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField, ← map_add, ← map_mul, hY]

end Relation

section Decompose

variable (W : WeierstrassCurve.Affine F)

/-- **Every function is `A + B y` with `A` and `B` rational functions of `x`.** Clearing a
polynomial denominator reduces to the coordinate ring, where Mathlib's basis `{1, Y}` supplies the
decomposition. -/
theorem exists_ratFunc_add_mul_mk_Y (z : W.FunctionField) :
    ∃ A B : RatFunc F, algebraMap (RatFunc F) W.FunctionField A
      + algebraMap (RatFunc F) W.FunctionField B *
        algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) = z := by
  -- Write `z` over a polynomial denominator, and decompose its numerator on the basis `{1, Y}`.
  obtain ⟨⟨u, ⟨-, p, hp, rfl⟩⟩, h⟩ := IsLocalization.surj
    (Algebra.algebraMapSubmonoid W.CoordinateRing (nonZeroDivisors F[X])) z
  obtain ⟨a, b, rfl⟩ := CoordinateRing.exists_smul_basis_eq u
  have hp0 : algebraMap F[X] W.FunctionField p ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective F[X] W.FunctionField)).2
      (nonZeroDivisors.ne_zero hp)
  rw [← IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField, Algebra.smul_def,
    Algebra.smul_def, map_add, map_mul, map_mul, map_one, mul_one,
    ← IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField,
    ← IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField] at h
  refine ⟨algebraMap F[X] (RatFunc F) a / algebraMap F[X] (RatFunc F) p,
    algebraMap F[X] (RatFunc F) b / algebraMap F[X] (RatFunc F) p, ?_⟩
  rw [map_div₀, map_div₀, ← IsScalarTower.algebraMap_apply F[X] (RatFunc F) W.FunctionField,
    ← IsScalarTower.algebraMap_apply F[X] (RatFunc F) W.FunctionField,
    ← IsScalarTower.algebraMap_apply F[X] (RatFunc F) W.FunctionField]
  field_simp
  linear_combination -h

end Decompose

end WeierstrassCurve.Affine

end
