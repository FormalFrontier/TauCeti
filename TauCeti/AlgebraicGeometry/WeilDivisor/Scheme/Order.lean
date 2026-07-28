/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Basic
public import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# Orders of rational functions at codimension-one points

For a locally Noetherian integral scheme `X`, Mathlib defines the order of vanishing
`Scheme.ord f x : ℤ` of a rational function at a point. This file packages its restriction to
nonzero rational functions at a codimension-one point as an additive homomorphism

`SchemeWeilDivisor.orderAt x : Additive X.functionFieldˣ →+ ℤ`.

This is the local algebraic input for the scheme-theoretic principal-divisor map. Constructing
that map also requires the separate global theorem that a nonzero rational function has nonzero
order at only finitely many codimension-one points; no finiteness assumption is hidden here.

The construction advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, the
"principal divisors" part of "Divisors on a curve". It reuses Mathlib's
`AlgebraicGeometry.Scheme.ord`, `ord_mul`, and `ord_eq_unzero_ordHom`; no external
formalization is vendored.
-/

public section

open AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

noncomputable section

/-- The order of a nonzero rational function at a codimension-one point, as an additive
homomorphism from the additive form of the unit group of the function field. -/
noncomputable def orderAt (x : CodimensionOnePoint X) :
    Additive (X.functionFieldˣ) →+ ℤ where
  toFun f := X.ord ((Additive.toMul f : X.functionFieldˣ) : X.functionField) x
  map_zero' := by
    have h := X.ord_mul (x := x.1)
      (Units.ne_zero (1 : X.functionFieldˣ)) (Units.ne_zero (1 : X.functionFieldˣ))
    have h' : X.ord (1 : X.functionField) x =
        X.ord (1 : X.functionField) x + X.ord (1 : X.functionField) x := by
      simpa only [Units.val_one, one_mul] using h
    have hz : X.ord (1 : X.functionField) x = 0 := by
      apply add_left_cancel (a := X.ord (1 : X.functionField) x)
      simpa only [add_zero] using h'.symm
    simpa only [toMul_zero, Units.val_one] using hz
  map_add' f g := by
    simp only [toMul_add]
    exact X.ord_mul (x := x.1)
      (Units.ne_zero (Additive.toMul f)) (Units.ne_zero (Additive.toMul g))

/-- Evaluating `orderAt` gives Mathlib's integer-valued order of vanishing. -/
@[simp]
lemma orderAt_apply (x : CodimensionOnePoint X) (f : Additive X.functionFieldˣ) :
    orderAt x f = X.ord ((Additive.toMul f : X.functionFieldˣ) : X.functionField) x :=
  (rfl)

/-- The constant rational function `1` has order zero. -/
@[simp]
lemma orderAt_ofMul_one (x : CodimensionOnePoint X) :
    orderAt x (Additive.ofMul (1 : X.functionFieldˣ)) = 0 :=
  map_zero (orderAt x)

/-- Taking the inverse of a nonzero rational function negates its order. -/
@[simp]
lemma orderAt_ofMul_inv (x : CodimensionOnePoint X) (f : X.functionFieldˣ) :
    orderAt x (Additive.ofMul f⁻¹) = -orderAt x (Additive.ofMul f) :=
  map_neg (orderAt x) (Additive.ofMul f)

/-- The order homomorphism is the additive form of Mathlib's `ordHom`, after removing the
nonzero wrapper from its value. -/
lemma orderAt_eq_unzero_ordHom (x : CodimensionOnePoint X)
    (f : Additive X.functionFieldˣ) :
    orderAt x f =
      (WithZero.unzero
        ((map_ne_zero (X.ordHom x x.property)).mpr
          (Units.ne_zero (Additive.toMul f : X.functionFieldˣ)))).toAdd := by
  rw [orderAt_apply, X.ord_eq_unzero_ordHom x.property
    (Units.ne_zero (Additive.toMul f : X.functionFieldˣ))]

/-- The order at `x` equals `n` exactly when Mathlib's multiplicative order homomorphism has
value `Multiplicative.ofAdd n`. -/
lemma orderAt_eq_iff (x : CodimensionOnePoint X) (f : Additive X.functionFieldˣ) (n : ℤ) :
    orderAt x f = n ↔
      X.ordHom x x.property ((Additive.toMul f : X.functionFieldˣ) : X.functionField) =
        Multiplicative.ofAdd n := by
  rw [orderAt_apply]
  exact X.ord_eq_iff x.property (Units.ne_zero (Additive.toMul f : X.functionFieldˣ))

/-- The order at `x` vanishes exactly when Mathlib's multiplicative order homomorphism has
value one. -/
lemma orderAt_eq_zero_iff (x : CodimensionOnePoint X) (f : Additive X.functionFieldˣ) :
    orderAt x f = 0 ↔
      X.ordHom x x.property ((Additive.toMul f : X.functionFieldˣ) : X.functionField) = 1 := by
  simpa only [ofAdd_zero, WithZero.coe_one] using orderAt_eq_iff x f 0

/-- A codimension-one point belongs to the order support of a rational function exactly when
Mathlib's multiplicative order homomorphism is nontrivial there. -/
lemma orderAt_ne_zero_iff (x : CodimensionOnePoint X) (f : Additive X.functionFieldˣ) :
    orderAt x f ≠ 0 ↔
      X.ordHom x x.property ((Additive.toMul f : X.functionFieldˣ) : X.functionField) ≠ 1 :=
  not_congr (orderAt_eq_zero_iff x f)

/-- A rational function represented by a unit on an open neighbourhood of `x` has order zero
at `x`. -/
lemma orderAt_eq_zero_of_isUnit {U : X.Opens} [Nonempty U] {f : Γ(X, U)}
    (hf : IsUnit f) (x : CodimensionOnePoint X) (hx : x.1 ∈ U) :
    orderAt x
      (Additive.ofMul
        (Units.mk0 (X.germToFunctionField U f)
          (by
            intro h
            apply IsUnit.ne_zero hf
            apply X.germToFunctionField_injective U
            simpa using h))) = 0 := by
  rw [orderAt_apply]
  exact X.ord_of_isUnit hf hx

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
