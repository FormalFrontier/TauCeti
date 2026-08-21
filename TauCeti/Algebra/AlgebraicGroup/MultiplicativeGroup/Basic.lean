/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints

/-!
# The multiplicative group example

This file records the functor-of-points calculation for the multiplicative group. Mathlib
already equips the Laurent polynomial algebra `R[T;T⁻¹]` with its Hopf algebra structure,
where `T n` is group-like and the antipode sends `T n` to `T (-n)`. We package the resulting
`R`-points of `Spec R[T;T⁻¹]`: for every commutative `R`-algebra `A`, convolution points
`R[T;T⁻¹] →ₐ[R] A` are multiplicatively equivalent to units of `A`.

This is a worked-example check for the reductive-groups roadmap Layer 0 target "R-points as a
group" and the listed example `𝔾_m`.

## Main declarations

* `TauCeti.MultiplicativeGroup.point`: the point corresponding to a unit of `A`.
* `TauCeti.MultiplicativeGroup.pointEquiv`: algebra maps from `R[T;T⁻¹]` to `A` are
  equivalent to units of `A`.
* `TauCeti.MultiplicativeGroup.pointsMulEquiv`: the same equivalence as a multiplicative
  equivalence from the convolution group to `Aˣ`.
* `TauCeti.MultiplicativeGroup.pointsMulEquiv_mapValue`: the points equivalence is natural
  in the value algebra.

## References

The Hopf algebra structure and Laurent polynomial evaluation API are from Mathlib's
`Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra` and `Mathlib.Algebra.Polynomial.Laurent`,
building on Amelia Livingston's monoid-algebra Hopf algebra formalization.
-/

public section

open WithConv
open scoped LaurentPolynomial

namespace TauCeti

universe u v w

namespace MultiplicativeGroup

variable {R : Type u} {A : Type v}
variable [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- The `R[T;T⁻¹]`-point of the multiplicative group corresponding to a unit of the value
algebra. It sends `T n` to `u ^ n`. -/
@[expose] noncomputable def point (u : Aˣ) : R[T;T⁻¹] →ₐ[R] A :=
  { LaurentPolynomial.eval₂ (algebraMap R A) u with
    commutes' := LaurentPolynomial.eval₂_C (algebraMap R A) u }

/-- The point associated to a unit sends `T n` to `u ^ n`. -/
@[simp]
theorem point_T (u : Aˣ) (n : ℤ) :
    point (R := R) (A := A) u (LaurentPolynomial.T n) = (u ^ n).val :=
  LaurentPolynomial.eval₂_T (algebraMap R A) u n

/-- The point associated to a unit sends constants through the algebra map. -/
@[simp]
theorem point_C (u : Aˣ) (r : R) :
    point (R := R) (A := A) u (LaurentPolynomial.C r) = algebraMap R A r :=
  LaurentPolynomial.eval₂_C (algebraMap R A) u r

/-- The unit of `A` obtained by evaluating an `R[T;T⁻¹]`-point at `T`. -/
@[expose] noncomputable def unitOfPoint (f : R[T;T⁻¹] →ₐ[R] A) : Aˣ where
  val := f (LaurentPolynomial.T 1)
  inv := f (LaurentPolynomial.T (-1))
  val_inv := by
    rw [← map_mul, ← LaurentPolynomial.T_add]
    norm_num
  inv_val := by
    rw [← map_mul, ← LaurentPolynomial.T_add]
    norm_num

/-- Evaluating `unitOfPoint f` as an element of `A` gives the value of `f` on `T`. -/
@[simp]
theorem unitOfPoint_val (f : R[T;T⁻¹] →ₐ[R] A) :
    (unitOfPoint f : A) = f (LaurentPolynomial.T 1) :=
  rfl

/-- The inverse of `unitOfPoint f` is the value of `f` on `T⁻¹`. -/
@[simp]
theorem unitOfPoint_inv (f : R[T;T⁻¹] →ₐ[R] A) :
    ↑(unitOfPoint f)⁻¹ = f (LaurentPolynomial.T (-1)) :=
  rfl

/-- The point-to-unit construction inverts `point`. -/
@[simp]
theorem unitOfPoint_point (u : Aˣ) : unitOfPoint (point (R := R) (A := A) u) = u := by
  ext
  simp

private theorem point_unitOfPoint_single (f : R[T;T⁻¹] →ₐ[R] A) (n : ℤ) :
    (unitOfPoint f ^ n).val = f (LaurentPolynomial.T n) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
      rw [zpow_add, zpow_one, Units.val_mul, ih,
        unitOfPoint_val, ← map_mul, ← LaurentPolynomial.T_add]
  | pred n ih =>
      have ih' : ↑((unitOfPoint f ^ (n : ℤ))⁻¹) = f (LaurentPolynomial.T (-(n : ℤ))) := by
        simpa [zpow_neg] using ih
      have hinv : ↑(unitOfPoint f ^ (-1 : ℤ)) = f (LaurentPolynomial.T (-1)) := by
        simp [zpow_neg, unitOfPoint_inv (R := R) (A := A) f]
      rw [sub_eq_add_neg, zpow_add, zpow_neg, Units.val_mul, ih', hinv, ← map_mul,
        ← LaurentPolynomial.T_add]

/-- The unit-to-point construction inverts `unitOfPoint`. -/
@[simp]
theorem point_unitOfPoint (f : R[T;T⁻¹] →ₐ[R] A) :
    point (R := R) (A := A) (unitOfPoint f) = f := by
  apply AddMonoidAlgebra.algHom_ext
  · intro n
    -- `AddMonoidAlgebra.single n 1` is `LaurentPolynomial.T n`; rewrite via the public lemma
    -- `single_eq_C_mul_T` rather than relying on the bare definitional unfolding of `T`.
    rw [LaurentPolynomial.single_eq_C_mul_T, map_one, one_mul, point_T]
    exact point_unitOfPoint_single (R := R) (A := A) f n
  · ext

/-- Algebra maps out of `R[T;T⁻¹]` are the same as units of the value algebra. -/
@[expose] noncomputable def pointEquiv : (R[T;T⁻¹] →ₐ[R] A) ≃ Aˣ where
  toFun := unitOfPoint
  invFun := point (R := R) (A := A)
  left_inv := point_unitOfPoint
  right_inv := unitOfPoint_point

/-- The equivalence sends a point to its value on `T`. -/
@[simp]
theorem pointEquiv_apply (f : R[T;T⁻¹] →ₐ[R] A) :
    pointEquiv (R := R) (A := A) f = unitOfPoint f :=
  rfl

/-- The inverse equivalence sends a unit to the corresponding evaluation map. -/
@[simp]
theorem pointEquiv_symm_apply (u : Aˣ) :
    (pointEquiv (R := R) (A := A)).symm u = point (R := R) (A := A) u :=
  rfl

/-- The functor of points of the multiplicative group is the unit group of the value algebra.

The source is the convolution group of `R`-algebra maps out of `R[T;T⁻¹]`; the target is the
ordinary unit group of `A`. -/
@[expose] noncomputable def pointsMulEquiv : WithConv (R[T;T⁻¹] →ₐ[R] A) ≃* Aˣ where
  toFun f := unitOfPoint f.ofConv
  invFun u := toConv (point (R := R) (A := A) u)
  left_inv f := by
    exact congrArg toConv (point_unitOfPoint (R := R) (A := A) f.ofConv)
  right_inv := unitOfPoint_point
  map_mul' f g := by
    ext
    rw [unitOfPoint_val, Units.val_mul]
    simp only [unitOfPoint_val]
    rw [AlgHom.convMul_apply]
    simp

/-- The multiplicative equivalence sends a convolution point to its value on `T`. -/
@[simp]
theorem pointsMulEquiv_apply (f : WithConv (R[T;T⁻¹] →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) f = unitOfPoint f.ofConv :=
  rfl

/-- The inverse multiplicative equivalence sends a unit to the corresponding point. -/
@[simp]
theorem pointsMulEquiv_symm_apply (u : Aˣ) :
    (pointsMulEquiv (R := R) (A := A)).symm u = toConv (point (R := R) (A := A) u) :=
  rfl

section Naturality

variable {B : Type w} [CommSemiring B] [Algebra R B]

/-- Reading a Laurent-polynomial point as a unit is natural under post-composition of algebra
maps. -/
@[simp]
theorem unitOfPoint_comp (φ : A →ₐ[R] B) (f : R[T;T⁻¹] →ₐ[R] A) :
    unitOfPoint (φ.comp f) = Units.map φ.toMonoidHom (unitOfPoint f) := by
  ext
  simp [unitOfPoint_val, Units.coe_map]

/-- The plain Laurent-polynomial points equivalence is natural in the value algebra. -/
theorem pointEquiv_comp (φ : A →ₐ[R] B) (f : R[T;T⁻¹] →ₐ[R] A) :
    pointEquiv (R := R) (A := B) (φ.comp f) =
      Units.map φ.toMonoidHom (pointEquiv (R := R) (A := A) f) :=
  by
    rw [pointEquiv_apply, pointEquiv_apply]
    exact unitOfPoint_comp φ f

/-- Naturality of the inverse plain points equivalence in the value algebra. -/
@[simp]
theorem comp_point (φ : A →ₐ[R] B) (u : Aˣ) :
    φ.comp (point (R := R) (A := A) u) =
      point (R := R) (A := B) (Units.map φ.toMonoidHom u) := by
  apply (pointEquiv (R := R) (A := B)).injective
  rw [pointEquiv_comp]
  simp

/-- Reading a multiplicative-group point as a unit is natural in the value algebra:
post-composing the point with an `R`-algebra map applies the induced map on unit groups. -/
theorem unitOfPoint_mapValue (φ : A →ₐ[R] B)
    (f : WithConv (R[T;T⁻¹] →ₐ[R] A)) :
    unitOfPoint ((AlgHom.mapValue (H := R[T;T⁻¹]) φ f).ofConv) =
      Units.map φ.toMonoidHom (unitOfPoint f.ofConv) := by
  rw [AlgHom.mapValue_apply, ofConv_toConv]
  exact unitOfPoint_comp φ f.ofConv

/-- The `𝔾ₘ` points equivalence is natural in the value algebra. -/
theorem pointsMulEquiv_mapValue (φ : A →ₐ[R] B)
    (f : WithConv (R[T;T⁻¹] →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := B)
        (AlgHom.mapValue (H := R[T;T⁻¹]) φ f) =
      Units.map φ.toMonoidHom (pointsMulEquiv f) :=
  by
    rw [pointsMulEquiv_apply, pointsMulEquiv_apply]
    exact unitOfPoint_mapValue φ f

/-- Naturality of the inverse `𝔾ₘ` points equivalence in the value algebra. -/
theorem mapValue_pointsMulEquiv_symm_apply (φ : A →ₐ[R] B) (u : Aˣ) :
    AlgHom.mapValue (H := R[T;T⁻¹]) φ
        ((pointsMulEquiv (R := R) (A := A)).symm u) =
      (pointsMulEquiv (R := R) (A := B)).symm (Units.map φ.toMonoidHom u) := by
  apply (pointsMulEquiv (R := R) (A := B)).injective
  rw [pointsMulEquiv_mapValue]
  rw [(pointsMulEquiv (R := R) (A := A)).apply_symm_apply u]
  exact ((pointsMulEquiv (R := R) (A := B)).apply_symm_apply
    (Units.map φ.toMonoidHom u)).symm

end Naturality

end MultiplicativeGroup

end TauCeti
