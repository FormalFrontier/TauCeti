/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.RingTheory.IsTensorProduct
public import TauCeti.LinearAlgebra.IntegralLattice.Basic
public import TauCeti.LinearAlgebra.Submodule.IsLattice

/-!
# Rationalizing an integral lattice form

Let `L` be a full integral lattice in a rational vector space `V`. The inclusion
`L →ₗ[ℤ] V` exhibits `V` as the scalar extension `ℚ ⊗[ℤ] L`. This file records that
canonical base-change equivalence and proves that it identifies the scalar extension of
`L.integralForm` with the ambient rational form `L.form`.

Mathlib already supplies `LinearMap.BilinForm.baseChange`; the point here is to connect that
abstract tensor-product construction to the embedded-carrier model used by integral lattices.
In particular, no choice of carrier basis appears in the resulting equivalence or its
characteristic equations.

## Main results

* `TauCeti.IntegralLattice.isBaseChange_subtype`: the carrier inclusion is a base change from
  `ℤ` to `ℚ`.
* `TauCeti.IntegralLattice.rationalizationEquiv`: the canonical equivalence
  `ℚ ⊗[ℤ] L ≃ₗ[ℚ] V`.
* `TauCeti.IntegralLattice.form_rationalizationEquiv`: the base-changed integral form equals
  the ambient form under the equivalence.
* `TauCeti.IntegralLattice.rationalizationIsometry`: this equivalence is an isometry from
  `L.integralForm.baseChange ℚ` to `L.form`.

## References

This is the rational-extension target in Layer 1 of
`TauCetiRoadmap/IntegralLattices/README.md`. See W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

open Module TensorProduct

namespace TauCeti

namespace IsBaseChange

variable {R : Type*} {A : Type*} {M : Type*} {N : Type*}
variable [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module A N] [Module R N] [IsScalarTower R A N]
variable {f : M →ₗ[R] N} (h : IsBaseChange A f)

/-- Evaluating a bilinear form on base-changed vectors via an `IsBaseChange` equivalence
identifies it with the canonical base change of the original bilinear form. -/
theorem bilinForm_baseChange (B' : LinearMap.BilinForm R M) (B : LinearMap.BilinForm A N)
    (hB : ∀ x y : M, B (f x) (f y) = algebraMap R A (B' x y)) (x y : A ⊗[R] M) :
    B (h.equiv x) (h.equiv y) = B'.baseChange A x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [map_add, LinearMap.add_apply, hx₁, hx₂]
  | tmul a m =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ hy₁ hy₂ =>
      simp only [map_add, hy₁, hy₂]
    | tmul a' m' =>
      simp only [IsBaseChange.equiv_tmul, LinearMap.BilinForm.smul_left,
        LinearMap.BilinForm.smul_right, LinearMap.BilinForm.baseChange_tmul,
        hB, Algebra.smul_def]
      ring

end IsBaseChange

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

namespace IntegralLattice

/-- The inclusion of the carrier of a full integral lattice into its ambient rational vector
space exhibits that space as base change from `ℤ` to `ℚ`. -/
theorem isBaseChange_subtype (L : IntegralLattice V) :
    IsBaseChange ℚ L.carrier.subtype :=
  Submodule.IsLattice.isBaseChange_subtype L.carrier

/-- The canonical rationalization equivalence from the abstract scalar extension of the carrier
to the ambient rational vector space. -/
noncomputable def rationalizationEquiv (L : IntegralLattice V) :
    ℚ ⊗[ℤ] L ≃ₗ[ℚ] V :=
  L.isBaseChange_subtype.equiv

/-- The rationalization equivalence sends a pure tensor to scalar multiplication of the embedded
lattice vector. This equation characterizes the equivalence. -/
@[simp]
theorem rationalizationEquiv_tmul (L : IntegralLattice V) (q : ℚ) (x : L) :
    L.rationalizationEquiv (q ⊗ₜ[ℤ] x) = q • (x : V) :=
  L.isBaseChange_subtype.equiv_tmul q x

/-- The rationalization equivalence sends a unit pure tensor to the embedded lattice vector. -/
theorem rationalizationEquiv_one_tmul (L : IntegralLattice V) (x : L) :
    L.rationalizationEquiv (1 ⊗ₜ[ℤ] x) = (x : V) := by
  simp

/-- The inverse rationalization equivalence sends an embedded lattice vector to the corresponding
unit pure tensor. -/
@[simp]
theorem rationalizationEquiv_symm_coe (L : IntegralLattice V) (x : L) :
    L.rationalizationEquiv.symm (x : V) = 1 ⊗ₜ[ℤ] x :=
  L.isBaseChange_subtype.equiv_symm_apply x

/-- The scalar extension of the carrier's integral form is the ambient rational form under the
canonical rationalization equivalence. -/
@[simp]
theorem form_rationalizationEquiv (L : IntegralLattice V) (x y : ℚ ⊗[ℤ] L) :
    L.form (L.rationalizationEquiv x) (L.rationalizationEquiv y) =
      L.integralForm.baseChange ℚ x y :=
  IsBaseChange.bilinForm_baseChange L.isBaseChange_subtype L.integralForm L.form
    (fun x y ↦ (L.integralForm_cast x y).symm) x y

/-- The canonical rationalization is an isometry from the base-changed integral form to the
ambient rational form. -/
noncomputable def rationalizationIsometry (L : IntegralLattice V) :
    (L.integralForm.baseChange ℚ).IsometryEquiv L.form where
  toLinearEquiv := L.rationalizationEquiv
  map_app' := L.form_rationalizationEquiv

/-- Evaluating the rationalization isometry on a tensor product element coincides with the
rationalization equivalence. -/
-- BilinForm.IsometryEquiv has no toLinearEquiv lemma; definition unfolding is canonical.
@[simp]
theorem rationalizationIsometry_apply (L : IntegralLattice V) (x : ℚ ⊗[ℤ] L) :
    L.rationalizationIsometry x = L.rationalizationEquiv x := by
  rfl

/-- Evaluating the inverse rationalization isometry coincides with the inverse rationalization
equivalence. -/
-- BilinForm.IsometryEquiv has no symm_toLinearEquiv lemma; definition unfolding is canonical.
@[simp]
theorem rationalizationIsometry_symm_apply (L : IntegralLattice V) (y : V) :
    L.rationalizationIsometry.symm y = L.rationalizationEquiv.symm y := by
  rfl

end IntegralLattice

end TauCeti
