/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.RingTheory.IsTensorProduct
public import TauCeti.LinearAlgebra.IntegralLattice.Basic

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

* `TauCeti.Submodule.IsLattice.isBaseChange_subtype`: the inclusion of a full lattice submodule
  is a base change from `ℤ` to `ℚ`.
* `TauCeti.IntegralLattice.isBaseChange_subtype`: the carrier inclusion is a base change from
  `ℤ` to `ℚ`.
* `TauCeti.IntegralLattice.rationalizationEquiv`: the canonical equivalence
  `ℚ ⊗[ℤ] L ≃ₗ[ℚ] V`.
* `TauCeti.IntegralLattice.rationalizationIsometry`: this equivalence is an isometry from
  `L.integralForm.baseChange ℚ` to `L.form`.
* `TauCeti.IntegralLattice.rationalizationIsometry_apply`: evaluating the rationalization isometry
  coincides with the rationalization equivalence.

## References

This is the rational-extension target in Layer 1 of
`TauCetiRoadmap/IntegralLattices/README.md`. See W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

open Module TensorProduct

namespace TauCeti

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

namespace Submodule

namespace IsLattice

/-- The inclusion of a full lattice submodule into its ambient rational vector space exhibits that
space as base change from `ℤ` to `ℚ`. -/
theorem isBaseChange_subtype (S : Submodule ℤ V) [S.IsLattice ℚ] :
    IsBaseChange ℚ S.subtype := by
  let b := Module.Free.chooseBasis ℤ S
  let e : ℚ ⊗[ℤ] S ≃ₗ[ℚ] V :=
    (b.baseChange ℚ).equiv (b.extendOfIsLattice ℚ) (Equiv.refl _)
  have hmap : (e.toLinearMap.restrictScalars ℤ).comp (TensorProduct.mk ℤ ℚ S 1) =
      S.subtype := by
    apply b.ext
    intro i
    -- The two wrapper coercions prevent the basis simp lemmas from seeing the pure tensor.
    change e (1 ⊗ₜ[ℤ] b i) = (b i : V)
    rw [← Module.Basis.baseChange_apply ℚ b i, Basis.equiv_apply,
      Basis.extendOfIsLattice_apply, Equiv.refl_apply]
  exact IsBaseChange.of_equiv e fun x ↦ DFunLike.congr_fun hmap x

end IsLattice

end Submodule

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
      L.integralForm.baseChange ℚ x y := by
  let b := (Module.Free.chooseBasis ℤ L).baseChange ℚ
  suffices L.form.comp L.rationalizationEquiv.toLinearMap
      L.rationalizationEquiv.toLinearMap = L.integralForm.baseChange ℚ by
    exact LinearMap.BilinForm.congr_fun this x y
  apply LinearMap.BilinForm.ext_basis b
  intro i j
  have hb (k) : b k = 1 ⊗ₜ[ℤ] Module.Free.chooseBasis ℤ L k :=
    Module.Basis.baseChange_apply ℚ _ _
  rw [hb i, hb j, LinearMap.BilinForm.comp_apply]
  have hi : L.rationalizationEquiv (1 ⊗ₜ[ℤ] Module.Free.chooseBasis ℤ L i) =
      (Module.Free.chooseBasis ℤ L i : V) := by
    simpa only [one_smul] using
      L.rationalizationEquiv_tmul 1 (Module.Free.chooseBasis ℤ L i)
  have hj : L.rationalizationEquiv (1 ⊗ₜ[ℤ] Module.Free.chooseBasis ℤ L j) =
      (Module.Free.chooseBasis ℤ L j : V) := by
    simpa only [one_smul] using
      L.rationalizationEquiv_tmul 1 (Module.Free.chooseBasis ℤ L j)
  calc
    _ = L.form (Module.Free.chooseBasis ℤ L i)
        (L.rationalizationEquiv (1 ⊗ₜ[ℤ] Module.Free.chooseBasis ℤ L j)) :=
      congrArg (fun z : V ↦ L.form z
        (L.rationalizationEquiv (1 ⊗ₜ[ℤ] Module.Free.chooseBasis ℤ L j))) hi
    _ = L.form (Module.Free.chooseBasis ℤ L i) (Module.Free.chooseBasis ℤ L j) :=
      congrArg (L.form (Module.Free.chooseBasis ℤ L i)) hj
    _ = (L.integralForm (Module.Free.chooseBasis ℤ L i)
        (Module.Free.chooseBasis ℤ L j) : ℚ) := (L.integralForm_cast _ _).symm
    _ = _ := by
      simp only [LinearMap.BilinForm.baseChange_tmul, mul_one, zsmul_eq_mul]

/-- The canonical rationalization is an isometry from the base-changed integral form to the
ambient rational form. -/
noncomputable def rationalizationIsometry (L : IntegralLattice V) :
    (L.integralForm.baseChange ℚ).IsometryEquiv L.form where
  toLinearEquiv := L.rationalizationEquiv
  map_app' := L.form_rationalizationEquiv

/-- Evaluating the rationalization isometry on a tensor product element coincides with the
rationalization equivalence. -/
@[simp]
theorem rationalizationIsometry_apply (L : IntegralLattice V) (x : ℚ ⊗[ℤ] L) :
    L.rationalizationIsometry x = L.rationalizationEquiv x := by
  rfl

/-- Evaluating the ambient form on rational multiples of lattice vectors recovers the scalar
extension formula for the integral form. -/
theorem form_smul_coe (L : IntegralLattice V) (q r : ℚ) (x y : L) :
    L.form (q • (x : V)) (r • (y : V)) = q * r * (L.integralForm x y : ℚ) := by
  rw [← rationalizationEquiv_tmul, ← rationalizationEquiv_tmul,
    form_rationalizationEquiv, LinearMap.BilinForm.baseChange_tmul, zsmul_eq_mul]
  ring

end IntegralLattice

end TauCeti
