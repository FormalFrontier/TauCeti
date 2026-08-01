/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.LinearAlgebra.Coevaluation
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Dual
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Monoidal

/-!
# Right rigidity of finite-dimensional comodules

Let `H` be a Hopf algebra over a field `k`. This file equips the monoidal category
`FGComoduleCat.{u,v,u} k H` with right duals. The right dual of a finite-dimensional
comodule is its antipode-twisted linear dual; evaluation and coevaluation are the
ordinary finite-dimensional linear maps, proved colinear using the two antipode
identities.

No commutativity or finite-dimensionality hypothesis is imposed on `H`, and the
antipode need not be bijective.

## Main declarations

* `TauCeti.FGComoduleCat.dualEvaluation`: evaluation as a finite-comodule morphism.
* `TauCeti.FGComoduleCat.dualCoevaluation`: coevaluation as a finite-comodule morphism.
* `TauCeti.FGComoduleCat.instRightRigidCategory`: finite-dimensional comodules form a
  right rigid monoidal category.

## References

See Etingof--Gelaki--Nikshych--Ostrik, *Tensor Categories*, Definition 2.10.1 and
Remark 5.3.8; Milne, *Algebraic Groups* (2017), Section 9.26; and Humphreys,
*Linear Algebraic Groups*, Section 8.2.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace TauCeti.FGComoduleCat

universe u v

variable (k : Type u) [Field k]
variable (H : Type v) [Semiring H] [HopfAlgebra k H]

attribute [local instance] Comodule.dual Comodule.tensor

private theorem coact_eq_sum_basis_matrixCoefficient
    {M : FGComoduleCat.{u, v, u} k H}
    (b : Module.Basis (Module.Basis.ofVectorSpaceIndex k M) k M) (m : M) :
    Comodule.coact (R := k) (C := H) (M := M) m =
      ∑ i, b i ⊗ₜ[k]
        Comodule.matrixCoefficient (R := k) (C := H) (b.coord i) m := by
  classical
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := H) b
  calc
    Comodule.coact (R := k) (C := H) (M := M) m =
        e.symm (e (Comodule.coact (R := k) (C := H) (M := M) m)) :=
      ((e.symm_apply_apply _).symm)
    _ = (e (Comodule.coact (R := k) (C := H) (M := M) m)).sum
        fun i h ↦ b i ⊗ₜ[k] h :=
      TensorProduct.equivFinsuppOfBasisLeft_symm_apply b _
    _ = ∑ i, b i ⊗ₜ[k]
        (e (Comodule.coact (R := k) (C := H) (M := M) m)) i :=
      Finsupp.sum_fintype _ _ (by simp)
    _ = ∑ i, b i ⊗ₜ[k]
        Comodule.matrixCoefficient (R := k) (C := H) (b.coord i) m := by
      congr 1
      funext i
      rw [TensorProduct.equivFinsuppOfBasisLeft_apply]
      rfl

private theorem dualCoact_coord_eq_sum
    {M : FGComoduleCat.{u, v, u} k H}
    (b : Module.Basis (Module.Basis.ofVectorSpaceIndex k M) k M)
    (i : Module.Basis.ofVectorSpaceIndex k M) :
    Comodule.dualCoact (R := k) (H := H) (M := M) (b.coord i) =
      ∑ j, b.coord j ⊗ₜ[k]
        HopfAlgebra.antipode k
          (Comodule.matrixCoefficient (R := k) (C := H) (b.coord i) (b j)) := by
  classical
  apply (dualTensorHom_bijective (R := k) (M := M) (N := H)).1
  apply b.ext
  intro j
  rw [Comodule.dualTensorHom_dualCoact_apply]
  simp only [map_sum, LinearMap.sum_apply, dualTensorHom_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self_apply]
  simp

private theorem lid_map_contractLeft_tensorCombine
    {M : FGComoduleCat.{u, v, u} k H}
    (x : Module.Dual k M ⊗[k] H) (y : M ⊗[k] H) :
    TensorProduct.lid k H
        (TensorProduct.map (contractLeft k M) (LinearMap.id : H →ₗ[k] H)
          (Comodule.tensorCombine (R := k) (C := H) (M := Module.Dual k M) (N := M)
            (x ⊗ₜ[k] y))) =
      LinearMap.mul' k H
        (TensorProduct.map (dualTensorHom k M H x) (LinearMap.id : H →ₗ[k] H) y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x z hx hz =>
      simpa only [TensorProduct.add_tmul, map_add, TensorProduct.map_add_left,
        LinearMap.add_apply] using congrArg₂ (· + ·) hx hz
  | tmul φ a =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz =>
          simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hy hz
      | tmul m b =>
          simp only [Comodule.tensorCombine_tmul_tmul, TensorProduct.map_tmul,
            LinearMap.id_apply, contractLeft_apply, TensorProduct.lid_tmul,
            dualTensorHom_apply, LinearMap.mul'_apply]
          exact (smul_mul_assoc (φ m) a b).symm

/-- Evaluation of the antipode-twisted dual against a finite-dimensional comodule, as a
finite-comodule morphism. -/
@[expose]
noncomputable def dualEvaluation (M : FGComoduleCat.{u, v, u} k H) :
    dual k H M ⊗ M ⟶ 𝟙_ (FGComoduleCat.{u, v, u} k H) :=
  letI : Comodule k H k := Comodule.trivial (R := k) (C := H) (M := k)
  ofHom (R := k) (C := H) {
    toLinearMap := contractLeft k M
    map_coact := by
      apply TensorProduct.ext'
      intro φ m
      simp only [LinearMap.comp_apply, Comodule.tensor_coact, Comodule.tensorCoact_tmul,
        dual_coact, Comodule.trivial_coact_apply]
      apply (TensorProduct.lid k H).injective
      calc
        _ = LinearMap.mul' k H
            (TensorProduct.map
              (dualTensorHom k M H
                (Comodule.dualCoact (R := k) (H := H) (M := M) φ))
              LinearMap.id (Comodule.coact (R := k) (C := H) (M := M) m)) :=
          lid_map_contractLeft_tensorCombine k H _ _
        _ = LinearMap.mul' k H
            ((HopfAlgebra.antipode k).rTensor H
              (Coalgebra.comul
                (Comodule.matrixCoefficient (R := k) (C := H) φ m))) := by
          rw [Comodule.dualTensorHom_dualCoact]
          simp only [Comodule.matrixCoefficientBilinear_apply]
          rw [Comodule.comul_matrixCoefficient, LinearMap.rTensor_def,
            TensorProduct.map_map, LinearMap.id_comp]
        _ = TensorProduct.lid k H (φ m ⊗ₜ[k] (1 : H)) := by
          rw [HopfAlgebra.mul_antipode_rTensor_comul_apply,
            Comodule.counit_matrixCoefficient]
          simp [Algebra.smul_def]
  }

/-- Evaluation applies the underlying functional to the vector. -/
@[simp]
theorem dualEvaluation_apply (M : FGComoduleCat.{u, v, u} k H)
    (φ : dual k H M) (m : M) :
    dualEvaluation k H M (φ ⊗ₜ[k] m) = φ m :=
  rfl

@[simp]
theorem dualEvaluation_toLinearMap (M : FGComoduleCat.{u, v, u} k H) :
    (dualEvaluation k H M).hom.toLinearMap = contractLeft k M :=
  rfl

private theorem tensorCoact_coevaluation_apply_one
    (M : FGComoduleCat.{u, v, u} k H) :
    Comodule.tensorCoact (R := k) (C := H) (M := M) (N := Module.Dual k M)
        (coevaluation k M 1) =
      coevaluation k M 1 ⊗ₜ[k] (1 : H) := by
  classical
  let b := Module.Basis.ofVectorSpace k M
  rw [coevaluation_apply_one]
  dsimp only [b]
  simp only [map_sum, Comodule.tensorCoact_tmul,
    coact_eq_sum_basis_matrixCoefficient k H (Module.Basis.ofVectorSpace k M),
    Comodule.dual_coact,
    dualCoact_coord_eq_sum k H (Module.Basis.ofVectorSpace k M),
    TensorProduct.sum_tmul, TensorProduct.tmul_sum,
    Comodule.tensorCombine_tmul_tmul]
  have hrepr (i j : Module.Basis.ofVectorSpaceIndex k M) :
      (Module.Basis.ofVectorSpace k M).repr (i : M) j =
        if i = j then 1 else 0 := by
    rw [← Module.Basis.ofVectorSpace_apply_self k M i]
    exact Module.Basis.repr_self_apply (Module.Basis.ofVectorSpace k M) i j
  let bt := (Module.Basis.ofVectorSpace k M).tensorProduct
    (Module.Basis.ofVectorSpace k M).dualBasis
  apply (TensorProduct.equivFinsuppOfBasisLeft (N := H) bt).injective
  ext ⟨p, q⟩
  suffices h :
      (∑ x : Module.Basis.ofVectorSpaceIndex k M,
        Comodule.matrixCoefficient (R := k) (C := H)
          ((Module.Basis.ofVectorSpace k M).coord p) (x : M) *
        HopfAlgebra.antipode k
          (Comodule.matrixCoefficient (R := k) (C := H)
            ((Module.Basis.ofVectorSpace k M).coord x) (q : M))) =
        if q = p then 1 else 0 by
    simpa [bt, Module.Basis.coe_ofVectorSpace,
      Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.dualBasis_repr,
      hrepr] using h
  calc
    _ = LinearMap.mul' k H
        ((HopfAlgebra.antipode k).lTensor H
          (Coalgebra.comul
            (Comodule.matrixCoefficient (R := k) (C := H)
              ((Module.Basis.ofVectorSpace k M).coord p)
              ((Module.Basis.ofVectorSpace k M) q)))) := by
      rw [Comodule.comul_matrixCoefficient_eq_sum (Module.Basis.ofVectorSpace k M)]
      simp only [map_sum, LinearMap.lTensor_tmul, LinearMap.mul'_apply,
        Module.Basis.coe_ofVectorSpace]
    _ = algebraMap k H
        (Coalgebra.counit
          (Comodule.matrixCoefficient (R := k) (C := H)
            ((Module.Basis.ofVectorSpace k M).coord p)
            ((Module.Basis.ofVectorSpace k M) q))) :=
      HopfAlgebra.mul_antipode_lTensor_comul_apply _
    _ = if q = p then 1 else 0 := by
      rw [Comodule.counit_matrixCoefficient]
      simp [Module.Basis.coord_apply, hrepr]

/-- The ordinary finite-dimensional coevaluation, as a finite-comodule morphism into the
tensor product with the antipode-twisted dual. -/
@[expose]
noncomputable def dualCoevaluation (M : FGComoduleCat.{u, v, u} k H) :
    𝟙_ (FGComoduleCat.{u, v, u} k H) ⟶ M ⊗ dual k H M :=
  letI : Comodule k H k := Comodule.trivial (R := k) (C := H) (M := k)
  ofHom (R := k) (C := H) {
    toLinearMap := coevaluation k M
    map_coact := by
      apply LinearMap.ext_ring
      simp only [LinearMap.comp_apply, Comodule.trivial_coact_apply,
        TensorProduct.map_tmul, LinearMap.id_apply, Comodule.tensor_coact]
      exact (tensorCoact_coevaluation_apply_one k H M).symm
  }

/-- Coevaluation at one is the canonical basis-independent tensor. -/
theorem dualCoevaluation_apply_one (M : FGComoduleCat.{u, v, u} k H) :
    dualCoevaluation k H M (1 : k) =
      ∑ i : Module.Basis.ofVectorSpaceIndex k M,
        (Module.Basis.ofVectorSpace k M) i ⊗ₜ[k]
          (Module.Basis.ofVectorSpace k M).coord i :=
  coevaluation_apply_one k M

@[simp]
theorem dualCoevaluation_toLinearMap (M : FGComoduleCat.{u, v, u} k H) :
    (dualCoevaluation k H M).hom.toLinearMap = coevaluation k M :=
  rfl

private theorem associator_hom_toLinearMap
    (M N P : FGComoduleCat.{u, v, u} k H) :
    ((α_ M N P).hom).hom.toLinearMap =
      (TensorProduct.assoc k M N P).toLinearMap := by
  apply TensorProduct.ext_threefold
  intro m n p
  exact associator_hom_apply m n p

private theorem associator_inv_toLinearMap
    (M N P : FGComoduleCat.{u, v, u} k H) :
    ((α_ M N P).inv).hom.toLinearMap =
      (TensorProduct.assoc k M N P).symm.toLinearMap := by
  apply TensorProduct.ext_threefold'
  intro m n p
  exact associator_inv_apply m n p

private theorem leftUnitor_hom_toLinearMap
    (M : FGComoduleCat.{u, v, u} k H) :
    ((λ_ M).hom).hom.toLinearMap = (TensorProduct.lid k M).toLinearMap := by
  apply TensorProduct.ext'
  intro r m
  exact leftUnitor_hom_apply r m

private theorem leftUnitor_inv_toLinearMap
    (M : FGComoduleCat.{u, v, u} k H) :
    ((λ_ M).inv).hom.toLinearMap = (TensorProduct.lid k M).symm.toLinearMap := by
  apply LinearMap.ext
  intro m
  exact leftUnitor_inv_apply m

private theorem rightUnitor_hom_toLinearMap
    (M : FGComoduleCat.{u, v, u} k H) :
    ((ρ_ M).hom).hom.toLinearMap = (TensorProduct.rid k M).toLinearMap := by
  apply TensorProduct.ext'
  intro m r
  exact rightUnitor_hom_apply m r

private theorem rightUnitor_inv_toLinearMap
    (M : FGComoduleCat.{u, v, u} k H) :
    ((ρ_ M).inv).hom.toLinearMap = (TensorProduct.rid k M).symm.toLinearMap := by
  apply LinearMap.ext
  intro m
  exact rightUnitor_inv_apply m

set_option backward.privateInPublic true in
private theorem coevaluation_evaluation
    (M : FGComoduleCat.{u, v, u} k H) :
    letI M' : FGComoduleCat.{u, v, u} k H := dual k H M
    M' ◁ dualCoevaluation k H M ≫ (α_ M' M M').inv ≫
        dualEvaluation k H M ▷ M' =
      (ρ_ M').hom ≫ (λ_ M').inv := by
  have hleft :
      ((dual k H M ◁ dualCoevaluation k H M ≫
          (α_ (dual k H M) M (dual k H M)).inv ≫
            dualEvaluation k H M ▷ dual k H M).hom).toLinearMap =
        (contractLeft k M).rTensor (Module.Dual k M) ∘ₗ
          (TensorProduct.assoc k (Module.Dual k M) M (Module.Dual k M)).symm.toLinearMap ∘ₗ
            (coevaluation k M).lTensor (Module.Dual k M) := by
    rw [← id_tensorHom, ← tensorHom_id]
    simp only [ObjectProperty.FullSubcategory.comp_hom, ComoduleCat.toLinearMap_comp,
      tensorHom_toLinearMap, ObjectProperty.FullSubcategory.id_hom,
      ComoduleCat.toLinearMap_id, dualCoevaluation_toLinearMap,
      dualEvaluation_toLinearMap, associator_inv_toLinearMap,
      dual_coe, LinearMap.lTensor_def, LinearMap.rTensor_def,
      LinearMap.comp_assoc]
  have hright :
      (((ρ_ (dual k H M)).hom ≫ (λ_ (dual k H M)).inv).hom).toLinearMap =
        (TensorProduct.lid k (Module.Dual k M)).symm.toLinearMap ∘ₗ
          (TensorProduct.rid k (Module.Dual k M)).toLinearMap := by
    simp only [ObjectProperty.FullSubcategory.comp_hom, ComoduleCat.toLinearMap_comp,
      rightUnitor_hom_toLinearMap, leftUnitor_inv_toLinearMap]
  apply ObjectProperty.hom_ext
  apply ComoduleCat.hom_ext
  intro x
  change
    ((dual k H M ◁ dualCoevaluation k H M ≫
        (α_ (dual k H M) M (dual k H M)).inv ≫
          dualEvaluation k H M ▷ dual k H M).hom).toLinearMap x =
      (((ρ_ (dual k H M)).hom ≫ (λ_ (dual k H M)).inv).hom).toLinearMap x
  rw [hleft, hright]
  exact LinearMap.congr_fun (contractLeft_assoc_coevaluation k M) x

set_option backward.privateInPublic true in
private theorem evaluation_coevaluation
    (M : FGComoduleCat.{u, v, u} k H) :
    dualCoevaluation k H M ▷ M ≫
        (α_ M (dual k H M) M).hom ≫ M ◁ dualEvaluation k H M =
      (λ_ M).hom ≫ (ρ_ M).inv := by
  have hleft :
      ((dualCoevaluation k H M ▷ M ≫
          (α_ M (dual k H M) M).hom ≫
            M ◁ dualEvaluation k H M).hom).toLinearMap =
        (contractLeft k M).lTensor M ∘ₗ
          (TensorProduct.assoc k M (Module.Dual k M) M).toLinearMap ∘ₗ
            (coevaluation k M).rTensor M := by
    rw [← tensorHom_id, ← id_tensorHom]
    simp only [ObjectProperty.FullSubcategory.comp_hom, ComoduleCat.toLinearMap_comp,
      tensorHom_toLinearMap, ObjectProperty.FullSubcategory.id_hom,
      ComoduleCat.toLinearMap_id, dualCoevaluation_toLinearMap,
      dualEvaluation_toLinearMap, associator_hom_toLinearMap,
      dual_coe, LinearMap.lTensor_def, LinearMap.rTensor_def,
      LinearMap.comp_assoc]
  have hright :
      (((λ_ M).hom ≫ (ρ_ M).inv).hom).toLinearMap =
        (TensorProduct.rid k M).symm.toLinearMap ∘ₗ
          (TensorProduct.lid k M).toLinearMap := by
    simp only [ObjectProperty.FullSubcategory.comp_hom, ComoduleCat.toLinearMap_comp,
      leftUnitor_hom_toLinearMap, rightUnitor_inv_toLinearMap]
  apply ObjectProperty.hom_ext
  apply ComoduleCat.hom_ext
  intro x
  change
    ((dualCoevaluation k H M ▷ M ≫
        (α_ M (dual k H M) M).hom ≫
          M ◁ dualEvaluation k H M).hom).toLinearMap x =
      (((λ_ M).hom ≫ (ρ_ M).inv).hom).toLinearMap x
  rw [hleft, hright]
  exact LinearMap.congr_fun (contractLeft_assoc_coevaluation' k M) x

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The antipode-twisted linear dual is an exact right dual of a finite-dimensional
comodule. -/
noncomputable instance instExactPairingDual
    (M : FGComoduleCat.{u, v, u} k H) : ExactPairing M (dual k H M) where
  coevaluation' := dualCoevaluation k H M
  evaluation' := dualEvaluation k H M
  coevaluation_evaluation' := coevaluation_evaluation k H M
  evaluation_coevaluation' := evaluation_coevaluation k H M

/-- Every finite-dimensional comodule has the antipode-twisted linear dual as a right dual. -/
noncomputable instance instHasRightDual
    (M : FGComoduleCat.{u, v, u} k H) : HasRightDual M :=
  ⟨dual k H M⟩

/-- Finite-dimensional comodules over a Hopf algebra form a right rigid monoidal category. -/
noncomputable instance instRightRigidCategory :
    RightRigidCategory (FGComoduleCat.{u, v, u} k H) where

end TauCeti.FGComoduleCat
