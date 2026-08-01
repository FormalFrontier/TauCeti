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

The exact-pairing packaging adapts the finite-dimensional module construction in
`Mathlib/Algebra/Category/FGModuleCat/Basic.lean`.

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

private theorem dualEvaluation_apply_aux (M : FGComoduleCat.{u, v, u} k H)
    (φ : dual k H M) (m : M) :
    dualEvaluation k H M (φ ⊗ₜ[k] m) = φ m :=
  rfl

private theorem dualEvaluation_toLinearMap_aux (M : FGComoduleCat.{u, v, u} k H) :
    (dualEvaluation k H M).hom.toLinearMap = contractLeft k M :=
  rfl

/-- Evaluation applies the underlying functional to the vector. -/
@[simp]
theorem dualEvaluation_apply (M : FGComoduleCat.{u, v, u} k H)
    (φ : dual k H M) (m : M) :
    dualEvaluation k H M (φ ⊗ₜ[k] m) = φ m :=
  dualEvaluation_apply_aux k H M φ m

/-- The underlying linear map of evaluation is ordinary contraction. -/
@[simp]
theorem dualEvaluation_toLinearMap (M : FGComoduleCat.{u, v, u} k H) :
    (dualEvaluation k H M).hom.toLinearMap = contractLeft k M :=
  dualEvaluation_toLinearMap_aux k H M

/-- Multiplying the matrix-coefficient matrix by its entrywise antipode transform gives the image
under `algebraMap` of a single basis coordinate. Taking `p` and `q` basis indices, the right-hand
side is `1` when they agree and `0` otherwise, so the antipode transform is a right inverse of the
matrix-coefficient matrix in this multiplication order; the opposite order is not claimed here.

Stated over its own base ring, for any comodule with a finite basis: neither the ambient field,
nor the canonical `Module.Basis.ofVectorSpace` choice, nor finite-dimensionality, nor decidable
equality on the index type plays a part. -/
private lemma sum_matrixCoefficient_mul_antipode_eq_algebraMap (R : Type*) [CommSemiring R]
    (A : Type*) [Semiring A] [HopfAlgebra R A] {M : Type*} [AddCommMonoid M] [Module R M]
    [Comodule R A M] {ι : Type*} [Fintype ι] (b : Module.Basis ι R M) (p q : ι) :
    (∑ x : ι,
      Comodule.matrixCoefficient (R := R) (C := A) (b.coord p) (b x) *
      HopfAlgebra.antipode R
        (Comodule.matrixCoefficient (R := R) (C := A) (b.coord x) (b q))) =
      algebraMap R A (b.coord p (b q)) := by
  -- The basis expansion of `comul` is a `Coalgebra.Repr`, so Mathlib's antipode sum applies.
  let repr : Coalgebra.Repr R
      (Comodule.matrixCoefficient (R := R) (C := A) (b.coord p) (b q)) ι :=
    { index := Finset.univ
      left := fun x => Comodule.matrixCoefficient (R := R) (C := A) (b.coord p) (b x)
      right := fun x => Comodule.matrixCoefficient (R := R) (C := A) (b.coord x) (b q)
      eq := (Comodule.comul_matrixCoefficient_eq_sum b (b.coord p) (b q)).symm }
  rw [← Comodule.counit_matrixCoefficient (R := R) (C := A) (b.coord p) (b q)]
  exact HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit repr

private theorem tensorCoact_coevaluation_apply_one
    (M : FGComoduleCat.{u, v, u} k H) :
    Comodule.tensorCoact (R := k) (C := H) (M := M) (N := Module.Dual k M)
        (coevaluation k M 1) =
      coevaluation k M 1 ⊗ₜ[k] (1 : H) := by
  classical
  -- Expand coevaluation and both coactions in a basis, then compare tensor coordinates.
  -- The remaining matrix-coefficient sum collapses by the antipode identity below.
  let b := Module.Basis.ofVectorSpace k M
  rw [coevaluation_apply_one]
  dsimp only [b]
  simp only [map_sum, Comodule.tensorCoact_tmul,
    Comodule.coact_eq_sum_basis_matrixCoefficient (C := H) (Module.Basis.ofVectorSpace k M),
    Comodule.dual_coact,
    dualCoact_coord_eq_sum k H (Module.Basis.ofVectorSpace k M),
    TensorProduct.sum_tmul, TensorProduct.tmul_sum,
    Comodule.tensorCombine_tmul_tmul]
  let bt := (Module.Basis.ofVectorSpace k M).tensorProduct
    (Module.Basis.ofVectorSpace k M).dualBasis
  apply (TensorProduct.equivFinsuppOfBasisLeft (N := H) bt).injective
  ext ⟨p, q⟩
  have hrepr (i j : Module.Basis.ofVectorSpaceIndex k M) :
      (Module.Basis.ofVectorSpace k M).repr (i : M) j = if i = j then 1 else 0 := by
    rw [← Module.Basis.ofVectorSpace_apply_self k M i]
    exact Module.Basis.repr_self_apply (Module.Basis.ofVectorSpace k M) i j
  simpa only [Module.Basis.coe_ofVectorSpace, map_sum,
    TensorProduct.equivFinsuppOfBasisLeft_apply_tmul, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.mapRange_apply, Module.Basis.tensorProduct_repr_tmul_apply,
    Module.Basis.dualBasis_repr, Module.Basis.coord_apply, hrepr, smul_eq_mul,
    mul_ite, mul_one, mul_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, Finset.sum_ite_eq, bt,
    apply_ite (algebraMap k H), map_one, map_zero] using
    sum_matrixCoefficient_mul_antipode_eq_algebraMap k H (Module.Basis.ofVectorSpace k M) p q

/-- The ordinary finite-dimensional coevaluation, as a finite-comodule morphism into the
tensor product with the antipode-twisted dual. -/
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

private theorem dualCoevaluation_toLinearMap_aux (M : FGComoduleCat.{u, v, u} k H) :
    (dualCoevaluation k H M).hom.toLinearMap = coevaluation k M :=
  rfl

/-- Coevaluation at one is the canonical basis-independent tensor. -/
theorem dualCoevaluation_apply_one (M : FGComoduleCat.{u, v, u} k H) :
    dualCoevaluation k H M (1 : k) =
      ∑ i : Module.Basis.ofVectorSpaceIndex k M,
        (Module.Basis.ofVectorSpace k M) i ⊗ₜ[k]
          (Module.Basis.ofVectorSpace k M).coord i :=
  coevaluation_apply_one k M

/-- The underlying linear map of coevaluation is ordinary finite-dimensional coevaluation. -/
@[simp]
theorem dualCoevaluation_toLinearMap (M : FGComoduleCat.{u, v, u} k H) :
    (dualCoevaluation k H M).hom.toLinearMap = coevaluation k M :=
  dualCoevaluation_toLinearMap_aux k H M

/-- The antipode-twisted linear dual is an exact right dual of a finite-dimensional
comodule. -/
noncomputable instance instExactPairingDual
    (M : FGComoduleCat.{u, v, u} k H) : ExactPairing M (dual k H M) where
  coevaluation' := dualCoevaluation k H M
  evaluation' := dualEvaluation k H M
  coevaluation_evaluation' := by
    have h :
        ((dual k H M ◁ dualCoevaluation k H M ≫
            (α_ (dual k H M) M (dual k H M)).inv ≫
              dualEvaluation k H M ▷ dual k H M).hom).toLinearMap =
          (((ρ_ (dual k H M)).hom ≫ (λ_ (dual k H M)).inv).hom).toLinearMap := by
      rw [← id_tensorHom, ← tensorHom_id]
      simp only [ObjectProperty.FullSubcategory.comp_hom, ComoduleCat.toLinearMap_comp,
        tensorHom_toLinearMap, ObjectProperty.FullSubcategory.id_hom,
        ComoduleCat.toLinearMap_id, dualCoevaluation_toLinearMap,
        dualEvaluation_toLinearMap, associator_inv_toLinearMap,
        rightUnitor_hom_toLinearMap, leftUnitor_inv_toLinearMap,
        dual_coe, LinearMap.comp_assoc]
      exact contractLeft_assoc_coevaluation k M
    apply ObjectProperty.hom_ext
    apply ComoduleCat.hom_ext
    exact fun x => LinearMap.congr_fun h x
  evaluation_coevaluation' := by
    have h :
        ((dualCoevaluation k H M ▷ M ≫
            (α_ M (dual k H M) M).hom ≫
              M ◁ dualEvaluation k H M).hom).toLinearMap =
          (((λ_ M).hom ≫ (ρ_ M).inv).hom).toLinearMap := by
      rw [← tensorHom_id, ← id_tensorHom]
      simp only [ObjectProperty.FullSubcategory.comp_hom, ComoduleCat.toLinearMap_comp,
        tensorHom_toLinearMap, ObjectProperty.FullSubcategory.id_hom,
        ComoduleCat.toLinearMap_id, dualCoevaluation_toLinearMap,
        dualEvaluation_toLinearMap, associator_hom_toLinearMap,
        leftUnitor_hom_toLinearMap, rightUnitor_inv_toLinearMap,
        dual_coe, LinearMap.comp_assoc]
      exact contractLeft_assoc_coevaluation' k M
    apply ObjectProperty.hom_ext
    apply ComoduleCat.hom_ext
    exact fun x => LinearMap.congr_fun h x

/-- Every finite-dimensional comodule has the antipode-twisted linear dual as a right dual. -/
noncomputable instance instHasRightDual
    (M : FGComoduleCat.{u, v, u} k H) : HasRightDual M :=
  ⟨dual k H M⟩

/-- Finite-dimensional comodules over a Hopf algebra form a right rigid monoidal category. -/
noncomputable instance instRightRigidCategory :
    RightRigidCategory (FGComoduleCat.{u, v, u} k H) where

end TauCeti.FGComoduleCat
