/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Automorphisms of scalar extensions

For a module `V` over a commutative ring `R`, this file packages

`A ↦ Autₐ(A ⊗[R] V)`

as a functor from commutative `R`-algebras to groups. A morphism `φ : A ⟶ B` acts by
extending an automorphism to `B ⊗[A] (A ⊗[R] V)` and conjugating through the canonical
equivalence with `B ⊗[R] V`.

The public characterization uses the canonical map `A ⊗[R] V → B ⊗[R] V`. Scalar
extension of an automorphism commutes with this map, and its value on a pure tensor is consequently
determined by the original automorphism on `1 ⊗ₜ v`. These formulas avoid exposing the iterated
tensor product to downstream representation-theoretic constructions.

No finiteness, freeness, projectivity, flatness, or nontriviality hypothesis is used. In particular,
the construction includes zero rings and the zero module. This is only the fixed-module
automorphism functor; no representability or functoriality in `V` is asserted.

## Main declarations

* `GeneralLinear.scalarExtensionAutomorphisms`: the automorphism group at a value algebra.
* `GeneralLinear.mapScalarExtensionAutomorphisms`: extension of automorphisms along a value-algebra
  morphism.
* `GeneralLinear.scalarExtensionAutomorphismsFunctor`: the resulting group-valued functor.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.8 and Chapter 4(a).
* The Stacks Project, Tags [00CV](https://stacks.math.columbia.edu/tag/00CV) and
  [05G3](https://stacks.math.columbia.edu/tag/05G3).
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

namespace GeneralLinear

universe u v w

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]

/-- The group of linear automorphisms of the scalar extension `A ⊗[R] V`. -/
abbrev scalarExtensionAutomorphisms (A : CommAlgCat.{w} R) :
    GrpCat.{max v w} :=
  GrpCat.of (LinearMap.GeneralLinearGroup A (A ⊗[R] V))

/-- The canonical map between scalar extensions induced by a morphism of value algebras. -/
def scalarExtensionMap {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    A ⊗[R] V →ₗ[R] B ⊗[R] V :=
  φ.hom.toLinearMap.rTensor V

/-- The canonical map between scalar extensions sends a pure tensor to the corresponding pure
tensor with its scalar mapped into the target algebra. -/
@[simp]
lemma scalarExtensionMap_tmul {A B : CommAlgCat.{w} R} (φ : A ⟶ B) (a : A) (v : V) :
    scalarExtensionMap (V := V) φ (a ⊗ₜ[R] v) = φ.hom a ⊗ₜ[R] v := by
  simp [scalarExtensionMap]

/-- The canonical map associated to the identity morphism is the identity linear map. -/
@[simp]
lemma scalarExtensionMap_id (A : CommAlgCat.{w} R) :
    scalarExtensionMap (V := V) (𝟙 A) = LinearMap.id := by
  unfold scalarExtensionMap
  simpa only [CommAlgCat.hom_id, AlgHom.toLinearMap_id] using
    (LinearMap.rTensor_id (R := R) V A)

/-- Canonical maps between scalar extensions compose covariantly. -/
lemma scalarExtensionMap_comp {A B C : CommAlgCat.{w} R} (φ : A ⟶ B) (ψ : B ⟶ C) :
    scalarExtensionMap (V := V) (φ ≫ ψ) =
      (scalarExtensionMap (V := V) ψ).comp (scalarExtensionMap (V := V) φ) := by
  unfold scalarExtensionMap
  simpa only [CommAlgCat.hom_comp, AlgHom.comp_toLinearMap] using
    (LinearMap.rTensor_comp (M := V) (f := φ.hom.toLinearMap) (g := ψ.hom.toLinearMap))

/-- The canonical map between scalar extensions is semilinear for the value-algebra morphism. -/
@[simp]
lemma scalarExtensionMap_smul {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (a : A) (x : A ⊗[R] V) :
    scalarExtensionMap (V := V) φ (a • x) =
      φ.hom a • scalarExtensionMap (V := V) φ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b v =>
      rw [TensorProduct.smul_tmul', scalarExtensionMap_tmul, scalarExtensionMap_tmul,
        TensorProduct.smul_tmul']
      simp
  | add x y hx hy => simp [hx, hy, smul_add]

/-- Extend a scalar-extension automorphism along a morphism of value algebras.

The automorphism is first extended from `A` to `B`, on the iterated tensor product
`B ⊗[A] (A ⊗[R] V)`, and then conjugated through the canonical equivalence with `B ⊗[R] V`. -/
def mapScalarExtensionAutomorphisms
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    scalarExtensionAutomorphisms (V := V) A ⟶
      scalarExtensionAutomorphisms (V := V) B := by
  letI : Algebra A B := φ.hom.toRingHom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algHom φ.hom
  exact GrpCat.ofHom <|
    (LinearMap.GeneralLinearGroup.congrLinearEquiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B V)).toMonoidHom.comp
        (Units.map (Module.End.baseChangeHom A B (A ⊗[R] V)).toMonoidHom)

private lemma hom_mul_tmul_eq_smul_scalarExtensionMap
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B) (a : A) (b : B) (v : V) :
    (φ.hom a * b) ⊗ₜ[R] v = b • scalarExtensionMap (V := V) φ (a ⊗ₜ[R] v) := by
  simpa only [scalarExtensionMap_tmul, TensorProduct.smul_tmul', smul_eq_mul] using
    congrArg (fun c : B ↦ c ⊗ₜ[R] v) (mul_comm (φ.hom a) b)

/-- Scalar extension of an automorphism is characterized on pure tensors by its value on the
canonical copy of the original module. -/
@[simp]
lemma mapScalarExtensionAutomorphisms_tmul
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (g : scalarExtensionAutomorphisms (V := V) A) (b : B) (v : V) :
    (mapScalarExtensionAutomorphisms (V := V) φ g).val (b ⊗ₜ[R] v) =
      b • scalarExtensionMap (V := V) φ (g.val (1 ⊗ₜ[R] v)) := by
  letI : Algebra A B := φ.hom.toRingHom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algHom φ.hom
  -- The group-hom wrappers have no pointwise reduction lemma, so expose their underlying
  -- base-change-and-conjugation formula before computing on the tensor generator.
  change
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B V)
        (g.val.baseChange B
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B V).symm
            (b ⊗ₜ[R] v))) = _
  simp only [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearMap.baseChange_tmul]
  induction g.val (1 ⊗ₜ[R] v) using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
      change (φ.hom a * b) ⊗ₜ[R] v = _
      exact hom_mul_tmul_eq_smul_scalarExtensionMap (V := V) φ a b v
  | add x y hx hy =>
      rw [TensorProduct.tmul_add, map_add, map_add, hx, hy, smul_add]

/-- Extending an automorphism commutes with the canonical map between scalar extensions. -/
@[simp]
lemma mapScalarExtensionAutomorphisms_apply_scalarExtensionMap
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (g : scalarExtensionAutomorphisms (V := V) A) (x : A ⊗[R] V) :
    (mapScalarExtensionAutomorphisms (V := V) φ g).val
        (scalarExtensionMap (V := V) φ x) =
      scalarExtensionMap (V := V) φ (g.val x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
      rw [scalarExtensionMap_tmul, mapScalarExtensionAutomorphisms_tmul]
      have hg : g.val (a ⊗ₜ[R] v) = a • g.val (1 ⊗ₜ[R] v) := by
        rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul]
      rw [hg, scalarExtensionMap_smul]
  | add x y hx hy => simp [hx, hy]

/-- A target automorphism that intertwines the canonical map with `g` is the scalar extension of
`g`. -/
lemma eq_mapScalarExtensionAutomorphisms_of_apply_scalarExtensionMap_eq
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (g : scalarExtensionAutomorphisms (V := V) A)
    (h : scalarExtensionAutomorphisms (V := V) B)
    (h_apply : ∀ x, h.val (scalarExtensionMap (V := V) φ x) =
      scalarExtensionMap (V := V) φ (g.val x)) :
    h = mapScalarExtensionAutomorphisms (V := V) φ g := by
  apply Units.ext
  refine TensorProduct.AlgebraTensorModule.ext fun b v => ?_
  rw [mapScalarExtensionAutomorphisms_tmul,
    TensorProduct.tmul_eq_smul_one_tmul (M := V) b v, map_smul]
  congr 1
  simpa only [scalarExtensionMap_tmul, map_one] using h_apply (1 ⊗ₜ[R] v)

/-- Extension of scalar-extension automorphisms preserves identity morphisms of value algebras. -/
@[simp]
lemma mapScalarExtensionAutomorphisms_id (A : CommAlgCat.{w} R) :
    mapScalarExtensionAutomorphisms (V := V) (𝟙 A) =
      𝟙 (scalarExtensionAutomorphisms (V := V) A) := by
  apply GrpCat.ext
  intro g
  apply Units.ext
  refine TensorProduct.AlgebraTensorModule.ext fun a v => ?_
  rw [mapScalarExtensionAutomorphisms_tmul, TensorProduct.tmul_eq_smul_one_tmul (M := V) a v]
  simp

/-- Extension of scalar-extension automorphisms preserves composition of value-algebra
morphisms. -/
lemma mapScalarExtensionAutomorphisms_comp
    {A B C : CommAlgCat.{w} R} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapScalarExtensionAutomorphisms (V := V) (φ ≫ ψ) =
      mapScalarExtensionAutomorphisms (V := V) φ ≫
        mapScalarExtensionAutomorphisms (V := V) ψ := by
  apply GrpCat.ext
  intro g
  apply Units.ext
  refine TensorProduct.AlgebraTensorModule.ext fun a v => ?_
  rw [mapScalarExtensionAutomorphisms_tmul, CategoryTheory.comp_apply,
    mapScalarExtensionAutomorphisms_tmul, mapScalarExtensionAutomorphisms_tmul,
    scalarExtensionMap_comp]
  simp

/-- The group-valued functor of linear automorphisms of scalar extensions of `V`. -/
def scalarExtensionAutomorphismsFunctor :
    CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj A := scalarExtensionAutomorphisms (V := V) A
  map φ := mapScalarExtensionAutomorphisms (V := V) φ
  map_id A := mapScalarExtensionAutomorphisms_id (V := V) A
  map_comp φ ψ := mapScalarExtensionAutomorphisms_comp (V := V) φ ψ

/-- The functor takes a value algebra to the automorphism group of the corresponding scalar
extension. -/
@[simp]
lemma scalarExtensionAutomorphismsFunctor_obj (A : CommAlgCat.{w} R) :
    (scalarExtensionAutomorphismsFunctor (V := V)).obj A =
      scalarExtensionAutomorphisms (V := V) A :=
  (rfl)

/-- The functor takes a morphism of value algebras to the corresponding extension of
automorphisms. -/
@[simp]
lemma scalarExtensionAutomorphismsFunctor_map {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    (scalarExtensionAutomorphismsFunctor (V := V)).map φ =
      eqToHom (scalarExtensionAutomorphismsFunctor_obj (V := V) A) ≫
        mapScalarExtensionAutomorphisms (V := V) φ ≫
          eqToHom (scalarExtensionAutomorphismsFunctor_obj (V := V) B).symm := by
  apply (conj_eqToHom_iff_heq _ _
    (scalarExtensionAutomorphismsFunctor_obj (V := V) A)
    (scalarExtensionAutomorphismsFunctor_obj (V := V) B)).2
  unfold scalarExtensionAutomorphismsFunctor
  rfl

end GeneralLinear

end TauCeti
