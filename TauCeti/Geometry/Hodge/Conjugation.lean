/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.IsTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Tactic.Ring

namespace TauCeti.Geometry.Hodge

open Complex

/-- The canonical complexification `ℂ ⊗[ℤ] V` of a `ℤ`-module `V`. -/
public abbrev Complexification (V : Type*) [AddCommGroup V] : Type _ :=
  TensorProduct ℤ ℂ V

variable {V : Type*} [AddCommGroup V]

/-- A conjugate-linear involution on a complex vector space `W`. -/
@[ext]
public structure Conjugation (W : Type*) [AddCommGroup W] [Module ℂ W] where
  /-- The underlying conjugate-linear equivalence on `W`. -/
  toEquiv : W ≃ₛₗ[starRingEnd ℂ] W
  /-- Involution property: applying the conjugation twice is the identity. -/
  involutive : Function.Involutive toEquiv

namespace Conjugation

variable {W : Type*} [AddCommGroup W] [Module ℂ W] (ω : Conjugation W)

/-- Conjugation preserves the top submodule `⊤`. -/
public theorem map_top : (⊤ : Submodule ℂ W).map ω.toEquiv.toLinearMap = ⊤ := by
  rw [Submodule.map_top]
  exact LinearEquiv.range _

/-- Conjugating a submodule twice returns the original submodule. -/
@[simp]
public theorem map_map_self (p : Submodule ℂ W) :
    (p.map ω.toEquiv.toLinearMap).map ω.toEquiv.toLinearMap = p := by
  rw [← Submodule.map_comp,
    show ω.toEquiv.toLinearMap.comp ω.toEquiv.toLinearMap = LinearMap.id from
      LinearMap.ext ω.involutive,
    Submodule.map_id]

end Conjugation

/-- The canonical conjugate-linear involution on the concrete complexification `ℂ ⊗[ℤ] V`,
acting by complex conjugation on `ℂ` and the identity on `V`. -/
@[expose]
public def concreteLatticeConj : Complexification V →ₛₗ[starRingEnd ℂ] Complexification V where
  toFun := TensorProduct.map (starRingEnd ℂ).toAddMonoidHom.toIntLinearMap
    (LinearMap.id : V →ₗ[ℤ] V)
  map_add' := (TensorProduct.map (starRingEnd ℂ).toAddMonoidHom.toIntLinearMap
    (LinearMap.id : V →ₗ[ℤ] V)).map_add
  map_smul' c x := by
    refine TensorProduct.induction_on x ?hz ?ht ?ha
    · simp
    · intro z v
      rw [TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.map_tmul,
        TensorProduct.map_tmul, TensorProduct.smul_tmul', smul_eq_mul]
      dsimp
      rw [map_mul]
    · intro x y hx hy
      simp only [smul_add, map_add, hx, hy]

/-- Evaluation of the concrete lattice conjugation on pure tensors. -/
@[simp]
public theorem concreteLatticeConj_tmul (z : ℂ) (v : V) :
    concreteLatticeConj (V := V) (z ⊗ₜ[ℤ] v) = (starRingEnd ℂ z) ⊗ₜ[ℤ] v :=
  TensorProduct.map_tmul _ _ z v

/-- The concrete lattice conjugation is an involution. -/
public theorem concreteLatticeConj_involutive :
    Function.Involutive (concreteLatticeConj (V := V)) := by
  intro x
  refine TensorProduct.induction_on x ?hz ?ht ?ha
  · simp
  · intro z v
    simp only [concreteLatticeConj_tmul, starRingEnd_self_apply]
  · intro x y hx hy
    simp only [map_add, hx, hy]

variable {Vℂ : Type*} [AddCommGroup Vℂ] [Module ℂ Vℂ]
  {ιℂ : V →ₗ[ℤ] Vℂ}
variable {hℂ : IsBaseChange ℂ ιℂ}

/-- The conjugate-linear involution on an abstract complexification `Vℂ` with base change data `hℂ`,
transporting `concreteLatticeConj` across the canonical linear equivalence `hℂ.equiv`. -/
@[expose]
public noncomputable def latticeConj (hℂ : IsBaseChange ℂ ιℂ) :
    Vℂ →ₛₗ[starRingEnd ℂ] Vℂ where
  toFun x := hℂ.equiv (concreteLatticeConj (hℂ.equiv.symm x))
  map_add' x y := by
    rw [map_add, map_add, map_add]
  map_smul' c x := by
    have h_symm : hℂ.equiv.symm (c • x) = c • hℂ.equiv.symm x := map_smul _ _ _
    rw [h_symm]
    have h_conj : concreteLatticeConj (c • hℂ.equiv.symm x) =
        (starRingEnd ℂ c) • concreteLatticeConj (hℂ.equiv.symm x) :=
      concreteLatticeConj.map_smulₛₗ c _
    rw [h_conj]
    exact map_smul _ _ _

/-- Definitional reduction of `latticeConj` on elements. -/
@[simp]
public theorem latticeConj_apply (hℂ : IsBaseChange ℂ ιℂ) (x : Vℂ) :
    latticeConj hℂ x = hℂ.equiv (concreteLatticeConj (hℂ.equiv.symm x)) := rfl

/-- The lattice conjugation fixes the image of the underlying lattice `V`. -/
public theorem latticeConj_ι (hℂ : IsBaseChange ℂ ιℂ) (v : V) :
    latticeConj hℂ (ιℂ v) = ιℂ v := by
  have hιv : hℂ.equiv.symm (ιℂ v) = (1 : ℂ) ⊗ₜ[ℤ] v := by
    apply hℂ.equiv.injective
    rw [LinearEquiv.apply_symm_apply]
    have h_eq := hℂ.equiv_tmul 1 v
    rw [one_smul] at h_eq
    exact h_eq.symm
  rw [latticeConj_apply, hιv, concreteLatticeConj_tmul, map_one]
  have h_eq := hℂ.equiv_tmul 1 v
  rw [one_smul] at h_eq
  exact h_eq

/-- The lattice conjugation is an involution. -/
public theorem latticeConj_involutive (hℂ : IsBaseChange ℂ ιℂ) :
    Function.Involutive (latticeConj hℂ) := by
  intro x
  rw [latticeConj_apply, latticeConj_apply, LinearEquiv.symm_apply_apply,
    concreteLatticeConj_involutive]
  exact hℂ.equiv.apply_symm_apply x

/-- The `Conjugation` structure on an abstract complexification `Vℂ`
induced by a `ℤ`-lattice `V`. -/
@[expose]
public noncomputable def latticeConjugation (hℂ : IsBaseChange ℂ ιℂ) : Conjugation Vℂ where
  toEquiv := LinearEquiv.ofInvolutive (latticeConj hℂ) (latticeConj_involutive hℂ)
  involutive := latticeConj_involutive hℂ

/-- The underlying equivalence of `latticeConjugation` agrees with `latticeConj`. -/
@[simp]
public theorem latticeConjugation_toEquiv_apply (hℂ : IsBaseChange ℂ ιℂ) (x : Vℂ) :
    (latticeConjugation hℂ).toEquiv x = latticeConj hℂ x := rfl

/-- The linear map of `latticeConjugation` agrees with `latticeConj`. -/
@[simp]
public theorem latticeConjugation_toLinearMap (hℂ : IsBaseChange ℂ ιℂ) :
    (latticeConjugation hℂ).toEquiv.toLinearMap = (latticeConj hℂ : Vℂ →ₗ⋆[ℂ] Vℂ) := rfl

/-- Uniqueness of conjugate-linear map fixing the lattice `ιℂ V`. -/
public theorem latticeConj_unique (f : Vℂ →ₛₗ[starRingEnd ℂ] Vℂ)
    (hf : ∀ v, f (ιℂ v) = ιℂ v) : f = latticeConj hℂ := by
  ext x
  have h_eq : x = hℂ.equiv (hℂ.equiv.symm x) := (hℂ.equiv.apply_symm_apply x).symm
  rw [h_eq]
  generalize hℂ.equiv.symm x = y
  refine TensorProduct.induction_on y ?hz ?ht ?ha
  · simp
  · intro z v
    have hz_smul : (z ⊗ₜ[ℤ] v : Complexification V) = z • ((1 : ℂ) ⊗ₜ[ℤ] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h_one : hℂ.equiv ((1 : ℂ) ⊗ₜ[ℤ] v) = ιℂ v := by
      have h_eq' := hℂ.equiv_tmul 1 v
      rw [one_smul] at h_eq'
      exact h_eq'
    have h_smul : hℂ.equiv (z ⊗ₜ[ℤ] v) = z • ιℂ v := by
      rw [hz_smul, LinearEquiv.map_smul, h_one]
    have h1 : f (hℂ.equiv (z ⊗ₜ[ℤ] v)) = (starRingEnd ℂ z) • ιℂ v := by
      rw [h_smul, f.map_smulₛₗ, hf v]
    have h2 : (latticeConj hℂ) (hℂ.equiv (z ⊗ₜ[ℤ] v)) = (starRingEnd ℂ z) • ιℂ v := by
      rw [h_smul, (latticeConj hℂ).map_smulₛₗ, latticeConj_ι]
    rw [h1, h2]
  · intro u w hu hw
    simp only [map_add] at hu hw ⊢
    rw [hu, hw]

/-- Compatibility between `concreteLatticeConj` and `latticeConj` on the canonical
tensor product. -/
public theorem concreteLatticeConj_eq_latticeConj :
    concreteLatticeConj (V := V) = latticeConj (TensorProduct.isBaseChange ℤ V ℂ) :=
  latticeConj_unique (hℂ := TensorProduct.isBaseChange ℤ V ℂ) concreteLatticeConj (fun v => by
    have : (concreteLatticeConj (V := V)) (TensorProduct.mk ℤ ℂ V 1 v) =
        TensorProduct.mk ℤ ℂ V 1 v := by
      rw [TensorProduct.mk_apply, concreteLatticeConj_tmul, map_one]
    exact this)

end TauCeti.Geometry.Hodge
