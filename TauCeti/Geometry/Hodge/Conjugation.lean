/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Conjugation and maps on complexifications of integral modules

This file packages a conjugation on a complex vector space as a conjugate-linear involution and
constructs the canonical conjugation on any abstract complexification of an integral module.
The construction uses Mathlib's `IsBaseChange` interface: it transports coordinatewise conjugation
on `ℂ ⊗[ℤ] V` to an arbitrary complex base-change model and is uniquely characterized by fixing the
image of `V`. The same interface canonically complexifies integral linear maps between abstract
complexification models.

## Main declarations

* `TauCeti.Hodge.Conjugation`: a conjugate-linear involution of a complex vector space.
* `TauCeti.Hodge.concreteLatticeConj`: conjugation on the tensor model `ℂ ⊗[ℤ] V`.
* `TauCeti.Hodge.latticeConj`: conjugation on an abstract complex base-change model.
* `TauCeti.Hodge.latticeConj_unique`: uniqueness among conjugate-linear maps fixing the integral
  module.
* `TauCeti.Hodge.Conjugation.restrict`: the conjugation induced on a stable complex subspace.
* `TauCeti.Hodge.latticeConjugation`: the abstract map bundled as a `Conjugation`.
* `TauCeti.Hodge.integralMapToComplex`: complexification of an integral linear map between abstract
  complexification models.

The base-change design follows the Hodge structures roadmap and the discussion by Johan Commelin,
Andrew Yang, Kevin Buzzard, and Joël Riou in the `#mathlib4` Zulip thread *Complexifications with a
view towards Hodge theory*. The opposed-filtration formulation that consumes this conjugation is
Deligne's, *Théorie de Hodge II*, §1.2.1.
-/

public section

namespace TauCeti.Hodge

open scoped TensorProduct

universe u v

/-- A conjugation on a complex vector space: a conjugate-linear involution. -/
@[ext]
structure Conjugation (W : Type u) [AddCommGroup W] [Module ℂ W] where
  /-- The conjugate-linear equivalence underlying the conjugation. -/
  toEquiv : W ≃ₛₗ[starRingEnd ℂ] W
  /-- Applying the conjugation twice is the identity. -/
  involutive : Function.Involutive toEquiv

namespace Conjugation

variable {W : Type u} [AddCommGroup W] [Module ℂ W]

/-- The inverse of a conjugation is the conjugation itself. -/
@[simp]
theorem toEquiv_symm (ω : Conjugation W) : ω.toEquiv.symm = ω.toEquiv := by
  ext x
  apply ω.toEquiv.injective
  simp [ω.involutive x]

/-- Applying a conjugation twice returns the original vector. -/
@[simp]
theorem apply_apply (ω : Conjugation W) (x : W) : ω.toEquiv (ω.toEquiv x) = x :=
  ω.involutive x

/-- Mapping a complex subspace twice by a conjugation returns the original subspace. -/
@[simp]
theorem map_map_eq_self (ω : Conjugation W) (U : Submodule ℂ W) :
    (U.map ω.toEquiv.toLinearMap).map ω.toEquiv.toLinearMap = U := by
  have h : (U.map ω.toEquiv.toLinearMap).map ω.toEquiv.symm.toLinearMap = U :=
    (Submodule.map_symm_eq_iff ω.toEquiv).2 rfl
  simpa only [ω.toEquiv_symm] using h

/-- A conjugation restricted to a stable complex subspace is involutive. -/
private theorem restrict_involutive (ω : Conjugation W) {U : Submodule ℂ W}
    (hU : ∀ x ∈ U, ω.toEquiv x ∈ U) :
    Function.Involutive (ω.toEquiv.toLinearMap.restrict hU) := fun x ↦ by
  ext
  simp

/-- The conjugation induced on a complex subspace stable under a given conjugation. -/
noncomputable def restrict (ω : Conjugation W) {U : Submodule ℂ W}
    (hU : ∀ x ∈ U, ω.toEquiv x ∈ U) : Conjugation U where
  toEquiv := LinearEquiv.ofInvolutive _ (ω.restrict_involutive hU)
  involutive := ω.restrict_involutive hU

/-- A restricted conjugation acts as the ambient one. -/
@[simp]
theorem restrict_toEquiv_apply (ω : Conjugation W) {U : Submodule ℂ W}
    (hU : ∀ x ∈ U, ω.toEquiv x ∈ U) (x : U) :
    ((ω.restrict hU).toEquiv x : W) = ω.toEquiv x :=
  (rfl)

/-- Conjugating inside a stable subspace is conjugating in the ambient space: the image of an
intersection with the subspace under the restricted conjugation is the intersection with the
conjugate subspace. -/
@[simp]
theorem map_restrict_comap_subtype (ω : Conjugation W) {U : Submodule ℂ W}
    (hU : ∀ x ∈ U, ω.toEquiv x ∈ U) (A : Submodule ℂ W) :
    (A.comap U.subtype).map (ω.restrict hU).toEquiv.toLinearMap =
      (A.map ω.toEquiv.toLinearMap).comap U.subtype := by
  ext x
  simp

end Conjugation

section Concrete

variable {V : Type u} [AddCommGroup V]

/-- The canonical complexification `ℂ ⊗[ℤ] V` of an integral module. -/
abbrev Complexification (V : Type u) [AddCommGroup V] :=
  TensorProduct ℤ ℂ V

/-- The canonical map from an integral module to its tensor-product complexification. -/
def complexificationMap : V →ₗ[ℤ] Complexification V :=
  (TensorProduct.mk ℤ ℂ V) 1

/-- The tensor-product complexification satisfies the abstract base-change interface. -/
theorem isBaseChange_complexificationMap :
    IsBaseChange ℂ (complexificationMap (V := V)) :=
  TensorProduct.isBaseChange ℤ V ℂ

/-- The integral-linear map underlying conjugation on the tensor-product complexification. -/
private noncomputable def concreteLatticeConjIntLinear :=
  TensorProduct.map (starRingEnd ℂ).toAddMonoidHom.toIntLinearMap
    (LinearMap.id : V →ₗ[ℤ] V)

/-- Lattice-induced conjugation on the tensor model `ℂ ⊗[ℤ] V`, acting by complex conjugation on
the scalar tensor factor and by the identity on the integral module. -/
noncomputable def concreteLatticeConj :
    Complexification V →ₛₗ[starRingEnd ℂ] Complexification V where
  toFun := concreteLatticeConjIntLinear
  map_add' := concreteLatticeConjIntLinear.map_add
  map_smul' c x := by
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro z v
      simp only [TensorProduct.smul_tmul']
      unfold concreteLatticeConjIntLinear
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul]
      simp [map_mul, TensorProduct.smul_tmul']
    · intro x y hx hy
      simp [map_add, hx, hy]

/-- Conjugation on the tensor model conjugates the scalar in a pure tensor. -/
@[simp]
theorem concreteLatticeConj_tmul (z : ℂ) (v : V) :
    concreteLatticeConj (V := V) (z ⊗ₜ[ℤ] v) = (starRingEnd ℂ z) ⊗ₜ[ℤ] v :=
  by
    -- The tensor map is `ℤ`-linear while the bundled result is conjugate-linear over `ℂ`, so the
    -- public pure-tensor equation is the stable bridge between the two scalar interfaces.
    change concreteLatticeConjIntLinear (z ⊗ₜ[ℤ] v) = _
    unfold concreteLatticeConjIntLinear
    rw [TensorProduct.map_tmul]
    simp

/-- Conjugation on the tensor model fixes the image of the integral module. -/
@[simp]
theorem concreteLatticeConj_complexificationMap (v : V) :
    concreteLatticeConj (complexificationMap v) = complexificationMap v := by
  -- `Complexification V` has both the tensor-product and canonical integer-module instances;
  -- restating the goal as a pure tensor avoids exposing that harmless instance diamond.
  change concreteLatticeConj (1 ⊗ₜ[ℤ] v) = 1 ⊗ₜ[ℤ] v
  simpa only [map_one] using concreteLatticeConj_tmul (V := V) 1 v

private theorem concreteLatticeConjIntLinear_comp :
    concreteLatticeConjIntLinear (V := V) ∘ₗ concreteLatticeConjIntLinear = LinearMap.id := by
  unfold concreteLatticeConjIntLinear
  rw [← TensorProduct.map_comp]
  have hstar : (starRingEnd ℂ).toAddMonoidHom.toIntLinearMap ∘ₗ
      (starRingEnd ℂ).toAddMonoidHom.toIntLinearMap = LinearMap.id := by
    ext z
    simp
  rw [hstar]
  exact TensorProduct.map_id

/-- Conjugation on the tensor model is involutive. -/
theorem concreteLatticeConj_involutive :
    Function.Involutive (concreteLatticeConj (V := V)) := by
  intro x
  exact LinearMap.congr_fun (concreteLatticeConjIntLinear_comp (V := V)) x

/-- Applying conjugation on the tensor model twice returns the original vector. -/
@[simp]
theorem concreteLatticeConj_apply_apply (x : Complexification V) :
    concreteLatticeConj (concreteLatticeConj x) = x :=
  concreteLatticeConj_involutive x

end Concrete

section Abstract

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

/-- Lattice-induced conjugation on an abstract complex base-change model. -/
noncomputable def latticeConj (hℂ : IsBaseChange ℂ ιℂ) :
    Vℂ →ₛₗ[starRingEnd ℂ] Vℂ :=
  hℂ.equiv.toLinearMap.comp
    ((concreteLatticeConj (V := V)).comp hℂ.equiv.symm.toLinearMap)

/-- Abstract lattice-induced conjugation fixes the image of the integral module. -/
@[simp]
theorem latticeConj_ι (hℂ : IsBaseChange ℂ ιℂ) (v : V) :
    latticeConj hℂ (ιℂ v) = ιℂ v := by
  simp [latticeConj]

/-- Abstract lattice-induced conjugation is involutive. -/
theorem latticeConj_involutive (hℂ : IsBaseChange ℂ ιℂ) :
    Function.Involutive (latticeConj hℂ) := by
  intro x
  simp only [latticeConj, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hℂ.equiv.symm_apply_apply, concreteLatticeConj_involutive,
    hℂ.equiv.apply_symm_apply]

/-- Applying abstract lattice-induced conjugation twice returns the original vector. -/
@[simp]
theorem latticeConj_apply_apply (hℂ : IsBaseChange ℂ ιℂ) (x : Vℂ) :
    latticeConj hℂ (latticeConj hℂ x) = x :=
  latticeConj_involutive hℂ x

/-- Lattice-induced conjugation is the unique conjugate-linear map on an abstract complexification
that fixes every integral vector. -/
theorem latticeConj_unique (hℂ : IsBaseChange ℂ ιℂ)
    (c : Vℂ →ₛₗ[starRingEnd ℂ] Vℂ) (hc : ∀ v, c (ιℂ v) = ιℂ v) :
    c = latticeConj hℂ := by
  ext x
  induction x using hℂ.inductionOn with
  | zero => simp
  | tmul v => simp [hc]
  | smul z x hx => simp [hx]
  | add x y hx hy => simp [hx, hy]

/-- On the canonical tensor-product model, abstract lattice-induced conjugation is the concrete
tensor map. -/
theorem latticeConj_complexificationMap :
    latticeConj (isBaseChange_complexificationMap (V := V)) =
      concreteLatticeConj (V := V) :=
  (latticeConj_unique isBaseChange_complexificationMap concreteLatticeConj
    concreteLatticeConj_complexificationMap).symm

/-- Lattice-induced conjugation on an abstract complexification, bundled as a conjugation. -/
noncomputable def latticeConjugation (hℂ : IsBaseChange ℂ ιℂ) : Conjugation Vℂ where
  toEquiv := LinearEquiv.ofInvolutive (latticeConj hℂ) (latticeConj_involutive hℂ)
  involutive := latticeConj_involutive hℂ

/-- The equivalence underlying bundled lattice conjugation applies as `latticeConj`. -/
@[simp]
theorem latticeConjugation_toEquiv_apply (hℂ : IsBaseChange ℂ ιℂ) (x : Vℂ) :
    (latticeConjugation hℂ).toEquiv x = latticeConj hℂ x :=
  by simp [latticeConjugation]

/-- The linear map underlying bundled lattice conjugation is `latticeConj`, bridging the bundled
spelling used by `HodgeStructureOn` and the bare spelling used by the base-change API. This is not
a `simp` lemma: rewriting with it discards the equivalence, and with it `simp`'s ability to see
that conjugating a subspace preserves `⊤`. -/
theorem latticeConjugation_toLinearMap (hℂ : IsBaseChange ℂ ιℂ) :
    (latticeConjugation hℂ).toEquiv.toLinearMap = latticeConj hℂ :=
  (rfl)

/-- Bundled lattice conjugation fixes the image of the integral module. -/
theorem latticeConjugation_toEquiv_ι (hℂ : IsBaseChange ℂ ιℂ) (v : V) :
    (latticeConjugation hℂ).toEquiv (ιℂ v) = ιℂ v := by
  simp

end Abstract

section IntegralMaps

universe u₁ v₁ u₂ v₂ u₃ v₃

variable {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃}
variable {W₁ : Type v₁} {W₂ : Type v₂} {W₃ : Type v₃}
variable [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃]
variable [AddCommGroup W₁] [Module ℂ W₁]
variable [AddCommGroup W₂] [Module ℂ W₂]
variable [AddCommGroup W₃] [Module ℂ W₃]
variable {ι₁ : V₁ →ₗ[ℤ] W₁} {ι₂ : V₂ →ₗ[ℤ] W₂} {ι₃ : V₃ →ₗ[ℤ] W₃}

/-- The complexification of an integral linear map between abstract complexification models. -/
noncomputable def integralMapToComplex (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂)
    (f : V₁ →ₗ[ℤ] V₂) : W₁ →ₗ[ℂ] W₂ :=
  h₁.lift (ι₂ ∘ₗ f)

/-- Complexification agrees with the target lattice map on integral vectors. -/
@[simp]
theorem integralMapToComplex_apply_ι (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂)
    (f : V₁ →ₗ[ℤ] V₂) (x : V₁) :
    integralMapToComplex h₁ ι₂ f (ι₁ x) = ι₂ (f x) :=
  h₁.lift_eq (ι₂ ∘ₗ f) x

/-- Complexification sends the identity integral map to the identity complex map. -/
@[simp]
theorem integralMapToComplex_id (h₁ : IsBaseChange ℂ ι₁) :
    integralMapToComplex h₁ ι₁ (LinearMap.id : V₁ →ₗ[ℤ] V₁) = LinearMap.id :=
  h₁.algHom_ext _ _ fun x ↦ by simp

/-- Complexification sends the zero integral map to the zero complex map. -/
@[simp]
theorem integralMapToComplex_zero (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂) :
    integralMapToComplex h₁ ι₂ (0 : V₁ →ₗ[ℤ] V₂) = 0 :=
  h₁.algHom_ext _ _ fun x ↦ by simp

/-- Complexification preserves addition of integral linear maps. -/
@[simp]
theorem integralMapToComplex_add (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂)
    (f g : V₁ →ₗ[ℤ] V₂) :
    integralMapToComplex h₁ ι₂ (f + g) =
      integralMapToComplex h₁ ι₂ f + integralMapToComplex h₁ ι₂ g :=
  h₁.algHom_ext _ _ fun x ↦ by simp

/-- Complexification preserves negation of integral linear maps. -/
@[simp]
theorem integralMapToComplex_neg (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂)
    (f : V₁ →ₗ[ℤ] V₂) :
    integralMapToComplex h₁ ι₂ (-f) = -integralMapToComplex h₁ ι₂ f :=
  h₁.algHom_ext _ _ fun x ↦ by simp

/-- Complexification preserves subtraction of integral linear maps. -/
@[simp]
theorem integralMapToComplex_sub (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂)
    (f g : V₁ →ₗ[ℤ] V₂) :
    integralMapToComplex h₁ ι₂ (f - g) =
      integralMapToComplex h₁ ι₂ f - integralMapToComplex h₁ ι₂ g :=
  h₁.algHom_ext _ _ fun x ↦ by simp

/-- Complexification preserves natural-number multiples of integral linear maps. -/
@[simp]
theorem integralMapToComplex_nsmul (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂) (k : ℕ)
    (f : V₁ →ₗ[ℤ] V₂) :
    integralMapToComplex h₁ ι₂ (k • f) = k • integralMapToComplex h₁ ι₂ f :=
  h₁.algHom_ext _ _ fun x ↦ by simp

/-- Complexification preserves integer multiples of integral linear maps. -/
@[simp]
theorem integralMapToComplex_zsmul (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂) (k : ℤ)
    (f : V₁ →ₗ[ℤ] V₂) :
    integralMapToComplex h₁ ι₂ (k • f) = k • integralMapToComplex h₁ ι₂ f :=
  h₁.algHom_ext _ _ fun x ↦ by simp

/-- Complexification preserves composition of integral linear maps. -/
theorem integralMapToComplex_comp (h₁ : IsBaseChange ℂ ι₁) (h₂ : IsBaseChange ℂ ι₂)
    (ι₃ : V₃ →ₗ[ℤ] W₃) (f : V₁ →ₗ[ℤ] V₂) (g : V₂ →ₗ[ℤ] V₃) :
    integralMapToComplex h₁ ι₃ (g ∘ₗ f) =
      integralMapToComplex h₂ ι₃ g ∘ₗ integralMapToComplex h₁ ι₂ f :=
  h₁.algHom_ext _ _ fun x ↦ by simp

/-- The complexification of an integral map commutes with lattice-induced conjugation. -/
@[simp]
theorem integralMapToComplex_commutes_conj (h₁ : IsBaseChange ℂ ι₁)
    (h₂ : IsBaseChange ℂ ι₂) (f : V₁ →ₗ[ℤ] V₂) (x : W₁) :
    integralMapToComplex h₁ ι₂ f (latticeConj h₁ x) =
      latticeConj h₂ (integralMapToComplex h₁ ι₂ f x) := by
  induction x using h₁.inductionOn with
  | zero => simp
  | tmul x => simp
  | smul z x hx => simp [hx]
  | add x y hx hy => simp [hx, hy]

end IntegralMaps

end TauCeti.Hodge
