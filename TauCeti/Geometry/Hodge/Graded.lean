/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import TauCeti.Geometry.Hodge.BaseChange

/-!
# Graded pieces of a rational weight filtration

A mixed Hodge structure carries an increasing weight filtration `W` on the rational model `Vℚ`
and a decreasing Hodge filtration `F` on the complex model `Vℂ`, and asks that `F` induce a pure
Hodge structure of weight `k` on each graded piece `grᵂ_k = W_k / W_{k-1}`. This file supplies
the objects that condition is stated against.

The graded piece is taken **rationally**, and the pure structure lives on its complexification
`ℂ ⊗[ℚ] grᵂ_k`. That model is preferred to the complex graded piece `(W_k)_ℂ / (W_{k-1})_ℂ`
because it carries a canonical conjugation for free: `ℂ ⊗[ℚ] U` is a base change of the
`ℚ`-vector space `U` along `ℤ → ℂ` (`TauCeti.isBaseChange_ratTensorMap`), so
`TauCeti.Hodge.latticeConj` applies to it verbatim. The two models are identified by
`TauCeti.Hodge.gradedComplexEquiv`, which says that complexification commutes with the graded
quotient, and the Hodge filtration is transported across that identification.

## Main declarations

* `TauCeti.Hodge.weightGradedRat`, `TauCeti.Hodge.weightGradedComplex`: the rational and complex
  graded pieces of a filtration.
* `TauCeti.Hodge.gradedComplexEquiv`: complexification commutes with the weight-graded quotient.
* `TauCeti.Hodge.complexGradedF`, `TauCeti.Hodge.gradedF`: the Hodge filtration induced on the
  complex graded piece and on the complexified rational graded piece.
* `TauCeti.Hodge.gradedEquivOfEqBotOfEqTop`: across a step where the weight filtration jumps from
  zero to everything, the complexified graded piece is the whole complex model, compatibly with
  the conjugations and with the induced filtration.

The conventions for opposed and induced filtrations follow Deligne, *Théorie de Hodge II*,
§1.2.1; the graded-piece comparison is the one used throughout Peters–Steenbrink, *Mixed Hodge
Structures*, Ch. 3. The signatures of `weightGradedRat`, `gradedComplexEquiv` and `gradedF` are
adapted from the proposed definitions in
[`HodgeStructures/Suggested.lean`](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/HodgeStructures/Suggested.lean),
whose definitive mathematical specification is the accompanying Hodge structures roadmap.
-/

public section

namespace TauCeti.Hodge

open scoped TensorProduct

universe u v w

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ]
variable [AddCommGroup Vℚ] [Module ℚ Vℚ]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}

/-- Complexifying the inclusion of one rational subspace into a larger one, then identifying the
larger tensor product with the complexified subspace, has the complexification of the smaller
subspace as its range. -/
theorem map_range_lTensor_submoduleOf (hℚ : IsBaseChange ℚ ιℚ) (hℂ : IsBaseChange ℂ ιℂ)
    {A B : Submodule ℚ Vℚ} (hAB : A ≤ B) :
    (LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ
        ((A.submoduleOf B).subtype.restrictScalars ℚ))).map
        (rationalToComplexSubmoduleEquiv hℚ hℂ B).toLinearMap =
      (rationalToComplexSubmodule hℚ hℂ A).submoduleOf
        (rationalToComplexSubmodule hℚ hℂ B) := by
  have key : (rationalToComplexSubmodule hℚ hℂ B).subtype ∘ₗ
      (rationalToComplexSubmoduleEquiv hℚ hℂ B).toLinearMap ∘ₗ
        TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ
          ((A.submoduleOf B).subtype.restrictScalars ℚ) =
      (rationalToComplexLinearEquiv hℚ hℂ).toLinearMap ∘ₗ A.subtype.baseChange ℂ ∘ₗ
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ)
          (Submodule.submoduleOfEquivOfLe hAB)).toLinearMap := by
    refine LinearMap.ext fun t ↦ ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul z x => simp [Submodule.submoduleOfEquivOfLe]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hbase : (Submodule.baseChange ℂ A).map (rationalToComplexLinearEquiv hℚ hℂ).toLinearMap =
      rationalToComplexSubmodule hℚ hℂ A := by
    rw [Submodule.baseChange_eq_span, Submodule.map_span, rationalToComplexSubmodule_eq_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨1 ⊗ₜ[ℚ] y, ⟨y, hy, rfl⟩, rfl⟩
  have hrange : LinearMap.range (A.subtype.baseChange ℂ) = Submodule.baseChange ℂ A := by
    rw [Submodule.baseChange]
  apply Submodule.map_injective_of_injective (Submodule.injective_subtype _)
  have step1 : Submodule.map (rationalToComplexSubmodule hℚ hℂ B).subtype
      (Submodule.map (rationalToComplexSubmoduleEquiv hℚ hℂ B).toLinearMap
        (LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ
          ((A.submoduleOf B).subtype.restrictScalars ℚ)))) =
      LinearMap.range ((rationalToComplexSubmodule hℚ hℂ B).subtype ∘ₗ
        (rationalToComplexSubmoduleEquiv hℚ hℂ B).toLinearMap ∘ₗ
          TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ
            ((A.submoduleOf B).subtype.restrictScalars ℚ)) := by
    rw [LinearMap.range_comp, LinearMap.range_comp]
  rw [step1, key, LinearMap.range_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.2 (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ)
      (Submodule.submoduleOfEquivOfLe hAB)).surjective, Submodule.map_top, hrange, hbase]
  simp only [Submodule.submoduleOf, Submodule.map_comap_subtype,
    inf_of_le_right (rationalToComplexSubmodule_mono hℚ hℂ hAB)]

/-- The `k`-th graded piece `grᵂ_k = W_k / W_{k-1}` of an increasing rational filtration `W`.
The lower step is viewed inside `W_k` through `Submodule.submoduleOf`. -/
abbrev weightGradedRat (WQ : ℤ → Submodule ℚ Vℚ) (k : ℤ) : Type v :=
  WQ k ⧸ (WQ (k - 1)).submoduleOf (WQ k)

/-- The `k`-th graded piece of an increasing complex filtration. -/
abbrev weightGradedComplex (WC : ℤ → Submodule ℂ Vℂ) (k : ℤ) : Type w :=
  WC k ⧸ (WC (k - 1)).submoduleOf (WC k)

/-- **Complexification commutes with the weight-graded quotient**: the complexification of the
rational graded piece `grᵂ_k` is the graded piece of the complexified filtration. -/
noncomputable def gradedComplexEquiv (hℚ : IsBaseChange ℚ ιℚ) (hℂ : IsBaseChange ℂ ιℂ)
    (WQ : ℤ → Submodule ℚ Vℚ) (hWQ : Monotone WQ) (k : ℤ) :
    ℂ ⊗[ℚ] weightGradedRat WQ k ≃ₗ[ℂ]
      weightGradedComplex (fun k ↦ rationalToComplexSubmodule hℚ hℂ (WQ k)) k :=
  (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv ℂ ℚ ℂ
      ((WQ (k - 1)).submoduleOf (WQ k))).trans
    (Submodule.Quotient.equiv _ _ (rationalToComplexSubmoduleEquiv hℚ hℂ (WQ k))
      (map_range_lTensor_submoduleOf hℚ hℂ (hWQ (by omega))))

@[simp]
theorem gradedComplexEquiv_tmul_mk (hℚ : IsBaseChange ℚ ιℚ) (hℂ : IsBaseChange ℂ ιℂ)
    (WQ : ℤ → Submodule ℚ Vℚ) (hWQ : Monotone WQ) (k : ℤ) (z : ℂ) (x : WQ k) :
    gradedComplexEquiv hℚ hℂ WQ hWQ k (z ⊗ₜ[ℚ] Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (rationalToComplexSubmoduleEquiv hℚ hℂ (WQ k) (z ⊗ₜ[ℚ] x)) :=
  by
    rw [gradedComplexEquiv, LinearEquiv.trans_apply,
      TensorProduct.AlgebraTensorModule.tensorQuotientEquiv_apply_tmul,
      Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
    congr 1

/-- The Hodge filtration induced on the `k`-th complex graded piece: the image of `F^p ∩ W_k`
under the quotient map `W_k → W_k / W_{k-1}`. -/
noncomputable def complexGradedF (WC F : ℤ → Submodule ℂ Vℂ) (k p : ℤ) :
    Submodule ℂ (weightGradedComplex WC k) :=
  ((F p ⊓ WC k).submoduleOf (WC k)).map ((WC (k - 1)).submoduleOf (WC k)).mkQ

/-- The Hodge filtration induced on the complexification of the rational graded piece `grᵂ_k`,
transported from the complex graded piece along `gradedComplexEquiv`. -/
noncomputable def gradedF (hℚ : IsBaseChange ℚ ιℚ) (hℂ : IsBaseChange ℂ ιℂ)
    (WQ : ℤ → Submodule ℚ Vℚ) (hWQ : Monotone WQ) (F : ℤ → Submodule ℂ Vℂ) (k p : ℤ) :
    Submodule ℂ (ℂ ⊗[ℚ] weightGradedRat WQ k) :=
  (complexGradedF (fun k ↦ rationalToComplexSubmodule hℚ hℂ (WQ k)) F k p).comap
    (gradedComplexEquiv hℚ hℂ WQ hWQ k).toLinearMap

/-- Membership in the induced filtration on a complex graded piece is witnessed by a
representative in the corresponding ambient Hodge-filtration step. -/
@[simp]
theorem mem_complexGradedF_iff (WC F : ℤ → Submodule ℂ Vℂ) (k p : ℤ)
    (x : weightGradedComplex WC k) :
    x ∈ complexGradedF WC F k p ↔
      ∃ y : WC k, (y : Vℂ) ∈ F p ∧ Submodule.Quotient.mk y = x := by
  rw [complexGradedF]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy.1, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, ⟨hy, y.property⟩, rfl⟩

/-- Membership in the filtration on a complexified rational graded piece is detected after
transport to the complex graded piece and represented there by an element of `F p`. -/
@[simp]
theorem mem_gradedF_iff (hℚ : IsBaseChange ℚ ιℚ) (hℂ : IsBaseChange ℂ ιℂ)
    (WQ : ℤ → Submodule ℚ Vℚ) (hWQ : Monotone WQ) (F : ℤ → Submodule ℂ Vℂ) (k p : ℤ)
    (x : ℂ ⊗[ℚ] weightGradedRat WQ k) :
    x ∈ gradedF hℚ hℂ WQ hWQ F k p ↔
      ∃ y : rationalToComplexSubmodule hℚ hℂ (WQ k), (y : Vℂ) ∈ F p ∧
        Submodule.Quotient.mk y = gradedComplexEquiv hℚ hℂ WQ hWQ k x := by
  simp [gradedF]

/-- The induced filtration on a complex graded piece is decreasing. -/
theorem complexGradedF_antitone (WC F : ℤ → Submodule ℂ Vℂ) (hF : Antitone F) (k : ℤ) :
    Antitone (complexGradedF WC F k) := fun _ _ h ↦
  Submodule.map_mono (Submodule.comap_mono (inf_le_inf_right _ (hF h)))

/-- A step where the Hodge filtration is everything induces everything on a graded piece. -/
@[simp]
theorem complexGradedF_of_eq_top (WC F : ℤ → Submodule ℂ Vℂ) {k p : ℤ} (hp : F p = ⊤) :
    complexGradedF WC F k p = ⊤ := by
  rw [complexGradedF, hp, top_inf_eq, Submodule.submoduleOf_self, Submodule.map_top,
    Submodule.range_mkQ]

/-- A step where the Hodge filtration is zero induces zero on a graded piece. -/
@[simp]
theorem complexGradedF_of_eq_bot (WC F : ℤ → Submodule ℂ Vℂ) {k p : ℤ} (hp : F p = ⊥) :
    complexGradedF WC F k p = ⊥ := by
  have hbot : (⊥ : Submodule ℂ Vℂ).submoduleOf (WC k) = ⊥ := by
    simp [Submodule.submoduleOf]
  rw [complexGradedF, hp, bot_inf_eq, hbot, Submodule.map_bot]

/-- The filtration induced on a complexified rational graded piece is decreasing. -/
theorem gradedF_antitone (hℚ : IsBaseChange ℚ ιℚ) (hℂ : IsBaseChange ℂ ιℂ)
    (WQ : ℤ → Submodule ℚ Vℚ) (hWQ : Monotone WQ) (F : ℤ → Submodule ℂ Vℂ) (hF : Antitone F)
    (k : ℤ) : Antitone (gradedF hℚ hℂ WQ hWQ F k) := fun _ _ h ↦
  Submodule.comap_mono (complexGradedF_antitone _ F hF k h)

/-- A step where the Hodge filtration is everything induces everything on a graded piece. -/
@[simp]
theorem gradedF_of_eq_top (hℚ : IsBaseChange ℚ ιℚ) (hℂ : IsBaseChange ℂ ιℂ)
    (WQ : ℤ → Submodule ℚ Vℚ) (hWQ : Monotone WQ) (F : ℤ → Submodule ℂ Vℂ) {k p : ℤ}
    (hp : F p = ⊤) : gradedF hℚ hℂ WQ hWQ F k p = ⊤ := by
  rw [gradedF, complexGradedF_of_eq_top _ F hp, Submodule.comap_top]

/-- A step where the Hodge filtration is zero induces zero on a graded piece. -/
@[simp]
theorem gradedF_of_eq_bot (hℚ : IsBaseChange ℚ ιℚ) (hℂ : IsBaseChange ℂ ιℂ)
    (WQ : ℤ → Submodule ℚ Vℚ) (hWQ : Monotone WQ) (F : ℤ → Submodule ℂ Vℂ) {k p : ℤ}
    (hp : F p = ⊥) : gradedF hℚ hℂ WQ hWQ F k p = ⊥ := by
  rw [gradedF, complexGradedF_of_eq_bot _ F hp, Submodule.comap_bot, LinearMap.ker_eq_bot]
  exact (gradedComplexEquiv hℚ hℂ WQ hWQ k).injective

section Concentrated

variable (hℚ : IsBaseChange ℚ ιℚ) (hℂ : IsBaseChange ℂ ιℂ)

variable (WQ : ℤ → Submodule ℚ Vℚ) (hWQ : Monotone WQ) {k : ℤ}
  (hbot : WQ (k - 1) = ⊥) (htop : WQ k = ⊤)

include hbot in
private theorem submoduleOf_rationalToComplexSubmodule_eq_bot :
    (rationalToComplexSubmodule hℚ hℂ (WQ (k - 1))).submoduleOf
      (rationalToComplexSubmodule hℚ hℂ (WQ k)) = ⊥ := by
  rw [hbot, rationalToComplexSubmodule_bot]
  simp [Submodule.submoduleOf]

/-- Across a step where the weight filtration jumps from zero to everything, the complexification
of the rational graded piece `grᵂ_k` is the whole complex model. -/
noncomputable def gradedEquivOfEqBotOfEqTop :
    ℂ ⊗[ℚ] weightGradedRat WQ k ≃ₗ[ℂ] Vℂ :=
  (gradedComplexEquiv hℚ hℂ WQ hWQ k).trans
    ((Submodule.quotEquivOfEqBot _
        (submoduleOf_rationalToComplexSubmodule_eq_bot hℚ hℂ WQ hbot)).trans
      ((LinearEquiv.ofEq _ ⊤ (by rw [htop, rationalToComplexSubmodule_top])).trans
        Submodule.topEquiv))

@[simp]
theorem gradedEquivOfEqBotOfEqTop_tmul_mk (z : ℂ) (x : WQ k) :
    gradedEquivOfEqBotOfEqTop hℚ hℂ WQ hWQ hbot htop (z ⊗ₜ[ℚ] Submodule.Quotient.mk x) =
      rationalToComplexLinearEquiv hℚ hℂ (z ⊗ₜ[ℚ] (x : Vℚ)) := by
  simp [gradedEquivOfEqBotOfEqTop]

/-- Across such a step, the filtration induced on the graded piece is the Hodge filtration
itself, read through the identification above. -/
theorem gradedF_eq_comap (F : ℤ → Submodule ℂ Vℂ) (p : ℤ) :
    gradedF hℚ hℂ WQ hWQ F k p =
      (F p).comap (gradedEquivOfEqBotOfEqTop hℚ hℂ WQ hWQ hbot htop).toLinearMap := by
  have hker := submoduleOf_rationalToComplexSubmodule_eq_bot hℚ hℂ WQ hbot
  ext t
  simp only [gradedF, gradedEquivOfEqBotOfEqTop, Submodule.mem_comap, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply]
  generalize gradedComplexEquiv hℚ hℂ WQ hWQ k t = q
  induction q using Submodule.Quotient.induction_on with
  | _ y =>
    have hmemS : ∀ z : rationalToComplexSubmodule hℚ hℂ (WQ k),
        z ∈ (F p ⊓ rationalToComplexSubmodule hℚ hℂ (WQ k)).submoduleOf
            (rationalToComplexSubmodule hℚ hℂ (WQ k)) ↔ (z : Vℂ) ∈ F p := by
      intro z
      simp [Submodule.submoduleOf]
    simp only [complexGradedF, Submodule.mem_map, Submodule.mkQ_apply,
      Submodule.quotEquivOfEqBot_apply_mk, Submodule.topEquiv_apply, LinearEquiv.coe_ofEq_apply]
    constructor
    · rintro ⟨z, hz, hzy⟩
      rw [Submodule.Quotient.eq, hker, Submodule.mem_bot, sub_eq_zero] at hzy
      rw [← hzy]
      exact (hmemS z).1 hz
    · intro hy
      exact ⟨y, (hmemS y).2 hy, rfl⟩

/-- The identification of the graded piece with the whole complex model intertwines the canonical
conjugation of the complexified rational graded piece with lattice conjugation. -/
theorem gradedEquivOfEqBotOfEqTop_latticeConj (x : ℂ ⊗[ℚ] weightGradedRat WQ k) :
    gradedEquivOfEqBotOfEqTop hℚ hℂ WQ hWQ hbot htop
        (latticeConj (isBaseChange_ratTensorMap ℂ (weightGradedRat WQ k)) x) =
      latticeConj hℂ (gradedEquivOfEqBotOfEqTop hℚ hℂ WQ hWQ hbot htop x) := by
  have hfix : ∀ v : Vℤ,
      ((gradedEquivOfEqBotOfEqTop hℚ hℂ WQ hWQ hbot htop).toLinearMap.comp
          ((latticeConj (isBaseChange_ratTensorMap ℂ (weightGradedRat WQ k))).comp
            (gradedEquivOfEqBotOfEqTop hℚ hℂ WQ hWQ hbot htop).symm.toLinearMap)) (ιℂ v) =
        ιℂ v := by
    intro v
    have hmem : ιℚ v ∈ WQ k := by rw [htop]; trivial
    have hpre : (gradedEquivOfEqBotOfEqTop hℚ hℂ WQ hWQ hbot htop).symm (ιℂ v) =
        (1 : ℂ) ⊗ₜ[ℚ] Submodule.Quotient.mk ⟨ιℚ v, hmem⟩ := by
      rw [LinearEquiv.symm_apply_eq, gradedEquivOfEqBotOfEqTop_tmul_mk]
      simp
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      hpre, latticeConj_ratTensorMap_tmul, map_one, gradedEquivOfEqBotOfEqTop_tmul_mk]
    simp
  have hx := congrArg
    (fun f : Vℂ →ₛₗ[starRingEnd ℂ] Vℂ ↦ f (gradedEquivOfEqBotOfEqTop hℚ hℂ WQ hWQ hbot htop x))
    (latticeConj_unique hℂ _ hfix)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hx

end Concentrated

end TauCeti.Hodge
