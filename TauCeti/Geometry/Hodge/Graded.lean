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
* `TauCeti.Hodge.weightGradedRatMap`, `TauCeti.Hodge.weightGradedComplexMap`: the maps induced on
  the graded pieces by a linear map preserving every step of the filtration, together with their
  functoriality and the naturality of `TauCeti.Hodge.gradedComplexEquiv` in that map.
* `TauCeti.Hodge.complexGradedF`, `TauCeti.Hodge.gradedF`: the Hodge filtration induced on the
  complex graded piece and on the complexified rational graded piece.
* `TauCeti.Hodge.complexGradedConjugation`, `TauCeti.Hodge.gradedComplexConjugation`: the
  conjugation induced on a complex graded piece by a conjugation stabilising the two filtration
  steps it is built from, and its instance for a complexified rational filtration and lattice
  conjugation.
* `TauCeti.Hodge.gradedComplexEquiv_latticeConj`: the comparison of the two graded models
  intertwines those conjugations.
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

universe u v w u' v' w'

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

section Map

variable {V'ℤ : Type u'} {V'ℚ : Type v'} {V'ℂ : Type w'}
variable [AddCommGroup V'ℤ]
variable [AddCommGroup V'ℚ] [Module ℚ V'ℚ]
variable [AddCommGroup V'ℂ] [Module ℂ V'ℂ]
variable {ι'ℚ : V'ℤ →ₗ[ℤ] V'ℚ} {ι'ℂ : V'ℤ →ₗ[ℤ] V'ℂ}

/-- The map induced on the `k`-th rational graded piece by a linear map carrying every step of one
increasing filtration into the corresponding step of another. -/
noncomputable def weightGradedRatMap (WQ : ℤ → Submodule ℚ Vℚ) (W'Q : ℤ → Submodule ℚ V'ℚ)
    (f : Vℚ →ₗ[ℚ] V'ℚ) (hf : ∀ k x, x ∈ WQ k → f x ∈ W'Q k) (k : ℤ) :
    weightGradedRat WQ k →ₗ[ℚ] weightGradedRat W'Q k :=
  Submodule.mapQ _ _ (f.restrict fun x hx ↦ hf k x hx) fun x hx ↦ hf (k - 1) x hx

/-- The induced map on a rational graded piece sends the class of a vector to the class of its
image. -/
@[simp]
theorem weightGradedRatMap_mk (WQ : ℤ → Submodule ℚ Vℚ) (W'Q : ℤ → Submodule ℚ V'ℚ)
    (f : Vℚ →ₗ[ℚ] V'ℚ) (hf : ∀ k x, x ∈ WQ k → f x ∈ W'Q k) (k : ℤ) (x : WQ k) :
    weightGradedRatMap WQ W'Q f hf k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨f x, hf k x x.2⟩ :=
  (rfl)

/-- The map induced on the `k`-th graded piece of a complex filtration by a complex-linear map
carrying every step into the corresponding step of another filtration. -/
noncomputable def weightGradedComplexMap (WC : ℤ → Submodule ℂ Vℂ) (W'C : ℤ → Submodule ℂ V'ℂ)
    (g : Vℂ →ₗ[ℂ] V'ℂ) (hg : ∀ k x, x ∈ WC k → g x ∈ W'C k) (k : ℤ) :
    weightGradedComplex WC k →ₗ[ℂ] weightGradedComplex W'C k :=
  Submodule.mapQ _ _ (g.restrict fun x hx ↦ hg k x hx) fun x hx ↦ hg (k - 1) x hx

/-- The induced map on a complex graded piece sends the class of a vector to the class of its
image. -/
@[simp]
theorem weightGradedComplexMap_mk (WC : ℤ → Submodule ℂ Vℂ) (W'C : ℤ → Submodule ℂ V'ℂ)
    (g : Vℂ →ₗ[ℂ] V'ℂ) (hg : ∀ k x, x ∈ WC k → g x ∈ W'C k) (k : ℤ)
    (x : WC k) :
    weightGradedComplexMap WC W'C g hg k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨g x, hg k x x.2⟩ :=
  (rfl)

/-- Passage to the complex graded pieces sends the identity map to the identity. -/
@[simp]
theorem weightGradedComplexMap_id (WC : ℤ → Submodule ℂ Vℂ) (k : ℤ) :
    weightGradedComplexMap WC WC LinearMap.id (fun _ _ hx ↦ hx) k = LinearMap.id := by
  have hrestrict : (LinearMap.id : Vℂ →ₗ[ℂ] Vℂ).restrict (fun x (hx : x ∈ WC k) ↦ hx) =
      LinearMap.id := LinearMap.ext fun _ ↦ Subtype.ext rfl
  simp only [weightGradedComplexMap, hrestrict, Submodule.mapQ_id]

/-- Passage to the complex graded pieces is compatible with composition. -/
@[simp]
theorem weightGradedComplexMap_comp {V''ℂ : Type*} [AddCommGroup V''ℂ] [Module ℂ V''ℂ]
    (WC : ℤ → Submodule ℂ Vℂ) (W'C : ℤ → Submodule ℂ V'ℂ) (W''C : ℤ → Submodule ℂ V''ℂ)
    (f : Vℂ →ₗ[ℂ] V'ℂ) (hf : ∀ k x, x ∈ WC k → f x ∈ W'C k)
    (g : V'ℂ →ₗ[ℂ] V''ℂ) (hg : ∀ k x, x ∈ W'C k → g x ∈ W''C k) (k : ℤ) :
    weightGradedComplexMap WC W''C (g ∘ₗ f) (fun j x hx ↦ hg j _ (hf j x hx)) k =
      weightGradedComplexMap W'C W''C g hg k ∘ₗ weightGradedComplexMap WC W'C f hf k := by
  have hrestrict : (g ∘ₗ f).restrict (fun x (hx : x ∈ WC k) ↦ hg k _ (hf k x hx)) =
      (g.restrict fun x (hx : x ∈ W'C k) ↦ hg k x hx) ∘ₗ
        f.restrict fun x (hx : x ∈ WC k) ↦ hf k x hx :=
    LinearMap.ext fun _ ↦ Subtype.ext rfl
  simp only [weightGradedComplexMap, hrestrict]
  exact Submodule.mapQ_comp _ _ _ _ _ _ _

/-- Passage to the rational graded pieces sends the identity map to the identity. -/
@[simp]
theorem weightGradedRatMap_id (WQ : ℤ → Submodule ℚ Vℚ) (k : ℤ) :
    weightGradedRatMap WQ WQ LinearMap.id (fun _ _ hx ↦ hx) k = LinearMap.id := by
  have hrestrict : (LinearMap.id : Vℚ →ₗ[ℚ] Vℚ).restrict (fun x (hx : x ∈ WQ k) ↦ hx) =
      LinearMap.id := LinearMap.ext fun _ ↦ Subtype.ext rfl
  simp only [weightGradedRatMap, hrestrict, Submodule.mapQ_id]

/-- Passage to the rational graded pieces is compatible with composition. -/
@[simp]
theorem weightGradedRatMap_comp {V''ℚ : Type*} [AddCommGroup V''ℚ] [Module ℚ V''ℚ]
    (WQ : ℤ → Submodule ℚ Vℚ) (W'Q : ℤ → Submodule ℚ V'ℚ) (W''Q : ℤ → Submodule ℚ V''ℚ)
    (f : Vℚ →ₗ[ℚ] V'ℚ) (hf : ∀ k x, x ∈ WQ k → f x ∈ W'Q k)
    (g : V'ℚ →ₗ[ℚ] V''ℚ) (hg : ∀ k x, x ∈ W'Q k → g x ∈ W''Q k) (k : ℤ) :
    weightGradedRatMap WQ W''Q (g ∘ₗ f) (fun j x hx ↦ hg j _ (hf j x hx)) k =
      weightGradedRatMap W'Q W''Q g hg k ∘ₗ weightGradedRatMap WQ W'Q f hf k := by
  have hrestrict : (g ∘ₗ f).restrict (fun x (hx : x ∈ WQ k) ↦ hg k _ (hf k x hx)) =
      (g.restrict fun x (hx : x ∈ W'Q k) ↦ hg k x hx) ∘ₗ
        f.restrict fun x (hx : x ∈ WQ k) ↦ hf k x hx :=
    LinearMap.ext fun _ ↦ Subtype.ext rfl
  simp only [weightGradedRatMap, hrestrict]
  exact Submodule.mapQ_comp _ _ _ _ _ _ _

/-- **The comparison `TauCeti.Hodge.gradedComplexEquiv` is natural in the filtered map**: the
square formed by the map induced on the rational graded pieces, its base change, and the map
induced by the complexification on the graded pieces of the complexified filtrations, commutes.
Preservation of the complexified filtration is not a separate hypothesis: it follows from the
rational one by `TauCeti.Hodge.map_rationalToComplexSubmodule_le`. -/
theorem gradedComplexEquiv_baseChange_weightGradedRatMap (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (h'ℚ : IsBaseChange ℚ ι'ℚ) (h'ℂ : IsBaseChange ℂ ι'ℂ)
    (WQ : ℤ → Submodule ℚ Vℚ) (hWQ : Monotone WQ) (W'Q : ℤ → Submodule ℚ V'ℚ)
    (hW'Q : Monotone W'Q) (f : Vℚ →ₗ[ℚ] V'ℚ) (hf : ∀ k x, x ∈ WQ k → f x ∈ W'Q k)
    (k : ℤ) (t : ℂ ⊗[ℚ] weightGradedRat WQ k) :
    gradedComplexEquiv h'ℚ h'ℂ W'Q hW'Q k ((weightGradedRatMap WQ W'Q f hf k).baseChange ℂ t) =
      weightGradedComplexMap (fun j ↦ rationalToComplexSubmodule hℚ hℂ (WQ j))
          (fun j ↦ rationalToComplexSubmodule h'ℚ h'ℂ (W'Q j))
          (rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f)
          (fun j _ hx ↦ map_rationalToComplexSubmodule_le hℚ hℂ h'ℚ h'ℂ f
            (Submodule.map_le_iff_le_comap.2 fun y hy ↦ hf j y hy) ⟨_, hx, rfl⟩) k
        (gradedComplexEquiv hℚ hℂ WQ hWQ k t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul z x =>
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        rw [LinearMap.baseChange_tmul, weightGradedRatMap_mk, gradedComplexEquiv_tmul_mk,
          gradedComplexEquiv_tmul_mk, weightGradedComplexMap_mk]
        refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
        simp only [coe_rationalToComplexSubmoduleEquiv, LinearMap.baseChange_tmul,
          Submodule.subtype_apply, rationalMapToComplex_rationalToComplexLinearEquiv_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Map

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

section GradedConjugation

variable (WC : ℤ → Submodule ℂ Vℂ) (ω : Conjugation Vℂ) (k : ℤ)

/-- The conjugation induced on the `k`-th complex graded piece by a conjugation of the ambient
space that stabilises the two steps `WC k` and `WC (k - 1)` the piece is built from. -/
noncomputable def complexGradedConjugation (hk : ∀ x ∈ WC k, ω.toEquiv x ∈ WC k)
    (hk₁ : ∀ x ∈ WC (k - 1), ω.toEquiv x ∈ WC (k - 1)) :
    Conjugation (weightGradedComplex WC k) :=
  (ω.restrict hk).quotient fun x hx ↦ by
    simpa only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
      Conjugation.restrict_toEquiv_apply] using hk₁ (x : Vℂ) hx

/-- The induced conjugation on a complex graded piece acts on classes through the ambient
conjugation. -/
@[simp]
theorem complexGradedConjugation_mk (hk : ∀ x ∈ WC k, ω.toEquiv x ∈ WC k)
    (hk₁ : ∀ x ∈ WC (k - 1), ω.toEquiv x ∈ WC (k - 1)) (x : WC k) :
    (complexGradedConjugation WC ω k hk hk₁).toEquiv (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨ω.toEquiv (x : Vℂ), hk (x : Vℂ) x.2⟩ := by
  rw [complexGradedConjugation, Conjugation.quotient_toEquiv_mk]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (ω.restrict_toEquiv_apply hk x))

/-- Conjugating the filtration induced on a complex graded piece is inducing the conjugate
filtration. -/
theorem map_complexGradedConjugation_complexGradedF
    (hk : ∀ x ∈ WC k, ω.toEquiv x ∈ WC k)
    (hk₁ : ∀ x ∈ WC (k - 1), ω.toEquiv x ∈ WC (k - 1)) (F : ℤ → Submodule ℂ Vℂ) (p : ℤ) :
    (complexGradedF WC F k p).map
        (complexGradedConjugation WC ω k hk hk₁).toEquiv.toLinearMap =
      complexGradedF WC (fun q ↦ (F q).map ω.toEquiv.toLinearMap) k p := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    intro u hu
    obtain ⟨z, hz, rfl⟩ := (mem_complexGradedF_iff WC F k p u).1 hu
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, complexGradedConjugation_mk,
      mem_complexGradedF_iff]
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  · intro u hu
    obtain ⟨y, hy, rfl⟩ :=
      (mem_complexGradedF_iff WC (fun q ↦ (F q).map ω.toEquiv.toLinearMap) k p u).1 hu
    obtain ⟨w, hw, hwy⟩ := hy
    refine ⟨Submodule.Quotient.mk ⟨ω.toEquiv (y : Vℂ), hk (y : Vℂ) y.2⟩, ?_, ?_⟩
    · simp only [SetLike.mem_coe, mem_complexGradedF_iff]
      refine ⟨_, ?_, rfl⟩
      simpa only [← hwy, LinearEquiv.coe_coe, ω.apply_apply, SetLike.mem_coe] using hw
    · rw [LinearEquiv.coe_coe, complexGradedConjugation_mk]
      exact congrArg Submodule.Quotient.mk (Subtype.ext (ω.apply_apply (y : Vℂ)))

end GradedConjugation

section RationalGradedConjugation

variable (hℚ : IsBaseChange ℚ ιℚ) (hℂ : IsBaseChange ℂ ιℂ) (WQ : ℤ → Submodule ℚ Vℚ)

/-- The conjugation induced on the `k`-th graded piece of a complexified rational weight
filtration by lattice conjugation. Every step of the filtration is the complexification of a
rational subspace, hence conjugation-stable. -/
noncomputable def gradedComplexConjugation (k : ℤ) :
    Conjugation (weightGradedComplex (fun j ↦ rationalToComplexSubmodule hℚ hℂ (WQ j)) k) :=
  complexGradedConjugation (fun j ↦ rationalToComplexSubmodule hℚ hℂ (WQ j))
    (latticeConjugation hℂ) k
    (fun x hx ↦ by
      simpa only [latticeConjugation_toEquiv_apply] using
        (rationalToComplexSubmodule_conj hℚ hℂ (WQ k)).le ⟨x, hx, rfl⟩)
    (fun x hx ↦ by
      simpa only [latticeConjugation_toEquiv_apply] using
        (rationalToComplexSubmodule_conj hℚ hℂ (WQ (k - 1))).le ⟨x, hx, rfl⟩)

/-- The induced conjugation on the graded piece of a complexified rational filtration acts on a
class through lattice conjugation of a representative. -/
@[simp]
theorem gradedComplexConjugation_mk (k : ℤ)
    (x : rationalToComplexSubmodule hℚ hℂ (WQ k)) :
    (gradedComplexConjugation hℚ hℂ WQ k).toEquiv (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨latticeConj hℂ (x : Vℂ),
        (rationalToComplexSubmodule_conj hℚ hℂ (WQ k)).le ⟨x, x.2, rfl⟩⟩ := by
  rw [gradedComplexConjugation, complexGradedConjugation_mk]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (latticeConjugation_toEquiv_apply hℂ _))

/-- Conjugating the filtration induced on the graded piece of a complexified rational filtration
is inducing the conjugate filtration. -/
theorem map_gradedComplexConjugation_complexGradedF (F : ℤ → Submodule ℂ Vℂ) (k p : ℤ) :
    (complexGradedF (fun j ↦ rationalToComplexSubmodule hℚ hℂ (WQ j)) F k p).map
        (gradedComplexConjugation hℚ hℂ WQ k).toEquiv.toLinearMap =
      complexGradedF (fun j ↦ rationalToComplexSubmodule hℚ hℂ (WQ j))
        (fun q ↦ (F q).map (latticeConj hℂ)) k p := by
  rw [gradedComplexConjugation, map_complexGradedConjugation_complexGradedF]
  simp only [latticeConjugation_toLinearMap]

/-- **The comparison `TauCeti.Hodge.gradedComplexEquiv` intertwines the conjugations**: the
canonical conjugation of the complexified rational graded piece corresponds to the conjugation
that lattice conjugation induces on the complex graded piece.

This is what makes the pure Hodge structure carried by `ℂ ⊗[ℚ] grᵂ_k` transportable to the
complex graded piece `(W_k)_ℂ / (W_{k-1})_ℂ`, where the Hodge filtration of a mixed Hodge
structure lives. -/
theorem gradedComplexEquiv_latticeConj (hWQ : Monotone WQ) (k : ℤ)
    (x : ℂ ⊗[ℚ] weightGradedRat WQ k) :
    gradedComplexEquiv hℚ hℂ WQ hWQ k
        (latticeConj (isBaseChange_ratTensorMap ℂ (weightGradedRat WQ k)) x) =
      (gradedComplexConjugation hℚ hℂ WQ k).toEquiv (gradedComplexEquiv hℚ hℂ WQ hWQ k x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z y =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        rw [latticeConj_ratTensorMap_tmul, gradedComplexEquiv_tmul_mk, gradedComplexEquiv_tmul_mk,
          gradedComplexConjugation, complexGradedConjugation_mk]
        refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
        simp only [coe_rationalToComplexSubmoduleEquiv, LinearMap.baseChange_tmul,
          Submodule.subtype_apply, latticeConjugation_toEquiv_apply]
        rw [latticeConj_rationalToComplexLinearEquiv_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The inverse of the comparison intertwines the conjugations, in the form in which transport of
a pure Hodge structure onto the complex graded piece consumes it. -/
theorem gradedComplexEquiv_symm_latticeConj (hWQ : Monotone WQ) (k : ℤ)
    (y : weightGradedComplex (fun j ↦ rationalToComplexSubmodule hℚ hℂ (WQ j)) k) :
    (gradedComplexEquiv hℚ hℂ WQ hWQ k).symm ((gradedComplexConjugation hℚ hℂ WQ k).toEquiv y) =
      (latticeConjugation (isBaseChange_ratTensorMap ℂ (weightGradedRat WQ k))).toEquiv
        ((gradedComplexEquiv hℚ hℂ WQ hWQ k).symm y) := by
  apply (gradedComplexEquiv hℚ hℂ WQ hWQ k).injective
  rw [LinearEquiv.apply_symm_apply, latticeConjugation_toEquiv_apply,
    gradedComplexEquiv_latticeConj hℚ hℂ WQ hWQ k, LinearEquiv.apply_symm_apply]

end RationalGradedConjugation

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
