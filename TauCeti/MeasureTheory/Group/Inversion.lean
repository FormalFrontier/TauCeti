/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import TauCeti.MeasureTheory.Group.Conjugation

/-!
# Precomposition with inversion on `Lp` of a group

A measure on a group that is invariant under inversion — normalized Haar measure on a compact
group, for instance — makes `g ↦ g⁻¹` measure preserving, so precomposition with it is a linear
isometry of `Lp E p μ`.  Inversion is an involution, so this isometry is an involution too, and in
particular injective: an element of `Lp` vanishes exactly when its inverse-translate does.

The construction is Mathlib's `MeasureTheory.Lp.compMeasurePreservingₗᵢ` at the map `Inv.inv`; what
this file adds is the involutivity, the interaction with the class functions of
`TauCeti/MeasureTheory/Group/Conjugation.lean`, and the compatibility with the continuous functions
that supply the elements of `Lp` in practice.

The intended use is the change of variables `∫ f g⁻¹ dg = ∫ f g dg` in inner-product form: for `p`
equal to `2` this map preserves the inner product, which is what turns a statement about a function
into the corresponding statement about its inverse-translate.

## Main definitions

* `TauCeti.invLpₗᵢ`: precomposition with inversion, as a linear isometry of `Lp E p μ`.

## Main statements

* `TauCeti.coeFn_invLpₗᵢ`: it is represented by `g ↦ f g⁻¹`.
* `TauCeti.invLpₗᵢ_invLpₗᵢ`: it is an involution, hence
  (`TauCeti.invLpₗᵢ_eq_zero_iff`) injective.
* `TauCeti.invLpₗᵢ_mem_classFunctionLp` and `TauCeti.invLpₗᵢ_mem_classFunctionLp_iff`: it preserves
  the class functions, because inversion commutes with conjugation, and being an involution it
  reflects them too.
* `TauCeti.invLpₗᵢ_toLp`: on a continuous function it is precomposition with inversion.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {G E : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure G} [μ.IsInvInvariant]
variable (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- **Precomposition with inversion on `Lp` of a group**, for a measure invariant under inversion.
It is a linear isometry because `g ↦ g⁻¹` preserves `μ`. -/
noncomputable def invLpₗᵢ : Lp E p μ →ₗᵢ[𝕜] Lp E p μ :=
  Lp.compMeasurePreservingₗᵢ 𝕜 Inv.inv (Measure.measurePreserving_inv μ)

variable {𝕜}

/-- The inverse-translate of a class of functions is represented by `g ↦ f g⁻¹`. -/
theorem coeFn_invLpₗᵢ (f : Lp E p μ) : invLpₗᵢ 𝕜 f =ᵐ[μ] fun g ↦ f g⁻¹ :=
  Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_inv μ)

/-- **Inverting twice is the identity.**  The two precompositions compose to precomposition with
`g ↦ (g⁻¹)⁻¹`, which is the identity on the nose. -/
@[simp]
theorem invLpₗᵢ_invLpₗᵢ (f : Lp E p μ) : invLpₗᵢ 𝕜 (invLpₗᵢ 𝕜 f) = f := by
  refine Lp.ext ?_
  have h : ∀ᵐ g ∂μ, (invLpₗᵢ 𝕜 f) g⁻¹ = f g := by
    refine ((Measure.measurePreserving_inv μ).quasiMeasurePreserving.ae_eq
      (coeFn_invLpₗᵢ (𝕜 := 𝕜) f)).mono fun g hg ↦ ?_
    simpa using hg
  exact ((coeFn_invLpₗᵢ (𝕜 := 𝕜) (invLpₗᵢ 𝕜 f)).trans h)

/-- **The inverse-translate of `f` vanishes exactly when `f` does.**  Injectivity of a linear
isometry, in the form in which the argument on the inverse-translate of a function returns a
statement about the function itself. -/
@[simp]
theorem invLpₗᵢ_eq_zero_iff {f : Lp E p μ} : invLpₗᵢ 𝕜 f = 0 ↔ f = 0 :=
  map_eq_zero_iff _ (invLpₗᵢ (E := E) (p := p) (μ := μ) 𝕜).injective

section ClassFunction

variable [MeasurableMul G] [SMulInvariantMeasure (ConjAct G) G μ]

/-- **Inversion preserves the class functions.**  Conjugation commutes with inversion,
`(h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹`, so the conjugates of the inverse-translate of `f` are the
inverse-translates of the conjugates of `f`. -/
theorem invLpₗᵢ_mem_classFunctionLp {f : Lp E p μ} (hf : f ∈ classFunctionLp 𝕜 E p μ) :
    invLpₗᵢ 𝕜 f ∈ classFunctionLp 𝕜 E p μ := by
  rw [mem_classFunctionLp_iff_ae] at hf ⊢
  intro h
  -- Read both sides through the representative `g ↦ f g⁻¹`.
  have hconj : (fun g ↦ (invLpₗᵢ 𝕜 f) (h * g * h⁻¹)) =ᵐ[μ] fun g ↦ f (h * g⁻¹ * h⁻¹) := by
    refine ((measurePreserving_conj μ h).quasiMeasurePreserving.ae_eq
      (coeFn_invLpₗᵢ (𝕜 := 𝕜) f)).mono fun g hg ↦ ?_
    simpa [mul_assoc] using hg
  have hcl : (fun g ↦ f (h * g⁻¹ * h⁻¹)) =ᵐ[μ] fun g ↦ f g⁻¹ :=
    (Measure.measurePreserving_inv μ).quasiMeasurePreserving.ae_eq (hf h)
  exact (hconj.trans hcl).trans (coeFn_invLpₗᵢ (𝕜 := 𝕜) f).symm

/-- **Inversion reflects the class functions.**  Preservation both ways, since inversion is an
involution: the inverse-translate of `f` is a class function exactly when `f` is one.

Not a `simp` lemma: `TauCeti.mem_classFunctionLp_iff` already rewrites the left-hand side to the
invariance condition, so `simp` never reaches this one (the `simpNF` linter rejects it). -/
theorem invLpₗᵢ_mem_classFunctionLp_iff {f : Lp E p μ} :
    invLpₗᵢ 𝕜 f ∈ classFunctionLp 𝕜 E p μ ↔ f ∈ classFunctionLp 𝕜 E p μ :=
  ⟨fun hf ↦ by simpa only [invLpₗᵢ_invLpₗᵢ] using invLpₗᵢ_mem_classFunctionLp (𝕜 := 𝕜) hf,
    invLpₗᵢ_mem_classFunctionLp⟩

end ClassFunction

section Continuous

variable [TopologicalSpace G] [ContinuousInv G] [CompactSpace G] [BorelSpace G]
  [SecondCountableTopologyEither G E] [IsFiniteMeasure μ]

/-- **On a continuous function, inversion on `Lp` is precomposition with inversion.** -/
theorem invLpₗᵢ_toLp (F : C(G, E)) :
    invLpₗᵢ 𝕜 (ContinuousMap.toLp p μ 𝕜 F) =
      ContinuousMap.toLp p μ 𝕜 (F.comp ⟨Inv.inv, continuous_inv⟩) := by
  refine Lp.ext ((coeFn_invLpₗᵢ (𝕜 := 𝕜) _).trans ?_)
  have hF := ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := p) μ F
  have hFinv : (fun g ↦ (ContinuousMap.toLp p μ 𝕜 F) g⁻¹) =ᵐ[μ] fun g ↦ F g⁻¹ :=
    (Measure.measurePreserving_inv μ).quasiMeasurePreserving.ae_eq hF
  exact hFinv.trans (ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := p) μ
    (F.comp ⟨Inv.inv, continuous_inv⟩)).symm

end Continuous

end TauCeti
