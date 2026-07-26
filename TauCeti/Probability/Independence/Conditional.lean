/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Independence.Conditional
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Conditional independence and the indicator conditional-expectation projection

The two directions relating Mathlib's `ProbabilityTheory.CondIndep` to the "drop-information"
identity `μ[𝟙_H | mF ⊔ mG] =ᵐ μ[𝟙_H | mG]` on conditional expectations of indicators, together with
the generic contraction-independence identity that feeds them:

* `condIndep_of_indicator_condExp_eq` — builds `CondIndep mG mF mH` from that criterion (for all
  `mH`-measurable `H`).
* `condExp_indicator_sup_eq_of_condIndep` — the converse projection: from `CondIndep mG mF mH`,
  conditioning an `mH`-measurable indicator on the join `mF ⊔ mG` collapses to conditioning on `mG`.
* `condExp_indicator_eq_of_law_eq_of_comap_le` — Kallenberg's contraction-independence identity
  (Lemma 1.3): if the pair laws agree, `(X, W) =ᵈ (X, W')`, and `σ(W) ≤ σ(W')`, then conditioning
  the indicator of `X ⁻¹' A` on the finer `σ(W')` equals conditioning on the coarser `σ(W)`.  Its
  pair-law/L² machinery is generic conditional-expectation infrastructure, kept `private` here.

These feed the de Finetti block-product factorisation / prefix-deletion drop-info step —
the standard conditional-independence characterisation of the de Finetti route; see Kallenberg,
*Probabilistic Symmetries and Invariance Principles* (Springer, 2005). Adapted from
`cameronfreer/exchangeability` (`Probability/CondExp.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

/-- **Conditional independence from the drop-information criterion.** If conditioning `𝟙_H` on
`mF ⊔ mG` is a.e. the same as conditioning on `mG` (for every `mH`-measurable `H`), then `mF` and
`mH` are conditionally independent given `mG`. -/
theorem condIndep_of_indicator_condExp_eq {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {mF mG mH : MeasurableSpace Ω}
    (hmF : mF ≤ mΩ) (hmG : mG ≤ mΩ) (hmH : mH ≤ mΩ)
    (h : ∀ H, MeasurableSet[mH] H →
      μ[H.indicator (fun _ => (1 : ℝ)) | mF ⊔ mG]
        =ᵐ[μ] μ[H.indicator (fun _ => (1 : ℝ)) | mG]) :
    CondIndep mG mF mH hmG μ := by
  classical
  refine (condIndep_iff mG mF mH hmG hmF hmH μ).2 ?_
  intro tF tH htF htH
  set f1 : Ω → ℝ := tF.indicator (fun _ : Ω => (1 : ℝ)) with hf1
  set f2 : Ω → ℝ := tH.indicator (fun _ : Ω => (1 : ℝ)) with hf2
  -- The product of the two indicators is the indicator of the intersection; named once and reused.
  have h_f1f2 : (fun ω => f1 ω * f2 ω) = (tF ∩ tH).indicator (fun _ => (1 : ℝ)) := by
    funext ω; by_cases h1 : ω ∈ tF <;> by_cases h2 : ω ∈ tH <;>
      simp [hf1, hf2, Set.indicator, h1, h2, Set.mem_inter_iff] at *
  have hf1_int : Integrable f1 μ := Integrable.indicator (integrable_const (1 : ℝ)) (hmF _ htF)
  have hf2_int : Integrable f2 μ := Integrable.indicator (integrable_const (1 : ℝ)) (hmH _ htH)
  have hf1_aesm : AEStronglyMeasurable[mF ⊔ mG] f1 μ :=
    ((stronglyMeasurable_const.indicator htF).aestronglyMeasurable).mono
      (le_sup_left : mF ≤ mF ⊔ mG)
  have hProj : μ[f2 | mF ⊔ mG] =ᵐ[μ] μ[f2 | mG] := h tH htH
  have h_tower : μ[(fun ω => f1 ω * f2 ω) | mG]
      =ᵐ[μ] μ[ μ[(fun ω => f1 ω * f2 ω) | mF ⊔ mG] | mG] := by
    simpa using (condExp_condExp_of_le (μ := μ) (hm₁₂ := le_sup_right) (hm₂ := sup_le hmF hmG)
      (f := fun ω => f1 ω * f2 ω)).symm
  have hf1f2_int : Integrable (fun ω => f1 ω * f2 ω) μ := by
    rw [h_f1f2]
    exact Integrable.indicator (integrable_const (1 : ℝ))
      (MeasurableSet.inter (hmF _ htF) (hmH _ htH))
  have h_pull_middle : μ[(fun ω => f1 ω * f2 ω) | mF ⊔ mG] =ᵐ[μ] f1 * μ[f2 | mF ⊔ mG] :=
    condExp_mul_of_aestronglyMeasurable_left (μ := μ) (m := mF ⊔ mG) hf1_aesm hf1f2_int hf2_int
  have h_middle_to_G : μ[(fun ω => f1 ω * f2 ω) | mF ⊔ mG] =ᵐ[μ] f1 * μ[f2 | mG] :=
    h_pull_middle.trans <| Filter.EventuallyEq.mul Filter.EventuallyEq.rfl hProj
  have hf1_condExp_int : Integrable (f1 * μ[f2 | mG]) μ := by
    have heq : f1 * μ[f2 | mG] = tF.indicator (fun ω => μ[f2 | mG] ω) := by
      funext ω; by_cases hω : ω ∈ tF <;> simp [hf1, Set.indicator, hω]
    rw [heq]
    exact Integrable.indicator (integrable_condExp (μ := μ) (m := mG) (f := f2)) (hmF _ htF)
  have h_pull_outer : μ[f1 * μ[f2 | mG] | mG] =ᵐ[μ] μ[f1 | mG] * μ[f2 | mG] :=
    condExp_mul_of_aestronglyMeasurable_right (μ := μ) (m := mG)
      (stronglyMeasurable_condExp (μ := μ) (m := mG) (f := f2)).aestronglyMeasurable
      hf1_condExp_int hf1_int
  have h_prod : μ[(fun ω => f1 ω * f2 ω) | mG] =ᵐ[μ] μ[f1 | mG] * μ[f2 | mG] :=
    h_tower.trans ((condExp_congr_ae h_middle_to_G).trans h_pull_outer)
  rw [h_f1f2] at h_prod
  simpa only [hf1, hf2] using h_prod

/-- Pointwise product with the constant-`1` indicator of `s` restricts a function to the
indicator of `s`. Lets indicator products be rewritten without pointwise case splits. -/
private lemma mul_indicator_one_eq_indicator {Ω : Type*} (s : Set Ω) (φ : Ω → ℝ) :
    φ * s.indicator (fun _ => (1 : ℝ)) = s.indicator φ := by
  funext ω
  rw [Pi.mul_apply, ← Set.indicator_mul_right]
  simp

/-- Rectangle step for `condExp_indicator_sup_eq_of_condIndep`: over a rectangle `tF ∩ tG` (`tF`
`mF`-measurable, `tG` `mG`-measurable), the conditional expectation given `mG` of an
`mH`-measurable indicator integrates to the same value as the indicator itself. -/
private lemma setIntegral_condExp_indicator_eq_on_rectangle {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] {μ : @Measure Ω mΩ} [IsFiniteMeasure μ]
    {mF mG mH : MeasurableSpace Ω}
    (hmF : mF ≤ mΩ) (hmG : mG ≤ mΩ) (hmH : mH ≤ mΩ)
    (hCI : CondIndep mG mF mH hmG μ)
    {H : Set Ω} (hH : MeasurableSet[mH] H)
    {tF tG : Set Ω} (htF : MeasurableSet[mF] tF) (htG : MeasurableSet[mG] tG) :
    ∫ x in tF ∩ tG, (μ[H.indicator (fun _ => (1 : ℝ)) | mG]) x ∂μ
      = ∫ x in tF ∩ tG, H.indicator (fun _ => (1 : ℝ)) x ∂μ := by
  classical
  let m0 : MeasurableSpace Ω := mΩ
  set f : Ω → ℝ := H.indicator (fun _ => (1 : ℝ)) with hf_def
  have htF_m0 : MeasurableSet[m0] tF := hmF _ htF
  set gB : Ω → ℝ := tF.indicator (fun _ => (1 : ℝ)) with hgB_def
  have hInt_ce : Integrable (μ[f | mG]) μ := integrable_condExp
  have h_mul_eq_indicator :
      (fun ω => μ[f | mG] ω * gB ω) = tF.indicator (μ[f | mG]) := by
    rw [hgB_def]; exact mul_indicator_one_eq_indicator tF (μ[f | mG])
  have hint_prod : Integrable (fun ω => μ[f | mG] ω * gB ω) μ := by
    simpa only [h_mul_eq_indicator] using hInt_ce.indicator htF_m0
  have hint_B : Integrable gB μ := Integrable.indicator (integrable_const 1) htF_m0
  have hfg : (f * gB) = (tF ∩ H).indicator (fun _ => (1 : ℝ)) := by
    rw [hgB_def, mul_indicator_one_eq_indicator, hf_def, Set.indicator_indicator]
  have hprod_int : Integrable (f * gB) μ := by
    rw [hfg]
    exact Integrable.indicator (integrable_const 1) ((hmF _ htF).inter (hmH _ hH))
  have hprodf : μ[f * gB | mG] =ᵐ[μ] μ[f | mG] * μ[gB | mG] := by
    rw [hfg]
    exact ((condIndep_iff mG mF mH hmG hmF hmH μ).mp hCI _ _ htF hH).trans
      (Filter.EventuallyEq.of_eq (mul_comm _ _))
  have h_pull : μ[(μ[f | mG]) * gB | mG] =ᵐ[μ] (μ[f | mG]) * μ[gB | mG] :=
    condExp_mul_of_aestronglyMeasurable_left
      stronglyMeasurable_condExp.aestronglyMeasurable hint_prod hint_B
  calc ∫ x in tF ∩ tG, (μ[f | mG]) x ∂μ
      = ∫ x in tG, (μ[f | mG] * gB) x ∂μ := by
        have hh1 : ∫ ω in tG ∩ tF, μ[f | mG] ω ∂μ
            = ∫ ω in tG, tF.indicator (μ[f | mG]) ω ∂μ := by
          rw [setIntegral_indicator htF_m0]
        have hh2 : ∫ ω in tG, tF.indicator (μ[f | mG]) ω ∂μ
            = ∫ ω in tG, μ[f | mG] ω * gB ω ∂μ := by rw [h_mul_eq_indicator]
        rw [Set.inter_comm]; exact hh1.trans hh2
    _ = ∫ x in tG, (μ[f | mG] * μ[gB | mG]) x ∂μ := by
        have h_set_eq : ∫ x in tG, μ[(μ[f | mG]) * gB | mG] x ∂μ
            = ∫ x in tG, ((μ[f | mG]) * gB) x ∂μ :=
          setIntegral_condExp hmG hint_prod htG
        rw [← h_set_eq]
        exact setIntegral_congr_ae (hmG _ htG)
          (by filter_upwards [h_pull] with x hx _; exact hx)
    _ = ∫ x in tG, (μ[f * gB | mG]) x ∂μ :=
        setIntegral_congr_ae (hmG _ htG)
          (by filter_upwards [hprodf] with x hx _; exact hx.symm)
    _ = ∫ x in tG, (f * gB) x ∂μ := setIntegral_condExp hmG hprod_int htG
    _ = ∫ x in tF ∩ tG, f x ∂μ := by
        have h_fg : (f * gB) = tF.indicator f := by
          rw [hgB_def, mul_indicator_one_eq_indicator]
        rw [h_fg, Set.inter_comm tF, setIntegral_indicator htF_m0]

/-- The sets `tF ∩ tG`, with `tF` being `mF`-measurable and `tG` being `mG`-measurable, form a
π-system. -/
private lemma isPiSystem_inter_measurableSet {Ω : Type*} (mF mG : MeasurableSpace Ω) :
    IsPiSystem
      {s : Set Ω | ∃ tF tG, MeasurableSet[mF] tF ∧ MeasurableSet[mG] tG ∧ s = tF ∩ tG} := by
  rintro s₁ ⟨tF₁, tG₁, htF₁, htG₁, rfl⟩ s₂ ⟨tF₂, tG₂, htF₂, htG₂, rfl⟩ _
  exact ⟨tF₁ ∩ tF₂, tG₁ ∩ tG₂, htF₁.inter htF₂, htG₁.inter htG₂, by
    ext ω; simp only [Set.mem_inter_iff]; tauto⟩

/-- The join `mF ⊔ mG` is generated by the sets `tF ∩ tG` with `tF` being `mF`-measurable and
`tG` being `mG`-measurable. -/
private lemma sup_eq_generateFrom_inter_measurableSet {Ω : Type*} (mF mG : MeasurableSpace Ω) :
    mF ⊔ mG = MeasurableSpace.generateFrom
      {s : Set Ω | ∃ tF tG, MeasurableSet[mF] tF ∧ MeasurableSet[mG] tG ∧ s = tF ∩ tG} := by
  refine le_antisymm (sup_le ?_ ?_) (MeasurableSpace.generateFrom_le ?_)
  · intro s hs
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨s, Set.univ, hs, MeasurableSet.univ, (Set.inter_univ s).symm⟩
  · intro s hs
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨Set.univ, s, MeasurableSet.univ, hs, (Set.univ_inter s).symm⟩
  · rintro s ⟨tF, tG, htF, htG, rfl⟩
    exact ((le_sup_left : mF ≤ mF ⊔ mG) _ htF).inter ((le_sup_right : mG ≤ mF ⊔ mG) _ htG)

/-- Under conditional independence, the conditional expectation `μ[𝟙_H | mG]` has the same
integral as `𝟙_H` over every `mF ⊔ mG`-measurable set. -/
private lemma setIntegral_condExp_indicator_eq_of_measurableSet_sup {Ω : Type*}
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {μ : @Measure Ω mΩ} [IsFiniteMeasure μ]
    {mF mG mH : MeasurableSpace Ω} (hmF : mF ≤ mΩ) (hmG : mG ≤ mΩ) (hmH : mH ≤ mΩ)
    (hCI : CondIndep mG mF mH hmG μ) {H : Set Ω} (hH : MeasurableSet[mH] H)
    {s : Set Ω} (hs : MeasurableSet[mF ⊔ mG] s) :
    ∫ x in s, (μ[H.indicator (fun _ => (1 : ℝ)) | mG]) x ∂μ
      = ∫ x in s, H.indicator (fun _ => (1 : ℝ)) x ∂μ := by
  classical
  set f : Ω → ℝ := H.indicator (fun _ => (1 : ℝ))
  have hmFG_le : mF ⊔ mG ≤ mΩ := sup_le hmF hmG
  have hf_int : Integrable f μ := Integrable.indicator (integrable_const (1 : ℝ)) (hmH _ hH)
  -- Induct over the π-system of rectangles `tF ∩ tG` generating the join.
  apply MeasurableSpace.induction_on_inter
    (C := fun s _ => ∫ x in s, (μ[f | mG]) x ∂μ = ∫ x in s, f x ∂μ)
    (sup_eq_generateFrom_inter_measurableSet mF mG) (isPiSystem_inter_measurableSet mF mG)
  · simp
  · rintro t ⟨tF, tG, htF, htG, rfl⟩
    exact setIntegral_condExp_indicator_eq_on_rectangle hmF hmG hmH hCI hH htF htG
  · intro t htm ht_ind
    have h_add : ∫ x in t, (μ[f | mG]) x ∂μ + ∫ x in tᶜ, (μ[f | mG]) x ∂μ
        = ∫ x, (μ[f | mG]) x ∂μ :=
      integral_add_compl₀ (hmFG_le _ htm).nullMeasurableSet integrable_condExp
    have h_add' : ∫ x in t, f x ∂μ + ∫ x in tᶜ, f x ∂μ = ∫ x, f x ∂μ :=
      integral_add_compl₀ (hmFG_le _ htm).nullMeasurableSet hf_int
    rw [ht_ind] at h_add
    have h_total : ∫ x, (μ[f | mG]) x ∂μ = ∫ x, f x ∂μ := integral_condExp hmG
    linarith
  · intro t_seq hdisjoint htm_seq ht_ind_seq
    have hd : Pairwise (Function.onFun Disjoint t_seq) := hdisjoint
    have h1 := hasSum_integral_iUnion (fun i => hmFG_le _ (htm_seq i)) hd
      (integrable_condExp : Integrable (μ[f | mG]) μ).integrableOn
    have h2 := hasSum_integral_iUnion (fun i => hmFG_le _ (htm_seq i)) hd hf_int.integrableOn
    exact h1.unique ((funext ht_ind_seq : (fun i => ∫ x in t_seq i, (μ[f | mG]) x ∂μ)
      = fun i => ∫ x in t_seq i, f x ∂μ) ▸ h2)
  · exact hs

/-- **Projection from conditional independence.** If `mF` and `mH` are conditionally independent
given `mG` (in the sense of Mathlib's `ProbabilityTheory.CondIndep`), then conditioning the
indicator of an `mH`-measurable set `H` on the join `mF ⊔ mG` collapses to conditioning on `mG`.
This is the converse of `condIndep_of_indicator_condExp_eq`. -/
theorem condExp_indicator_sup_eq_of_condIndep {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] {μ : @Measure Ω mΩ} [IsFiniteMeasure μ]
    {mF mG mH : MeasurableSpace Ω}
    (hmF : mF ≤ mΩ) (hmG : mG ≤ mΩ) (hmH : mH ≤ mΩ)
    (hCI : CondIndep mG mF mH hmG μ)
    {H : Set Ω} (hH : MeasurableSet[mH] H) :
    μ[H.indicator (fun _ => (1 : ℝ)) | mF ⊔ mG]
      =ᵐ[μ]
    μ[H.indicator (fun _ => (1 : ℝ)) | mG] := by
  have hf_int : Integrable (H.indicator (fun _ => (1 : ℝ))) μ :=
    Integrable.indicator (integrable_const (1 : ℝ)) (hmH _ hH)
  refine (ae_eq_condExp_of_forall_setIntegral_eq (sup_le hmF hmG) hf_int
    (fun _ _ _ => integrable_condExp.integrableOn) (fun s hs _ =>
      setIntegral_condExp_indicator_eq_of_measurableSet_sup hmF hmG hmH hCI hH hs)
    (stronglyMeasurable_condExp.aestronglyMeasurable.mono le_sup_right)).symm

/-! ### Kallenberg Lemma 1.3 (contraction-independence)

The pair-law/L² machinery below is generic conditional-expectation infrastructure: its hypotheses
mention only measurable maps, equality of pair laws, and the σ-algebra ordering `σ(W) ≤ σ(W')` —
never contractability.  The four support lemmas stay `private`; the contraction-independence
conclusion is public so the de Finetti prefix-deletion file can reuse it across the module boundary.
-/

variable {Ω α γ : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace γ]
  {μ : Measure Ω}

/-- From the pair-law equality `(X, W) =ᵈ (X, W')`, extract the marginal `W =ᵈ W'`. -/
private lemma marginal_law_eq_of_pair_law (X : Ω → α) (W W' : Ω → γ)
    (hX : Measurable X) (hW : Measurable W) (hW' : Measurable W')
    (h_law : Measure.map (fun ω => (X ω, W ω)) μ = Measure.map (fun ω => (X ω, W' ω)) μ) :
    Measure.map W μ = Measure.map W' μ := by
  have h := congrArg (Measure.map (Prod.snd : α × γ → γ)) h_law
  rwa [Measure.map_map measurable_snd (hX.prodMk hW),
    Measure.map_map measurable_snd (hX.prodMk hW')] at h

/-- If the pair laws agree, `(X, W) =ᵈ (X, W')`, the indicator of `X ⁻¹' A` has the same integral
over `W ⁻¹' B` as over `W' ⁻¹' B`. -/
private lemma setIntegral_indicator_preimage_eq_of_pair_law
    (X : Ω → α) (W W' : Ω → γ)
    (hX : Measurable X) (hW : Measurable W) (hW' : Measurable W')
    (h_law : Measure.map (fun ω => (X ω, W ω)) μ = Measure.map (fun ω => (X ω, W' ω)) μ)
    {A : Set α} (hA : MeasurableSet A) {B : Set γ} (hB : MeasurableSet B) :
    ∫ ω in W ⁻¹' B, (X ⁻¹' A).indicator (fun _ => (1 : ℝ)) ω ∂μ
      = ∫ ω in W' ⁻¹' B, (X ⁻¹' A).indicator (fun _ => (1 : ℝ)) ω ∂μ := by
  rw [setIntegral_indicator (hX hA), setIntegral_indicator (hX hA),
    setIntegral_const, setIntegral_const]
  congr 1
  rw [Set.inter_comm (W ⁻¹' B), Set.inter_comm (W' ⁻¹' B)]
  rw [← Set.mk_preimage_prod X W, ← Set.mk_preimage_prod X W']
  have h_meas1 : μ ((fun ω => (X ω, W ω)) ⁻¹' (A ×ˢ B))
      = (Measure.map (fun ω => (X ω, W ω)) μ) (A ×ˢ B) :=
    (Measure.map_apply (hX.prodMk hW) (hA.prod hB)).symm
  have h_meas2 : μ ((fun ω => (X ω, W' ω)) ⁻¹' (A ×ˢ B))
      = (Measure.map (fun ω => (X ω, W' ω)) μ) (A ×ˢ B) :=
    (Measure.map_apply (hX.prodMk hW') (hA.prod hB)).symm
  simp only [Measure.real, ENNReal.toReal_eq_toReal_iff]
  left
  rw [h_meas1, h_meas2, h_law]

/-- Set-integral of a Doob–Dynkin factor: if `g ∘ W` represents `μ[φ | comap W]`, the integral of
`g` over `B` against `Measure.map W μ` equals the integral of `φ` over `W ⁻¹' B`. -/
private lemma setIntegral_map_eq_setIntegral_preimage_of_condExp_comp
    {W : Ω → γ} (hW : Measurable W) [SigmaFinite (μ.trim (measurable_iff_comap_le.mp hW))]
    {g : γ → ℝ} (hg : AEStronglyMeasurable g (Measure.map W μ))
    {φ : Ω → ℝ} (hφ_int : Integrable φ μ)
    (hg_eq : μ[φ | MeasurableSpace.comap W inferInstance] = g ∘ W)
    {B : Set γ} (hB : MeasurableSet B) :
    ∫ y in B, g y ∂(Measure.map W μ) = ∫ ω in W ⁻¹' B, φ ω ∂μ := by
  have hmW_le : MeasurableSpace.comap W inferInstance ≤ ‹MeasurableSpace Ω› :=
    measurable_iff_comap_le.mp hW
  calc ∫ y in B, g y ∂(Measure.map W μ)
      = ∫ ω in W ⁻¹' B, g (W ω) ∂μ :=
          setIntegral_map hB hg hW.aemeasurable
    _ = ∫ ω in W ⁻¹' B, μ[φ | MeasurableSpace.comap W inferInstance] ω ∂μ :=
          setIntegral_congr_fun (hW hB) fun ω _ => (congrFun hg_eq ω).symm
    _ = ∫ ω in W ⁻¹' B, φ ω ∂μ :=
          setIntegral_condExp hmW_le hφ_int
            (MeasurableSpace.measurableSet_comap.mpr ⟨B, hB, rfl⟩)

/-- Helper for Kallenberg 1.3: the square-integrals of the two conditional expectations agree. -/
private lemma integral_sq_condExp_eq_of_pair_law [IsFiniteMeasure μ]
    (X : Ω → α) (W W' : Ω → γ)
    (hX : Measurable X) (hW : Measurable W) (hW' : Measurable W')
    (h_law : Measure.map (fun ω => (X ω, W ω)) μ = Measure.map (fun ω => (X ω, W' ω)) μ)
    {A : Set α} (hA : MeasurableSet A) :
    ∫ ω, (μ[(X ⁻¹' A).indicator (fun _ => (1 : ℝ))
            | MeasurableSpace.comap W inferInstance]) ω
        * (μ[(X ⁻¹' A).indicator (fun _ => (1 : ℝ))
            | MeasurableSpace.comap W inferInstance]) ω ∂μ
      = ∫ ω, (μ[(X ⁻¹' A).indicator (fun _ => (1 : ℝ))
              | MeasurableSpace.comap W' inferInstance]) ω
          * (μ[(X ⁻¹' A).indicator (fun _ => (1 : ℝ))
              | MeasurableSpace.comap W' inferInstance]) ω ∂μ := by
  have hρ_eq : Measure.map W μ = Measure.map W' μ :=
    marginal_law_eq_of_pair_law X W W' hX hW hW' h_law
  let φ : Ω → ℝ := (X ⁻¹' A).indicator (fun _ => (1 : ℝ))
  let μ₁ : Ω → ℝ := μ[φ | MeasurableSpace.comap W inferInstance]
  let μ₂ : Ω → ℝ := μ[φ | MeasurableSpace.comap W' inferInstance]
  have hφ_int : Integrable φ μ := Integrable.indicator (integrable_const 1) (hX hA)
  -- Doob–Dynkin factorisation `μ₁ = g₁ ∘ W`, `μ₂ = g₂ ∘ W'`.
  have hμ₁_sm : StronglyMeasurable[MeasurableSpace.comap W inferInstance] μ₁ :=
    stronglyMeasurable_condExp
  obtain ⟨g₁, hg₁_sm, hμ₁_eq⟩ := hμ₁_sm.exists_eq_measurable_comp
  have hμ₂_sm : StronglyMeasurable[MeasurableSpace.comap W' inferInstance] μ₂ :=
    stronglyMeasurable_condExp
  obtain ⟨g₂, hg₂_sm, hμ₂_eq⟩ := hμ₂_sm.exists_eq_measurable_comp
  have hg₁_int : Integrable g₁ (Measure.map W μ) := by
    have h : Integrable (g₁ ∘ W) μ := by rw [← hμ₁_eq]; exact integrable_condExp
    exact (integrable_map_measure hg₁_sm.aestronglyMeasurable hW.aemeasurable).mpr h
  have hg₂_int' : Integrable g₂ (Measure.map W μ) := by
    rw [hρ_eq]
    have h : Integrable (g₂ ∘ W') μ := by rw [← hμ₂_eq]; exact integrable_condExp
    exact (integrable_map_measure hg₂_sm.aestronglyMeasurable hW'.aemeasurable).mpr h
  -- `g₁ = g₂` a.e. on `ρ`, via the set-integral characterisation and the pair law.
  have hg_eq : g₁ =ᵐ[Measure.map W μ] g₂ := by
    refine Integrable.ae_eq_of_forall_setIntegral_eq g₁ g₂ hg₁_int hg₂_int' fun B hB _ => ?_
    calc ∫ y in B, g₁ y ∂(Measure.map W μ)
        = ∫ ω in W ⁻¹' B, φ ω ∂μ :=
          setIntegral_map_eq_setIntegral_preimage_of_condExp_comp hW hg₁_sm.aestronglyMeasurable
            hφ_int hμ₁_eq hB
      _ = ∫ ω in W' ⁻¹' B, φ ω ∂μ :=
          setIntegral_indicator_preimage_eq_of_pair_law X W W' hX hW hW' h_law hA hB
      _ = ∫ y in B, g₂ y ∂(Measure.map W μ) := by
          rw [hρ_eq]
          exact (setIntegral_map_eq_setIntegral_preimage_of_condExp_comp
            hW' hg₂_sm.aestronglyMeasurable hφ_int hμ₂_eq hB).symm
  -- Push the square through `integral_map` on both sides.
  calc ∫ ω, μ₁ ω * μ₁ ω ∂μ
      = ∫ ω, (g₁ (W ω)) ^ 2 ∂μ := by
        refine integral_congr_ae (.of_forall fun ω => ?_)
        simp only [hμ₁_eq, Function.comp_apply, pow_two]
    _ = ∫ y, (g₁ y) ^ 2 ∂(Measure.map W μ) :=
        (integral_map hW.aemeasurable (hg₁_sm.pow 2).aestronglyMeasurable).symm
    _ = ∫ y, (g₂ y) ^ 2 ∂(Measure.map W μ) := by
        refine integral_congr_ae ?_; filter_upwards [hg_eq] with y hy; rw [hy]
    _ = ∫ ω, (g₂ (W' ω)) ^ 2 ∂μ := by
        rw [hρ_eq]; exact integral_map hW'.aemeasurable (hg₂_sm.pow 2).aestronglyMeasurable
    _ = ∫ ω, μ₂ ω * μ₂ ω ∂μ := by
        refine integral_congr_ae (.of_forall fun ω => ?_)
        simp only [hμ₂_eq, Function.comp_apply, pow_two]

/-- Two real functions with equal integrals of their squares (`∫ g₁² = ∫ g₂²`) and matching cross
integral (`∫ g₂ g₁ = ∫ g₁²`) are a.e. equal: the `L²` distance polarises to
`∫ (g₂ - g₁)² = ∫ g₂² - 2 ∫ g₂ g₁ + ∫ g₁² = 0`. The products `g₁²`, `g₂²`, `g₂ g₁` are assumed
integrable. -/
private lemma ae_eq_of_integral_mul_eq_of_integral_sq_eq {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {g₁ g₂ : Ω → ℝ}
    (hg₁sq : Integrable (fun ω => g₁ ω * g₁ ω) μ)
    (hg₂sq : Integrable (fun ω => g₂ ω * g₂ ω) μ)
    (hg₂g₁ : Integrable (fun ω => g₂ ω * g₁ ω) μ)
    (h_cross : ∫ ω, g₂ ω * g₁ ω ∂μ = ∫ ω, g₁ ω * g₁ ω ∂μ)
    (h_sq : ∫ ω, g₁ ω * g₁ ω ∂μ = ∫ ω, g₂ ω * g₂ ω ∂μ) :
    g₁ =ᵐ[μ] g₂ := by
  have h_L2_zero : ∫ ω, (g₂ ω - g₁ ω) ^ 2 ∂μ = 0 := by
    have h_expand : ∀ᵐ ω ∂μ,
        (g₂ ω - g₁ ω) ^ 2 = g₂ ω * g₂ ω - 2 * (g₂ ω * g₁ ω) + g₁ ω * g₁ ω := by
      filter_upwards with ω; ring
    have hc2_int : Integrable (fun ω => 2 * (g₂ ω * g₁ ω)) μ := hg₂g₁.const_mul 2
    have hsub_int : Integrable (fun ω => g₂ ω * g₂ ω - 2 * (g₂ ω * g₁ ω)) μ := hg₂sq.sub hc2_int
    have h1 : ∫ ω, (g₂ ω - g₁ ω) ^ 2 ∂μ =
        ∫ ω, g₂ ω * g₂ ω ∂μ - 2 * ∫ ω, g₂ ω * g₁ ω ∂μ + ∫ ω, g₁ ω * g₁ ω ∂μ := by
      rw [integral_congr_ae h_expand, integral_add hsub_int hg₁sq,
        integral_sub hg₂sq hc2_int, integral_const_mul]
    rw [h1, h_cross, h_sq]; ring
  have h_sq_int : Integrable (fun ω => (g₂ ω - g₁ ω) ^ 2) μ := by
    have h_eq : (fun ω => (g₂ ω - g₁ ω) ^ 2)
        = fun ω => g₂ ω * g₂ ω - 2 * (g₂ ω * g₁ ω) + g₁ ω * g₁ ω := by funext ω; ring
    rw [h_eq]; exact (hg₂sq.sub (hg₂g₁.const_mul 2)).add hg₁sq
  have h_diff_zero : ∀ᵐ ω ∂μ, (g₂ ω - g₁ ω) ^ 2 = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_of_all μ fun ω => sq_nonneg _) h_sq_int).mp h_L2_zero
  filter_upwards [h_diff_zero] with ω hω
  nlinarith [sq_nonneg (g₂ ω - g₁ ω)]

/-- **Kallenberg Lemma 1.3 (contraction-independence).** If `(X, W) =ᵈ (X, W')` and
`σ(W) ≤ σ(W')` (so `W` is a contraction of `W'`), then conditioning the indicator of `X` on the
finer `σ(W')` equals conditioning on the coarser `σ(W)`, almost everywhere. -/
theorem condExp_indicator_eq_of_law_eq_of_comap_le [IsFiniteMeasure μ]
    (X : Ω → α) (W W' : Ω → γ)
    (hX : Measurable X) (hW : Measurable W) (hW' : Measurable W')
    (h_law : Measure.map (fun ω => (X ω, W ω)) μ = Measure.map (fun ω => (X ω, W' ω)) μ)
    (h_le : MeasurableSpace.comap W inferInstance ≤ MeasurableSpace.comap W' inferInstance)
    {A : Set α} (hA : MeasurableSet A) :
    μ[(X ⁻¹' A).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap W' inferInstance]
      =ᵐ[μ]
    μ[(X ⁻¹' A).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap W inferInstance] := by
  have h_sq_eq_raw := integral_sq_condExp_eq_of_pair_law X W W' hX hW hW' h_law hA
  let φ : Ω → ℝ := (X ⁻¹' A).indicator (fun _ => (1 : ℝ))
  let mW : MeasurableSpace Ω := MeasurableSpace.comap W inferInstance
  let mW' : MeasurableSpace Ω := MeasurableSpace.comap W' inferInstance
  have hmW_le : mW ≤ _ := measurable_iff_comap_le.mp hW
  have hmW'_le : mW' ≤ _ := measurable_iff_comap_le.mp hW'
  haveI hσW : SigmaFinite (μ.trim hmW_le) :=
    (inferInstance : IsFiniteMeasure (μ.trim hmW_le)).toSigmaFinite
  haveI hσW' : SigmaFinite (μ.trim hmW'_le) :=
    (inferInstance : IsFiniteMeasure (μ.trim hmW'_le)).toSigmaFinite
  have hφ_int : Integrable φ μ := Integrable.indicator (integrable_const 1) (hX hA)
  set μ₁ := μ[φ | mW] with hμ₁_def
  set μ₂ := μ[φ | mW'] with hμ₂_def
  have h_tower : μ[μ₂ | mW] =ᵐ[μ] μ₁ := condExp_condExp_of_le h_le hmW'_le
  have hφ_bdd : ∀ ω, 0 ≤ φ ω ∧ φ ω ≤ 1 := fun ω => by
    by_cases hω : ω ∈ X ⁻¹' A
    · have h : φ ω = 1 := Set.indicator_of_mem hω _
      rw [h]; exact ⟨zero_le_one, le_rfl⟩
    · have h : φ ω = 0 := Set.indicator_of_notMem hω _
      rw [h]; exact ⟨le_rfl, zero_le_one⟩
  -- `|φ| ≤ 1` a.e., so each conditional expectation `μ[φ | ·]` inherits the same bound via
  -- Mathlib's conditional-expectation bound; the helper is applied once per σ-algebra below.
  have hφ_abs : ∀ᵐ ω ∂μ, |φ ω| ≤ (1 : ℝ) := by
    filter_upwards with ω
    rw [abs_of_nonneg (hφ_bdd ω).1]; exact (hφ_bdd ω).2
  have condExp_abs_le : ∀ m' : MeasurableSpace Ω, ∀ᵐ ω ∂μ, |μ[φ | m'] ω| ≤ 1 := fun m' => by
    simpa using ae_bdd_abs_condExp_of_ae_bdd_abs (m := m') (R := (1 : ℝ)) hφ_abs
  have hμ₁_int : Integrable μ₁ μ := integrable_condExp
  have hμ₂_int : Integrable μ₂ μ := integrable_condExp
  have hμ₁_bound : ∀ᵐ ω ∂μ, ‖μ₁ ω‖ ≤ 1 := by
    filter_upwards [condExp_abs_le mW] with ω hω; rwa [Real.norm_eq_abs, hμ₁_def]
  have hμ₂_bound : ∀ᵐ ω ∂μ, ‖μ₂ ω‖ ≤ 1 := by
    filter_upwards [condExp_abs_le mW'] with ω hω; rwa [Real.norm_eq_abs, hμ₂_def]
  have hμ₁sq_int : Integrable (fun ω => μ₁ ω * μ₁ ω) μ :=
    hμ₁_int.bdd_mul hμ₁_int.aestronglyMeasurable hμ₁_bound
  have hμ₂sq_int : Integrable (fun ω => μ₂ ω * μ₂ ω) μ :=
    hμ₂_int.bdd_mul hμ₂_int.aestronglyMeasurable hμ₂_bound
  have hμ₂μ₁_int : Integrable (fun ω => μ₂ ω * μ₁ ω) μ :=
    hμ₁_int.bdd_mul hμ₂_int.aestronglyMeasurable hμ₂_bound
  -- Cross term `∫ μ₂ μ₁ = ∫ μ₁ μ₁` via pull-out and the tower property.
  have h_cross : ∫ ω, μ₂ ω * μ₁ ω ∂μ = ∫ ω, μ₁ ω * μ₁ ω ∂μ := by
    have hμ₁_meas : StronglyMeasurable[mW] μ₁ := stronglyMeasurable_condExp
    have h_pullout := condExp_mul_of_stronglyMeasurable_right (m := mW) hμ₁_meas hμ₂μ₁_int hμ₂_int
    calc ∫ ω, μ₂ ω * μ₁ ω ∂μ
        = ∫ ω, μ[fun ω => μ₂ ω * μ₁ ω | mW] ω ∂μ := (integral_condExp hmW_le).symm
      _ = ∫ ω, μ[μ₂ | mW] ω * μ₁ ω ∂μ := integral_congr_ae h_pullout
      _ = ∫ ω, μ₁ ω * μ₁ ω ∂μ := by
          refine integral_congr_ae ?_; filter_upwards [h_tower] with ω hω; rw [hω]
  have h_sq_eq : ∫ ω, μ₁ ω * μ₁ ω ∂μ = ∫ ω, μ₂ ω * μ₂ ω ∂μ := h_sq_eq_raw
  -- `μ₁ =ᵐ μ₂` from the polarisation `∫ (μ₂ - μ₁)² = ∫ μ₂² - 2 ∫ μ₂ μ₁ + ∫ μ₁² = 0`.
  exact (ae_eq_of_integral_mul_eq_of_integral_sq_eq hμ₁sq_int hμ₂sq_int hμ₂μ₁_int
    h_cross h_sq_eq).symm

end Probability

end TauCeti
