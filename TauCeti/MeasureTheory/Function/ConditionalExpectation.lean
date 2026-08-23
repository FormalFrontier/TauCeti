/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
-- Non-public: `eLpNorm_condExp_le_eLpNorm` (the Lᵖ contraction of conditional expectation) is
-- used only inside the proof of the L¹-continuity lemma below, not in any public signature.
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Generic conditional-expectation facts

- `condExp_comp_ae_eq_of_pair_law_eq`: if `(Y, Z)` and `(Y', Z)` have the same law, then for a
  measurable real observable `f` the conditional expectations of `f ∘ Y` and `f ∘ Y'` given `σ(Z)`
  agree a.e.
- `condExp_ae_eq_of_forall_condExp_ae_eq_of_tendsto_eLpNorm`: L¹-continuity of conditional
  expectation — if `Xn → Xlim` in L¹ (in `eLpNorm`) and each `μ[Xn n | F]` agrees a.e. with a fixed
  `Y`, then `μ[Xlim | F]` agrees a.e. with `Y`.

Both are generic conditional-expectation facts (no exchangeability/tail/directing-measure
hypotheses), each the bridge for a downstream construction.

Adapted from `cameronfreer/exchangeability` (`Probability/CondExp.lean` and
`Probability/Martingale/Convergence.lean`, pin `e0532e59ceff23edab44dda9ab0655debbc9cc22`).
-/

public section

noncomputable section

open MeasureTheory Filter

open scoped Topology

namespace TauCeti

namespace MeasureTheory

/-- If the pairs `(Y, Z)` and `(Y', Z)` have the same law, then for a measurable real observable
`f` the conditional expectations of `f ∘ Y` and `f ∘ Y'` given `σ(Z)` agree almost everywhere.

Both conditional expectations are pinned down by their integrals over the sets `Z ⁻¹' E`, and each
such integral is an integral of `fun p => f p.1` over the slab `univ ×ˢ E` against the joint law,
which is where the hypothesis applies. Equal laws make `f ∘ Y` integrable exactly when `f ∘ Y'` is,
so no integrability hypothesis is needed: when it fails both sides are `0`. -/
theorem condExp_comp_ae_eq_of_pair_law_eq {Ω α β : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace α] [mβ : MeasurableSpace β] {μ : Measure Ω} [IsFiniteMeasure μ]
    (Y Y' : Ω → α) (Z : Ω → β) (hY : Measurable Y) (hY' : Measurable Y') (hZ : Measurable Z)
    (hpair : μ.map (fun ω => (Y ω, Z ω)) = μ.map (fun ω => (Y' ω, Z ω)))
    {f : α → ℝ} (hf : Measurable f) :
    μ[fun ω => f (Y ω) | MeasurableSpace.comap Z mβ]
      =ᵐ[μ] μ[fun ω => f (Y' ω) | MeasurableSpace.comap Z mβ] := by
  have hmZ_le : MeasurableSpace.comap Z mβ ≤ mΩ := by
    rintro s ⟨E, hE, rfl⟩
    exact hZ hE
  -- Equal joint laws have equal first marginals, so integrability transfers to `Y'`.
  have hmap : μ.map Y = μ.map Y' := by
    have h := congrArg (Measure.map Prod.fst) hpair
    rwa [Measure.map_map measurable_fst (hY.prodMk hZ),
      Measure.map_map measurable_fst (hY'.prodMk hZ)] at h
  have hiff : Integrable (fun ω => f (Y ω)) μ ↔ Integrable (fun ω => f (Y' ω)) μ := by
    have h : Integrable f (μ.map Y) ↔ Integrable (fun ω => f (Y ω)) μ :=
      integrable_map_measure hf.aestronglyMeasurable hY.aemeasurable
    have h' : Integrable f (μ.map Y') ↔ Integrable (fun ω => f (Y' ω)) μ :=
      integrable_map_measure hf.aestronglyMeasurable hY'.aemeasurable
    rw [hmap] at h
    exact h.symm.trans h'
  by_cases hf_int : Integrable (fun ω => f (Y ω)) μ
  case neg =>
    -- Neither composite is integrable, so both conditional expectations are `0`.
    rw [condExp_of_not_integrable hf_int, condExp_of_not_integrable (mt hiff.2 hf_int)]
  have hf'_int : Integrable (fun ω => f (Y' ω)) μ := hiff.1 hf_int
  have hslice : ∀ W : Ω → α, Measurable W → ∀ {E : Set β}, MeasurableSet E →
      ∫ p in Set.univ ×ˢ E, f p.1 ∂(μ.map fun ω => (W ω, Z ω))
        = ∫ ω in Z ⁻¹' E, f (W ω) ∂μ := by
    intro W hW E hE
    have hfst : Measurable fun p : α × β => f p.1 := hf.comp measurable_fst
    rw [setIntegral_map (MeasurableSet.univ.prod hE) hfst.aestronglyMeasurable
      (hW.prodMk hZ).aemeasurable]
    have hpre : (fun ω => (W ω, Z ω)) ⁻¹' (Set.univ ×ˢ E) = Z ⁻¹' E := by
      ext ω; simp
    rw [hpre]
  refine (ae_eq_condExp_of_forall_setIntegral_eq hmZ_le hf_int
    (fun s _ _ => integrable_condExp.integrableOn) (fun A hA _ => ?_)
    stronglyMeasurable_condExp.aestronglyMeasurable).symm
  obtain ⟨E, hE, rfl⟩ := hA
  rw [setIntegral_condExp hmZ_le hf'_int ⟨E, hE, rfl⟩, ← hslice Y' hY' hE, ← hpair,
    hslice Y hY hE]

/-- **L¹-continuity of conditional expectation.** If `Xn → Xlim` in `L¹` (in `eLpNorm`) and each
`μ[Xn n | F]` agrees a.e. with a fixed `Y`, then `μ[Xlim | F]` agrees a.e. with `Y`. -/
-- Stated for an arbitrary conditioning σ-algebra `F` (no `F ≤ m₀`, no `[SigmaFinite (μ.trim)]`):
-- the bound goes through Mathlib's Lᵖ contraction `eLpNorm_condExp_le_eLpNorm`, which holds at
-- every `F` via the `condExp = 0` convention — whereas `condExpL1CLM` would require both. Proof:
-- bound `‖μ[Xlim|F] - Y‖₁` by `‖Xlim - Xn n‖₁` (triangle + `condExp_sub` + the contraction + the
-- vanishing `μ[Xn n|F] - Y` term), then let `n → ∞`. Consumed by the reverse-martingale
-- Lévy-downward theorem `MeasureTheory.tendsto_ae_condExp_iInf`.
lemma condExp_ae_eq_of_forall_condExp_ae_eq_of_tendsto_eLpNorm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : MeasurableSpace Ω} {Xlim Y : Ω → ℝ} {Xn : ℕ → Ω → ℝ}
    (hXlimint : Integrable Xlim μ) (hXn_int : ∀ n, Integrable (Xn n) μ)
    (h_condExp : ∀ n, μ[Xn n | F] =ᵐ[μ] Y)
    (hL1 : Tendsto (fun n => eLpNorm (Xlim - Xn n) 1 μ) atTop (𝓝 0)) :
    μ[Xlim | F] =ᵐ[μ] Y := by
  have hY_meas := integrable_condExp.aestronglyMeasurable.congr (h_condExp 0)
  have h_bound (n : ℕ) : eLpNorm (μ[Xlim | F] - Y) 1 μ ≤ eLpNorm (Xlim - Xn n) 1 μ := by
    have htri : eLpNorm (μ[Xlim | F] - Y) 1 μ
                ≤ eLpNorm (μ[Xlim | F] - μ[Xn n | F]) 1 μ
                  + eLpNorm (μ[Xn n | F] - Y) 1 μ := by
      have : μ[Xlim | F] - Y = (μ[Xlim | F] - μ[Xn n | F]) + (μ[Xn n | F] - Y) := by ring
      rw [this]
      refine eLpNorm_add_le ?_ ?_ ?_
      · exact (integrable_condExp.sub integrable_condExp).aestronglyMeasurable
      · exact integrable_condExp.aestronglyMeasurable.sub hY_meas
      · norm_num
    have hzero : eLpNorm (μ[Xn n | F] - Y) 1 μ = 0 := by
      have h0 : μ[Xn n | F] - Y =ᵐ[μ] 0 := by
        filter_upwards [h_condExp n] with ω hω; simp [hω]
      rw [eLpNorm_congr_ae h0]; simp
    have hfirst : eLpNorm (μ[Xlim | F] - μ[Xn n | F]) 1 μ ≤ eLpNorm (Xlim - Xn n) 1 μ := by
      have hsub : μ[Xlim | F] - μ[Xn n | F] =ᵐ[μ] μ[Xlim - Xn n | F] :=
        (condExp_sub hXlimint (hXn_int n) F).symm
      rw [eLpNorm_congr_ae hsub]
      exact eLpNorm_condExp_le_eLpNorm _ le_rfl
    calc eLpNorm (μ[Xlim | F] - Y) 1 μ
        ≤ eLpNorm (μ[Xlim | F] - μ[Xn n | F]) 1 μ + eLpNorm (μ[Xn n | F] - Y) 1 μ := htri
      _ = eLpNorm (μ[Xlim | F] - μ[Xn n | F]) 1 μ := by rw [hzero]; ring
      _ ≤ eLpNorm (Xlim - Xn n) 1 μ := hfirst
  have h_norm_zero : eLpNorm (μ[Xlim | F] - Y) 1 μ = 0 :=
    le_antisymm
      (le_of_tendsto_of_tendsto tendsto_const_nhds hL1 (Eventually.of_forall h_bound)) bot_le
  rw [eLpNorm_eq_zero_iff (integrable_condExp.aestronglyMeasurable.sub hY_meas)
    one_ne_zero] at h_norm_zero
  filter_upwards [h_norm_zero] with ω hω
  simp only [Pi.zero_apply] at hω
  exact sub_eq_zero.mp hω

end MeasureTheory

end TauCeti
