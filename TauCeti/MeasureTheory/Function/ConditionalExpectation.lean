/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
-- Non-public: `eLpNorm_condExp_le_eLpNorm` (the Lᵖ contraction of conditional expectation) is
-- used only inside the proof of the L¹-continuity lemma below, not in any public signature.
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Generic conditional-expectation facts

- `condExp_indicator_eq_of_pair_law_eq`: if `(Y, Z)` and `(Y', Z)` have the same law, then for
  measurable `B` the conditional expectations of `𝟙_B ∘ Y` and `𝟙_B ∘ Y'` given `σ(Z)` agree a.e.
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

/-- If the pairs `(Y, Z)` and `(Y', Z)` have the same law, then for measurable `B` the conditional
expectations of `𝟙_B ∘ Y` and `𝟙_B ∘ Y'` given `σ(Z)` agree almost everywhere. -/
theorem condExp_indicator_eq_of_pair_law_eq {Ω α β : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace α] [mβ : MeasurableSpace β] {μ : Measure Ω} [IsFiniteMeasure μ]
    (Y Y' : Ω → α) (Z : Ω → β) (hY : Measurable Y) (hY' : Measurable Y') (hZ : Measurable Z)
    (hpair : μ.map (fun ω => (Y ω, Z ω)) = μ.map (fun ω => (Y' ω, Z ω)))
    {B : Set α} (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ Y | MeasurableSpace.comap Z mβ]
      =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ Y' | MeasurableSpace.comap Z mβ] := by
  classical
  set f := Set.indicator B (fun _ => (1 : ℝ)) ∘ Y with hf_def
  set f' := Set.indicator B (fun _ => (1 : ℝ)) ∘ Y' with hf'_def
  set mZ := MeasurableSpace.comap Z mβ with hmZ_def
  have hmZ_le : mZ ≤ mΩ := by
    rintro s ⟨E, hE, rfl⟩
    exact hZ hE
  have hf_int : Integrable f μ := Integrable.indicator (integrable_const (1 : ℝ)) (hY hB)
  have hf'_int : Integrable f' μ := Integrable.indicator (integrable_const (1 : ℝ)) (hY' hB)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hmZ_le hf_int
    (fun s _ _ => integrable_condExp.integrableOn) (fun A hA _ => ?_)
    stronglyMeasurable_condExp.aestronglyMeasurable).symm
  obtain ⟨E, hE, rfl⟩ := hA
  have h_meas_eq : μ (Y ⁻¹' B ∩ Z ⁻¹' E) = μ (Y' ⁻¹' B ∩ Z ⁻¹' E) := by
    have h := congr_arg (fun ν => ν (B ×ˢ E)) hpair
    simp only [Measure.map_apply (hY.prodMk hZ) (hB.prod hE),
      Measure.map_apply (hY'.prodMk hZ) (hB.prod hE), Set.mk_preimage_prod] at h
    exact h
  -- The set-integral of a preimage indicator over `Z ⁻¹' E`, shared by both coordinates.
  have hint : ∀ W : Ω → α, Measurable[mΩ] W →
      ∫ ω in Z ⁻¹' E, (W ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω ∂μ
        = (μ (W ⁻¹' B ∩ Z ⁻¹' E)).toReal := by
    intro W hW
    rw [setIntegral_indicator (hW hB), setIntegral_const, Set.inter_comm]
    simp [Measure.real]
  have h_lhs : ∫ ω in Z ⁻¹' E, f ω ∂μ = (μ (Y ⁻¹' B ∩ Z ⁻¹' E)).toReal := by
    have hf_eq : f = (Y ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
      ext ω; simp only [hf_def, Function.comp_apply, Set.indicator, Set.mem_preimage]
    rw [hf_eq]; exact hint Y hY
  have h_rhs_ce : ∫ ω in Z ⁻¹' E, μ[f' | mZ] ω ∂μ = ∫ ω in Z ⁻¹' E, f' ω ∂μ :=
    setIntegral_condExp hmZ_le hf'_int ⟨E, hE, rfl⟩
  have h_rhs : ∫ ω in Z ⁻¹' E, f' ω ∂μ = (μ (Y' ⁻¹' B ∩ Z ⁻¹' E)).toReal := by
    have hf'_eq : f' = (Y' ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
      ext ω; simp only [hf'_def, Function.comp_apply, Set.indicator, Set.mem_preimage]
    rw [hf'_eq]; exact hint Y' hY'
  simp_rw [h_lhs, h_rhs_ce, h_rhs, h_meas_eq]

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
