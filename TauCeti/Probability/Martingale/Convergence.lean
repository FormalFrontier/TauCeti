/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Convergence
-- Non-public: `AntitoneLimit` supplies the a.e.-limit-existence lemma, and the generic
-- `AEStronglyMeasurable` / `ConditionalExpectation` helpers the `⨅`-measurability and L¹-continuity
-- steps — all used only in proofs, so they are not re-exported through the flagship path.
import TauCeti.Probability.Martingale.AntitoneLimit
import TauCeti.MeasureTheory.Function.AEStronglyMeasurable
import TauCeti.MeasureTheory.Function.ConditionalExpectation

/-!
# Martingale convergence theorems

Lévy's downward theorem for conditional expectations along a decreasing filtration.

This is the flagship of the reverse-martingale infrastructure: the finite-horizon reversal
(`Martingale/Reverse.lean`), the pathwise crossing adapters (`Martingale/Crossings/`), the
reverse-martingale upcrossing bound (`Crossings/Bounds.lean`), and the antitone-limit existence
result (`Martingale/AntitoneLimit.lean`) all feed into `tendsto_ae_condExp_iInf`.

## Main results

- `tendsto_ae_condExp_iInf`: Lévy's downward theorem — for antitone `𝔽`, the sequence
  `μ[f | 𝔽 n]` converges a.e. to `μ[f | ⨅ n, 𝔽 n]` (the reverse-martingale limit). This is
  the roadmap Layer-4 target, spelled in the Mathlib convergence-API grammar (conclusion-first)
  required by the naming convention.
- `tendsto_eLpNorm_condExp_iInf`: the L¹ form of the same theorem — the convergence also holds in
  `L¹`, i.e. `eLpNorm (μ[f | 𝔽 n] - μ[f | ⨅ n, 𝔽 n]) 1 μ → 0`. This is the follow-up Layer-4
  target and the form most downstream analytic uses want; it mirrors Mathlib's upward
  `MeasureTheory.tendsto_eLpNorm_condExp`.
- `measure_inter_eq_mul_of_forall_zero_or_one_iInf`: factorization along a decreasing filtration
  with `μ`-trivial intersection — if `B' n` is `𝔽 n`-measurable with `μ (B' n)` and `μ (A ∩ B' n)`
  independent of `n`, then `μ (A ∩ B) = μ A * μ B`, by Lévy's downward theorem applied to `1_A`.

## References

* Kallenberg, *Probabilistic Symmetries and Invariance Principles* (2005), Section 1
* Durrett, *Probability: Theory and Examples* (2019), Section 5.5
* Williams, *Probability with Martingales* (1991), Theorem 12.12

Adapted from `cameronfreer/exchangeability` (`Probability/Martingale/Convergence.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). Written Mathlib-shaped for eventual upstreaming.
-/

public section

noncomputable section

open MeasureTheory Filter

open scoped Topology ENNReal

open TauCeti.MeasureTheory

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Identification of the reverse-martingale limit.** If `μ[f | 𝔽 n]` converges to `Xlim` both
almost everywhere and in `L¹`, along an antitone filtration, then `Xlim` is the conditional
expectation of `f` on the tail σ-algebra `⨅ n, 𝔽 n`.

The proof uses the a.e. convergence to make `Xlim` measurable for `⨅ n, 𝔽 n`, and the `L¹`
convergence to transport the tower property `μ[μ[f | 𝔽 n] | ⨅ n, 𝔽 n] =ᵐ μ[f | ⨅ n, 𝔽 n]` to the
limit. -/
private lemma condExp_iInf_ae_eq_of_tendsto_ae_of_tendsto_eLpNorm
    [IsFiniteMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω} {f Xlim : Ω → ℝ} (h_filtration : Antitone 𝔽)
    (h_le0 : 𝔽 0 ≤ (inferInstance : MeasurableSpace Ω)) (hXlimint : Integrable Xlim μ)
    (h_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (Xlim ω)))
    (hL1_conv : Tendsto (fun n => eLpNorm (μ[f | 𝔽 n] - Xlim) 1 μ) atTop (𝓝 0)) :
    μ[f | ⨅ n, 𝔽 n] =ᵐ[μ] Xlim := by
  -- Antitonicity upgrades measurability at index `0` to every index.
  have h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω) :=
    fun n => (h_filtration (Nat.zero_le n)).trans h_le0
  -- `Xlim` is `AEStronglyMeasurable[⨅ n, 𝔽 n]` (a.e. limit of `𝔽 n`-strongly-measurable functions).
  have hXlim_iInf_meas : AEStronglyMeasurable[⨅ n, 𝔽 n] Xlim μ :=
    aestronglyMeasurable_iInf_of_tendsto_ae_antitone h_filtration
      (fun n => stronglyMeasurable_condExp.aestronglyMeasurable) h_tendsto
  -- We work with the raw `⨅ n, 𝔽 n` rather than a `set` alias: a local of type
  -- `MeasurableSpace Ω` shadows the ambient σ-algebra during the instance synthesis triggered by
  -- the L¹-continuity call below.
  have h_tower : ∀ n, μ[μ[f | 𝔽 n] | ⨅ n, 𝔽 n] =ᵐ[μ] μ[f | ⨅ n, 𝔽 n] :=
    fun n => condExp_condExp_of_le (iInf_le 𝔽 n) (h_le n)
  have hiInf_le : (⨅ n, 𝔽 n) ≤ (inferInstance : MeasurableSpace Ω) :=
    le_trans (iInf_le 𝔽 0) (h_le 0)
  have hL1_conv' : Tendsto (fun n => eLpNorm (Xlim - μ[f | 𝔽 n]) 1 μ) atTop (𝓝 0) := by
    simpa [eLpNorm_sub_comm] using hL1_conv
  -- L¹-continuity of conditional expectation carries the tower property to the limit.
  have hCE_eqY : μ[Xlim | ⨅ n, 𝔽 n] =ᵐ[μ] μ[f | ⨅ n, 𝔽 n] :=
    condExp_ae_eq_of_forall_condExp_ae_eq_of_tendsto_eLpNorm hXlimint
      (fun _ => integrable_condExp) h_tower hL1_conv'
  have hXlim_condExp_self : μ[Xlim | ⨅ n, 𝔽 n] =ᵐ[μ] Xlim :=
    condExp_of_aestronglyMeasurable' hiInf_le hXlim_iInf_meas hXlimint
  exact hCE_eqY.symm.trans hXlim_condExp_self

/-- Lévy's downward theorem, proving the almost-everywhere and `L¹` forms together.

The `L¹` convergence is not an afterthought of the a.e. convergence: the Vitali step that upgrades
a.e. convergence of the uniformly integrable family `μ[f | 𝔽ₙ]` to `L¹` convergence is what
identifies the a.e. limit as `μ[f | ⨅ₙ 𝔽ₙ]` in the first place. Proving the two conclusions in one
pass avoids running that step twice; the public `tendsto_ae_condExp_iInf` and
`tendsto_eLpNorm_condExp_iInf` are its two projections. -/
private theorem tendsto_ae_and_eLpNorm_condExp_iInf [IsFiniteMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽) (h_le0 : 𝔽 0 ≤ (inferInstance : MeasurableSpace Ω)) (f : Ω → ℝ) :
    (∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω)
        atTop
        (𝓝 (μ[f | ⨅ n, 𝔽 n] ω))) ∧
      Tendsto (fun n => eLpNorm (μ[f | 𝔽 n] - μ[f | ⨅ n, 𝔽 n]) 1 μ) atTop (𝓝 0) := by
  classical
  -- No integrability hypothesis is needed: `condExp` vanishes on non-integrable arguments, so
  -- every term of both sequences is `0` and both conclusions are trivial there.
  by_cases h_f_int : Integrable f μ
  swap
  · simp [condExp_of_not_integrable h_f_int]
  -- Only `𝔽 0 ≤ m₀` is assumed; antitonicity upgrades it to `𝔽 n ≤ m₀` for every `n`.
  have h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω) :=
    fun n => (h_filtration (Nat.zero_le n)).trans h_le0
  -- We follow the upcrossing-inequality route rather than reindexing by `ℕᵒᵈ`: for antitone `𝔽`,
  -- `⨆ i : ℕᵒᵈ, 𝔽 i.ofDual = 𝔽 0`, so dualising and applying Lévy's *upward* theorem would converge
  -- to the wrong limit `μ[f | 𝔽 0]` instead of `μ[f | ⨅ n, 𝔽 n]`.
  -- 1) A.s. limit `Xlim` exists (upcrossing bounds on the time-reversed martingales).
  obtain ⟨Xlim, hXlimint, h_tendsto⟩ :=
    exists_integrable_tendsto_ae_condExp_of_antitone (μ := μ) h_filtration h_le f h_f_int
  -- 2) Uniform integrability upgrades a.e. convergence to `L¹` convergence (Vitali).
  have hUI : UniformIntegrable (fun n => μ[f | 𝔽 n]) 1 μ := h_f_int.uniformIntegrable_condExp h_le
  have hL1_conv : Tendsto (fun n => eLpNorm (μ[f | 𝔽 n] - Xlim) 1 μ) atTop (𝓝 0) := by
    apply tendsto_Lp_finite_of_tendsto_ae (hp := le_refl 1) (hp' := ENNReal.one_ne_top)
    · intro n; exact integrable_condExp.aestronglyMeasurable
    · exact memLp_one_iff_integrable.2 hXlimint
    · exact hUI.unifIntegrable
    · exact h_tendsto
  -- 3) Identify the a.e. limit as the conditional expectation on the tail σ-algebra.
  have hXlim_eq : μ[f | ⨅ n, 𝔽 n] =ᵐ[μ] Xlim :=
    condExp_iInf_ae_eq_of_tendsto_ae_of_tendsto_eLpNorm h_filtration h_le0 hXlimint
      h_tendsto hL1_conv
  refine ⟨?_, ?_⟩
  · -- Combine `h_tendsto : μ[f | 𝔽 n] → Xlim` with `hXlim_eq : μ[f | ⨅ n, 𝔽 n] =ᵐ Xlim`.
    filter_upwards [h_tendsto, hXlim_eq] with ω h_tend h_eq
    rw [h_eq]
    exact h_tend
  · -- Transport the L¹ convergence `μ[f | 𝔽 n] → Xlim` along `hXlim_eq`.
    have h_eLp : ∀ n, eLpNorm (μ[f | 𝔽 n] - μ[f | ⨅ n, 𝔽 n]) 1 μ
        = eLpNorm (μ[f | 𝔽 n] - Xlim) 1 μ := fun n =>
      eLpNorm_congr_ae (by filter_upwards [hXlim_eq] with ω h_eq using by simp [h_eq])
    simpa only [h_eLp] using hL1_conv

/-- **Conditional expectation converges along a decreasing filtration (Lévy's downward theorem).**

For a decreasing filtration `𝔽ₙ`, the sequence `μ[f | 𝔽ₙ]` converges almost surely to
`μ[f | ⨅ₙ 𝔽ₙ]` — the reverse-martingale (Lévy downward) limit. As in Mathlib's upward
`MeasureTheory.tendsto_ae_condExp`, no integrability hypothesis is needed: `condExp` vanishes on
non-integrable arguments, so the statement is trivial there. -/
theorem tendsto_ae_condExp_iInf [IsFiniteMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽) (h_le0 : 𝔽 0 ≤ (inferInstance : MeasurableSpace Ω)) (f : Ω → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => μ[f | 𝔽 n] ω)
      atTop
      (𝓝 (μ[f | ⨅ n, 𝔽 n] ω)) :=
  (tendsto_ae_and_eLpNorm_condExp_iInf h_filtration h_le0 f).1

/-- **Conditional expectation converges in `L¹` along a decreasing filtration (Lévy's downward
theorem, `L¹` form).**

For a decreasing filtration `𝔽ₙ`, the sequence `μ[f | 𝔽ₙ]` converges in `L¹` to `μ[f | ⨅ₙ 𝔽ₙ]`.
This upgrades the almost-everywhere statement `tendsto_ae_condExp_iInf`: the conditional
expectations `μ[f | 𝔽ₙ]` of a fixed integrable function form a uniformly integrable family, so
their a.e. convergence is convergence in `L¹` by Vitali's theorem. As in Mathlib's upward
`MeasureTheory.tendsto_eLpNorm_condExp`, which this is the downward analogue of, no integrability
hypothesis is needed: `condExp` vanishes on non-integrable arguments, so the statement is trivial
there. -/
theorem tendsto_eLpNorm_condExp_iInf [IsFiniteMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽) (h_le0 : 𝔽 0 ≤ (inferInstance : MeasurableSpace Ω)) (f : Ω → ℝ) :
    Tendsto (fun n => eLpNorm (μ[f | 𝔽 n] - μ[f | ⨅ n, 𝔽 n]) 1 μ) atTop (𝓝 0) :=
  (tendsto_ae_and_eLpNorm_condExp_iInf h_filtration h_le0 f).2

/-- **Factorization along a decreasing filtration with trivial tail.** If `B' n` is `𝔽 n`-measurable
along an antitone sequence of sub-σ-algebras whose intersection is `μ`-trivial, and neither
`μ (B' n)` nor `μ (A ∩ B' n)` depends on `n`, then the joint mass factorizes: Lévy's downward
theorem drives `μ[1_A | 𝔽 n]` to the tail conditional expectation, which triviality makes the
constant `μ A`. -/
theorem measure_inter_eq_mul_of_forall_zero_or_one_iInf [IsProbabilityMeasure μ]
    {𝔽 : ℕ → MeasurableSpace Ω} (hanti : Antitone 𝔽) (h𝔽 : ∀ n, 𝔽 n ≤ ‹MeasurableSpace Ω›)
    (htriv : ∀ s, MeasurableSet[⨅ n, 𝔽 n] s → μ s = 0 ∨ μ s = 1)
    {A B : Set Ω} (hA : MeasurableSet A) {B' : ℕ → Set Ω}
    (hB' : ∀ n, MeasurableSet[𝔽 n] (B' n)) (hBmass : ∀ n, μ (B' n) = μ B)
    (hjoint : ∀ n, μ (A ∩ B' n) = μ (A ∩ B)) :
    μ (A ∩ B) = μ A * μ B := by
  have hinf : (⨅ n, 𝔽 n) ≤ ‹MeasurableSpace Ω› := (iInf_le 𝔽 0).trans (h𝔽 0)
  set f₀ : Ω → ℝ := A.indicator fun _ => 1 with hf₀def
  have hf₀ : Integrable f₀ μ := (integrable_const 1).indicator hA
  have hconst : μ[f₀|⨅ n, 𝔽 n] =ᵐ[μ] fun _ => ∫ x, f₀ x ∂μ :=
    condExp_ae_eq_integral_of_forall_zero_or_one hinf htriv hf₀
  have hc : ∫ x, f₀ x ∂μ = (μ A).toReal := by
    rw [hf₀def, integral_indicator_const (1 : ℝ) hA, smul_eq_mul, mul_one, measureReal_def]
  have hbound : ∀ n, |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| ≤
      (eLpNorm (μ[f₀|𝔽 n] - μ[f₀|⨅ m, 𝔽 m]) 1 μ).toReal := by
    intro n
    have hBn : MeasurableSet (B' n) := h𝔽 n _ (hB' n)
    have hg : Integrable (μ[f₀|𝔽 n] - μ[f₀|⨅ m, 𝔽 m]) μ :=
      integrable_condExp.sub integrable_condExp
    have h1 : ∫ x in B' n, (μ[f₀|𝔽 n]) x ∂μ = (μ (A ∩ B)).toReal := by
      rw [setIntegral_condExp (h𝔽 n) hf₀ (hB' n), hf₀def, setIntegral_indicator hA,
        setIntegral_const, smul_eq_mul, mul_one, Set.inter_comm (B' n) A, measureReal_def,
        hjoint n]
    have h2 : ∫ x in B' n, (μ[f₀|⨅ m, 𝔽 m]) x ∂μ = (μ A).toReal * (μ B).toReal := by
      rw [setIntegral_congr_ae hBn (hconst.mono fun x hx _ => hx), setIntegral_const,
        smul_eq_mul, hc, measureReal_def, hBmass n, mul_comm]
    have hsplit : ∫ x in B' n, (μ[f₀|𝔽 n] - μ[f₀|⨅ m, 𝔽 m]) x ∂μ =
        (μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal := by
      simp only [Pi.sub_apply]
      rw [integral_sub integrable_condExp.integrableOn integrable_condExp.integrableOn, h1, h2]
    calc |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal|
        = ‖∫ x in B' n, (μ[f₀|𝔽 n] - μ[f₀|⨅ m, 𝔽 m]) x ∂μ‖ := by
          rw [hsplit, Real.norm_eq_abs]
      _ ≤ ∫ x in B' n, ‖(μ[f₀|𝔽 n] - μ[f₀|⨅ m, 𝔽 m]) x‖ ∂μ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖(μ[f₀|𝔽 n] - μ[f₀|⨅ m, 𝔽 m]) x‖ ∂μ :=
          setIntegral_le_integral hg.norm (Eventually.of_forall fun x => norm_nonneg _)
      _ = (eLpNorm (μ[f₀|𝔽 n] - μ[f₀|⨅ m, 𝔽 m]) 1 μ).toReal := by
          rw [integral_norm_eq_lintegral_enorm hg.aestronglyMeasurable,
            eLpNorm_one_eq_lintegral_enorm]
  have hLevyReal : Tendsto
      (fun n => (eLpNorm (μ[f₀|𝔽 n] - μ[f₀|⨅ m, 𝔽 m]) 1 μ).toReal) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_eLpNorm_condExp_iInf hanti (h𝔽 0) f₀)
  have habs0 : |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| = 0 :=
    le_antisymm (ge_of_tendsto' hLevyReal hbound) (abs_nonneg _)
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _)
    (ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _))).mp ?_
  rw [ENNReal.toReal_mul]
  have := abs_eq_zero.mp habs0
  linarith

end MeasureTheory
