/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

/-!
# Additional lemmas for the Bochner integral

This file records general-purpose bridges between real-valued Bochner integrals and
extended-nonnegative Lebesgue integrals.

## Positive parts

* `ofReal_integral_le_lintegral_ofReal` bounds the positive part of a real-valued
  function's integral by the integral of its pointwise positive part.

## Set integrals

* `sq_setIntegral_le_measureReal_mul_setIntegral_sq` is Cauchy--Schwarz for a real-valued set
  integral, in squared form.

## `L¹` convergence

`L¹` convergence is often produced in the Bochner form `∫ ω, ‖f i ω - g ω‖ ∂μ → 0` but consumed
in the seminorm form `eLpNorm (f i - g) 1 μ → 0` (for instance by
`MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm`).

* `tendsto_eLpNorm_one_of_tendsto_integral_norm_sub` converts the former into the latter.

The conversion is `MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm`, whose home is
`Mathlib.MeasureTheory.Integral.Bochner.Basic`, plus continuity of `ENNReal.ofReal` at `0`.

## Kernel averages on the real line

* `integral_kernel_mem_Icc_of_antitoneOn` squeezes the average of a function against a probability
  density supported in `[-ε, 0]` between the function's values at `t + ε` and `t`, given only
  antitonicity on the sampled interval `[t, t + ε]`.
-/

public section

noncomputable section

open MeasureTheory Filter

open scoped ENNReal Topology

namespace TauCeti

namespace MeasureTheory

/-- Cauchy--Schwarz for a real-valued set integral over a set of finite measure, in squared form. -/
theorem sq_setIntegral_le_measureReal_mul_setIntegral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (f : Ω → ℝ) (S : Set Ω) (hS_top : μ S ≠ ⊤)
    (hf : IntegrableOn f S μ) (hf_sq : IntegrableOn (fun x => f x ^ 2) S μ) :
    (∫ x in S, f x ∂μ) ^ 2 ≤ μ.real S * ∫ x in S, f x ^ 2 ∂μ := by
  by_cases hS : μ S = 0
  · rw [Measure.restrict_eq_zero.mpr hS]
    simp
  · have hS_pos : 0 < μ.real S := ENNReal.toReal_pos hS hS_top
    have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
      Even.convexOn_pow (by norm_num : Even 2)
    have hjensen := hconv.map_set_average_le (continuous_pow 2).continuousOn isClosed_univ
      hS hS_top (ae_of_all _ fun _ => Set.mem_univ _) hf hf_sq
    rw [setAverage_eq, setAverage_eq] at hjensen
    simp only [smul_eq_mul] at hjensen
    have hkey : (μ.real S)⁻¹ ^ 2 * (∫ x in S, f x ∂μ) ^ 2
        ≤ (μ.real S)⁻¹ * ∫ x in S, f x ^ 2 ∂μ := by
      calc
        (μ.real S)⁻¹ ^ 2 * (∫ x in S, f x ∂μ) ^ 2 =
            ((μ.real S)⁻¹ * ∫ x in S, f x ∂μ) ^ 2 := by ring
        _ ≤ _ := hjensen
    calc
      (∫ x in S, f x ∂μ) ^ 2 =
          μ.real S ^ 2 * ((μ.real S)⁻¹ ^ 2 * (∫ x in S, f x ∂μ) ^ 2) := by
            field_simp
      _ ≤ μ.real S ^ 2 * ((μ.real S)⁻¹ * ∫ x in S, f x ^ 2 ∂μ) :=
        mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
      _ = μ.real S * ∫ x in S, f x ^ 2 ∂μ := by field_simp

/-- The positive part of the integral of a real-valued function is at most the integral of its
pointwise positive part. No integrability or pointwise sign assumption on `f` is needed. -/
theorem ofReal_integral_le_lintegral_ofReal {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hf : Integrable f μ
  · calc
      ENNReal.ofReal (∫ x, f x ∂μ) ≤ ENNReal.ofReal (∫ x, max (f x) 0 ∂μ) :=
        ENNReal.ofReal_mono <| integral_mono hf hf.pos_part fun x ↦ le_max_left _ _
      _ = ∫⁻ x, ENNReal.ofReal (max (f x) 0) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hf.pos_part <|
          Filter.Eventually.of_forall fun x ↦ le_max_right (f x) 0
      _ = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by simp
  · rw [integral_undef hf]
    simp

/-- **`L¹` convergence in Bochner form is `eLpNorm _ 1` convergence.** If `∫ ‖f i - g‖ → 0` along
`l`, with every `f i` and `g` integrable, then `eLpNorm (f i - g) 1 μ → 0`. -/
theorem tendsto_eLpNorm_one_of_tendsto_integral_norm_sub {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} {l : Filter ι} {f : ι → Ω → E} {g : Ω → E}
    (hf : ∀ i, Integrable (f i) μ) (hg : Integrable g μ)
    (h : Tendsto (fun i => ∫ ω, ‖f i ω - g ω‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (f i - g) 1 μ) l (𝓝 0) := by
  have heq : ∀ i, eLpNorm (f i - g) 1 μ = ENNReal.ofReal (∫ ω, ‖f i ω - g ω‖ ∂μ) := by
    intro i
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hf i).sub hg)]
    simp [Pi.sub_apply]
  simp_rw [heq]
  simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp h

/-- **Averaging against a kernel supported in `[-ε, 0]` samples only `[t, t + ε]`.** If `ψ` is a
nonnegative probability density with respect to `μ` vanishing outside `[-ε, 0]`, and `F` is antitone
on `[t, t + ε]`, then the average `∫ s, ψ s * F (t - s) ∂μ` lies between `F (t + ε)` and `F t`.

Use this to bound a mollification of a monotone function by two of its values; no regularity of
`F` beyond antitonicity on the sampled interval is needed. -/
theorem integral_kernel_mem_Icc_of_antitoneOn {μ : Measure ℝ} {ψ F : ℝ → ℝ} {ε t : ℝ}
    (hε : 0 ≤ ε) (hFanti : AntitoneOn F (Set.Icc t (t + ε))) (hψ0 : ∀ s, 0 ≤ ψ s)
    (hψint : ∫ s, ψ s ∂μ = 1) (hψi : Integrable ψ μ)
    (hintF : Integrable (fun s => ψ s * F (t - s)) μ)
    (hsupp : ∀ s : ℝ, ψ s ≠ 0 → s ∈ Set.Icc (-ε) 0) :
    (∫ s, ψ s * F (t - s) ∂μ) ∈ Set.Icc (F (t + ε)) (F t) := by
  have hmass : ∀ c : ℝ, ∫ s, ψ s * c ∂μ = c := by
    intro c
    rw [integral_mul_const, hψint, one_mul]
  have hsample : ∀ s : ℝ, -ε ≤ s → s ≤ 0 → t - s ∈ Set.Icc t (t + ε) := fun s h1 h2 =>
    ⟨by linarith, by linarith⟩
  have hlo : t ∈ Set.Icc t (t + ε) := ⟨le_rfl, by linarith⟩
  have hhi : t + ε ∈ Set.Icc t (t + ε) := ⟨by linarith, le_rfl⟩
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩
  · have hle : ∀ s : ℝ, ψ s * F (t + ε) ≤ ψ s * F (t - s) := by
      intro s
      rcases eq_or_ne (ψ s) 0 with h0 | h0
      · simp [h0]
      · obtain ⟨hs1, hs2⟩ := hsupp s h0
        exact mul_le_mul_of_nonneg_left (hFanti (hsample s hs1 hs2) hhi (by linarith)) (hψ0 s)
    calc F (t + ε) = ∫ s, ψ s * F (t + ε) ∂μ := (hmass _).symm
      _ ≤ ∫ s, ψ s * F (t - s) ∂μ := integral_mono (hψi.mul_const _) hintF hle
  · have hle : ∀ s : ℝ, ψ s * F (t - s) ≤ ψ s * F t := by
      intro s
      rcases eq_or_ne (ψ s) 0 with h0 | h0
      · simp [h0]
      · obtain ⟨hs1, hs2⟩ := hsupp s h0
        exact mul_le_mul_of_nonneg_left (hFanti hlo (hsample s hs1 hs2) (by linarith)) (hψ0 s)
    calc ∫ s, ψ s * F (t - s) ∂μ ≤ ∫ s, ψ s * F t ∂μ := integral_mono hintF (hψi.mul_const _) hle
      _ = F t := hmass _

end MeasureTheory

end TauCeti
