/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.L2.BlockAverages
import TauCeti.Probability.Exchangeability.Map
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# L¹ convergence of Cesàro averages of a contractable process

This file proves the `weighted_sums_converge_L1` milestone from Layer 3 of the Exchangeability
roadmap. For a bounded measurable real-valued observable `f` of a contractable process `X`, all
fixed-start Cesàro windows

```text
(m + 1)⁻¹ ∑_{i ≤ m} f(X_{r + i})
```

converge in `L¹` to the same measurable limit.

The proof first applies the two-window identity
`Contractable.integral_sq_blockAverage_sub_of_disjoint` to compare two prefix averages through a
third block disjoint from both. This makes the prefixes Cauchy in Mathlib's complete `L²` space.
The same disjoint-block comparison shows that every fixed-start window converges to the prefix
limit. Finally, `eLpNorm_le_eLpNorm_of_exponent_le` turns the `L²` convergence into `L¹`
convergence.

The mathematical argument follows the elementary `L²` route around Theorem 1.1 in Kallenberg,
*Probabilistic Symmetries and Invariance Principles* (2005). The theorem statement is adapted
from `weighted_sums_converge_L1` in `cameronfreer/exchangeability` at commit
`e0532e59ceff23edab44dda9ab0655debbc9cc22`; the proof is rewritten around Tau Ceti's
closed-form block-average covariance API.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The square of the distance between two `L²` representatives is the integral of the square
of their pointwise difference. -/
private theorem dist_toLp_sq_eq_integral_sq {μ : Measure Ω} {g h : Ω → ℝ}
    (hg : MemLp g 2 μ) (hh : MemLp h 2 μ) :
    dist (hg.toLp g) (hh.toLp h) ^ 2 = ∫ ω, (g ω - h ω) ^ 2 ∂μ := by
  rw [dist_eq_norm, norm_sq_eq_re_inner (𝕜 := ℝ), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hg.toLp g) (hh.toLp h), hg.coeFn_toLp, hh.coeFn_toLp]
    with ω hsub hgω hhω
  rw [hsub]
  simp [Pi.sub_apply, hgω, hhω, pow_two]

/-- A bounded measurable observable of a contractable process has fixed-start Cesàro averages
converging in `L¹` to one common measurable limit.

The start `r` is fixed while the window length `m + 1` tends to infinity. The successor in the
length avoids assigning any special meaning to an empty average. -/
theorem weighted_sums_converge_L1 {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ i, Measurable (X i))
    {f : α → ℝ} (hf : Measurable f) (hf_bdd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    ∃ a : Ω → ℝ, Measurable a ∧ MemLp a 1 μ ∧
      ∀ r : ℕ,
        Tendsto
          (fun m => ∫ ω,
            |blockAverage (fun i ω => f (X i ω)) (fun j : Fin (m + 1) => r + j) ω - a ω| ∂μ)
          atTop (𝓝 0) := by
  let Y : ℕ → Ω → ℝ := fun i ω => f (X i ω)
  have hY_meas : ∀ i, Measurable (Y i) := fun i => hf.comp (hX_meas i)
  have hY : Contractable μ Y := hX.map_values hf fun i => (hX_meas i).aemeasurable
  obtain ⟨C, hC⟩ := hf_bdd
  have hY_L2 : ∀ i, MemLp (Y i) 2 μ := by
    intro i
    apply MemLp.of_bound (hY_meas i).aestronglyMeasurable C
    filter_upwards with ω
    exact hC (X i ω)
  let D : ℝ := Var[Y 0; μ] - cov[Y 0, Y 1; μ]
  have hD : 0 ≤ D := by
    have hvar := hY.variance_blockAverage_sub_of_disjoint hY_L2
      (n := 1) (m := 1) (k := fun _ : Fin 1 => 0) (k' := fun _ : Fin 1 => 1)
      (by omega) (by omega) (fun _ _ _ => Subsingleton.elim _ _)
      (fun _ _ _ => Subsingleton.elim _ _) (by omega)
    have hnonneg := variance_nonneg
      (blockAverage Y (fun _ : Fin 1 => 0) - blockAverage Y (fun _ : Fin 1 => 1)) μ
    rw [hvar] at hnonneg
    norm_num at hnonneg
    dsimp only [D]
    linarith
  let A : ℕ → Ω → ℝ :=
    fun m => blockAverage Y (Fin.val : Fin (m + 1) → ℕ)
  have hA_L2 : ∀ m, MemLp (A m) 2 μ := fun m =>
    memLp_blockAverage (fun i : Fin (m + 1) => (i : ℕ)) fun i => hY_L2 i
  let A₂ : ℕ → Lp ℝ 2 μ := fun m => (hA_L2 m).toLp (A m)
  have hA₂_cauchy : CauchySeq A₂ := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hbound_tendsto :
        Tendsto (fun n : ℕ => 2 * D / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, one_mul, mul_zero] using
        (tendsto_const_nhds.mul
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) :
          Tendsto (fun n : ℕ => (2 * D) * (1 / (↑n + 1))) atTop (𝓝 ((2 * D) * 0)))
    have heventually :
        ∀ᶠ n : ℕ in atTop, 2 * D / ((n : ℝ) + 1) < (ε / 2) ^ 2 :=
      hbound_tendsto (Iio_mem_nhds (sq_pos_of_pos (half_pos hε)))
    obtain ⟨N, hN⟩ := eventually_atTop.1 heventually
    refine ⟨N, fun n hn m hm => ?_⟩
    let l := n + m + 2
    let k : Fin l → ℕ := fun i => l + i
    have hl : 0 < l := by omega
    have hk : Function.Injective k := by
      intro i j hij
      exact Fin.ext (Nat.add_left_cancel hij)
    have hn_disjoint : ∀ i : Fin (n + 1), ∀ j : Fin l, (i : ℕ) ≠ k j := by
      intro i j
      dsimp only [k, l]
      omega
    have hm_disjoint : ∀ i : Fin (m + 1), ∀ j : Fin l, (i : ℕ) ≠ k j := by
      intro i j
      dsimp only [k, l]
      omega
    let B : Ω → ℝ := blockAverage Y k
    have hB_L2 : MemLp B 2 μ := memLp_blockAverage k fun i => hY_L2 (k i)
    have hn_formula :
        ∫ ω, (A n ω - B ω) ^ 2 ∂μ =
          D / ((n : ℝ) + 1) + D / l := by
      simpa only [A, D, B, Nat.cast_succ] using
        hY.integral_sq_blockAverage_sub_of_disjoint hY_L2 (Nat.succ_pos n) hl
          Fin.val_injective hk hn_disjoint
    have hm_formula :
        ∫ ω, (A m ω - B ω) ^ 2 ∂μ =
          D / ((m : ℝ) + 1) + D / l := by
      simpa only [A, D, B, Nat.cast_succ] using
        hY.integral_sq_blockAverage_sub_of_disjoint hY_L2 (Nat.succ_pos m) hl
          Fin.val_injective hk hm_disjoint
    have hn_frac : D / (l : ℝ) ≤ D / ((n : ℝ) + 1) := by
      exact div_le_div_of_nonneg_left hD (by positivity)
        (by exact_mod_cast (show n + 1 ≤ l by omega))
    have hm_frac : D / (l : ℝ) ≤ D / ((m : ℝ) + 1) := by
      exact div_le_div_of_nonneg_left hD (by positivity)
        (by exact_mod_cast (show m + 1 ≤ l by omega))
    have hn_sq :
        dist (A₂ n) (hB_L2.toLp B) ^ 2 ≤ 2 * D / ((n : ℝ) + 1) := by
      rw [dist_toLp_sq_eq_integral_sq (hA_L2 n) hB_L2, hn_formula]
      calc
        D / ((n : ℝ) + 1) + D / (l : ℝ)
            ≤ D / ((n : ℝ) + 1) + D / ((n : ℝ) + 1) := add_le_add le_rfl hn_frac
        _ = 2 * D / ((n : ℝ) + 1) := by ring
    have hm_sq :
        dist (A₂ m) (hB_L2.toLp B) ^ 2 ≤ 2 * D / ((m : ℝ) + 1) := by
      rw [dist_toLp_sq_eq_integral_sq (hA_L2 m) hB_L2, hm_formula]
      calc
        D / ((m : ℝ) + 1) + D / (l : ℝ)
            ≤ D / ((m : ℝ) + 1) + D / ((m : ℝ) + 1) := add_le_add le_rfl hm_frac
        _ = 2 * D / ((m : ℝ) + 1) := by ring
    have hn_dist : dist (A₂ n) (hB_L2.toLp B) < ε / 2 := by
      have hn_bound := hN n hn
      nlinarith [show 0 ≤ dist (A₂ n) (hB_L2.toLp B) from dist_nonneg]
    have hm_dist : dist (A₂ m) (hB_L2.toLp B) < ε / 2 := by
      have hm_bound := hN m hm
      nlinarith [show 0 ≤ dist (A₂ m) (hB_L2.toLp B) from dist_nonneg]
    calc
      dist (A₂ n) (A₂ m)
          ≤ dist (A₂ n) (hB_L2.toLp B) + dist (hB_L2.toLp B) (A₂ m) :=
        dist_triangle _ _ _
      _ < ε := by rw [dist_comm (hB_L2.toLp B) (A₂ m)]; linarith
  obtain ⟨a₂, ha₂⟩ :
      ∃ a₂ : Lp ℝ 2 μ, Tendsto A₂ atTop (𝓝 a₂) :=
    CompleteSpace.complete (show Cauchy (atTop.map A₂) from hA₂_cauchy)
  let a : Ω → ℝ := (Lp.aestronglyMeasurable a₂).mk a₂
  have ha₂_ae : a₂ =ᵐ[μ] a := (Lp.aestronglyMeasurable a₂).ae_eq_mk
  have ha_meas : Measurable a := (Lp.aestronglyMeasurable a₂).measurable_mk
  have ha_L2 : MemLp a 2 μ :=
    (memLp_congr_ae ha₂_ae).mp (Lp.memLp a₂)
  have ha_L1 : MemLp a 1 μ := ha_L2.mono_exponent one_le_two
  have ha_toLp : ha_L2.toLp a = a₂ := by
    apply Lp.ext
    exact ha_L2.coeFn_toLp.trans ha₂_ae.symm
  refine ⟨a, ha_meas, ha_L1, fun r => ?_⟩
  let W : ℕ → Ω → ℝ :=
    fun m => blockAverage Y fun j : Fin (m + 1) => r + j
  have hW_L2 : ∀ m, MemLp (W m) 2 μ := fun m =>
    memLp_blockAverage (fun j : Fin (m + 1) => r + j) fun j => hY_L2 (r + j)
  let W₂ : ℕ → Lp ℝ 2 μ := fun m => (hW_L2 m).toLp (W m)
  have hWA_dist :
      Tendsto (fun m => dist (W₂ m) (A₂ m)) atTop (𝓝 0) := by
    have hq :
        Tendsto (fun m : ℕ => 2 * D / ((m : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, one_mul, mul_zero] using
        (tendsto_const_nhds.mul
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) :
          Tendsto (fun m : ℕ => (2 * D) * (1 / (↑m + 1))) atTop (𝓝 ((2 * D) * 0)))
    have hsqrt :
        Tendsto (fun m : ℕ => 2 * Real.sqrt (2 * D / ((m : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hq).const_mul 2
    refine squeeze_zero' (Eventually.of_forall fun m => dist_nonneg) ?_ hsqrt
    filter_upwards with m
    let l := r + m + 1
    let k : Fin (m + 1) → ℕ := fun i => l + i
    have hk : Function.Injective k := by
      intro i j hij
      exact Fin.ext (Nat.add_left_cancel hij)
    have hprefix_disjoint :
        ∀ i : Fin (m + 1), ∀ j : Fin (m + 1), (i : ℕ) ≠ k j := by
      intro i j
      dsimp only [k, l]
      omega
    have hwindow_disjoint :
        ∀ i : Fin (m + 1), ∀ j : Fin (m + 1), r + (i : ℕ) ≠ k j := by
      intro i j
      dsimp only [k, l]
      omega
    let B : Ω → ℝ := blockAverage Y k
    have hB_L2 : MemLp B 2 μ := memLp_blockAverage k fun i => hY_L2 (k i)
    have hprefix_formula :
        ∫ ω, (A m ω - B ω) ^ 2 ∂μ = 2 * D / ((m : ℝ) + 1) := by
      have hformula :=
        hY.integral_sq_blockAverage_sub_of_disjoint hY_L2
          (Nat.succ_pos m) (Nat.succ_pos m) Fin.val_injective hk hprefix_disjoint
      calc
        ∫ ω, (A m ω - B ω) ^ 2 ∂μ =
            D / ((m : ℝ) + 1) + D / ((m : ℝ) + 1) := by
          simpa only [A, D, B, Nat.cast_succ] using hformula
        _ = 2 * D / ((m : ℝ) + 1) := by ring
    have hwindow_formula :
        ∫ ω, (W m ω - B ω) ^ 2 ∂μ = 2 * D / ((m : ℝ) + 1) := by
      have hformula :=
        hY.integral_sq_blockAverage_sub_of_disjoint hY_L2
          (Nat.succ_pos m) (Nat.succ_pos m)
          (fun _ _ hij => Fin.ext (Nat.add_left_cancel hij)) hk hwindow_disjoint
      calc
        ∫ ω, (W m ω - B ω) ^ 2 ∂μ =
            D / ((m : ℝ) + 1) + D / ((m : ℝ) + 1) := by
          simpa only [W, D, B, Nat.cast_succ] using hformula
        _ = 2 * D / ((m : ℝ) + 1) := by ring
    have hq_nonneg : 0 ≤ 2 * D / ((m : ℝ) + 1) := by positivity
    have hprefix_dist :
        dist (A₂ m) (hB_L2.toLp B) = Real.sqrt (2 * D / ((m : ℝ) + 1)) := by
      have hsquare :
          dist (A₂ m) (hB_L2.toLp B) ^ 2 = 2 * D / ((m : ℝ) + 1) := by
        rw [dist_toLp_sq_eq_integral_sq (hA_L2 m) hB_L2, hprefix_formula]
      nlinarith [show 0 ≤ dist (A₂ m) (hB_L2.toLp B) from dist_nonneg,
        Real.sqrt_nonneg (2 * D / ((m : ℝ) + 1)),
        Real.sq_sqrt hq_nonneg]
    have hwindow_dist :
        dist (W₂ m) (hB_L2.toLp B) = Real.sqrt (2 * D / ((m : ℝ) + 1)) := by
      have hsquare :
          dist (W₂ m) (hB_L2.toLp B) ^ 2 = 2 * D / ((m : ℝ) + 1) := by
        rw [dist_toLp_sq_eq_integral_sq (hW_L2 m) hB_L2, hwindow_formula]
      nlinarith [show 0 ≤ dist (W₂ m) (hB_L2.toLp B) from dist_nonneg,
        Real.sqrt_nonneg (2 * D / ((m : ℝ) + 1)),
        Real.sq_sqrt hq_nonneg]
    calc
      dist (W₂ m) (A₂ m)
          ≤ dist (W₂ m) (hB_L2.toLp B) + dist (hB_L2.toLp B) (A₂ m) :=
        dist_triangle _ _ _
      _ = 2 * Real.sqrt (2 * D / ((m : ℝ) + 1)) := by
        rw [hwindow_dist, dist_comm (hB_L2.toLp B), hprefix_dist]
        ring
  have hW₂_tendsto : Tendsto W₂ atTop (𝓝 a₂) := by
    apply tendsto_iff_dist_tendsto_zero.2
    have hupper :
        Tendsto (fun m => dist (W₂ m) (A₂ m) + dist (A₂ m) a₂) atTop (𝓝 0) := by
      simpa only [zero_add] using hWA_dist.add (tendsto_iff_dist_tendsto_zero.mp ha₂)
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hupper
    filter_upwards with m
    exact dist_triangle _ (A₂ m) _
  have hW_L2_tendsto :
      Tendsto (fun m => eLpNorm (W m - a) 2 μ) atTop (𝓝 0) := by
    rw [← Lp.tendsto_Lp_iff_tendsto_eLpNorm'' W hW_L2 a ha_L2]
    simpa only [ha_toLp] using hW₂_tendsto
  have hW_L1_tendsto :
      Tendsto (fun m => eLpNorm (W m - a) 1 μ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hW_L2_tendsto
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards with m
    exact eLpNorm_le_eLpNorm_of_exponent_le one_le_two
      ((hW_L2 m).sub ha_L2).aestronglyMeasurable
  have hW_L1_real :
      Tendsto (fun m => (eLpNorm (W m - a) 1 μ).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hW_L1_tendsto
  convert hW_L1_real using 1
  ext m
  simpa only [Pi.sub_apply, Real.norm_eq_abs, eLpNorm_one_eq_lintegral_enorm] using
    (integral_norm_eq_lintegral_enorm ((hW_L2 m).sub ha_L2).aestronglyMeasurable)

end Probability

end TauCeti
