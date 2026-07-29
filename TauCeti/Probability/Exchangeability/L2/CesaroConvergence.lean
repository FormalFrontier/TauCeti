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
limit. Finally, `eLpNorm_le_eLpNorm_mul_rpow_measure_univ` turns the `L²` convergence into `L¹`
convergence, at the cost of the fixed factor `μ univ ^ (1 - 1/2)`.

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

/-- Bound the `L²` distance from a block average to a longer disjoint block average. -/
private theorem dist_blockAverage_toLp_le_of_disjoint {μ : Measure Ω}
    [IsFiniteMeasure μ] {Y : ℕ → Ω → ℝ} (hY : Contractable μ Y)
    (hY_L2 : ∀ i, MemLp (Y i) 2 μ)
    (hD : 0 ≤ Var[Y 0; μ] - cov[Y 0, Y 1; μ]) {n l : ℕ}
    (hn : 0 < n) (hl : 0 < l) {k : Fin n → ℕ} {k₀ : Fin l → ℕ}
    (hk : Function.Injective k) (hk₀ : Function.Injective k₀)
    (hdisj : ∀ i j, k i ≠ k₀ j) (hnl : n ≤ l) :
    dist
        ((memLp_blockAverage k fun i => hY_L2 (k i)).toLp (blockAverage Y k))
        ((memLp_blockAverage k₀ fun i => hY_L2 (k₀ i)).toLp (blockAverage Y k₀)) ≤
      Real.sqrt (2 * (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / n) := by
  let B : Ω → ℝ := blockAverage Y k₀
  have hB_L2 : MemLp B 2 μ := memLp_blockAverage k₀ fun i => hY_L2 (k₀ i)
  have hformula :
      ∫ ω, (blockAverage Y k ω - B ω) ^ 2 ∂μ =
        (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / n +
          (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / l := by
    simpa only [B] using
      hY.integral_sq_blockAverage_sub_of_disjoint hY_L2 hn hl hk hk₀ hdisj
  have hfrac :
      (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / (l : ℝ) ≤
        (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / n := by
    exact div_le_div_of_nonneg_left hD (by positivity) (by exact_mod_cast hnl)
  have hsq :
      dist
          ((memLp_blockAverage k fun i => hY_L2 (k i)).toLp (blockAverage Y k))
          (hB_L2.toLp B) ^ 2 ≤
        2 * (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / n := by
    rw [dist_toLp_sq_eq_integral_sq _ hB_L2, hformula]
    calc
      (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / (n : ℝ) +
            (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / (l : ℝ)
          ≤ (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / n +
              (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / n :=
        add_le_add le_rfl hfrac
      _ = 2 * (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / n := by ring
  have hnonneg : 0 ≤ 2 * (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / (n : ℝ) := by positivity
  have hdist_nonneg :
      0 ≤ dist
        ((memLp_blockAverage k fun i => hY_L2 (k i)).toLp (blockAverage Y k))
        (hB_L2.toLp B) :=
    dist_nonneg
  have hdist_le_sqrt :
      dist
          ((memLp_blockAverage k fun i => hY_L2 (k i)).toLp (blockAverage Y k))
          (hB_L2.toLp B) ≤
        Real.sqrt (2 * (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / n) := by
    nlinarith [hdist_nonneg, Real.sqrt_nonneg
      (2 * (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / n), Real.sq_sqrt hnonneg]
  simpa only [B] using hdist_le_sqrt

/-- Compare two block averages in `L²` through a longer block disjoint from both. -/
private theorem dist_blockAverages_toLp_le_via_disjoint {μ : Measure Ω}
    [IsFiniteMeasure μ] {Y : ℕ → Ω → ℝ} (hY : Contractable μ Y)
    (hY_L2 : ∀ i, MemLp (Y i) 2 μ)
    (hD : 0 ≤ Var[Y 0; μ] - cov[Y 0, Y 1; μ]) {n m l : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hl : 0 < l)
    {k : Fin n → ℕ} {k' : Fin m → ℕ} {k₀ : Fin l → ℕ}
    (hk : Function.Injective k) (hk' : Function.Injective k')
    (hk₀ : Function.Injective k₀) (hdisj : ∀ i j, k i ≠ k₀ j)
    (hdisj' : ∀ i j, k' i ≠ k₀ j) (hnl : n ≤ l) (hml : m ≤ l) :
    dist
        ((memLp_blockAverage k fun i => hY_L2 (k i)).toLp (blockAverage Y k))
        ((memLp_blockAverage k' fun i => hY_L2 (k' i)).toLp (blockAverage Y k')) ≤
      Real.sqrt (2 * (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / n) +
        Real.sqrt (2 * (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / m) := by
  have hk_bound :=
    dist_blockAverage_toLp_le_of_disjoint hY hY_L2 hD hn hl hk hk₀ hdisj hnl
  have hk'_bound :=
    dist_blockAverage_toLp_le_of_disjoint hY hY_L2 hD hm hl hk' hk₀ hdisj' hml
  calc
    dist
          ((memLp_blockAverage k fun i => hY_L2 (k i)).toLp (blockAverage Y k))
          ((memLp_blockAverage k' fun i => hY_L2 (k' i)).toLp (blockAverage Y k'))
        ≤ dist
            ((memLp_blockAverage k fun i => hY_L2 (k i)).toLp (blockAverage Y k))
            ((memLp_blockAverage k₀ fun i => hY_L2 (k₀ i)).toLp (blockAverage Y k₀)) +
          dist ((memLp_blockAverage k₀ fun i => hY_L2 (k₀ i)).toLp (blockAverage Y k₀))
            ((memLp_blockAverage k' fun i => hY_L2 (k' i)).toLp (blockAverage Y k')) :=
      dist_triangle _ _ _
    _ ≤ Real.sqrt (2 * (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / n) +
          Real.sqrt (2 * (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / m) := by
      rw [dist_comm
        ((memLp_blockAverage k₀ fun i => hY_L2 (k₀ i)).toLp (blockAverage Y k₀))]
      exact add_le_add hk_bound hk'_bound

/-- For a contractable `L²` sequence the lag-one covariance never exceeds the variance. -/
private theorem zero_le_variance_sub_covariance_of_contractable {μ : Measure Ω} [IsFiniteMeasure μ]
    {Y : ℕ → Ω → ℝ} (hY : Contractable μ Y) (hY_L2 : ∀ i, MemLp (Y i) 2 μ) :
    0 ≤ Var[Y 0; μ] - cov[Y 0, Y 1; μ] := by
  -- The two-window identity exhibits the gap as a nonnegative multiple of a variance.
  have hvar := hY.variance_blockAverage_sub_of_disjoint hY_L2
    (n := 1) (m := 1) (k := fun _ : Fin 1 => 0) (k' := fun _ : Fin 1 => 1)
    (by omega) (by omega) (fun _ _ _ => Subsingleton.elim _ _)
    (fun _ _ _ => Subsingleton.elim _ _) (by omega)
  have hnonneg := variance_nonneg
    (blockAverage Y (fun _ : Fin 1 => 0) - blockAverage Y (fun _ : Fin 1 => 1)) μ
  rw [hvar] at hnonneg
  norm_num at hnonneg
  linarith

/-- The prefix block averages of a contractable `L²` sequence are Cauchy in `L²`. -/
private theorem cauchySeq_blockAverage_prefix_toLp {μ : Measure Ω} [IsFiniteMeasure μ]
    {Y : ℕ → Ω → ℝ} (hY : Contractable μ Y) (hY_L2 : ∀ i, MemLp (Y i) 2 μ) :
    CauchySeq fun m : ℕ =>
      (memLp_blockAverage (fun i : Fin (m + 1) => (i : ℕ)) fun i => hY_L2 i).toLp
        (blockAverage Y fun i : Fin (m + 1) => (i : ℕ)) := by
  -- Compare any two prefixes through a fresh block lying beyond both.
  have hD := zero_le_variance_sub_covariance_of_contractable hY hY_L2
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hquot : Tendsto (fun n : ℕ => 2 * (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using (tendsto_const_div_atTop_nhds_zero_nat
      (2 * (Var[Y 0; μ] - cov[Y 0, Y 1; μ]))).comp (Filter.tendsto_add_atTop_nat 1)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hquot (Iio_mem_nhds (sq_pos_of_pos (half_pos hε))))
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
  have hdist :=
    dist_blockAverages_toLp_le_via_disjoint hY hY_L2 hD
      (Nat.succ_pos n) (Nat.succ_pos m) hl Fin.val_injective Fin.val_injective hk
      hn_disjoint hm_disjoint (by omega) (by omega)
  have hlt : ∀ j : ℕ, N ≤ j →
      Real.sqrt (2 * (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / ((j : ℝ) + 1)) < ε / 2 :=
    fun j hj => (Real.sqrt_lt' (half_pos hε)).mpr (hN j hj)
  have hn_dist := hlt n hn
  have hm_dist := hlt m hm
  simp only [Nat.cast_succ] at hdist
  linarith

/-- Every fixed-start window approaches the prefix of the same length in `L²`. -/
private theorem tendsto_dist_blockAverage_window_prefix_toLp {μ : Measure Ω}
    [IsFiniteMeasure μ] {Y : ℕ → Ω → ℝ} (hY : Contractable μ Y)
    (hY_L2 : ∀ i, MemLp (Y i) 2 μ) (r : ℕ) :
    Tendsto (fun m : ℕ =>
        dist ((memLp_blockAverage (fun j : Fin (m + 1) => r + j) fun j => hY_L2 (r + j)).toLp
            (blockAverage Y fun j : Fin (m + 1) => r + j))
          ((memLp_blockAverage (fun i : Fin (m + 1) => (i : ℕ)) fun i => hY_L2 i).toLp
            (blockAverage Y fun i : Fin (m + 1) => (i : ℕ))))
      atTop (𝓝 0) := by
  -- Compare window and prefix through a block lying beyond them both.
  have hD := zero_le_variance_sub_covariance_of_contractable hY hY_L2
  have hsqrt :
      Tendsto (fun m : ℕ =>
          2 * Real.sqrt (2 * (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / ((m : ℝ) + 1))) atTop (𝓝 0) := by
    have hquot : Tendsto (fun n : ℕ => 2 * (Var[Y 0; μ] - cov[Y 0, Y 1; μ]) / ((n : ℝ) + 1))
        atTop (𝓝 0) := by
      simpa [Function.comp_def] using (tendsto_const_div_atTop_nhds_zero_nat
        (2 * (Var[Y 0; μ] - cov[Y 0, Y 1; μ]))).comp (Filter.tendsto_add_atTop_nat 1)
    simpa using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hquot).const_mul 2
  refine squeeze_zero' (Eventually.of_forall fun m => dist_nonneg) ?_ hsqrt
  filter_upwards with m
  let l := r + m + 1
  let k : Fin (m + 1) → ℕ := fun i => l + i
  have hk : Function.Injective k := by
    intro i j hij
    exact Fin.ext (Nat.add_left_cancel hij)
  have hprefix_disjoint : ∀ i : Fin (m + 1), ∀ j : Fin (m + 1), (i : ℕ) ≠ k j := by
    intro i j
    dsimp only [k, l]
    omega
  have hwindow_disjoint : ∀ i : Fin (m + 1), ∀ j : Fin (m + 1), r + (i : ℕ) ≠ k j := by
    intro i j
    dsimp only [k, l]
    omega
  have hdist :=
    dist_blockAverages_toLp_le_via_disjoint hY hY_L2 hD
      (Nat.succ_pos m) (Nat.succ_pos m) (Nat.succ_pos m)
      (fun _ _ hij => Fin.ext (Nat.add_left_cancel hij)) Fin.val_injective hk
      hwindow_disjoint hprefix_disjoint le_rfl le_rfl
  simp only [Nat.cast_succ] at hdist
  linarith

/-- On a finite measure space, `L²` convergence to a limit gives `L¹` convergence of the
integrated absolute difference. -/
private theorem tendsto_integral_abs_sub_of_tendsto_eLpNorm_two {μ : Measure Ω}
    [IsFiniteMeasure μ] {W : ℕ → Ω → ℝ} {a : Ω → ℝ}
    (hWa_meas : ∀ m, AEStronglyMeasurable (W m - a) μ)
    (h : Tendsto (fun m => eLpNorm (W m - a) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ ω, |W m ω - a ω| ∂μ) atTop (𝓝 0) := by
  have hW_L1 : Tendsto (fun m => eLpNorm (W m - a) 1 μ) atTop (𝓝 0) := by
    -- The exponent comparison costs a fixed finite factor, which the limit absorbs.
    have hbound := fun m => eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
      one_le_two (hWa_meas m)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
      (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall hbound)
    simpa using ENNReal.Tendsto.mul_const h
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ Set.univ)))
  have hreal : Tendsto (fun m => (eLpNorm (W m - a) 1 μ).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hW_L1
  convert hreal using 1
  ext m
  simpa only [Pi.sub_apply, Real.norm_eq_abs, eLpNorm_one_eq_lintegral_enorm] using
    (integral_norm_eq_lintegral_enorm (hWa_meas m))

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
  have hA_L2 : ∀ m : ℕ, MemLp (blockAverage Y fun i : Fin (m + 1) => (i : ℕ)) 2 μ := fun m =>
    memLp_blockAverage (fun i : Fin (m + 1) => (i : ℕ)) fun i => hY_L2 i
  let A₂ : ℕ → Lp ℝ 2 μ := fun m =>
    (hA_L2 m).toLp (blockAverage Y fun i : Fin (m + 1) => (i : ℕ))
  -- Completeness of `L²` turns the Cauchy prefixes into a limit with a measurable representative.
  obtain ⟨a₂, ha₂⟩ : ∃ a₂ : Lp ℝ 2 μ, Tendsto A₂ atTop (𝓝 a₂) :=
    cauchySeq_tendsto_of_complete (cauchySeq_blockAverage_prefix_toLp hY hY_L2)
  let a : Ω → ℝ := (Lp.aestronglyMeasurable a₂).mk a₂
  have ha₂_ae : a₂ =ᵐ[μ] a := (Lp.aestronglyMeasurable a₂).ae_eq_mk
  have ha_meas : Measurable a := (Lp.aestronglyMeasurable a₂).measurable_mk
  have ha_L2 : MemLp a 2 μ := (memLp_congr_ae ha₂_ae).mp (Lp.memLp a₂)
  have ha_toLp : ha_L2.toLp a = a₂ :=
    Lp.ext (ha_L2.coeFn_toLp.trans ha₂_ae.symm)
  refine ⟨a, ha_meas, ha_L2.mono_exponent one_le_two, fun r => ?_⟩
  have hW_L2 : ∀ m : ℕ, MemLp (blockAverage Y fun j : Fin (m + 1) => r + j) 2 μ := fun m =>
    memLp_blockAverage (fun j : Fin (m + 1) => r + j) fun j => hY_L2 (r + j)
  let W₂ : ℕ → Lp ℝ 2 μ := fun m =>
    (hW_L2 m).toLp (blockAverage Y fun j : Fin (m + 1) => r + j)
  -- Each fixed-start window tracks the same-length prefix, so it shares the prefix limit.
  have hW₂_tendsto : Tendsto W₂ atTop (𝓝 a₂) := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero'
      (Eventually.of_forall fun _ => dist_nonneg) (Eventually.of_forall fun m =>
        dist_triangle _ (A₂ m) _) ?_)
    simpa only [zero_add] using
      (tendsto_dist_blockAverage_window_prefix_toLp hY hY_L2 r).add
        (tendsto_iff_dist_tendsto_zero.mp ha₂)
  refine tendsto_integral_abs_sub_of_tendsto_eLpNorm_two
    (fun m => ((hW_L2 m).sub ha_L2).aestronglyMeasurable) ?_
  rw [← Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hW_L2 a ha_L2]
  simpa only [ha_toLp] using hW₂_tendsto

end Probability

end TauCeti
