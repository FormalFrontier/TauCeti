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

/-- Bound the `L²` distance from a block average to a longer disjoint block average. -/
private theorem dist_blockAverage_toLp_le_of_disjoint {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ} (hY : Contractable μ Y)
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
    [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ} (hY : Contractable μ Y)
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
  -- Compare any two prefixes through a fresh block beyond both to obtain an `L²` Cauchy sequence.
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
    have hdist :
        dist (A₂ n) (A₂ m) ≤
          Real.sqrt (2 * D / ((n : ℝ) + 1)) +
            Real.sqrt (2 * D / ((m : ℝ) + 1)) := by
      simpa only [A₂, A, D, Nat.cast_succ] using
        dist_blockAverages_toLp_le_via_disjoint hY hY_L2 hD
          (Nat.succ_pos n) (Nat.succ_pos m) hl Fin.val_injective Fin.val_injective hk
          hn_disjoint hm_disjoint (by omega) (by omega)
    have hn_dist : Real.sqrt (2 * D / ((n : ℝ) + 1)) < ε / 2 := by
      have hn_bound := hN n hn
      have hn_nonneg : 0 ≤ 2 * D / ((n : ℝ) + 1) := by positivity
      nlinarith [Real.sqrt_nonneg (2 * D / ((n : ℝ) + 1)), Real.sq_sqrt hn_nonneg]
    have hm_dist : Real.sqrt (2 * D / ((m : ℝ) + 1)) < ε / 2 := by
      have hm_bound := hN m hm
      have hm_nonneg : 0 ≤ 2 * D / ((m : ℝ) + 1) := by positivity
      nlinarith [Real.sqrt_nonneg (2 * D / ((m : ℝ) + 1)), Real.sq_sqrt hm_nonneg]
    linarith
  -- Completeness of `L²` supplies the common prefix limit and a measurable representative.
  obtain ⟨a₂, ha₂⟩ :
      ∃ a₂ : Lp ℝ 2 μ, Tendsto A₂ atTop (𝓝 a₂) :=
    cauchySeq_tendsto_of_complete hA₂_cauchy
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
  -- A fresh disjoint block makes each fixed-start window close to the same-length prefix.
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
    calc
      dist (W₂ m) (A₂ m)
          ≤ Real.sqrt (2 * D / ((m : ℝ) + 1)) +
              Real.sqrt (2 * D / ((m : ℝ) + 1)) := by
        simpa only [W₂, A₂, hW_L2, hA_L2, W, A, D, Nat.cast_succ] using
          dist_blockAverages_toLp_le_via_disjoint hY hY_L2 hD
            (Nat.succ_pos m) (Nat.succ_pos m) (Nat.succ_pos m)
            (fun _ _ hij => Fin.ext (Nat.add_left_cancel hij)) Fin.val_injective hk
            hwindow_disjoint hprefix_disjoint le_rfl le_rfl
      _ = 2 * Real.sqrt (2 * D / ((m : ℝ) + 1)) := by ring
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
  -- Probability-space norm monotonicity descends convergence from `L²` to `L¹`.
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
