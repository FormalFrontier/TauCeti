/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.L2.BlockAverages
import TauCeti.MeasureTheory.Function.L2ToL1Convergence
import TauCeti.Probability.Exchangeability.Map
import TauCeti.MeasureTheory.Function.BoundedMemLp
import Mathlib.MeasureTheory.Function.L2Space

/-!
# L¹ convergence of Cesàro averages of a contractable process

This file proves the `weighted_sums_converge_L1` milestone from Layer 3 of the Exchangeability
roadmap. For a measurable real-valued observable `f` of a contractable process `X` with
`f ∘ X 0` square-integrable — in particular for any bounded `f` — the block averages

```text
(m + 1)⁻¹ ∑_{i ≤ m} f(X_{k m i})
```

converge in `L¹` to the same measurable limit, for **every** selection `k` that is injective for
all sufficiently large lengths. The selection may *move* with the length: fixed-start windows
`k m i = r + i` are one instance, and disjoint windows `k m i = c * (m + 1) + i` — which fixed
starts cannot express — are another.

The proof first applies the two-window identity
`Contractable.integral_sq_blockAverage_sub_of_disjoint` to compare two prefix averages through a
third block disjoint from both. This makes the prefixes Cauchy in Mathlib's complete `L²` space.
The same disjoint-block comparison shows that every such selection converges to
the prefix limit: its bound depends on the block *lengths* and not on their positions, so a
comparison block beyond the selection's range is available at every length. Finally,
`eLpNorm_le_eLpNorm_mul_rpow_measure_univ` turns the `L²` convergence into `L¹`
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
  simpa only [B] using Real.le_sqrt_of_sq_le hsq

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

/-- **Compare a moving injective selection with the prefix in `L²`.** The selection `k n` may move
with the length `n + 1`; injectivity is needed only for all sufficiently large lengths, since
the conclusion is a limit.

This is where the length-only bound of `dist_blockAverages_toLp_le_via_disjoint` earns its keep:
that bound is `√(2(v−c)/n) + √(2(v−c)/m)`, depending on the two block *lengths* and not on where
the blocks sit. A comparison block placed beyond both — past `sup (k m)` as well as past the
prefix — is therefore available at every length, whatever the selection does. -/
private theorem tendsto_dist_blockAverage_moving_prefix_toLp {μ : Measure Ω}
    [IsFiniteMeasure μ] {Y : ℕ → Ω → ℝ} (hY : Contractable μ Y)
    (hY_L2 : ∀ i, MemLp (Y i) 2 μ) {k : ∀ n : ℕ, Fin (n + 1) → ℕ}
    (hk : ∀ᶠ n in atTop, Function.Injective (k n)) :
    Tendsto (fun m : ℕ =>
        dist ((memLp_blockAverage (k m) fun j => hY_L2 (k m j)).toLp (blockAverage Y (k m)))
          ((memLp_blockAverage (fun i : Fin (m + 1) => (i : ℕ)) fun i => hY_L2 i).toLp
            (blockAverage Y fun i : Fin (m + 1) => (i : ℕ))))
      atTop (𝓝 0) := by
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
  filter_upwards [hk] with m hkm
  -- A block placed beyond both the selection's range and the prefix.
  set l : ℕ := max (Finset.univ.sup fun i : Fin (m + 1) => k m i) m + 1 with hl
  have hsel_lt : ∀ i : Fin (m + 1), k m i < l := by
    intro i
    have hle : k m i ≤ Finset.univ.sup fun i : Fin (m + 1) => k m i :=
      Finset.le_sup (Finset.mem_univ i)
    have := le_max_left (Finset.univ.sup fun i : Fin (m + 1) => k m i) m
    omega
  have hpre_lt : ∀ i : Fin (m + 1), (i : ℕ) < l := by
    intro i
    have := le_max_right (Finset.univ.sup fun i : Fin (m + 1) => k m i) m
    have := i.isLt
    omega
  have hk₀ : Function.Injective (fun i : Fin (m + 1) => l + (i : ℕ)) :=
    fun i j hij => Fin.ext (Nat.add_left_cancel hij)
  have hsel_disjoint : ∀ i j : Fin (m + 1), k m i ≠ l + (j : ℕ) := by
    intro i j; have := hsel_lt i; omega
  have hpre_disjoint : ∀ i j : Fin (m + 1), (i : ℕ) ≠ l + (j : ℕ) := by
    intro i j; have := hpre_lt i; omega
  have hdist :=
    dist_blockAverages_toLp_le_via_disjoint hY hY_L2 hD
      (Nat.succ_pos m) (Nat.succ_pos m) (Nat.succ_pos m)
      hkm Fin.val_injective hk₀ hsel_disjoint hpre_disjoint le_rfl le_rfl
  simp only [Nat.cast_succ] at hdist
  linarith

/-- A measurable observable of a contractable process whose composite with a *single* coordinate is
square-integrable has moving injective block averages converging in `L¹` to one common measurable
limit.

The selection `k m` may **move** with the length `m + 1`, and need only be injective
*eventually* — finitely many degenerate initial selections cannot affect a limit. This costs
nothing because the underlying `L²` comparison is bounded in terms of the block lengths and not
their positions. Fixed starts are the instance `fixedStart r`, with
`fixedStart_eventually_injective`.
Disjoint windows are the instance `k m j = c * (m + 1) + j`, which fixed starts cannot give:
windows from distinct fixed starts overlap once the common length exceeds the gap between them.

The limit `a` does not depend on the selection: it is the prefix limit, so every moving selection
converges to the *same* function. The successor in the length avoids assigning any special meaning
to an empty average.

Contractability makes the mapped coordinates identically distributed, so square-integrability at
coordinate `0` carries to all of them. -/
theorem weighted_sums_converge_L1_of_memLp {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_ae : ∀ i, AEMeasurable (X i) μ)
    {f : α → ℝ} (hf : Measurable f) (hf_L2 : MemLp (fun ω => f (X 0 ω)) 2 μ) :
    ∃ a : Ω → ℝ, Measurable a ∧ MemLp a 1 μ ∧
      ∀ k : ∀ n : ℕ, Fin (n + 1) → ℕ, (∀ᶠ n in atTop, Function.Injective (k n)) →
        Tendsto
          (fun m => ∫ ω, |blockAverage (fun i ω => f (X i ω)) (k m) ω - a ω| ∂μ)
          atTop (𝓝 0) := by
  let Y : ℕ → Ω → ℝ := fun i ω => f (X i ω)
  have hY : Contractable μ Y := hX.map_values hf hX_ae
  have hY_ae : ∀ i, AEMeasurable (Y i) μ := fun i => hf.comp_aemeasurable (hX_ae i)
  have hY_L2 : ∀ i, MemLp (Y i) 2 μ := fun i =>
    (hY.identDistrib_coord (hY_ae 0) (hY_ae i)).memLp_snd hf_L2
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
  refine ⟨a, ha_meas, ha_L2.mono_exponent one_le_two, fun k hk => ?_⟩
  have hW_L2 : ∀ m : ℕ, MemLp (blockAverage Y (k m)) 2 μ := fun m =>
    memLp_blockAverage (k m) fun j => hY_L2 (k m j)
  let W₂ : ℕ → Lp ℝ 2 μ := fun m => (hW_L2 m).toLp (blockAverage Y (k m))
  -- Every injective selection tracks the same-length prefix, so it shares the prefix limit.
  have hW₂_tendsto : Tendsto W₂ atTop (𝓝 a₂) := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero'
      (Eventually.of_forall fun _ => dist_nonneg) (Eventually.of_forall fun m =>
        dist_triangle _ (A₂ m) _) ?_)
    simpa only [zero_add] using
      (tendsto_dist_blockAverage_moving_prefix_toLp hY hY_L2 hk).add
        (tendsto_iff_dist_tendsto_zero.mp ha₂)
  have hL2 : Tendsto (fun m : ℕ =>
      eLpNorm (blockAverage Y (k m) - a) 2 μ) atTop (𝓝 0) := by
    rw [← Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hW_L2 a ha_L2]
    simpa only [ha_toLp] using hW₂_tendsto
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    TauCeti.MeasureTheory.tendsto_integral_norm_of_tendsto_eLpNorm_two
      (fun m => ((hW_L2 m).sub ha_L2).aestronglyMeasurable) hL2

/-- **Bounded-observable form**, the shape the Layer 3 roadmap names. A uniform bound on `f` gives
square-integrability of the composite on a finite measure space, so this is the direct entry point
for bounded observables. -/
theorem weighted_sums_converge_L1 {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_ae : ∀ i, AEMeasurable (X i) μ)
    {f : α → ℝ} (hf : Measurable f) (hf_bdd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    ∃ a : Ω → ℝ, Measurable a ∧ MemLp a 1 μ ∧
      ∀ k : ∀ n : ℕ, Fin (n + 1) → ℕ, (∀ᶠ n in atTop, Function.Injective (k n)) →
        Tendsto
          (fun m => ∫ ω, |blockAverage (fun i ω => f (X i ω)) (k m) ω - a ω| ∂μ)
          atTop (𝓝 0) :=
  let ⟨C, hC⟩ := hf_bdd
  weighted_sums_converge_L1_of_memLp hX hX_ae hf
    (memLp_comp_of_bound hf (hX_ae 0) C (Filter.Eventually.of_forall fun ω => hC (X 0 ω)) 2)

end Probability

end TauCeti
