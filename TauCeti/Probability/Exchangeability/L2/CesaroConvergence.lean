/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Exchangeability.L2.BlockAverages
import TauCeti.Probability.Exchangeability.Map
import TauCeti.MeasureTheory.Function.BoundedMemLp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# L¹ convergence of moving Cesàro averages

For a contractable process and a bounded measurable observable, the Cesàro averages converge in
`L¹` to a **single** limit — the same one for every starting index.

## Main results

* `Contractable.exists_cesaro_limit_L1` — the generic form, for a contractable real sequence with
  square-integrable coordinates. The limit is returned in `L²`, which is what the construction
  produces.
* `weighted_sums_converge_L1` — the roadmap-named bounded-observable corollary, on an arbitrary
  measurable state space, with the limit weakened to `L¹`.

Despite the roadmap name, the sums here are unweighted: they are the moving Cesàro averages
`(1/m) ∑_{i<m} f (X (n + i))`.

## Implementation

The whole argument runs off one landed estimate. `integral_sq_blockAverage_sub_of_disjoint` gives
an **equality**, not a bound: for non-overlapping windows,
`∫ (A - A') ^ 2 = varGap / m₁ + varGap / m₂`, where `varGap = Var[X 0] - cov[X 0, X 1]`. Read
through `Lp.dist_def`, that is the `L²` distance between the bundled averages.

Two arbitrary windows may overlap, so they are compared against a third window that is *longer than
both* (length `max m₁ m₂`) and *starts beyond both*. Disjointness is then automatic and the remote
window's own contribution is dominated by the other two terms, giving

`dist A₁ A₂ ≤ √(2 * varGap / m₁) + √(2 * varGap / m₂)`

with no limit taken. That single bound supplies both the Cauchy property and — applied with equal
window lengths — the fact that every fixed-start sequence stays close to the zero-start one, hence
shares its limit.

The descent from `L²` to `L¹` converts the exponent comparison into a real-valued estimate once,
`∫ ‖g‖ ≤ lpNorm g 2 μ * K` with `K` a fixed constant, so that no convergence argument takes place
in `ℝ≥0∞`.

`varGap` is nonnegative: the singleton case of the same disjoint-window identity evaluates
`∫ (X 0 - X 1) ^ 2` as `2 * varGap`.

This advances `TauCetiRoadmap/Exchangeability/README.md`, **Layer 3** — the *L¹ convergence of
weighted block averages* bullet. The determining-class and directing-measure steps that follow it
there are not addressed here.

## Sources

The mathematical target is taken from `cameronfreer/exchangeability`
(`Exchangeability/DeFinetti/ViaL2/MainConvergence.lean`), which states it for a real-valued process
carrying an explicit `L²` hypothesis. The proof here is not a port of that argument: it replaces the
source's three-segment overlap analysis with the remote-window comparison above, which TauCeti's
arbitrary-disjoint-window identity makes available and which needs no overlap algebra. The
real-valuedness is moved from the process onto the observable, and the `L²` hypothesis is dropped,
since boundedness supplies it.
-/
public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The moving average of `X` over the `m` coordinates starting at `n`. -/
private def movingAverage (X : ℕ → Ω → ℝ) (n m : ℕ) : Ω → ℝ :=
  blockAverage X fun i : Fin m => n + i

omit [MeasurableSpace Ω] in
private theorem movingAverage_apply (n m : ℕ) (ω : Ω) :
    movingAverage X n m ω = (m : ℝ)⁻¹ * ∑ i : Fin m, X (n + i) ω := by
  simp [movingAverage]

private theorem injective_movingIndex (n m : ℕ) :
    Function.Injective fun i : Fin m => n + i.val := by
  intro i j hij
  exact Fin.ext (Nat.add_left_cancel hij)

/-- Two moving windows that do not overlap have disjoint index sets. -/
private theorem movingIndex_disjoint {n₁ m₁ n₂ m₂ : ℕ} (h : n₁ + m₁ ≤ n₂) :
    ∀ (i : Fin m₁) (j : Fin m₂), n₁ + i.val ≠ n₂ + j.val := by
  intro i j hij
  omega

private theorem memLp_movingAverage (hX_L2 : ∀ i, MemLp (X i) 2 μ) (n m : ℕ) :
    MemLp (movingAverage X n m) 2 μ :=
  memLp_blockAverage _ fun _ => hX_L2 _

/-- The variance gap `Var[X 0] - cov[X 0, X 1]` controlling every disjoint-window comparison. -/
private def varGap (μ : Measure Ω) (X : ℕ → Ω → ℝ) : ℝ := Var[X 0; μ] - cov[X 0, X 1; μ]

/-- The variance gap is nonnegative: the singleton disjoint-window identity evaluates
`∫ (X 0 - X 1) ^ 2` as `2 * varGap`, and an integral of a square is nonnegative. -/
private theorem varGap_nonneg [IsFiniteMeasure μ] (hX : Contractable μ X)
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) : 0 ≤ varGap μ X := by
  have h := hX.integral_sq_blockAverage_sub_of_disjoint hX_L2 (n := 1) (m := 1)
    one_pos one_pos (k := fun _ : Fin 1 => 0) (k' := fun _ : Fin 1 => 1)
    (Function.injective_of_subsingleton _) (Function.injective_of_subsingleton _) (by simp)
  have hnn : (0 : ℝ) ≤ ∫ ω, (blockAverage X (fun _ : Fin 1 => 0) ω
      - blockAverage X (fun _ : Fin 1 => 1) ω) ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  rw [h] at hnn
  simp only [Nat.cast_one, div_one, varGap] at hnn ⊢
  linarith

/-- **The L² distance between two non-overlapping moving averages.** The landed disjoint-window
identity evaluates `∫ (A - A') ^ 2` exactly, so the distance is the square root of
`varGap / m₁ + varGap / m₂`. -/
private theorem dist_toLp_movingAverage_of_le [IsFiniteMeasure μ]
    (hX : Contractable μ X) (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    {n₁ m₁ n₂ m₂ : ℕ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hsep : n₁ + m₁ ≤ n₂) :
    dist ((memLp_movingAverage hX_L2 n₁ m₁).toLp _)
        ((memLp_movingAverage hX_L2 n₂ m₂).toLp _)
      = Real.sqrt (varGap μ X / m₁ + varGap μ X / m₂) := by
  have hid := hX.integral_sq_blockAverage_sub_of_disjoint hX_L2 hm₁ hm₂
    (injective_movingIndex n₁ m₁) (injective_movingIndex n₂ m₂) (movingIndex_disjoint hsep)
  have hsub : MemLp (movingAverage X n₁ m₁ - movingAverage X n₂ m₂) 2 μ :=
    (memLp_movingAverage hX_L2 n₁ m₁).sub (memLp_movingAverage hX_L2 n₂ m₂)
  rw [dist_edist, Lp.edist_toLp_toLp, toReal_eLpNorm hsub.1,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hsub.1,
    Real.sqrt_eq_rpow]
  congr 1
  · simp only [varGap]
    rw [← hid]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have h2 : ENNReal.toReal 2 = ((2 : ℕ) : ℝ) := by norm_num
    simp only [Pi.sub_apply, movingAverage, Real.norm_eq_abs, h2, Real.rpow_natCast, sq_abs]
  · norm_num


/-- **The remote-block estimate.** Comparing two arbitrary moving averages against a third window
that is longer than both and starts beyond both removes any overlap, giving a bound depending only
on the two lengths. No limit is taken: the remote window has length `max m₁ m₂`, so its
contribution is absorbed into the other two terms. -/
private theorem dist_toLp_movingAverage_le [IsFiniteMeasure μ]
    (hX : Contractable μ X) (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    {n₁ m₁ n₂ m₂ : ℕ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    dist ((memLp_movingAverage hX_L2 n₁ m₁).toLp _)
        ((memLp_movingAverage hX_L2 n₂ m₂).toLp _)
      ≤ Real.sqrt (2 * varGap μ X / m₁) + Real.sqrt (2 * varGap μ X / m₂) := by
  have hC : 0 ≤ varGap μ X := varGap_nonneg hX hX_L2
  set p := max m₁ m₂ with hp_def
  set r := max (n₁ + m₁) (n₂ + m₂) with hr_def
  have hp : 0 < p := lt_of_lt_of_le hm₁ (le_max_left _ _)
  have e1 := dist_toLp_movingAverage_of_le hX hX_L2 (n₁ := n₁) (m₁ := m₁) (n₂ := r) (m₂ := p)
    hm₁ hp (le_max_left _ _)
  have e2 := dist_toLp_movingAverage_of_le hX hX_L2 (n₁ := n₂) (m₁ := m₂) (n₂ := r) (m₂ := p)
    hm₂ hp (le_max_right _ _)
  have habs : ∀ {a : ℕ}, 0 < a → a ≤ p →
      varGap μ X / a + varGap μ X / p ≤ 2 * varGap μ X / a := by
    intro a ha hap
    have h1 : varGap μ X / p ≤ varGap μ X / a :=
      div_le_div_of_nonneg_left hC (by exact_mod_cast ha) (by exact_mod_cast hap)
    have : (2 : ℝ) * varGap μ X / a = varGap μ X / a + varGap μ X / a := by ring
    linarith
  calc dist ((memLp_movingAverage hX_L2 n₁ m₁).toLp _)
        ((memLp_movingAverage hX_L2 n₂ m₂).toLp _)
      ≤ dist ((memLp_movingAverage hX_L2 n₁ m₁).toLp _)
            ((memLp_movingAverage hX_L2 r p).toLp _)
          + dist ((memLp_movingAverage hX_L2 r p).toLp _)
            ((memLp_movingAverage hX_L2 n₂ m₂).toLp _) := dist_triangle _ _ _
    _ = Real.sqrt (varGap μ X / m₁ + varGap μ X / p)
          + Real.sqrt (varGap μ X / m₂ + varGap μ X / p) := by
        rw [e1, dist_comm, e2]
    _ ≤ Real.sqrt (2 * varGap μ X / m₁) + Real.sqrt (2 * varGap μ X / m₂) :=
        add_le_add (Real.sqrt_le_sqrt (habs hm₁ (le_max_left _ _)))
          (Real.sqrt_le_sqrt (habs hm₂ (le_max_right _ _)))

/-- The remote-block bound tends to zero along the window length. -/
private theorem tendsto_sqrt_varGap [IsFiniteMeasure μ] :
    Tendsto (fun m : ℕ => Real.sqrt (2 * varGap μ X / (m + 1))) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun m : ℕ => 2 * varGap μ X / ((m : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (2 * varGap μ X)).comp
      (tendsto_add_atTop_nat 1)
    refine h.congr fun m => ?_
    simp only [Function.comp_def]
    push_cast
    ring
  simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hdiv

/-- The bundled moving averages, indexed so the window length is positive. -/
private def movingAverageLp [IsFiniteMeasure μ] (hX_L2 : ∀ i, MemLp (X i) 2 μ) (n m : ℕ) :
    Lp ℝ 2 μ :=
  (memLp_movingAverage hX_L2 n (m + 1)).toLp _

/-- **Cauchy.** The remote-block bound makes every fixed-start sequence of moving averages Cauchy
in `L²`, uniformly in the starting index. -/
private theorem cauchySeq_movingAverageLp [IsFiniteMeasure μ]
    (hX : Contractable μ X) (hX_L2 : ∀ i, MemLp (X i) 2 μ) (n : ℕ) :
    CauchySeq (movingAverageLp hX_L2 n) := by
  refine Metric.cauchySeq_iff.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (tendsto_sqrt_varGap (X := X) (μ := μ))) (ε / 2)
    (by linarith)
  refine ⟨N, fun a ha b hb => ?_⟩
  have hbound := dist_toLp_movingAverage_le hX hX_L2 (n₁ := n) (m₁ := a + 1) (n₂ := n)
    (m₂ := b + 1) a.succ_pos b.succ_pos
  have ha' := hN a ha
  have hb' := hN b hb
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Real.sqrt_nonneg _)] at ha' hb'
  calc dist (movingAverageLp hX_L2 n a) (movingAverageLp hX_L2 n b)
      ≤ Real.sqrt (2 * varGap μ X / (a + 1)) + Real.sqrt (2 * varGap μ X / (b + 1)) := by
        simpa [movingAverageLp] using hbound
    _ < ε := by linarith

/-- **The common L² limit.** Completeness supplies a limit for the zero-start averages, and the
remote-block bound with equal window lengths shows every fixed-start sequence stays within
`2√(2C/m)` of it, hence converges to the same limit. -/
private theorem exists_tendsto_movingAverageLp [IsFiniteMeasure μ]
    (hX : Contractable μ X) (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∃ g : Lp ℝ 2 μ, ∀ n : ℕ, Tendsto (movingAverageLp hX_L2 n) atTop (𝓝 g) := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete (cauchySeq_movingAverageLp hX hX_L2 0)
  refine ⟨g, fun n => ?_⟩
  have hsum : Tendsto (fun m : ℕ => Real.sqrt (2 * varGap μ X / (m + 1))
      + Real.sqrt (2 * varGap μ X / (m + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_sqrt_varGap (X := X) (μ := μ)).add (tendsto_sqrt_varGap (X := X) (μ := μ))
  have hclose : Tendsto (fun m => dist (movingAverageLp hX_L2 n m) (movingAverageLp hX_L2 0 m))
      atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => dist_nonneg) (fun m => ?_) hsum
    simpa [movingAverageLp] using dist_toLp_movingAverage_le hX hX_L2 (n₁ := n) (m₁ := m + 1)
      (n₂ := 0) (m₂ := m + 1) m.succ_pos m.succ_pos
  rw [tendsto_iff_dist_tendsto_zero] at hg ⊢
  refine squeeze_zero (fun _ => dist_nonneg)
    (fun m => dist_triangle _ (movingAverageLp hX_L2 0 m) _) ?_
  simpa using hclose.add hg

/-- **The L² → L¹ descent, as a real estimate.** On a finite measure space the exponent comparison
is a single fixed constant, converted out of `ℝ≥0∞` once so that no convergence argument has to
happen there. -/
private theorem integral_norm_le_lpNorm_two [IsFiniteMeasure μ] {g : Ω → ℝ} (hg : MemLp g 2 μ) :
    ∫ ω, ‖g ω‖ ∂μ ≤ lpNorm g 2 μ * (μ Set.univ ^ (2 : ℝ)⁻¹).toReal := by
  have hle : eLpNorm g 1 μ ≤ eLpNorm g 2 μ * μ Set.univ ^ (2 : ℝ)⁻¹ := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hg.1
    simpa [show ((1 : ℝ) - 2⁻¹) = 2⁻¹ by norm_num] using h
  have hfin : eLpNorm g 2 μ * μ Set.univ ^ (2 : ℝ)⁻¹ ≠ ⊤ := by
    have : eLpNorm g 2 μ ≠ ⊤ := hg.2.ne
    finiteness
  have h1 : ∫ ω, ‖g ω‖ ∂μ = (eLpNorm g 1 μ).toReal :=
    ((toReal_eLpNorm hg.1).trans (lpNorm_one_eq_integral_norm hg.1)).symm
  rw [h1]
  refine (ENNReal.toReal_mono hfin hle).trans_eq ?_
  rw [ENNReal.toReal_mul, toReal_eLpNorm hg.1]


/-- **L¹ convergence of Cesàro averages, generic form.** For a contractable `L²` sequence there is a
single limit `g`, independent of the starting index, to which every moving average converges in
`L¹`. -/
theorem Contractable.exists_cesaro_limit_L1 [IsFiniteMeasure μ]
    (hX : Contractable μ X) (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∃ g : Ω → ℝ, MemLp g 2 μ ∧ ∀ n : ℕ,
      Tendsto (fun m : ℕ => ∫ ω, |(m : ℝ)⁻¹ * ∑ i : Fin m, X (n + i) ω - g ω| ∂μ)
        atTop (𝓝 0) := by
  obtain ⟨g, hg⟩ := exists_tendsto_movingAverageLp hX hX_L2
  have hgL2 : MemLp (⇑g) 2 μ := Lp.memLp g
  refine ⟨⇑g, hgL2, fun n => ?_⟩
  set K : ℝ := (μ Set.univ ^ (2 : ℝ)⁻¹).toReal with hK
  have hdist : Tendsto (fun m : ℕ => dist (movingAverageLp hX_L2 n m) g) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.1 (hg n)
  have hbound : ∀ m : ℕ,
      ∫ ω, |movingAverage X n (m + 1) ω - g ω| ∂μ
        ≤ dist (movingAverageLp hX_L2 n m) g * K := by
    intro m
    have hsub : MemLp (movingAverage X n (m + 1) - ⇑g) 2 μ :=
      (memLp_movingAverage hX_L2 n (m + 1)).sub hgL2
    have h1 := integral_norm_le_lpNorm_two hsub
    have h2 : dist (movingAverageLp hX_L2 n m) g = lpNorm (movingAverage X n (m + 1) - ⇑g) 2 μ := by
      simp only [movingAverageLp]
      rw [Lp.dist_def,
        eLpNorm_congr_ae ((MemLp.coeFn_toLp _).sub (Filter.EventuallyEq.refl _ (⇑g))),
        toReal_eLpNorm hsub.1]
    rw [h2]
    refine le_trans (le_of_eq ?_) h1
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (Real.norm_eq_abs _).symm)
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  refine squeeze_zero (g := fun m : ℕ => dist (movingAverageLp hX_L2 n m) g * K)
    (fun _ => integral_nonneg fun _ => abs_nonneg _) (fun m => ?_) ?_
  · simpa only [movingAverage_apply] using hbound m
  · simpa using hdist.mul_const K

/-- **L¹ convergence of weighted block averages.** For a contractable process on an arbitrary
measurable state space and a bounded measurable observable `f`, the Cesàro averages of
`f ∘ X` converge in `L¹` to a single limit, the same one for every starting index.

Neither the process nor its coordinates need be real-valued or square-integrable: boundedness of
`f` supplies `MemLp (f ∘ X i) 2 μ` on a finite measure space. -/
theorem weighted_sums_converge_L1 {α : Type*} [MeasurableSpace α] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → α} (hY : Contractable μ Y) (hY_meas : ∀ i, AEMeasurable (Y i) μ)
    {f : α → ℝ} (hf : Measurable f) (C : ℝ) (hbdd : ∀ i, ∀ᵐ ω ∂μ, |f (Y i ω)| ≤ C) :
    ∃ g : Ω → ℝ, MemLp g 1 μ ∧ ∀ n : ℕ,
      Tendsto (fun m : ℕ => ∫ ω, |(m : ℝ)⁻¹ * ∑ i : Fin m, f (Y (n + i) ω) - g ω| ∂μ)
        atTop (𝓝 0) :=
  let ⟨g, hg2, hlim⟩ := (hY.map_values hf hY_meas).exists_cesaro_limit_L1 fun i =>
    memLp_comp_of_bound hf (hY_meas i) C (by simpa only [Real.norm_eq_abs] using hbdd i) 2
  ⟨g, hg2.mono_exponent (by norm_num), hlim⟩

end Probability

end TauCeti
