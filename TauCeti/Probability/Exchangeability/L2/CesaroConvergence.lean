/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Exchangeability.L2.BlockAverages
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Work in progress
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

private theorem injective_of_fin_one {β : Type*} (g : Fin 1 → β) : Function.Injective g :=
  fun a b _ => Subsingleton.elim a b

/-- The variance gap is nonnegative: the singleton disjoint-window identity evaluates
`∫ (X 0 - X 1) ^ 2` as `2 * varGap`, and an integral of a square is nonnegative. -/
private theorem varGap_nonneg [IsFiniteMeasure μ] (hX : Contractable μ X)
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) : 0 ≤ varGap μ X := by
  have h := hX.integral_sq_blockAverage_sub_of_disjoint hX_L2 (n := 1) (m := 1)
    one_pos one_pos (k := fun _ : Fin 1 => 0) (k' := fun _ : Fin 1 => 1)
    (injective_of_fin_one _) (injective_of_fin_one _) (by simp)
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

end Probability

end TauCeti
