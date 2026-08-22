/-
Copyright (c) 2026 Tau Ceti Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.MGFAnalytic

import Mathlib.Data.Nat.Choose.Cast

/-!
# Elementary theory of the geometric distribution

This file develops moments and transforms of Mathlib's geometric measure, using the convention
that the random variable counts failures before the first success.  It also records its cumulative
mass and memoryless tail identity.  Mathlib totalizes the zero-success parameter by
`geometricMeasure 0 = Measure.dirac 0`; the boundary formulas are stated separately.  The
hypothesis `p ≠ 0` used throughout only excludes that totalized boundary: it still admits the
degenerate endpoint `p = 1`, where the law is Dirac at zero and the formulas below specialize to
the constant random variable `0`.

## Main results

* `integral_id_map_cast_geometricMeasure` and `variance_id_map_cast_geometricMeasure` compute the
  mean and variance of the real cast of a nonzero-parameter geometric law.
* `integrableExpSet_id_map_cast_geometricMeasure` and `mgf_id_map_cast_geometricMeasure` give its
  exact moment-generating domain and moment-generating function.
* `charFun_map_cast_geometricMeasure` computes its characteristic function.
* `geometricMeasure_real_Iic` and `geometricMeasure_memoryless` give the cumulative mass and the
  division-free memoryless identity on the native carrier.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed.,
  Wiley, 2005, Chapter 5.
-/

public section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti

namespace Probability

variable {p : unitInterval}

private lemma one_sub_coe_nonneg (p : unitInterval) : 0 ≤ 1 - (p : ℝ) := by grind

private lemma one_sub_coe_lt_one (hp : p ≠ 0) : 1 - (p : ℝ) < 1 := by grind

private lemma abs_one_sub_coe_lt_one (hp : p ≠ 0) : |1 - (p : ℝ)| < 1 := by
  rw [abs_of_nonneg (one_sub_coe_nonneg p)]
  exact one_sub_coe_lt_one hp

private lemma coe_ne_zero (hp : p ≠ 0) : (p : ℝ) ≠ 0 := by grind

private lemma hasSum_sq_mul_geometric {q : ℝ} (hq : |q| < 1) :
    HasSum (fun n : ℕ ↦ (n : ℝ) ^ 2 * q ^ n) (q * (1 + q) / (1 - q) ^ 3) := by
  have hchoose := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hq).mul_left
    (2 * q ^ 2)
  have hchoose' : HasSum (fun n : ℕ ↦ 2 * q ^ 2 * (((n + 2).choose 2 : ℕ) * q ^ n))
      (2 * q ^ 2 / (1 - q) ^ 3) := by
    simpa [div_eq_mul_inv] using hchoose
  have hfallShift :
      HasSum (fun n : ℕ ↦ ((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1) * q ^ (n + 2))
        (2 * q ^ 2 / (1 - q) ^ 3) := by
    refine hchoose'.congr_fun fun n ↦ ?_
    rw [Nat.cast_choose_two, pow_add]
    field_simp
  have hfall : HasSum (fun n : ℕ ↦ (n : ℝ) * ((n : ℝ) - 1) * q ^ n)
      (2 * q ^ 2 / (1 - q) ^ 3) := by
    have h := (hasSum_nat_add_iff
      (f := fun n : ℕ ↦ (n : ℝ) * ((n : ℝ) - 1) * q ^ n) 2).mp hfallShift
    have hsum : ∑ i ∈ Finset.range 2, (i : ℝ) * ((i : ℝ) - 1) * q ^ i = 0 := by
      norm_num [Finset.sum_range_succ]
    simpa only [hsum, add_zero] using h
  have hlinear := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hq
  have hadd := hfall.add hlinear
  have hq1 : 1 - q ≠ 0 := by
    have : q < 1 := (le_abs_self q).trans_lt hq
    linarith
  have hvalue :
      2 * q ^ 2 / (1 - q) ^ 3 + q / (1 - q) ^ 2 =
        q * (1 + q) / (1 - q) ^ 3 := by
    field_simp [hq1]
    ring
  rw [← hvalue]
  refine hadd.congr_fun fun n ↦ ?_
  ring

/-- The exponential integrand for the cast geometric law is integrable exactly below the pole of
its geometric series. -/
theorem integrable_exp_mul_id_map_cast_geometricMeasure_iff (hp : p ≠ 0) (t : ℝ) :
    Integrable (fun x : ℝ ↦ exp (t * x))
        ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) ↔
      (1 - (p : ℝ)) * exp t < 1 := by
  rw [(MeasurableEmbedding.natCast (α := ℝ)).integrable_map_iff,
    integrable_geometricMeasure_iff hp]
  have hexp (n : ℕ) : exp (t * (n : ℝ)) = (exp t) ^ n := by
    rw [mul_comm, Real.exp_nat_mul]
  simp_rw [Function.comp_apply, Real.norm_eq_abs, abs_exp, hexp]
  have hfun : (fun n : ℕ ↦ (1 - (p : ℝ)) ^ n * p * ((exp t) ^ n)) =
      fun n ↦ (p : ℝ) * (((1 - (p : ℝ)) * exp t) ^ n) := by
    funext n
    rw [mul_pow]
    ring
  rw [hfun, summable_mul_left_iff (coe_ne_zero hp), summable_geometric_iff_norm_lt_one,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (one_sub_coe_nonneg p) (exp_nonneg t))]

/-- The exact moment-generating domain of the real cast of a nonzero-parameter geometric law. -/
theorem integrableExpSet_id_map_cast_geometricMeasure (hp : p ≠ 0) :
    integrableExpSet id ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) =
      {t | (1 - (p : ℝ)) * exp t < 1} := by
  ext t
  exact integrable_exp_mul_id_map_cast_geometricMeasure_iff hp t

/-- The moment-generating function of the real cast of a nonzero-parameter geometric law. -/
theorem mgf_id_map_cast_geometricMeasure (hp : p ≠ 0)
    (ht : (1 - (p : ℝ)) * exp t < 1) :
    mgf id ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) t =
      (p : ℝ) / (1 - (1 - (p : ℝ)) * exp t) := by
  rw [mgf_id_map (Measurable.of_discrete.aemeasurable :
    AEMeasurable (Nat.cast : ℕ → ℝ) (geometricMeasure p)), mgf,
    integral_geometricMeasure hp]
  have hexp (n : ℕ) : exp (t * (n : ℝ)) = (exp t) ^ n := by
    rw [mul_comm, Real.exp_nat_mul]
  simp_rw [smul_eq_mul, hexp]
  have hfun : (fun n : ℕ ↦ (1 - (p : ℝ)) ^ n * p * ((exp t) ^ n)) =
      fun n ↦ (p : ℝ) * (((1 - (p : ℝ)) * exp t) ^ n) := by
    funext n
    rw [mul_pow]
    ring
  rw [hfun, tsum_mul_left, tsum_geometric_of_norm_lt_one]
  · simp [div_eq_mul_inv]
  · simpa [Real.norm_eq_abs,
      abs_of_nonneg (one_sub_coe_nonneg p)] using ht

/-- The cumulant-generating function of the real cast of a nonzero-parameter geometric law. -/
theorem cgf_id_map_cast_geometricMeasure (hp : p ≠ 0)
    (ht : (1 - (p : ℝ)) * exp t < 1) :
    cgf id ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) t =
      log ((p : ℝ) / (1 - (1 - (p : ℝ)) * exp t)) := by
  rw [cgf, mgf_id_map_cast_geometricMeasure hp ht]

/-- The mean of the real cast of a nonzero-parameter geometric law. -/
theorem integral_id_map_cast_geometricMeasure (hp : p ≠ 0) :
    ∫ x, x ∂((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) =
      (1 - (p : ℝ)) / (p : ℝ) := by
  rw [integral_map (by fun_prop) (by fun_prop), integral_geometricMeasure hp]
  simp_rw [smul_eq_mul]
  have hfun : (fun n : ℕ ↦ (1 - (p : ℝ)) ^ n * p * (n : ℝ)) =
      fun n : ℕ ↦ (p : ℝ) * ((n : ℝ) * (1 - (p : ℝ)) ^ n) := by
    funext n
    ring
  rw [hfun, tsum_mul_left,
    tsum_coe_mul_geometric_of_norm_lt_one (abs_one_sub_coe_lt_one hp)]
  field_simp [coe_ne_zero hp]
  ring

/-- The second raw moment of the real cast of a nonzero-parameter geometric law. -/
private theorem integral_sq_id_map_cast_geometricMeasure (hp : p ≠ 0) :
    ∫ x, x ^ 2 ∂((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) =
      (1 - (p : ℝ)) * (2 - (p : ℝ)) / (p : ℝ) ^ 2 := by
  rw [integral_map (by fun_prop) (by fun_prop), integral_geometricMeasure hp]
  simp_rw [smul_eq_mul]
  have hfun : (fun n : ℕ ↦ (1 - (p : ℝ)) ^ n * p * ((n : ℝ) ^ 2)) =
      fun n : ℕ ↦ (p : ℝ) * ((n : ℝ) ^ 2 * (1 - (p : ℝ)) ^ n) := by
    funext n
    ring
  rw [hfun, tsum_mul_left,
    (hasSum_sq_mul_geometric (abs_one_sub_coe_lt_one hp)).tsum_eq]
  field_simp [coe_ne_zero hp]
  ring

private theorem integrable_sq_id_map_cast_geometricMeasure (hp : p ≠ 0) :
    Integrable (fun x : ℝ ↦ x ^ 2)
      ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) := by
  rw [(MeasurableEmbedding.natCast (α := ℝ)).integrable_map_iff,
    integrable_geometricMeasure_iff hp]
  simp only [Function.comp_apply]
  have hs := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
    (abs_one_sub_coe_lt_one hp)
  have hfun : (fun n : ℕ ↦ (1 - (p : ℝ)) ^ n * p * ‖((n : ℕ) : ℝ) ^ 2‖) =
      fun n : ℕ ↦ (p : ℝ) * ((n : ℝ) ^ 2 * (1 - (p : ℝ)) ^ n) := by
    funext n
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (n : ℝ))]
    ring
  rw [hfun]
  exact hs.mul_left (p : ℝ)

/-- The variance of the real cast of a nonzero-parameter geometric law. -/
theorem variance_id_map_cast_geometricMeasure (hp : p ≠ 0) :
    variance id ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) =
      (1 - (p : ℝ)) / (p : ℝ) ^ 2 := by
  let _ : IsProbabilityMeasure ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hmem : MemLp id 2 ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      (integrable_sq_id_map_cast_geometricMeasure hp)
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_sq_id_map_cast_geometricMeasure hp, integral_id_map_cast_geometricMeasure hp]
  field_simp [coe_ne_zero hp]
  ring

/-- The characteristic function of the real cast of a nonzero-parameter geometric law. -/
theorem charFun_map_cast_geometricMeasure (hp : p ≠ 0) (t : ℝ) :
    charFun ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) t =
      (p : ℂ) / (1 - (1 - (p : ℂ)) * Complex.exp (Complex.I * t)) := by
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop), integral_geometricMeasure hp]
  have hexp (n : ℕ) : Complex.exp (((t : ℂ) * ((n : ℝ) : ℂ)) * Complex.I) =
      Complex.exp (Complex.I * t) ^ n := by
    have hmul : ((t : ℂ) * ((n : ℝ) : ℂ)) * Complex.I = n * (Complex.I * t) := by
      push_cast
      ring
    rw [hmul, Complex.exp_nat_mul]
  have hfun : (fun n : ℕ ↦ ((1 - (p : ℝ)) ^ n * p : ℝ) •
      Complex.exp ((t : ℂ) * ((n : ℝ) : ℂ) * Complex.I)) =
      fun n ↦ (p : ℂ) * (((1 - (p : ℂ)) * Complex.exp (Complex.I * t)) ^ n) := by
    funext n
    rw [hexp n, mul_pow, Complex.real_smul]
    push_cast
    ring
  rw [hfun, tsum_mul_left, tsum_geometric_of_norm_lt_one]
  · simp [div_eq_mul_inv]
  · have hnorm : ‖1 - (p : ℂ)‖ = |1 - (p : ℝ)| := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [norm_mul, hnorm, Complex.norm_exp]
    simpa [Complex.mul_re, abs_of_nonneg (one_sub_coe_nonneg p)] using one_sub_coe_lt_one hp

/-- The cumulative mass of a nonzero-parameter geometric law on its native carrier. -/
theorem geometricMeasure_real_Iic (hp : p ≠ 0) (n : ℕ) :
    (geometricMeasure p).real {k | k ≤ n} = 1 - (1 - (p : ℝ)) ^ (n + 1) := by
  have hset : {k : ℕ | k ≤ n} = (Finset.Iic n : Set ℕ) := by ext k; simp
  rw [hset, ← sum_measureReal_singleton]
  simp_rw [geometricMeasure_real_singleton hp]
  have hIic : Finset.Iic n = Finset.range (n + 1) := by ext k; simp
  rw [hIic, ← Finset.sum_mul]
  have h := geom_sum_mul_of_le_one (sub_le_self 1 p.2.1) (n + 1)
  convert h using 1
  ring

/-- The upper-tail mass of a nonzero-parameter geometric law on its native carrier. -/
theorem geometricMeasure_real_Ici (hp : p ≠ 0) (n : ℕ) :
    (geometricMeasure p).real {k | n ≤ k} = (1 - (p : ℝ)) ^ n := by
  have hcompl : {k : ℕ | n ≤ k} = {k : ℕ | k < n}ᶜ := by ext k; simp
  rw [hcompl, probReal_compl_eq_one_sub (MeasurableSet.of_discrete :
    MeasurableSet {k : ℕ | k < n})]
  have hset : {k : ℕ | k < n} = (Finset.range n : Set ℕ) := by ext k; simp
  rw [hset, ← sum_measureReal_singleton]
  simp_rw [geometricMeasure_real_singleton hp]
  rw [← Finset.sum_mul]
  calc
    1 - (∑ i ∈ Finset.range n, (1 - (p : ℝ)) ^ i) * (p : ℝ) =
        1 - (∑ i ∈ Finset.range n, (1 - (p : ℝ)) ^ i) *
          (1 - (1 - (p : ℝ))) := by ring
    _ = (1 - (p : ℝ)) ^ n := by
      rw [geom_sum_mul_of_le_one (sub_le_self 1 p.2.1)]
      ring

/-- The geometric law is memoryless for every parameter: the mass of the tail beyond `n + m`
is the product of the masses of the tails beyond `n` and beyond `m`. -/
theorem geometricMeasure_memoryless (p : unitInterval) (n m : ℕ) :
    (geometricMeasure p).real {k | n + m ≤ k} =
      (geometricMeasure p).real {k | n ≤ k} * (geometricMeasure p).real {k | m ≤ k} := by
  by_cases hp : p = 0
  · subst p
    rcases n with _ | n <;> rcases m with _ | m <;>
      simp [geometricMeasure, measureReal_def]
  · rw [geometricMeasure_real_Ici hp, geometricMeasure_real_Ici hp,
      geometricMeasure_real_Ici hp, pow_add]

/-- Conditional form of geometric memorylessness, stated only when the conditioning tail has
nonzero mass. -/
theorem geometricMeasure_cond_Ici (p : unitInterval) (n m : ℕ)
    (hn : geometricMeasure p {k | n ≤ k} ≠ 0) :
    (ProbabilityTheory.cond (geometricMeasure p) {k | n ≤ k}).real {k | n + m ≤ k} =
      (geometricMeasure p).real {k | m ≤ k} := by
  by_cases hp : p = 0
  · subst p
    rcases n with _ | n
    · simp [geometricMeasure]
    · simp [geometricMeasure] at hn
  · rw [measureReal_def,
      cond_apply (MeasurableSet.of_discrete : MeasurableSet {k : ℕ | n ≤ k}),
      ENNReal.toReal_mul, ENNReal.toReal_inv]
    have hinter : {k : ℕ | n ≤ k} ∩ {k | n + m ≤ k} = {k | n + m ≤ k} := by
      ext k
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      omega
    rw [hinter, ← measureReal_def, ← measureReal_def, geometricMeasure_real_Ici hp,
      geometricMeasure_real_Ici hp, geometricMeasure_real_Ici hp, pow_add]
    have hn' : (1 - (p : ℝ)) ^ n ≠ 0 := by
      rw [← geometricMeasure_real_Ici hp]
      exact (measureReal_ne_zero_iff (μ := geometricMeasure p) (s := {k | n ≤ k})).2 hn
    field_simp

/-- At success probability zero, Mathlib's totalized geometric law is Dirac at zero. -/
theorem geometricMeasure_zero : geometricMeasure (0 : unitInterval) = Measure.dirac 0 := by
  simp [geometricMeasure]

/-- The real cast of the zero-parameter geometric law has every exponential moment. -/
theorem integrableExpSet_id_map_cast_geometricMeasure_zero :
    integrableExpSet id
      ((geometricMeasure (0 : unitInterval)).map (Nat.cast : ℕ → ℝ)) = Set.univ := by
  rw [geometricMeasure_zero, Measure.map_dirac' (by fun_prop)]
  norm_num
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact integrable_dirac (by simp)

/-- The moment-generating function at the zero parameter is identically one. -/
theorem mgf_id_map_cast_geometricMeasure_zero (t : ℝ) :
    mgf id ((geometricMeasure (0 : unitInterval)).map (Nat.cast : ℕ → ℝ)) t = 1 := by
  rw [geometricMeasure_zero, Measure.map_dirac' (by fun_prop)]
  norm_num
  rw [mgf_dirac']
  simp

/-- The cumulant-generating function at the zero parameter is identically zero. -/
theorem cgf_id_map_cast_geometricMeasure_zero (t : ℝ) :
    cgf id ((geometricMeasure (0 : unitInterval)).map (Nat.cast : ℕ → ℝ)) t = 0 := by
  rw [cgf, mgf_id_map_cast_geometricMeasure_zero]
  simp

/-- The zero-parameter geometric law has mean zero after casting to the reals. -/
theorem integral_id_map_cast_geometricMeasure_zero :
    ∫ x, x ∂((geometricMeasure (0 : unitInterval)).map (Nat.cast : ℕ → ℝ)) = 0 := by
  rw [geometricMeasure_zero, Measure.map_dirac' (by fun_prop)]
  norm_num

/-- The zero-parameter geometric law has variance zero after casting to the reals. -/
theorem variance_id_map_cast_geometricMeasure_zero :
    variance id ((geometricMeasure (0 : unitInterval)).map (Nat.cast : ℕ → ℝ)) = 0 := by
  rw [geometricMeasure_zero, Measure.map_dirac' (by fun_prop)]
  norm_num

/-- The characteristic function at the zero parameter is identically one. -/
theorem charFun_map_cast_geometricMeasure_zero (t : ℝ) :
    charFun ((geometricMeasure (0 : unitInterval)).map (Nat.cast : ℕ → ℝ)) t = 1 := by
  rw [geometricMeasure_zero, Measure.map_dirac' (by fun_prop)]
  norm_num

/-- The cumulative mass of the zero-parameter geometric law is one at every natural cutoff. -/
theorem geometricMeasure_real_Iic_zero (n : ℕ) :
    (geometricMeasure (0 : unitInterval)).real {k | k ≤ n} = 1 := by
  rw [geometricMeasure_zero]
  rw [measureReal_def, Measure.dirac_apply_of_mem (by simp)]
  simp

/-- A real random variable with a nonzero-parameter geometric law has mean `(1 - p) / p`. -/
theorem integral_of_hasLaw_map_cast_geometricMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hp : p ≠ 0)
    (hX : HasLaw X ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) P) :
    P[X] = (1 - (p : ℝ)) / (p : ℝ) := by
  rw [hX.integral_eq, integral_id_map_cast_geometricMeasure hp]

/-- A real random variable with a nonzero-parameter geometric law has variance `(1 - p) / p²`. -/
theorem variance_of_hasLaw_map_cast_geometricMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hp : p ≠ 0)
    (hX : HasLaw X ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) P) :
    variance X P = (1 - (p : ℝ)) / (p : ℝ) ^ 2 := by
  rw [hX.variance_eq, variance_id_map_cast_geometricMeasure hp]

end Probability

end TauCeti
