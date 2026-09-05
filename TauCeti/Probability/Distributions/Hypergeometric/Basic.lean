/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Variance

/-!
# The hypergeometric distribution

The hypergeometric law describes the number of marked objects in a sample of size `n`, drawn
without replacement from a population of size `N` containing `K` marked objects.  For
`K ≤ N` and `n ≤ N`, its mass at `k` is

```text
  choose K k * choose (N - K) (n - k) / choose N n.
```

This file defines the law as a finite weighted sum of Dirac measures, proves its normalization
from Vandermonde's identity, and provides its mass, support, cumulative-mass, finite-integral,
mean, variance, and transform APIs. Outside the classical parameter range the measure is zero,
as required by the standard-distributions roadmap.

## Main definitions and results

* `TauCeti.Probability.hypergeometricWeight`: the `ℝ≥0∞`-valued mass function.
* `TauCeti.Probability.hypergeometricMeasure`: the totalized hypergeometric measure on `ℕ`.
* `TauCeti.Probability.measurable_hypergeometricMeasure`: measurability in all three parameters.
* `TauCeti.Probability.isProbabilityMeasure_hypergeometricMeasure`: normalization in the valid
  parameter range.
* `TauCeti.Probability.hypergeometricMeasure_singleton`: the exact singleton mass.
* `TauCeti.Probability.hypergeometricWeight_ne_zero_iff`: the exact support.
* `TauCeti.Probability.hypergeometricMeasure_real_Iic`: the native cumulative mass.
* `TauCeti.Probability.integral_hypergeometricMeasure`: integration as a finite weighted sum.
* `TauCeti.Probability.integral_id_map_cast_hypergeometricMeasure`: the mean of the real cast law.
* `TauCeti.Probability.variance_id_map_cast_hypergeometricMeasure`: its variance when `1 < N`,
  with separate zero-variance results for populations of size zero and one.
* `TauCeti.Probability.mgf_id_map_cast_hypergeometricMeasure` and
  `TauCeti.Probability.charFun_map_cast_hypergeometricMeasure`: the finite transform formulas for
  the real-valued cast law.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
* `TauCetiRoadmap/StandardDistributions/README.md`, Layer 3, "Hypergeometric".
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

/-- The mass assigned to `k` by the hypergeometric parameters `(N, K, n)`.

The explicit `k ≤ n` branch is necessary because natural subtraction is totalized: without it,
the displayed quotient would generally not vanish when `n < k`. -/
def hypergeometricWeight (N K n k : ℕ) : ℝ≥0∞ :=
  if k ≤ n then
    (K.choose k : ℝ≥0∞) * ((N - K).choose (n - k) : ℝ≥0∞) / (N.choose n : ℝ≥0∞)
  else 0

/-- The hypergeometric weight agrees with its defining ratio when `k ≤ n`. -/
@[simp]
theorem hypergeometricWeight_of_le {N K n k : ℕ} (hkn : k ≤ n) :
    hypergeometricWeight N K n k =
      (K.choose k : ℝ≥0∞) * ((N - K).choose (n - k) : ℝ≥0∞) / (N.choose n : ℝ≥0∞) := by
  simp [hypergeometricWeight, hkn]

/-- The hypergeometric weight vanishes when `n < k`. -/
@[simp]
theorem hypergeometricWeight_of_not_le {N K n k : ℕ} (hkn : ¬ k ≤ n) :
    hypergeometricWeight N K n k = 0 := by
  simp [hypergeometricWeight, hkn]

/-- The hypergeometric measure with population size `N`, marked count `K`, and sample size `n`.

It is the classical probability measure when `K ≤ N` and `n ≤ N`, and is the zero measure
otherwise. -/
def hypergeometricMeasure (N K n : ℕ) : Measure ℕ :=
  if K ≤ N ∧ n ≤ N then
    ∑ k ∈ Finset.range (n + 1), hypergeometricWeight N K n k • Measure.dirac k
  else 0

/-- The hypergeometric law depends measurably on its three natural-valued parameters. -/
theorem measurable_hypergeometricMeasure :
    Measurable fun p : ℕ × ℕ × ℕ ↦ hypergeometricMeasure p.1 p.2.1 p.2.2 :=
  Measurable.of_discrete

/-- Outside the valid parameter range, the hypergeometric measure is zero. -/
@[simp]
theorem hypergeometricMeasure_eq_zero_of_invalid {N K n : ℕ} (h : ¬ (K ≤ N ∧ n ≤ N)) :
    hypergeometricMeasure N K n = 0 := by
  simp [hypergeometricMeasure, h]

/-- In the valid parameter range, the hypergeometric measure is its defining finite sum. -/
theorem hypergeometricMeasure_eq_sum_dirac {N K n : ℕ} (hK : K ≤ N) (hn : n ≤ N) :
    hypergeometricMeasure N K n =
      ∑ k ∈ Finset.range (n + 1), hypergeometricWeight N K n k • Measure.dirac k := by
  simp [hypergeometricMeasure, hK, hn]

private theorem sum_choose_mul_choose {N K n : ℕ} (hK : K ≤ N) :
    ∑ k ∈ Finset.range (n + 1), K.choose k * (N - K).choose (n - k) = N.choose n := by
  calc
    _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        K.choose ij.1 * (N - K).choose ij.2 := by
      symm
      simpa using Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
        (fun ij ↦ K.choose ij.1 * (N - K).choose ij.2) n
    _ = (K + (N - K)).choose n := (Nat.add_choose_eq K (N - K) n).symm
    _ = N.choose n := by rw [Nat.add_sub_of_le hK]

/-- The hypergeometric weights sum to one in the valid parameter range. -/
theorem sum_hypergeometricWeight (hK : K ≤ N) (hn : n ≤ N) :
    ∑ k ∈ Finset.range (n + 1), hypergeometricWeight N K n k = 1 := by
  calc
    _ = ∑ k ∈ Finset.range (n + 1),
        (K.choose k : ℝ≥0∞) * ((N - K).choose (n - k) : ℝ≥0∞) /
          (N.choose n : ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [hypergeometricWeight, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)]
    _ = (∑ k ∈ Finset.range (n + 1),
        (K.choose k : ℝ≥0∞) * ((N - K).choose (n - k) : ℝ≥0∞)) /
          (N.choose n : ℝ≥0∞) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = 1 := by
      have hsum :
          ∑ k ∈ Finset.range (n + 1),
              (K.choose k : ℝ≥0∞) * ((N - K).choose (n - k) : ℝ≥0∞) =
            (N.choose n : ℝ≥0∞) := by
        exact_mod_cast sum_choose_mul_choose (N := N) (K := K) (n := n) hK
      rw [hsum]
      apply ENNReal.div_self
      · exact_mod_cast Nat.choose_ne_zero hn
      · exact ne_of_lt (ENNReal.natCast_lt_top _)

/-- The hypergeometric law is a probability measure in the classical parameter range. -/
theorem isProbabilityMeasure_hypergeometricMeasure (hK : K ≤ N) (hn : n ≤ N) :
    IsProbabilityMeasure (hypergeometricMeasure N K n) := by
  rw [isProbabilityMeasure_iff, hypergeometricMeasure_eq_sum_dirac hK hn]
  simpa [Measure.finsetSum_apply] using sum_hypergeometricWeight hK hn

/-- The singleton mass of a valid hypergeometric law is its defining weight. -/
@[simp]
theorem hypergeometricMeasure_singleton (hK : K ≤ N) (hn : n ≤ N) (k : ℕ) :
    hypergeometricMeasure N K n {k} = hypergeometricWeight N K n k := by
  rw [hypergeometricMeasure_eq_sum_dirac hK hn, Measure.finsetSum_apply]
  by_cases hk : k ≤ n
  · rw [Finset.sum_eq_single k]
    · simp
    · simp_all
    · simp_all
  · rw [Finset.sum_eq_zero]
    · simp [hypergeometricWeight, hk]
    · intro j hj
      have hjk : j ≠ k := ne_of_lt
        (lt_of_le_of_lt (Finset.mem_range_succ_iff.mp hj) (lt_of_not_ge hk))
      simp [hjk]

/-- The real singleton mass of a valid hypergeometric law. -/
theorem hypergeometricMeasure_real_singleton (hK : K ≤ N) (hn : n ≤ N) (k : ℕ) :
    (hypergeometricMeasure N K n).real {k} =
      if k ≤ n then
        (K.choose k : ℝ) * ((N - K).choose (n - k) : ℝ) / (N.choose n : ℝ)
      else 0 := by
  rw [measureReal_def, hypergeometricMeasure_singleton hK hn, hypergeometricWeight]
  split_ifs with hk
  · rw [ENNReal.toReal_div, ENNReal.toReal_mul]
    norm_cast
  · simp

/-- A hypergeometric weight is nonzero exactly on its classical support. -/
@[simp]
theorem hypergeometricWeight_ne_zero_iff (N K n k : ℕ) :
    hypergeometricWeight N K n k ≠ 0 ↔
      k ≤ K ∧ k ≤ n ∧ n - k ≤ N - K := by
  rw [hypergeometricWeight]
  by_cases hkn : k ≤ n
  · simp [hkn, Nat.choose_ne_zero_iff]
  · simp [hkn]

/-- The singleton mass of a valid hypergeometric law is nonzero exactly on its classical
support. -/
theorem hypergeometricMeasure_singleton_ne_zero_iff (hK : K ≤ N) (hn : n ≤ N) (k : ℕ) :
    hypergeometricMeasure N K n {k} ≠ 0 ↔
      k ≤ K ∧ k ≤ n ∧ n - k ≤ N - K := by
  rw [hypergeometricMeasure_singleton hK hn, hypergeometricWeight_ne_zero_iff]

/-- Every hypergeometric weight is finite when the sample size does not exceed the population
size. -/
theorem hypergeometricWeight_ne_top (N K n k : ℕ) (hn : n ≤ N) :
    hypergeometricWeight N K n k ≠ ∞ := by
  rw [hypergeometricWeight]
  split_ifs
  · apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top (ne_of_lt (ENNReal.natCast_lt_top _))
        (ne_of_lt (ENNReal.natCast_lt_top _))
    · exact_mod_cast Nat.choose_ne_zero hn
  · simp

/-- Every function is integrable against a hypergeometric measure, since the measure has finite
support. -/
theorem integrable_hypergeometricMeasure {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (N K n : ℕ) : Integrable f (hypergeometricMeasure N K n) := by
  rw [hypergeometricMeasure]
  split_ifs with h
  · exact integrable_finsetSum_measure.mpr fun _ _ ↦
      (integrable_dirac (by simp)).smul_measure
        (hypergeometricWeight_ne_top N K n _ h.2)
  · simp

/-- Integration against a valid hypergeometric measure is the corresponding finite weighted
sum. -/
theorem integral_hypergeometricMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℕ → E) (hK : K ≤ N) (hn : n ≤ N) :
    ∫ k, f k ∂hypergeometricMeasure N K n =
      ∑ k ∈ Finset.range (n + 1), (hypergeometricWeight N K n k).toReal • f k := by
  rw [hypergeometricMeasure_eq_sum_dirac hK hn, integral_finsetSum_measure]
  · simp
  · exact fun _ _ ↦
      (integrable_dirac (by simp)).smul_measure
        (hypergeometricWeight_ne_top N K n _ hn)

/-! ## Cumulative masses -/

/-- The cumulative mass of a hypergeometric law is the finite sum of its singleton masses. -/
theorem hypergeometricMeasure_real_Iic (k : ℕ) :
    (hypergeometricMeasure N K n).real {j | j ≤ k} =
      ∑ j ∈ Finset.Iic k, (hypergeometricMeasure N K n).real {j} := by
  let _ : IsFiniteMeasure (hypergeometricMeasure N K n) :=
    (integrable_const_iff_isFiniteMeasure one_ne_zero).mp
      (integrable_hypergeometricMeasure (fun _ ↦ (1 : ℝ)) N K n)
  have hset : {j : ℕ | j ≤ k} = (Finset.Iic k : Set ℕ) := by
    ext j
    simp
  rw [hset, ← sum_measureReal_singleton]

/-- The cumulative mass of a valid hypergeometric law as a finite sum of its explicit weights. -/
theorem hypergeometricMeasure_real_Iic_eq_sum (hK : K ≤ N) (hn : n ≤ N) (k : ℕ) :
    (hypergeometricMeasure N K n).real {j | j ≤ k} =
      ∑ j ∈ Finset.Iic k,
        if j ≤ n then
          (K.choose j : ℝ) * ((N - K).choose (n - j) : ℝ) / (N.choose n : ℝ)
        else 0 := by
  rw [hypergeometricMeasure_real_Iic]
  exact Finset.sum_congr rfl fun j _ ↦ hypergeometricMeasure_real_singleton hK hn j

/-! ## Moments of the real-valued cast law -/

private theorem sum_fst_mul_choose_mul_choose (A B r : ℕ) (hr : 0 < r) :
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal r,
        ij.1 * A.choose ij.1 * B.choose ij.2 =
      A * (A + B - 1).choose (r - 1) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  cases A with
  | zero =>
      simp only [Nat.zero_add, Nat.zero_mul]
      apply Finset.sum_eq_zero
      intro p hp
      by_cases h : p.1 = 0
      · simp [h]
      · simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero h)]
  | succ a =>
      rw [Finset.Nat.sum_antidiagonal_succ]
      simp only [Nat.zero_mul, zero_add]
      calc
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal s,
            (p.1 + 1) * (a + 1).choose (p.1 + 1) * B.choose p.2) =
            (a + 1) * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal s,
              a.choose p.1 * B.choose p.2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          have hchoose : (p.1 + 1) * (a + 1).choose (p.1 + 1) =
              (a + 1) * a.choose p.1 := by
            simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq a p.1).symm
          rw [hchoose]
          ring
        _ = (a + 1) * (a + B).choose s := by
          rw [← Nat.add_choose_eq]
        _ = (a + 1) * (a + 1 + B - 1).choose (s + 1 - 1) := by
          simp

private theorem sum_fst_mul_pred_mul_choose_mul_choose_add_two (a B s : ℕ) :
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (2 + s),
        ij.1 * (ij.1 - 1) * (a + 2).choose ij.1 * B.choose ij.2 =
      (a + 2) * (a + 2 - 1) * (a + 2 + B - 2).choose (2 + s - 2) := by
  -- Extract one factor `a + 2` with the choose recurrence, reducing the remaining sum to
  -- the first falling-factorial Vandermonde identity.
  have hr : 2 + s = (s + 1) + 1 := by omega
  rw [hr, Finset.Nat.sum_antidiagonal_succ]
  simp only [Nat.zero_mul, zero_add, Nat.add_sub_cancel]
  calc
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (s + 1),
        (p.1 + 1) * p.1 * (a + 2).choose (p.1 + 1) * B.choose p.2) =
        (a + 2) * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (s + 1),
          p.1 * (a + 1).choose p.1 * B.choose p.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      have hchoose : (p.1 + 1) * (a + 2).choose (p.1 + 1) =
          (a + 2) * (a + 1).choose p.1 := by
        calc
          _ = (a + 2).choose (p.1 + 1) * (p.1 + 1) := Nat.mul_comm _ _
          _ = _ := by simpa only [Nat.add_assoc] using
            (Nat.add_one_mul_choose_eq (a + 1) p.1).symm
      calc
        _ = p.1 * ((p.1 + 1) * (a + 2).choose (p.1 + 1)) * B.choose p.2 := by
          ring
        _ = p.1 * ((a + 2) * (a + 1).choose p.1) * B.choose p.2 := by rw [hchoose]
        _ = _ := by ring
    _ = (a + 2) * ((a + 1) * (a + 1 + B - 1).choose (s + 1 - 1)) := by
      rw [sum_fst_mul_choose_mul_choose (a + 1) B (s + 1) (by omega)]
    _ = (a + 2) * (a + 2 - 1) *
        (a + 2 + B - 2).choose (s + 1 + 1 - 2) := by
      have haPred : a + 2 - 1 = a + 1 := by omega
      have haBPred : a + 2 + B - 2 = a + B := by omega
      have hsPred : s + 1 + 1 - 2 = s := by omega
      have haBPred' : a + 1 + B - 1 = a + B := by omega
      have hsPred' : s + 1 - 1 = s := by omega
      rw [haPred, haBPred, hsPred, haBPred', hsPred']
      ring

private theorem sum_fst_mul_pred_mul_choose_mul_choose (A B r : ℕ) (hr : 2 ≤ r) :
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal r,
        ij.1 * (ij.1 - 1) * A.choose ij.1 * B.choose ij.2 =
      A * (A - 1) * (A + B - 2).choose (r - 2) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
  -- For `A = 0` or `A = 1`, every summand vanishes: either the binomial coefficient or
  -- the falling-factorial multiplier `ij.1 * (ij.1 - 1)` is zero.
  cases A with
  | zero =>
      simp only [Nat.zero_add, Nat.zero_mul]
      apply Finset.sum_eq_zero
      intro p hp
      by_cases h : p.1 = 0
      · simp [h]
      · simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero h)]
  | succ a =>
      cases a with
      | zero =>
          simp only [Nat.add_sub_cancel_left, Nat.sub_self, Nat.mul_zero]
          rw [Nat.zero_mul]
          apply Finset.sum_eq_zero
          intro p hp
          rcases lt_trichotomy p.1 1 with h | h | h
          · have hp0 : p.1 = 0 := by omega
            simp [hp0]
          · simp [h]
          · simp [Nat.choose_eq_zero_of_lt h]
      | succ a =>
          exact sum_fst_mul_pred_mul_choose_mul_choose_add_two a B s

private theorem sum_range_mul_choose_mul_choose {N K n : ℕ} (hK : K ≤ N) (hn : 0 < n) :
    ∑ k ∈ Finset.range (n + 1), k * K.choose k * (N - K).choose (n - k) =
      K * (N - 1).choose (n - 1) := by
  calc
    _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        ij.1 * K.choose ij.1 * (N - K).choose ij.2 := by
      symm
      simpa using Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
        (fun ij : ℕ × ℕ ↦ ij.1 * K.choose ij.1 * (N - K).choose ij.2) n
    _ = K * (K + (N - K) - 1).choose (n - 1) := sum_fst_mul_choose_mul_choose K (N - K) n hn
    _ = _ := by rw [Nat.add_sub_of_le hK]

private theorem sum_range_mul_pred_mul_choose_mul_choose {N K n : ℕ} (hK : K ≤ N) (hn : 2 ≤ n) :
    ∑ k ∈ Finset.range (n + 1),
        k * (k - 1) * K.choose k * (N - K).choose (n - k) =
      K * (K - 1) * (N - 2).choose (n - 2) := by
  calc
    _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        ij.1 * (ij.1 - 1) * K.choose ij.1 * (N - K).choose ij.2 := by
      symm
      simpa using Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
        (fun ij : ℕ × ℕ ↦
          ij.1 * (ij.1 - 1) * K.choose ij.1 * (N - K).choose ij.2) n
    _ = K * (K - 1) * (K + (N - K) - 2).choose (n - 2) :=
      sum_fst_mul_pred_mul_choose_mul_choose K (N - K) n hn
    _ = _ := by rw [Nat.add_sub_of_le hK]

private theorem sum_hypergeometricWeight_toReal_mul {N K n : ℕ} (hK : K ≤ N) (hn : n ≤ N)
    (hN : 0 < N) :
    ∑ k ∈ Finset.range (n + 1),
        (hypergeometricWeight N K n k).toReal * (k : ℝ) =
      (n : ℝ) * (K : ℝ) / (N : ℝ) := by
  by_cases hn0 : n = 0
  · subst n
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hchooseN : (N.choose n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hn
  calc
    _ = ∑ k ∈ Finset.range (n + 1),
        ((K.choose k : ℝ) * ((N - K).choose (n - k) : ℝ) /
          (N.choose n : ℝ)) * (k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hypergeometricWeight_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)),
        ENNReal.toReal_div, ENNReal.toReal_mul]
      norm_cast
    _ = ((∑ k ∈ Finset.range (n + 1),
        k * K.choose k * (N - K).choose (n - k) : ℕ) : ℝ) / (N.choose n : ℝ) := by
      push_cast
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ((K * (N - 1).choose (n - 1) : ℕ) : ℝ) / (N.choose n : ℝ) := by
      rw [sum_range_mul_choose_mul_choose hK hnpos]
    _ = (n : ℝ) * (K : ℝ) / (N : ℝ) := by
      have hchoose : N * (N - 1).choose (n - 1) = N.choose n * n := by
        obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
        exact Nat.add_one_mul_choose_eq M m
      have hchooseR : (N : ℝ) * ((N - 1).choose (n - 1) : ℝ) =
          (N.choose n : ℝ) * (n : ℝ) := by
        exact_mod_cast hchoose
      push_cast
      field_simp
      linear_combination (K : ℝ) * hchooseR

private theorem cast_mul_pred_mul_choose_pred_pred {N n : ℕ} (hn2 : 2 ≤ n) (hn : n ≤ N) :
    (N : ℝ) * ((N : ℝ) - 1) * ((N - 2).choose (n - 2) : ℝ) =
      (N.choose n : ℝ) * (n : ℝ) * ((n : ℝ) - 1) := by
  have hNtwo : 2 ≤ N := hn2.trans hn
  have hNpos : 0 < N := by omega
  have hnpos : 0 < n := by omega
  have hchoose₁ : N * (N - 1).choose (n - 1) = N.choose n * n := by
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNpos.ne'
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
    exact Nat.add_one_mul_choose_eq M m
  have hchoose₂ : (N - 1) * (N - 2).choose (n - 2) =
      (N - 1).choose (n - 1) * (n - 1) := by
    obtain ⟨M, hM⟩ := Nat.exists_eq_add_of_le hNtwo
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn2
    subst N
    subst n
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.add_one_mul_choose_eq M m
  have h₁ : (N : ℝ) * ((N - 1).choose (n - 1) : ℝ) =
      (N.choose n : ℝ) * (n : ℝ) := by exact_mod_cast hchoose₁
  have h₂ : ((N : ℝ) - 1) * ((N - 2).choose (n - 2) : ℝ) =
      ((N - 1).choose (n - 1) : ℝ) * ((n : ℝ) - 1) := by
    have h₂' : ((N - 1 : ℕ) : ℝ) * ((N - 2).choose (n - 2) : ℝ) =
        ((N - 1).choose (n - 1) : ℝ) * ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast hchoose₂
    simpa [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_sub (by omega : 1 ≤ n)] using h₂'
  calc
    _ = (N : ℝ) * (((N : ℝ) - 1) * ((N - 2).choose (n - 2) : ℝ)) := by ring
    _ = (N : ℝ) * (((N - 1).choose (n - 1) : ℝ) * ((n : ℝ) - 1)) := by rw [h₂]
    _ = ((N : ℝ) * ((N - 1).choose (n - 1) : ℝ)) * ((n : ℝ) - 1) := by ring
    _ = ((N.choose n : ℝ) * (n : ℝ)) * ((n : ℝ) - 1) := by rw [h₁]
    _ = _ := by ring

private theorem sum_hypergeometricWeight_toReal_mul_pred {N K n : ℕ} (hK : K ≤ N) (hn : n ≤ N)
    (hN : 1 < N) :
    ∑ k ∈ Finset.range (n + 1),
        (hypergeometricWeight N K n k).toReal * (k : ℝ) * ((k : ℝ) - 1) =
      (n : ℝ) * ((n : ℝ) - 1) * (K : ℝ) * ((K : ℝ) - 1) /
        ((N : ℝ) * ((N : ℝ) - 1)) := by
  by_cases hn2 : 2 ≤ n
  · -- Normalize the weights by `N.choose n`, apply the second-factorial-moment
    -- Vandermonde identity, and cancel the denominator using two choose recurrences.
    have hchooseN : (N.choose n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero hn
    calc
      _ = ∑ k ∈ Finset.range (n + 1),
          ((K.choose k : ℝ) * ((N - K).choose (n - k) : ℝ) /
            (N.choose n : ℝ)) * (k : ℝ) * ((k : ℝ) - 1) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hypergeometricWeight_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)),
          ENNReal.toReal_div, ENNReal.toReal_mul]
        norm_cast
      _ = ((∑ k ∈ Finset.range (n + 1),
          k * (k - 1) * K.choose k * (N - K).choose (n - k) : ℕ) : ℝ) /
            (N.choose n : ℝ) := by
        push_cast
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k hk
        cases k with
        | zero => simp
        | succ k =>
            simp only [Nat.cast_succ, Nat.succ_sub_one]
            ring
      _ = ((K * (K - 1) * (N - 2).choose (n - 2) : ℕ) : ℝ) /
            (N.choose n : ℝ) := by
        rw [sum_range_mul_pred_mul_choose_mul_choose hK hn2]
      _ = (n : ℝ) * ((n : ℝ) - 1) * (K : ℝ) * ((K : ℝ) - 1) /
          ((N : ℝ) * ((N : ℝ) - 1)) := by
        have hKpred : (K : ℝ) * ((K - 1 : ℕ) : ℝ) =
            (K : ℝ) * ((K : ℝ) - 1) := by
          cases K <;> norm_num [Nat.cast_sub]
        have hNreal : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
        have hNm1 : (N : ℝ) - 1 ≠ 0 := by linarith
        push_cast
        rw [hKpred]
        field_simp [hNm1]
        linear_combination (K : ℝ) * ((K : ℝ) - 1) *
          cast_mul_pred_mul_choose_pred_pred hn2 hn
  · -- When `n` is zero or one, the falling factorial `k * (k - 1)` vanishes on the support.
    have hnle : n ≤ 1 := by omega
    interval_cases n <;> norm_num [Finset.sum_range_succ, hypergeometricWeight]

/-- The mean of the real cast of a valid hypergeometric law is `nK / N` when the population
is nonempty. The only valid empty-population parameters are handled separately below. -/
@[simp]
theorem integral_id_map_cast_hypergeometricMeasure {N K n : ℕ}
    (hK : K ≤ N) (hn : n ≤ N) (hN : 0 < N) :
    ∫ x, x ∂((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)) =
      (n : ℝ) * (K : ℝ) / (N : ℝ) := by
  rw [integral_map (by fun_prop) (by fun_prop),
    integral_hypergeometricMeasure (fun k ↦ (k : ℝ)) hK hn]
  simpa only [smul_eq_mul] using sum_hypergeometricWeight_toReal_mul hK hn hN

private theorem integral_sq_id_map_cast_hypergeometricMeasure {N K n : ℕ}
    (hK : K ≤ N) (hn : n ≤ N) (hN : 1 < N) :
    ∫ x, x ^ 2 ∂((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)) =
      (n : ℝ) * ((n : ℝ) - 1) * (K : ℝ) * ((K : ℝ) - 1) /
          ((N : ℝ) * ((N : ℝ) - 1)) +
        (n : ℝ) * (K : ℝ) / (N : ℝ) := by
  rw [integral_map (by fun_prop) (by fun_prop),
    integral_hypergeometricMeasure (fun k ↦ (k : ℝ) ^ 2) hK hn]
  simp only [smul_eq_mul]
  calc
    _ = ∑ k ∈ Finset.range (n + 1),
          ((hypergeometricWeight N K n k).toReal * (k : ℝ) * ((k : ℝ) - 1) +
            (hypergeometricWeight N K n k).toReal * (k : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (∑ k ∈ Finset.range (n + 1),
          (hypergeometricWeight N K n k).toReal * (k : ℝ) * ((k : ℝ) - 1)) +
        ∑ k ∈ Finset.range (n + 1),
          (hypergeometricWeight N K n k).toReal * (k : ℝ) := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [sum_hypergeometricWeight_toReal_mul_pred hK hn hN,
        sum_hypergeometricWeight_toReal_mul hK hn (by omega)]

private theorem integrable_sq_id_map_cast_hypergeometricMeasure (N K n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ 2)
      ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)) := by
  rw [(MeasurableEmbedding.natCast (α := ℝ)).integrable_map_iff]
  convert integrable_hypergeometricMeasure (fun k : ℕ ↦ ((k : ℝ) ^ 2)) N K n using 1
  funext k
  rfl

/-- The variance of the real cast of a valid hypergeometric law for a population with at least
two elements. The finite-population correction is `(N - n) / (N - 1)`; populations of size zero
and one are handled separately below. -/
@[simp]
theorem variance_id_map_cast_hypergeometricMeasure {N K n : ℕ}
    (hK : K ≤ N) (hn : n ≤ N) (hN : 1 < N) :
    variance id ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)) =
      (n : ℝ) * ((K : ℝ) / (N : ℝ)) * (1 - (K : ℝ) / (N : ℝ)) *
        (((N : ℝ) - (n : ℝ)) / ((N : ℝ) - 1)) := by
  let _ : IsProbabilityMeasure (hypergeometricMeasure N K n) :=
    isProbabilityMeasure_hypergeometricMeasure hK hn
  have hmem : MemLp id 2
      ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      (integrable_sq_id_map_cast_hypergeometricMeasure N K n)
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_sq_id_map_cast_hypergeometricMeasure hK hn hN,
    integral_id_map_cast_hypergeometricMeasure hK hn (by omega)]
  have hNreal : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNm1 : (N : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hNm1]
  ring

/-- The real cast of the unique valid empty-population hypergeometric law has mean zero. -/
@[simp]
theorem integral_id_map_cast_hypergeometricMeasure_zero :
    ∫ x, x ∂((hypergeometricMeasure 0 0 0).map (Nat.cast : ℕ → ℝ)) = 0 := by
  norm_num [hypergeometricMeasure, hypergeometricWeight]

/-- The real cast of the unique valid empty-population hypergeometric law has variance zero. -/
@[simp]
theorem variance_id_map_cast_hypergeometricMeasure_zero :
    variance id ((hypergeometricMeasure 0 0 0).map (Nat.cast : ℕ → ℝ)) = 0 := by
  norm_num [hypergeometricMeasure, hypergeometricWeight]

/-- Every valid hypergeometric law on a population of size one has variance zero. This is stated
separately because the usual formula contains the totalized quotient by `N - 1`. -/
@[simp]
theorem variance_id_map_cast_hypergeometricMeasure_of_population_one {K n : ℕ}
    (hK : K ≤ 1) (hn : n ≤ 1) :
    variance id ((hypergeometricMeasure 1 K n).map (Nat.cast : ℕ → ℝ)) = 0 := by
  interval_cases K <;> interval_cases n <;>
    simp [hypergeometricMeasure, hypergeometricWeight, Finset.sum_range_succ]

/-! ## Transforms of the real-valued cast law -/

/-- Every function on `ℝ` is integrable against the real-valued cast of a hypergeometric law,
since the native law has finite support. -/
@[simp]
theorem integrable_map_cast_hypergeometricMeasure {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (N K n : ℕ) :
    Integrable f ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)) := by
  rw [(MeasurableEmbedding.natCast (α := ℝ)).integrable_map_iff]
  exact integrable_hypergeometricMeasure (fun k ↦ f (k : ℝ)) N K n

/-- Integration against the real-valued cast of a valid hypergeometric law is a finite weighted
sum. -/
theorem integral_map_cast_hypergeometricMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (hK : K ≤ N) (hn : n ≤ N) :
    ∫ x, f x ∂(hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ) =
      ∑ k ∈ Finset.range (n + 1),
        (hypergeometricWeight N K n k).toReal • f (k : ℝ) := by
  rw [integral_map Measurable.of_discrete.aemeasurable
      (integrable_map_cast_hypergeometricMeasure f N K n).aestronglyMeasurable,
    integral_hypergeometricMeasure (fun k ↦ f (k : ℝ)) hK hn]

/-- The real-valued cast of every hypergeometric law has all exponential moments. This includes
the invalid parameter range, where the totalized law is the zero measure. -/
@[simp]
theorem integrableExpSet_id_map_cast_hypergeometricMeasure (N K n : ℕ) :
    integrableExpSet id ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)) = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_univ, iff_true]
  exact integrable_map_cast_hypergeometricMeasure (fun x : ℝ ↦ Real.exp (t * id x)) N K n

/-- The moment-generating function of the real-valued cast of a valid hypergeometric law, as the
finite sum of its masses against the exponential kernel. -/
theorem mgf_id_map_cast_hypergeometricMeasure (hK : K ≤ N) (hn : n ≤ N) (t : ℝ) :
    mgf id ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)) t =
      ∑ k ∈ Finset.range (n + 1),
        (hypergeometricWeight N K n k).toReal * Real.exp (t * (k : ℝ)) := by
  rw [mgf, integral_map_cast_hypergeometricMeasure _ hK hn]
  simp only [id_eq, smul_eq_mul]

/-- The cumulant-generating function of the real-valued cast of a valid hypergeometric law is the
real logarithm of its finite-sum moment-generating function. -/
theorem cgf_id_map_cast_hypergeometricMeasure (hK : K ≤ N) (hn : n ≤ N) (t : ℝ) :
    cgf id ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)) t =
      Real.log (∑ k ∈ Finset.range (n + 1),
        (hypergeometricWeight N K n k).toReal * Real.exp (t * (k : ℝ))) := by
  rw [cgf, mgf_id_map_cast_hypergeometricMeasure hK hn]

/-- The characteristic function of the real-valued cast of a valid hypergeometric law, as the
finite sum of its masses against the complex exponential kernel. -/
theorem charFun_map_cast_hypergeometricMeasure (hK : K ≤ N) (hn : n ≤ N) (t : ℝ) :
    charFun ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)) t =
      ∑ k ∈ Finset.range (n + 1),
        (hypergeometricWeight N K n k).toReal *
          Complex.exp (((k : ℝ) * t) * Complex.I) := by
  rw [charFun_apply, integral_map_cast_hypergeometricMeasure _ hK hn]
  apply Finset.sum_congr rfl
  intro k _
  rw [Complex.real_smul]
  simp only [Real.inner_apply]
  congr 2
  push_cast
  ring

end Probability

end TauCeti
