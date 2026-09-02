/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# The hypergeometric distribution

The hypergeometric law describes the number of marked objects in a sample of size `n`, drawn
without replacement from a population of size `N` containing `K` marked objects.  For
`K ≤ N` and `n ≤ N`, its mass at `k` is

```text
  choose K k * choose (N - K) (n - k) / choose N n.
```

This file defines the law as a finite weighted sum of Dirac measures, proves its normalization
from Vandermonde's identity, and provides its mass, support, cumulative-mass, finite-integral, and
transform APIs. Outside the classical parameter range the measure is zero, as required by the
standard-distributions roadmap.

## Main definitions and results

* `TauCeti.Probability.hypergeometricWeight`: the `ℝ≥0∞`-valued mass function.
* `TauCeti.Probability.hypergeometricMeasure`: the totalized hypergeometric measure on `ℕ`.
* `TauCeti.Probability.measurable_hypergeometricMeasure`: measurability in all three parameters.
* `TauCeti.Probability.isProbabilityMeasure_hypergeometricMeasure`: normalization in the valid
  parameter range.
* `TauCeti.Probability.hypergeometricMeasure_singleton`: the exact singleton mass.
* `TauCeti.Probability.hypergeometricWeight_ne_zero_iff`: the exact support.
* `TauCeti.Probability.integral_hypergeometricMeasure`: integration as a finite weighted sum.
* `TauCeti.Probability.hypergeometricMeasure_real_Iic`: the native cumulative mass.
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
