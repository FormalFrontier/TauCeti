/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Hypergeometric.Basic
public import Mathlib.Probability.Distributions.Binomial
import TauCeti.Analysis.SpecialFunctions.Choose

/-!
# The binomial limit of hypergeometric probabilities

Fix a sample size `n`. Suppose a population of size `N` contains `K N` marked elements and the
marked proportion `K N / N` converges to `p`. Then, for every fixed `k`, the probability that a
sample without replacement contains `k` marked elements converges to the corresponding binomial
probability for `n` independent trials with success probability `p`.

The result includes the boundary proportions `p = 0` and `p = 1`. Its proof normalizes the three
binomial coefficients in the hypergeometric mass formula by powers of `N`; this avoids requiring
either `K N` or `N - K N` to tend to infinity at the boundary.

## Main result

* `TauCeti.Probability.tendsto_hypergeometricMeasure_real_singleton` — pointwise convergence of
  hypergeometric masses to binomial masses.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Topology

namespace TauCeti

namespace Probability

/-- If the marked proportion in a growing finite population tends to `p`, then each fixed
hypergeometric mass tends to the corresponding binomial mass. -/
theorem tendsto_hypergeometricMeasure_real_singleton (p : unitInterval) (K : ℕ → ℕ)
    (hK : ∀ N, K N ≤ N)
    (hKp : Tendsto (fun N ↦ (K N : ℝ) / N) atTop (nhds (p : ℝ))) (n k : ℕ) :
    Tendsto (fun N ↦ (hypergeometricMeasure N (K N) n).real {k}) atTop
      (nhds ((binomial n p).real {k})) := by
  by_cases hkn : k ≤ n
  · -- Normalize the marked, unmarked, and total population coefficients separately.
    have hinv : Tendsto (fun N : ℕ ↦ ((N : ℝ))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_nhds_zero_nat
    have hcomplement :
        Tendsto (fun N ↦ ((N - K N : ℕ) : ℝ) / N) atTop
          (nhds (1 - (p : ℝ))) := by
      refine Tendsto.congr' ?_ (tendsto_const_nhds.sub hKp)
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [Nat.cast_sub (hK N), sub_div, div_self]
      exact_mod_cast (show N ≠ 0 by omega)
    have htotal : Tendsto (fun N : ℕ ↦ (N : ℝ) / N) atTop (nhds 1) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [div_self]
      exact_mod_cast (show N ≠ 0 by omega)
    have hmarked := tendsto_choose_div_pow_of_tendsto_div
      (a := K) (b := fun N : ℕ ↦ (N : ℝ)) hKp hinv k
    have hunmarked :=
      tendsto_choose_div_pow_of_tendsto_div (a := fun N ↦ N - K N)
        (b := fun N : ℕ ↦ (N : ℝ)) hcomplement hinv (n - k)
    have hpopulation := tendsto_choose_div_pow_of_tendsto_div
      (a := id) (b := fun N : ℕ ↦ (N : ℝ)) htotal hinv n
    -- Combine the three limits before identifying the normalized ratio with the mass.
    have hnormalized := (hmarked.mul hunmarked).div hpopulation (by positivity)
    rw [binomial_real_singleton]
    have hfactorial :
        (n.choose k : ℝ) * (k.factorial : ℝ) * ((n - k).factorial : ℝ) =
          (n.factorial : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
    have hlimit :
        (p : ℝ) ^ k / (k.factorial : ℝ) *
              ((1 - (p : ℝ)) ^ (n - k) / ((n - k).factorial : ℝ)) /
            (1 ^ n / (n.factorial : ℝ)) =
          (n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) := by
      field_simp
      rw [← hfactorial]
      ring
    rw [hlimit] at hnormalized
    refine Tendsto.congr' ?_ hnormalized
    filter_upwards [eventually_ge_atTop (max n 1)] with N hN
    have hnN : n ≤ N := le_trans (le_max_left n 1) hN
    have hNpos : 0 < N := lt_of_lt_of_le (by omega) hN
    rw [hypergeometricMeasure_real_singleton (hK N) hnN k, ite_eq_left hkn]
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
    have hchooseN : (N.choose n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero hnN
    simp only [Pi.div_apply, id_eq]
    field_simp
    have hpow : (N : ℝ) ^ k * (N : ℝ) ^ (n - k) = (N : ℝ) ^ n := by
      rw [← pow_add, Nat.add_sub_of_le hkn]
    calc
      _ = (K N).choose k * (N - K N).choose (n - k) *
          ((N : ℝ) ^ k * (N : ℝ) ^ (n - k)) := by rw [hpow]
      _ = _ := by ring
  · -- Outside the common support, both the hypergeometric and binomial masses vanish.
    rw [binomial_real_singleton, Nat.choose_eq_zero_of_lt (lt_of_not_ge hkn)]
    simp only [Nat.cast_zero, zero_mul]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop n] with N hnN
    rw [hypergeometricMeasure_real_singleton (hK N) hnN k, ite_eq_right hkn]

end Probability

end TauCeti
