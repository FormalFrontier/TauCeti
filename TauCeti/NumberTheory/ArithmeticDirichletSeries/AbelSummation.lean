/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.NumberTheory.AbelSummation
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting

/-!
# Abel summation for norm-indexed summatory functions

Mathlib's `sum_mul_eq_sub_sub_integral_mul` is Abel summation for a sequence indexed by the natural
numbers.  Every counting argument of the arithmetic-Dirichlet-series roadmap instead sums a weight
over a carrier indexed by ideals or by height-one primes, cut off inclusively by the absolute norm.
This file supplies the bridge: the weight is regrouped into its norm fibres, Mathlib's identity is
applied to the resulting sequence, and the answer is read back as an equation between
`TauCeti.summatory` functions.

The bridge is stated for a general Northcott index `N : ι → ℕ`, because Layer 6 uses it for both
the ideal carrier and the prime carrier.  The integral runs over the half-open interval `Set.Ioc`,
so each boundary term is counted exactly once, as the roadmap's conventions table demands.

## Main results

* `TauCeti.summatory_mul_eq_sub_sub_integral_mul`: Abel summation between two nonnegative real
  cutoffs for a weight of the form `i ↦ w i * g (N i)`.
* `TauCeti.summatory_mul_eq_sub_integral_mul_of_two_le`: the form used by a carrier whose indices
  all have `N`-value at least `2`, where the boundary term at the cutoff `2` cancels.
* `TauCeti.primeSummatory_mul_eq_sub_integral_mul`: that form for the height-one primes of a
  number field.
* `TauCeti.primeTheta_eq_log_mul_primeCount_sub_integral` and
  `TauCeti.primeCount_eq_primeTheta_div_log_add_integral`: the two exact Abel identities relating
  the roadmap's weighted prime counts,
  `ϑ(x) = π(x) log x - ∫_2^x π(t)/t dt` and `π(x) = ϑ(x)/log x + ∫_2^x ϑ(t)/(t log²t) dt`.
  Both hold for every real cutoff; below `2` all three terms vanish.

## Roadmap role

This is Layer **6.1** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: Mathlib's exact
finite identity is consumed, not restated, and only the norm-indexed bridges are added.  The two
prime identities are the finite input to Layer 6.2, which turns `ϑ(x) ∼ δx` into `π(x) ∼ δ Li(x)`
by estimating the integrals appearing here.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped nonZeroDivisors NumberField
open IsDedekindDomain

variable {ι : Type*} (N : ι → ℕ) [Northcott N] {𝕜 : Type*} [RCLike 𝕜]

/-! ### Regrouping a weight into its norm fibres -/

/-- The sequence of fibre sums attached to a weight: the total weight of the indices of
`N`-value exactly `n`.  This is the sequence handed to Mathlib's Abel summation. -/
private noncomputable def normFiberSum (w : ι → 𝕜) (n : ℕ) : 𝕜 :=
  ∑ i ∈ normLE N (n : ℝ) with N i = n, w i

private theorem normFiberSum_eq_sum_filter (w : ι → 𝕜) (n : ℕ) {x : ℝ} (hx : (n : ℝ) ≤ x) :
    normFiberSum N w n = ∑ i ∈ normLE N x with N i = n, w i := by
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext i
  simp only [Finset.mem_filter, mem_normLE, and_congr_left_iff]
  rintro rfl
  simp [hx]

private theorem normFiberSum_mul (w : ι → 𝕜) (g : ℝ → 𝕜) (n : ℕ) :
    normFiberSum N (fun i ↦ w i * g (N i)) n = g n * normFiberSum N w n := by
  simp only [normFiberSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [(Finset.mem_filter.mp hi).2, mul_comm]

/-- A summatory function is the partial sum of the sequence of fibre sums. -/
private theorem summatory_eq_sum_Icc_normFiberSum (w : ι → 𝕜) {x : ℝ} (hx : 0 ≤ x) :
    summatory N w x = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, normFiberSum N w n := by
  have hmaps : ∀ i ∈ normLE N x, N i ∈ Finset.Icc 0 ⌊x⌋₊ := fun i hi ↦
    Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor ((mem_normLE N).mp hi)⟩
  rw [summatory_apply, ← Finset.sum_fiberwise_of_maps_to hmaps w]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  exact (normFiberSum_eq_sum_filter N w n
    (le_trans (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2) (Nat.floor_le hx))).symm

private theorem sum_Ioc_normFiberSum (w : ι → 𝕜) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, normFiberSum N w n = summatory N w b - summatory N w a := by
  have hfloor : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
  have hdisj : Disjoint (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) (Finset.Icc 0 ⌊a⌋₊) := by
    refine Finset.disjoint_left.mpr fun n hn hn' ↦ ?_
    simp only [Finset.mem_Ioc] at hn
    simp only [Finset.mem_Icc] at hn'
    omega
  have hunion : Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ ∪ Finset.Icc 0 ⌊a⌋₊ = Finset.Icc 0 ⌊b⌋₊ := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [summatory_eq_sum_Icc_normFiberSum N w (ha.trans hab),
    summatory_eq_sum_Icc_normFiberSum N w ha, eq_sub_iff_add_eq, ← Finset.sum_union hdisj, hunion]

/-! ### Abel summation over a Northcott carrier -/

/-- **Abel summation for a norm-indexed summatory function.**  For a weight `w` on the index type
and a function `g` differentiable on `[a, b]`, the summatory function of the twisted weight
`i ↦ w i * g (N i)` between the inclusive cutoffs `a` and `b` is the boundary term
`g b · A(b) - g a · A(a)` minus the integral of `g' · A`, where `A = summatory N w`.

This is Mathlib's `sum_mul_eq_sub_sub_integral_mul` read through the norm fibres of `N`. -/
theorem summatory_mul_eq_sub_sub_integral_mul (w : ι → 𝕜) {g : ℝ → 𝕜} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hg_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ g t)
    (hg_int : IntegrableOn (deriv g) (Set.Icc a b)) :
    summatory N (fun i ↦ w i * g (N i)) b - summatory N (fun i ↦ w i * g (N i)) a =
      g b * summatory N w b - g a * summatory N w a -
        ∫ t in Set.Ioc a b, deriv g t * summatory N w t := by
  have key := sum_mul_eq_sub_sub_integral_mul (normFiberSum N w) ha hab hg_diff hg_int
  have hL : ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, g (n : ℝ) * normFiberSum N w n =
      summatory N (fun i ↦ w i * g (N i)) b - summatory N (fun i ↦ w i * g (N i)) a := by
    simp_rw [← normFiberSum_mul N w g]
    exact sum_Ioc_normFiberSum N _ ha hab
  have hI : ∫ t in Set.Ioc a b, deriv g t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, normFiberSum N w n =
      ∫ t in Set.Ioc a b, deriv g t * summatory N w t :=
    setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ by
      rw [summatory_eq_sum_Icc_normFiberSum N w (ha.trans ht.1.le)]
  rw [hL, ← summatory_eq_sum_Icc_normFiberSum N w (ha.trans hab),
    ← summatory_eq_sum_Icc_normFiberSum N w ha, hI] at key
  exact key

/-- Abel summation from the cutoff `2` for a carrier all of whose indices have `N`-value at least
`2`, such as the height-one primes of a number field.  The boundary term at `2` cancels, because
there the twisted weight is `g 2` times the untwisted one.

The identity holds for every cutoff `b`: below `2` all three terms vanish. -/
theorem summatory_mul_eq_sub_integral_mul_of_two_le (h2 : ∀ i, 2 ≤ N i) (w : ι → 𝕜) {g : ℝ → 𝕜}
    (b : ℝ) (hg_diff : ∀ t ∈ Set.Icc 2 b, DifferentiableAt ℝ g t)
    (hg_int : IntegrableOn (deriv g) (Set.Icc 2 b)) :
    summatory N (fun i ↦ w i * g (N i)) b =
      g b * summatory N w b - ∫ t in Set.Ioc 2 b, deriv g t * summatory N w t := by
  have h2' : ∀ i, (2 : ℝ) ≤ (N i : ℝ) := fun i ↦ by exact_mod_cast h2 i
  rcases lt_or_ge b 2 with hb | hb
  · rw [summatory_eq_zero_of_lt N h2' hb, summatory_eq_zero_of_lt N h2' hb,
      Set.Ioc_eq_empty_of_le hb.le]
    simp
  · have hcut : summatory N (fun i ↦ w i * g (N i)) 2 = g 2 * summatory N w 2 := by
      rw [summatory_apply, summatory_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [le_antisymm ((mem_normLE N).mp hi) (h2' i), mul_comm]
    have key := summatory_mul_eq_sub_sub_integral_mul N w (by norm_num) hb hg_diff hg_int
    rw [hcut] at key
    linear_combination key

/-! ### The prime carrier of a number field -/

variable (K : Type*) [Field K] [NumberField K]

/-- Abel summation over the height-one primes of `𝓞 K`, from the cutoff `2`. -/
theorem primeSummatory_mul_eq_sub_integral_mul (w : HeightOneSpectrum (𝓞 K) → ℝ) {g : ℝ → ℝ}
    (x : ℝ) (hg_diff : ∀ t ∈ Set.Icc 2 x, DifferentiableAt ℝ g t)
    (hg_int : IntegrableOn (deriv g) (Set.Icc 2 x)) :
    primeSummatory K (fun v ↦ w v * g (Ideal.absNorm v.asIdeal)) x =
      g x * primeSummatory K w x - ∫ t in Set.Ioc 2 x, deriv g t * primeSummatory K w t :=
  summatory_mul_eq_sub_integral_mul_of_two_le _
    (fun v ↦ by have := NumberField.HeightOneSpectrum.one_lt_absNorm v; omega) w x hg_diff hg_int

variable {K}

private theorem primeTheta_eq_primeSummatory (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeTheta K S x =
      primeSummatory K (S.indicator fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ)) x := by
  rw [primeTheta_apply, primeSummatory_apply]

private theorem primeCount_eq_primeSummatory (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeCount K S x = primeSummatory K (S.indicator 1) x := by
  rw [primeCount_apply, primeSummatory_apply]

/-- **Chebyshev's `ϑ` from `π`.**  The logarithmically weighted prime count is recovered from the
unweighted one by Abel summation, with the inclusive cutoff and the half-open integration range
fixed by the roadmap's conventions. -/
theorem primeTheta_eq_log_mul_primeCount_sub_integral (S : Set (HeightOneSpectrum (𝓞 K)))
    (x : ℝ) :
    primeTheta K S x =
      Real.log x * primeCount K S x - ∫ t in Set.Ioc 2 x, primeCount K S t / t := by
  have hw : (fun v : HeightOneSpectrum (𝓞 K) ↦ S.indicator (1 : HeightOneSpectrum (𝓞 K) → ℝ) v *
      Real.log (Ideal.absNorm v.asIdeal : ℝ)) =
      S.indicator fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
    funext v
    by_cases hv : v ∈ S
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, Pi.one_apply, one_mul]
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, zero_mul]
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) x, DifferentiableAt ℝ Real.log t := fun t ht ↦
    Real.differentiableAt_log (by linarith [ht.1] : (0 : ℝ) < t).ne'
  have hint : IntegrableOn (deriv Real.log) (Set.Icc (2 : ℝ) x) := by
    rw [Real.deriv_log']
    refine ContinuousOn.integrableOn_Icc (continuousOn_inv₀.mono fun t ht ↦ ?_)
    simpa using (by linarith [ht.1] : (0 : ℝ) < t).ne'
  have key : primeTheta K S x = Real.log x * primeCount K S x -
      ∫ t in Set.Ioc (2 : ℝ) x, deriv Real.log t * primeCount K S t := by
    simp only [primeTheta_eq_primeSummatory, primeCount_eq_primeSummatory]
    rw [← hw]
    exact primeSummatory_mul_eq_sub_integral_mul K _ x hdiff hint
  have hI : ∫ t in Set.Ioc (2 : ℝ) x, deriv Real.log t * primeCount K S t =
      ∫ t in Set.Ioc (2 : ℝ) x, primeCount K S t / t :=
    setIntegral_congr_fun measurableSet_Ioc fun t _ ↦ by rw [Real.deriv_log, inv_mul_eq_div]
  rw [key, hI]

/-- **Chebyshev's `π` from `ϑ`.**  The unweighted prime count is recovered from the logarithmically
weighted one by Abel summation.  This is the finite identity whose two terms Layer 6.2 estimates
in order to turn `ϑ(x) ∼ δx` into `π(x) ∼ δ Li(x)`. -/
theorem primeCount_eq_primeTheta_div_log_add_integral (S : Set (HeightOneSpectrum (𝓞 K)))
    (x : ℝ) :
    primeCount K S x = primeTheta K S x / Real.log x +
      ∫ t in Set.Ioc 2 x, primeTheta K S t / (t * Real.log t ^ 2) := by
  have hw : (fun v : HeightOneSpectrum (𝓞 K) ↦
      S.indicator (fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ)) v *
        (Real.log (Ideal.absNorm v.asIdeal : ℝ))⁻¹) =
      S.indicator (1 : HeightOneSpectrum (𝓞 K) → ℝ) := by
    funext v
    by_cases hv : v ∈ S
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, Pi.one_apply,
        mul_inv_cancel₀ (log_absNorm_asIdeal_pos v).ne']
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, zero_mul]
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) x, DifferentiableAt ℝ (fun u : ℝ ↦ (Real.log u)⁻¹) t :=
    fun t ht ↦ Real.differentiableAt_inv_log (by linarith [ht.1] : (0 : ℝ) < t).ne'
      (by linarith [ht.1] : (1 : ℝ) < t).ne' (by linarith [ht.1] : (-1 : ℝ) < t).ne'
  have hint : IntegrableOn (deriv fun u : ℝ ↦ (Real.log u)⁻¹) (Set.Icc (2 : ℝ) x) := by
    rw [Real.deriv_inv_log]
    refine ContinuousOn.integrableOn_Icc fun t ht ↦ ?_
    have ht0 : t ≠ 0 := (by linarith [ht.1] : (0 : ℝ) < t).ne'
    exact (((continuousAt_id.inv₀ ht0).neg).div ((Real.continuousAt_log ht0).pow 2)
      (pow_ne_zero 2 (Real.log_pos (by linarith [ht.1])).ne')).continuousWithinAt
  have key : primeCount K S x = (Real.log x)⁻¹ * primeTheta K S x -
      ∫ t in Set.Ioc (2 : ℝ) x, deriv (fun u : ℝ ↦ (Real.log u)⁻¹) t * primeTheta K S t := by
    simp only [primeCount_eq_primeSummatory, primeTheta_eq_primeSummatory]
    rw [← hw]
    exact primeSummatory_mul_eq_sub_integral_mul K _ x hdiff hint
  have hI : ∫ t in Set.Ioc (2 : ℝ) x, deriv (fun u : ℝ ↦ (Real.log u)⁻¹) t * primeTheta K S t =
      -∫ t in Set.Ioc (2 : ℝ) x, primeTheta K S t / (t * Real.log t ^ 2) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    have ht0 : t ≠ 0 := (by linarith [ht.1] : (0 : ℝ) < t).ne'
    have hlog : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    rw [Real.deriv_inv_log_apply]
    field_simp
  rw [key, hI]
  ring

end TauCeti
