/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta
public import Mathlib.Probability.Distributions.Binomial

/-!
# The binomial tail in closed form

For `m ≤ n` the mass a binomial law `Bin(n, p)` puts on `{k | m ≤ k}` is a single value of the
regularized incomplete beta function,

`Bin(n, p).real {k | m ≤ k} = I_p(m, n - m + 1)`.

This is the binomial entry of the "Closed-form cdfs and tails" target of
`TauCetiRoadmap/StandardDistributions/README.md`, Layer 2, and it is what supplies the cumulative
mass function that Layer 1 defers to Layer 2 for the binomial and Bernoulli laws.

The identity is proved by induction on `m` with `n` fixed. Removing the least point of the tail
subtracts the binomial weight `(n.choose m) * p ^ m * (1 - p) ^ (n - m)`, so the right-hand side
must satisfy the same recurrence, and it does: `I_p(m, n - m + 1)` and `I_p(m + 1, n - m)` are
neighbours along the antidiagonal `a + b = n + 1`, whose step
`TauCeti.regularizedIncompleteBeta_add_one_right_sub_add_one_left` has increment
`Γ(a + b + 1) / (Γ(a + 1) * Γ(b + 1))` times `p ^ a * (1 - p) ^ b`. At `a = m` and `b = n - m` that
generalized binomial coefficient is `n.choose m`, by
`Nat.choose_mul_factorial_mul_factorial`.

The induction starts at `m = 0`, where the tail is everything and the left-hand side is `1`. This
is the one place the boundary convention `I_x(0, b) = 1` of `TauCeti.regularizedIncompleteBeta`
is used, and it is the completion check the roadmap states for this target: at `m = 0` the
identity reads `1 = 1` for every admissible `p`, including `p = 0` and `p = 1`.

## Main results

* `TauCeti.binomial_tail_eq_regularizedIncompleteBeta` — the tail `I_p(m, n - m + 1)`;
* `TauCeti.sum_Icc_choose_mul_pow_eq_regularizedIncompleteBeta` — the same identity written as a
  partial sum of binomial weights, which is the classical form;
* `TauCeti.binomial_cumulative_eq_regularizedIncompleteBeta` — the complementary cumulative mass
  `I_{1-p}(n - m, m + 1)`.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 2, the "Closed-form cdfs and
  tails" target.
* *NIST Digital Library of Mathematical Functions*, [§8.17(v)](https://dlmf.nist.gov/8.17.v).
* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley, 2005,
  §3.4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti

variable {m n : ℕ}

/-- Removing the least point of an upper tail of a binomial law subtracts one binomial weight. -/
private lemma measureReal_Ici_binomial_succ (n m : ℕ) (p : unitInterval) :
    Bin(n, p).real (Ici (m + 1)) =
      Bin(n, p).real (Ici m) - (n.choose m : ℝ) * (p : ℝ) ^ m * (1 - p) ^ (n - m) := by
  have hsplit : ({m} : Set ℕ) ∪ Ici (m + 1) = Ici m := by
    ext k
    simp only [mem_union, mem_singleton_iff, mem_Ici]
    omega
  have hdisj : Disjoint ({m} : Set ℕ) (Ici (m + 1)) :=
    disjoint_singleton_left.2 (by simp)
  have hadd := measureReal_union (μ := Bin(n, p)) hdisj (.of_discrete)
  rw [hsplit, binomial_real_singleton] at hadd
  linarith

/-- The tail identity, proved by induction on the left endpoint. -/
private lemma measureReal_Ici_binomial (n : ℕ) (p : unitInterval) : ∀ m : ℕ, m ≤ n →
    Bin(n, p).real (Ici m) = regularizedIncompleteBeta m ((n : ℝ) - m + 1) (p : ℝ) := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := unitInterval.nonneg p
  have hp1 : (p : ℝ) ≤ 1 := unitInterval.le_one p
  intro m
  induction m with
  | zero =>
    intro _
    have huniv : (Ici (0 : ℕ)) = univ := by ext k; simp
    rw [huniv, probReal_univ, Nat.cast_zero, sub_zero]
    exact (regularizedIncompleteBeta_zero_left (by positivity) hp0).symm
  | succ m ih =>
    intro hmn
    have hmn' : m ≤ n := by omega
    have hcast : ((m : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hsub : (n : ℝ) - m = ((n - m : ℕ) : ℝ) := (Nat.cast_sub hmn').symm
    have hb : (0 : ℝ) < (n : ℝ) - m := by linarith
    have hstep := regularizedIncompleteBeta_add_one_right_sub_add_one_left
      (Nat.cast_nonneg m) hb hp0 hp1
    -- the increment of the antidiagonal step is the `m`-th binomial coefficient
    have hfac : (n.choose m : ℝ) * (m.factorial : ℝ) * ((n - m).factorial : ℝ) =
        (n.factorial : ℝ) := by
      exact_mod_cast congrArg (Nat.cast (R := ℝ)) (Nat.choose_mul_factorial_mul_factorial hmn')
    have hgamma_arg : (m : ℝ) + ((n : ℝ) - m) + 1 = (n : ℝ) + 1 := by ring
    have hcoeff : Real.Gamma ((m : ℝ) + ((n : ℝ) - m) + 1) /
        (Real.Gamma ((m : ℝ) + 1) * Real.Gamma ((n : ℝ) - m + 1)) = (n.choose m : ℝ) := by
      have hm0 : ((m.factorial : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 m.factorial_ne_zero
      have hnm0 : (((n - m).factorial : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (n - m).factorial_ne_zero
      rw [hgamma_arg, hsub,
        Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
        div_eq_iff (mul_ne_zero hm0 hnm0)]
      linarith
    have hpow : ((p : ℝ)) ^ ((m : ℝ)) = (p : ℝ) ^ m := Real.rpow_natCast _ m
    have hpow' : (1 - (p : ℝ)) ^ ((n : ℝ) - m) = (1 - (p : ℝ)) ^ (n - m) := by
      rw [hsub, Real.rpow_natCast]
    rw [hcoeff, hpow, hpow'] at hstep
    have hsub_succ : (n : ℝ) - ((m : ℝ) + 1) + 1 = (n : ℝ) - m := by ring
    rw [measureReal_Ici_binomial_succ, ih hmn', Nat.cast_add, Nat.cast_one, hsub_succ]
    linear_combination hstep

/-- **The binomial tail is a regularized incomplete beta value.** For `m ≤ n` the mass that
`Bin(n, p)` puts on `{k | m ≤ k}` is `I_p(m, n - m + 1)`.

At `m = 0` both sides are `1`: the left-hand side because `Bin(n, p)` is a probability measure,
the right-hand side by the boundary convention `I_x(0, b) = 1` built into
`TauCeti.regularizedIncompleteBeta`. -/
@[simp]
theorem binomial_tail_eq_regularizedIncompleteBeta (hmn : m ≤ n) (p : unitInterval) :
    Bin(n, p).real {k | m ≤ k} = regularizedIncompleteBeta m ((n : ℝ) - m + 1) (p : ℝ) :=
  measureReal_Ici_binomial n p m hmn

/-- The classical form of the tail identity: a partial sum of binomial weights is a value of the
regularized incomplete beta function. -/
theorem sum_Icc_choose_mul_pow_eq_regularizedIncompleteBeta (hmn : m ≤ n) (p : unitInterval) :
    ∑ k ∈ Finset.Icc m n, (n.choose k : ℝ) * (p : ℝ) ^ k * (1 - p) ^ (n - k) =
      regularizedIncompleteBeta m ((n : ℝ) - m + 1) (p : ℝ) := by
  rw [← binomial_tail_eq_regularizedIncompleteBeta hmn p,
    ← integral_indicator_one (μ := Bin(n, p)) (s := {k | m ≤ k}) .of_discrete, integral_binomial,
    ← Finset.sum_subset Finset.Icc_subset_Iic_self]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Set.indicator_of_mem (by simpa using (Finset.mem_Icc.1 hk).1)]
    simp
  · intro k hk hk'
    have : k < m := by
      simp only [Finset.mem_Iic] at hk
      simp only [Finset.mem_Icc, not_and] at hk'
      omega
    rw [Set.indicator_of_notMem (by simpa using this)]
    simp

/-- The cumulative mass of a binomial law, the complement of the tail identity: for `m ≤ n`,
`Bin(n, p).real {k | k ≤ m} = I_{1-p}(n - m, m + 1)`.

This is the cumulative mass function that `TauCetiRoadmap/StandardDistributions/README.md`,
Layer 1 defers to this layer. -/
@[simp]
theorem binomial_cumulative_eq_regularizedIncompleteBeta (hmn : m ≤ n) (p : unitInterval) :
    Bin(n, p).real {k | k ≤ m} =
      regularizedIncompleteBeta ((n : ℝ) - m) ((m : ℝ) + 1) (1 - (p : ℝ)) := by
  rcases hmn.eq_or_lt with rfl | hmn
  · have hsupport : {k : ℕ | k ≤ m} =ᵐ[Bin(m, p)] Set.univ := by
      filter_upwards [ae_le_of_hasLaw_binomial (P := Bin(m, p)) HasLaw.id] with k hk
      apply propext
      exact iff_true_intro hk
    rw [measureReal_congr hsupport, probReal_univ, sub_self,
      regularizedIncompleteBeta_zero_left (by positivity)
        (by exact sub_nonneg.mpr (unitInterval.le_one p))]
  have hcast : ((m : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hb : (0 : ℝ) < (n : ℝ) - m := by linarith
  have hcompl : {k : ℕ | k ≤ m}ᶜ = {k : ℕ | m + 1 ≤ k} := by
    ext k
    simp only [mem_compl_iff, mem_ofPred_eq, not_le]
    omega
  have htail := binomial_tail_eq_regularizedIncompleteBeta (m := m + 1) hmn p
  have hsub_succ : (n : ℝ) - ((m : ℝ) + 1) + 1 = (n : ℝ) - m := by ring
  rw [Nat.cast_add, Nat.cast_one, hsub_succ] at htail
  have hsymm := regularizedIncompleteBeta_symm (by linarith : (0 : ℝ) < (m : ℝ) + 1) hb (p : ℝ)
  have := measureReal_compl (μ := Bin(n, p)) (s := {k : ℕ | k ≤ m}) .of_discrete
  rw [hcompl, htail, probReal_univ] at this
  linarith

end TauCeti
