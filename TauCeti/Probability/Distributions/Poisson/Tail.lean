/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# The cumulative masses of a Poisson law in closed form

For a rate `r : ℝ≥0` the Poisson law `Po(r)` on `ℕ` assigns to the upper tail `{k | n < k}` the
value `P(n + 1, r)` of the regularized lower incomplete gamma function `TauCeti.regularizedGamma`,
and to the complementary lower half-line the value `1 - P(n + 1, r)`.

This is the Poisson entry of the closed-form cdf and tail target of
`TauCetiRoadmap/StandardDistributions/README.md`, Layer 2. It also supplies the native
cumulative-mass formula that the Poisson family entry of Layer 4 asks for, together with the cdf
of the cast law `Po(ℝ, r)` that the same entry derives from it.

The proof is an induction on `n` that needs no integral of its own. Stripping the atom at `n + 1`
off the tail above `n` decreases its mass by `exp (-r) * r ^ (n + 1) / (n + 1)!`, while
`TauCeti.regularizedGamma_add_one` decreases `P(n + 1, r)` by
`r ^ (n + 1) * exp (-r) / Γ(n + 2)`; the two decrements agree because
`Real.Gamma_nat_eq_factorial` identifies `Γ(n + 2)` with `(n + 1)!`. The induction starts at the
tail above `0`, whose mass `1 - exp (-r)` is `P(1, r)` by `TauCeti.regularizedGamma_one`.

Read the other way round, the resulting identity is the classical duality between a Poisson law of
rate `r` and a gamma law of integer shape: a Poisson variable of rate `r` exceeds `n` exactly as
often as the `(n + 1)`-st arrival of a unit-rate Poisson process occurs before time `r`, which is
the event `TauCeti.measureReal_Iic_gammaMeasure` measures.

## Main results

* `TauCeti.poissonMeasure_tail_eq_regularizedGamma` — the upper tail `Po(r) {k | n < k}` is
  `P(n + 1, r)`;
* `TauCeti.poissonMeasure_real_Iic` — the complementary cumulative mass `1 - P(n + 1, r)`;
* `TauCeti.sum_range_poissonMeasure_real_singleton` — the same identity written as the classical
  partial sum `∑ k ≤ n, exp (-r) * r ^ k / k !`;
* `TauCeti.cdf_map_cast_poissonMeasure` — the cumulative distribution function of the real-valued
  law `Po(ℝ, r)`, a step function with its jumps at the natural numbers;
* `TauCeti.measureReal_lt_of_hasLaw_poissonMeasure` and
  `TauCeti.measureReal_le_of_hasLaw_poissonMeasure` — the random-variable corollaries.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley, 2005,
  chapter 4.
-/

public section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal Nat

namespace TauCeti

variable {r : ℝ≥0} {n : ℕ}

/-! ### Stripping one atom at a time -/

/-- The Poisson tail above `n + 1` is the tail above `n` with the atom at `n + 1` removed, so it is
smaller by the Poisson mass `exp (-r) * r ^ (n + 1) / (n + 1)!` of that atom. -/
theorem poissonMeasure_real_tail_succ (r : ℝ≥0) (n : ℕ) :
    Po(r).real {k | n + 1 < k} =
      Po(r).real {k | n < k} - exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / (n + 1)! := by
  have hsplit : ({n + 1} : Set ℕ) ∪ {k | n + 1 < k} = {k | n < k} := by
    ext k
    simp only [mem_union, mem_singleton_iff, mem_ofPred_eq]
    omega
  have hdisj : Disjoint ({n + 1} : Set ℕ) {k | n + 1 < k} := by
    rw [Set.disjoint_left]
    intro k hk hk'
    rw [mem_singleton_iff] at hk
    rw [mem_ofPred_eq] at hk'
    omega
  have hunion := measureReal_union (μ := Po(r)) hdisj .of_discrete
  rw [hsplit, poissonMeasure_real_singleton] at hunion
  rw [hunion]
  ring

/-- A Poisson law of rate `r` puts mass `1 - exp (-r)` on the positive integers: only the atom at
`0` is left out. -/
theorem poissonMeasure_real_tail_zero (r : ℝ≥0) :
    Po(r).real {k | 0 < k} = 1 - exp (-(r : ℝ)) := by
  have hcompl : {k : ℕ | 0 < k} = ({0} : Set ℕ)ᶜ := by
    ext k
    simp only [mem_ofPred_eq, mem_compl_iff, mem_singleton_iff]
    omega
  rw [hcompl, probReal_compl_eq_one_sub .of_discrete, poissonMeasure_real_singleton]
  simp

/-! ### The closed form -/

/-- **The Poisson tail in closed form.** For a rate `r : ℝ≥0` and `n : ℕ`, the mass a Poisson law
assigns to `{k | n < k}` is the value `P(n + 1, r)` of the regularized lower incomplete gamma
function. -/
@[simp]
theorem poissonMeasure_tail_eq_regularizedGamma (r : ℝ≥0) (n : ℕ) :
    Po(r).real {k | n < k} = regularizedGamma (n + 1) (r : ℝ) := by
  have hr : (0 : ℝ) ≤ r := r.coe_nonneg
  induction n with
  | zero => rw [poissonMeasure_real_tail_zero, Nat.cast_zero, zero_add, regularizedGamma_one hr]
  | succ n ih =>
    have hs : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    -- the two decrements: `r ^ (n + 1)` as an `rpow` on the right, as a `Monoid.npow` on the left,
    -- and `Γ(n + 2) = (n + 1)!`
    have hpow : (r : ℝ) ^ ((n : ℝ) + 1) = (r : ℝ) ^ (n + 1) := by
      rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    have hgamma : Real.Gamma ((n : ℝ) + 1 + 1) = ((n + 1)! : ℝ) := by
      rw [show (n : ℝ) + 1 + 1 = ((n + 1 : ℕ) : ℝ) + 1 by push_cast; ring,
        Real.Gamma_nat_eq_factorial]
    rw [poissonMeasure_real_tail_succ, ih, show ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 1 + 1 by
      push_cast; ring, regularizedGamma_add_one hs hr, hpow, hgamma]
    ring

/-- The cumulative mass of a Poisson law, complementary to
`TauCeti.poissonMeasure_tail_eq_regularizedGamma`. -/
@[simp]
theorem poissonMeasure_real_Iic (r : ℝ≥0) (n : ℕ) :
    Po(r).real (Iic n) = 1 - regularizedGamma (n + 1) (r : ℝ) := by
  have hcompl : (Iic n : Set ℕ) = {k | n < k}ᶜ := by
    ext k
    simp only [mem_Iic, mem_compl_iff, mem_ofPred_eq, not_lt]
  rw [hcompl, probReal_compl_eq_one_sub .of_discrete, poissonMeasure_tail_eq_regularizedGamma]

/-- The classical partial-sum form of `TauCeti.poissonMeasure_real_Iic`: the first `n + 1` Poisson
masses sum to `1 - P(n + 1, r)`. Expanding the summand with
`ProbabilityTheory.poissonMeasure_real_singleton` writes the left-hand side as
`∑ k ≤ n, exp (-r) * r ^ k / k !`. -/
theorem sum_range_poissonMeasure_real_singleton (r : ℝ≥0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Po(r).real {k} = 1 - regularizedGamma (n + 1) (r : ℝ) := by
  rw [← poissonMeasure_real_Iic]
  induction n with
  | zero =>
    rw [show Iic (0 : ℕ) = {0} from Iic_bot]
    simp
  | succ n ih =>
    have hsplit : (Iic (n + 1) : Set ℕ) = Iic n ∪ {n + 1} := by
      ext k
      simp only [mem_union, mem_singleton_iff, mem_Iic]
      omega
    have hdisj : Disjoint (Iic n : Set ℕ) {n + 1} := by
      rw [Set.disjoint_left]
      intro k hk hk'
      rw [mem_Iic] at hk
      rw [mem_singleton_iff] at hk'
      omega
    rw [Finset.sum_range_succ, ih, hsplit, measureReal_union hdisj .of_discrete]

/-! ### The cast law -/

/-- The cumulative distribution function of the real-valued Poisson law `Po(ℝ, r)` at a
nonnegative point: it is the step function `1 - P(⌊x⌋₊ + 1, r)`. -/
theorem cdf_map_cast_poissonMeasure (r : ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    cdf Po(ℝ, r) x = 1 - regularizedGamma (⌊x⌋₊ + 1) (r : ℝ) := by
  have hpre : (Nat.cast : ℕ → ℝ) ⁻¹' Iic x = Iic ⌊x⌋₊ := by
    ext k
    simp only [mem_preimage, mem_Iic]
    exact (Nat.le_floor_iff hx).symm
  rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic, hpre,
    poissonMeasure_real_Iic]

/-- Below the origin the cumulative distribution function of `Po(ℝ, r)` vanishes: a Poisson law is
carried by the natural numbers. -/
theorem cdf_map_cast_poissonMeasure_of_neg (r : ℝ≥0) {x : ℝ} (hx : x < 0) :
    cdf Po(ℝ, r) x = 0 := by
  have hpre : (Nat.cast : ℕ → ℝ) ⁻¹' Iic x = ∅ := by
    ext k
    simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
    exact lt_of_lt_of_le hx (Nat.cast_nonneg k)
  rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic, hpre, measureReal_empty]

/-! ### Random-variable corollaries -/

/-- A random variable with a Poisson law of rate `r` exceeds `n` with probability `P(n + 1, r)`. -/
theorem measureReal_lt_of_hasLaw_poissonMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℕ} (hX : HasLaw X Po(r) P) (n : ℕ) :
    P.real {ω | n < X ω} = regularizedGamma (n + 1) (r : ℝ) := by
  rw [hX.measureReal_eq (p := fun k : ℕ => n < k) .of_discrete]
  exact poissonMeasure_tail_eq_regularizedGamma r n

/-- A random variable with a Poisson law of rate `r` is at most `n` with probability
`1 - P(n + 1, r)`. -/
theorem measureReal_le_of_hasLaw_poissonMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℕ} (hX : HasLaw X Po(r) P) (n : ℕ) :
    P.real {ω | X ω ≤ n} = 1 - regularizedGamma (n + 1) (r : ℝ) := by
  rw [hX.measureReal_eq (p := fun k : ℕ => k ≤ n) .of_discrete, Iic_def]
  exact poissonMeasure_real_Iic r n

end TauCeti
