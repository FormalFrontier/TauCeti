/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.CDF
public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta
public import TauCeti.Probability.Cdf
public import TauCeti.Probability.Distributions.NegativeBinomial.Basic
import TauCeti.Probability.Distributions.Dirac

/-!
# The negative-binomial cumulative distribution function

For a positive real shape `r` and a success probability `p` in `(0, 1]`, the cumulative mass of
the negative-binomial law through `k` is the regularized incomplete beta value `I_p(r, k + 1)`.
This is the discrete counterpart of the beta integral: it identifies the lower tail of a
negative-binomial law with a beta probability, so that questions about how much mass sits below a
cutoff become questions about the incomplete beta function.

Everything else here is read off from that identity.  The cdf of the real-valued pushforward is
zero below the origin and, at a nonnegative point `x`, is `I_p(r, ⌊x⌋₊ + 1)`, and the same
statement in `HasLaw` form measures the event `{X ≤ k}` for a negative-binomial random variable.

## Main results

* `TauCeti.Probability.negativeBinomialMeasure_real_Iic` computes the native cumulative mass;
* `TauCeti.Probability.cdf_map_cast_negativeBinomialMeasure` computes the cdf of the cast law;
* `TauCeti.Probability.measureReal_le_of_hasLaw_negativeBinomialMeasure` gives the corresponding
  random-variable statement.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 5.
* `TauCeti.Probability.Distributions.Poisson.Tail`, the in-repository formalization the cast-law
  cdf statements here are modelled on; the plumbing they share is `TauCeti.Probability.Cdf`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti

namespace Probability

variable {r p : ℝ}

/-- The cumulative mass of a negative-binomial law with positive shape is the corresponding
regularized incomplete beta value. -/
@[simp]
theorem negativeBinomialMeasure_real_Iic (hr : 0 < r) (hp : 0 < p) (hp1 : p ≤ 1) (k : ℕ) :
    (negativeBinomialMeasure r p).real (Iic k) =
      regularizedIncompleteBeta r (k + 1) p := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1
  induction k with
  | zero =>
      have hIic : (Iic 0 : Set ℕ) = {0} := Iic_bot
      rw [hIic, negativeBinomialMeasure_real_singleton hr.le hp hp1,
        negativeBinomialWeightReal_eq_coeff hr]
      norm_num
      exact regularizedIncompleteBeta_one_right hr hp.le hp1 |>.symm
  | succ k ih =>
      have hsplit : (Iic (k + 1) : Set ℕ) = Iic k ∪ {k + 1} := by
        rw [← Order.succ_eq_add_one, Order.Iic_succ, Set.insert_eq, Set.union_comm]
      have hdisj : Disjoint (Iic k : Set ℕ) {k + 1} := disjoint_singleton_right.mpr (by simp)
      have hstep := regularizedIncompleteBeta_add_one_right (a := r)
        (b := ((k + 1 : ℕ) : ℝ)) (x := p) hr (by positivity) hp.le hp1
      have hgammaFactorial : Real.Gamma ((k + 1 : ℕ) : ℝ) = (k.factorial : ℝ) := by
        simpa using Real.Gamma_nat_eq_factorial k
      have hgammaComm :
          Real.Gamma (((k + 1 : ℕ) : ℝ) + r) = Real.Gamma (r + ((k + 1 : ℕ) : ℝ)) := by
        rw [add_comm]
      have hcoeff :
          negativeBinomialWeightReal r p (k + 1) =
            p ^ r * (1 - p) ^ (((k + 1 : ℕ) : ℝ)) /
              (((k + 1 : ℕ) : ℝ) * beta r ((k + 1 : ℕ) : ℝ)) := by
        rw [negativeBinomialWeightReal_eq_gamma hr.ne', Real.rpow_eq_pow, ProbabilityTheory.beta,
          Real.rpow_natCast, hgammaFactorial, hgammaComm]
        have hgamma : Real.Gamma (r + ((k + 1 : ℕ) : ℝ)) ≠ 0 :=
          (Real.Gamma_pos_of_pos (by positivity)).ne'
        have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
        field_simp [hgamma, hfac]
        simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring
      rw [hsplit, measureReal_union hdisj .of_discrete, ih,
        negativeBinomialMeasure_real_singleton hr.le hp hp1, hcoeff]
      norm_num only [Nat.cast_add, Nat.cast_one] at hstep ⊢
      exact hstep.symm

/-- At shape zero, every native cumulative mass is one because the valid negative-binomial law is
the Dirac measure at zero. -/
theorem negativeBinomialMeasure_real_Iic_zero (hp : 0 < p) (hp1 : p ≤ 1) (k : ℕ) :
    (negativeBinomialMeasure 0 p).real (Iic k) = 1 := by
  rw [negativeBinomialMeasure_zero hp hp1, measureReal_def]
  simp

/-! ### The cast law -/

/-- The cdf of the real-valued negative-binomial law at a nonnegative point is the regularized
incomplete beta function evaluated at the natural floor of that point. -/
theorem cdf_map_cast_negativeBinomialMeasure (hr : 0 < r) (hp : 0 < p) (hp1 : p ≤ 1)
    {x : ℝ} (hx : 0 ≤ x) :
    cdf ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)) x =
      regularizedIncompleteBeta r (⌊x⌋₊ + 1) p := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1
  rw [cdf_map_natCast _ hx, negativeBinomialMeasure_real_Iic hr hp hp1]

/-- Below the origin, the cdf of the real-valued negative-binomial law vanishes, at the shape-zero
boundary as well: the law is carried by the natural numbers. -/
theorem cdf_map_cast_negativeBinomialMeasure_of_neg (hr : 0 ≤ r) (hp : 0 < p) (hp1 : p ≤ 1)
    {x : ℝ} (hx : x < 0) :
    cdf ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)) x = 0 := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr hp hp1
  exact cdf_map_natCast_of_neg _ hx

/-- At shape zero, the cdf of the real-valued negative-binomial law is the step function at the
origin. -/
theorem cdf_map_cast_negativeBinomialMeasure_zero (hp : 0 < p) (hp1 : p ≤ 1) (x : ℝ) :
    cdf ((negativeBinomialMeasure 0 p).map (Nat.cast : ℕ → ℝ)) x =
      if 0 ≤ x then 1 else 0 := by
  rw [negativeBinomialMeasure_zero hp hp1, Measure.map_dirac, Nat.cast_zero, cdf_dirac]

/-! ### Random-variable corollary -/

/-- A natural-valued random variable with a negative-binomial law is at most `k` with probability
`I_p(r, k + 1)`. -/
theorem measureReal_le_of_hasLaw_negativeBinomialMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℕ} (hX : HasLaw X (negativeBinomialMeasure r p) P)
    (hr : 0 < r) (hp : 0 < p) (hp1 : p ≤ 1) (k : ℕ) :
    P.real {ω | X ω ≤ k} = regularizedIncompleteBeta r (k + 1) p := by
  rw [hX.measureReal_eq (p := fun j : ℕ ↦ j ≤ k) .of_discrete, Iic_def]
  exact negativeBinomialMeasure_real_Iic hr hp hp1 k

end Probability

end TauCeti
