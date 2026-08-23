/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Elementary theory of the Bernoulli distribution

This file computes the elementary moments and transforms of the real-valued Bernoulli law
`Ber((1 : ℝ), 0, p)`. It uses Mathlib's convention that the value `1` has mass `p` and the value
`0` has mass `1 - p`.

## Main results

* `integral_id_bernoulliMeasure` and `variance_id_bernoulliMeasure` give the mean and variance;
* `integral_of_hasLaw_bernoulliMeasure` and `variance_of_hasLaw_bernoulliMeasure` give the
  corresponding random-variable statements;
* `mgf_id_bernoulliMeasure` and `cgf_id_bernoulliMeasure` compute the moment- and
  cumulant-generating functions;
* `charFun_bernoulliMeasure` computes the characteristic function.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 1, “Bernoulli and binomial”.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ProbabilityTheory unitInterval

namespace TauCeti

namespace Probability

/-- The mean of the real-valued Bernoulli law with success probability `p` is `p`. -/
@[simp]
theorem integral_id_bernoulliMeasure (p : I) :
    ∫ x, x ∂Ber((1 : ℝ), 0, p) = (p : ℝ) := by
  rw [integral_bernoulliMeasure]
  simp

/-- The variance of the real-valued Bernoulli law with success probability `p` is `p(1-p)`. -/
@[simp]
theorem variance_id_bernoulliMeasure (p : I) :
    Var[id; Ber((1 : ℝ), 0, p)] = (p : ℝ) * (1 - p) := by
  rw [variance_eq_integral (by fun_prop), integral_bernoulliMeasure]
  simp [integral_id_bernoulliMeasure]
  ring_nf

/-- A real-valued Bernoulli random variable with success probability `p` has mean `p`. -/
-- This cannot be a simp lemma because `p` does not occur on the left-hand side.
theorem integral_of_hasLaw_bernoulliMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {p : I} (hX : HasLaw X Ber((1 : ℝ), 0, p) P) : P[X] = (p : ℝ) := by
  rw [hX.integral_eq, integral_id_bernoulliMeasure]

/-- A real-valued Bernoulli random variable with success probability `p` has variance `p(1-p)`. -/
-- This cannot be a simp lemma because `p` does not occur on the left-hand side.
theorem variance_of_hasLaw_bernoulliMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {p : I} (hX : HasLaw X Ber((1 : ℝ), 0, p) P) :
    Var[X; P] = (p : ℝ) * (1 - p) := by
  rw [hX.variance_eq, variance_id_bernoulliMeasure]

/-- The moment-generating function of the real-valued Bernoulli law. -/
@[simp]
theorem mgf_id_bernoulliMeasure (p : I) (t : ℝ) :
    mgf id Ber((1 : ℝ), 0, p) t = 1 - (p : ℝ) + (p : ℝ) * Real.exp t := by
  rw [mgf, integral_bernoulliMeasure]
  simp
  ring_nf

/-- The moment-generating function of a real-valued Bernoulli law is strictly positive. -/
theorem mgf_id_bernoulliMeasure_pos (p : I) (t : ℝ) :
    0 < mgf id Ber((1 : ℝ), 0, p) t := by
  exact mgf_pos (integrable_bernoulliMeasure (1 : ℝ) 0 p fun x => Real.exp (t * id x))

/-- The cumulant-generating function of the real-valued Bernoulli law. -/
@[simp]
theorem cgf_id_bernoulliMeasure (p : I) (t : ℝ) :
    cgf id Ber((1 : ℝ), 0, p) t =
      Real.log (1 - (p : ℝ) + (p : ℝ) * Real.exp t) := by
  rw [cgf, mgf_id_bernoulliMeasure]

/-- The characteristic function of the real-valued Bernoulli law. -/
@[simp]
theorem charFun_bernoulliMeasure (p : I) (t : ℝ) :
    charFun Ber((1 : ℝ), 0, p) t =
      1 - (p : ℂ) + (p : ℂ) * Complex.exp (Complex.I * t) := by
  rw [charFun_apply_real, integral_bernoulliMeasure]
  simp
  ring_nf

end Probability

end TauCeti
