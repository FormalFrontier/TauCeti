/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Probability-generating functions

This file defines the probability-generating function of a natural-number-valued random variable
and establishes its basic measure-theoretic API.  The central results relate it to Mathlib's
moment-generating function and show that it turns sums of independent random variables into
products.  The file then computes the generating functions of the standard discrete families:
Bernoulli, binomial, Poisson, and geometric, the last one on its exact integrability domain.

These results implement the definition, the generic API and the distribution-specific formulas of
the probability-generating-function target in `TauCetiRoadmap/StandardDistributions/README.md`,
Layer 1.  Recovering the coefficients at the origin, and the resulting uniqueness theorem, remain
future work.

The Poisson series calculation follows the proof pattern of Mathlib's
`ProbabilityTheory.charFun_map_cast_poissonMeasure`: both factor the Poisson weights out of the
exponential power series.  The Bernoulli, binomial, and geometric calculations use Mathlib's
corresponding measure-integral formulas directly.

## Main declarations

* `TauCeti.Probability.pgf` — the probability-generating function.
* `TauCeti.Probability.pgf_exp` — evaluation at `exp t` is a moment-generating function.
* `TauCeti.Probability.integrable_pow_of_abs_le_one` — on the closed unit interval the integrand is
  integrable under a finite measure.
* `TauCeti.Probability.IndepFun.pgf_add` and `TauCeti.Probability.iIndepFun.pgf_sum` —
  multiplicativity over binary and finite sums of independent random variables.
* `TauCeti.Probability.pgf_bernoulliMeasure`, `pgf_binomial`, `pgf_poissonMeasure`, and
  `pgf_geometricMeasure` — the standard discrete-family formulas.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The probability-generating function of a natural-number-valued random variable `X` with
respect to a measure `μ`. -/
def pgf (X : Ω → ℕ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  ∫ ω, t ^ X ω ∂μ

/-- The defining integral formula for the probability-generating function.  This is the canonical
way to unfold `pgf`, which is otherwise sealed. -/
-- The parentheses around `rfl` opt this proof out of the exported-theorem exposure check, which
-- keeps `pgf` itself sealed.
theorem pgf_def (X : Ω → ℕ) (μ : Measure Ω) (t : ℝ) : pgf X μ t = ∫ ω, t ^ X ω ∂μ := (rfl)

/-- The probability-generating function is unchanged by replacing the random variable almost
everywhere. -/
theorem pgf_congr_ae {X Y : Ω → ℕ} (hXY : X =ᵐ[μ] Y) : pgf X μ = pgf Y μ := by
  funext t
  exact integral_congr_ae (hXY.fun_comp fun n => t ^ n)

/-- The probability-generating function of the zero measure vanishes. -/
@[simp]
theorem pgf_zero_measure (X : Ω → ℕ) : pgf X (0 : Measure Ω) = 0 := by
  funext t
  simp [pgf_def]

/-- Evaluation of a probability-generating function at one gives the total mass. -/
@[simp]
theorem pgf_one (X : Ω → ℕ) : pgf X μ 1 = μ.real Set.univ := by
  simp [pgf_def]

/-- A constant natural-number-valued random variable has the expected monomial generating
function. -/
@[simp]
theorem pgf_const (n : ℕ) (t : ℝ) : pgf (fun _ : Ω => n) μ t = μ.real Set.univ * t ^ n := by
  simp [pgf_def]

/-- The probability-generating function can be computed on the law of the random variable. -/
theorem pgf_map {X : Ω → ℕ} (hX : AEMeasurable X μ) (t : ℝ) :
    pgf id (μ.map X) t = pgf X μ t := by
  rw [pgf_def, pgf_def, integral_map hX (measurable_id.const_pow t).aestronglyMeasurable]
  simp only [id_eq]

/-- Random variables with a given law have the same probability-generating function as that law. -/
theorem HasLaw.pgf_eq {X : Ω → ℕ} {ν : Measure ℕ} (hX : HasLaw X ν μ) (t : ℝ) :
    pgf X μ t = pgf id ν t := by
  rw [← hX.map_eq, pgf_map hX.aemeasurable]

/-- Evaluating the probability-generating function at `exp t` recovers the moment-generating
function of the real-valued cast of the random variable. -/
theorem pgf_exp (X : Ω → ℕ) (μ : Measure Ω) (t : ℝ) :
    pgf X μ (Real.exp t) = mgf (fun ω => (X ω : ℝ)) μ t := by
  simp only [pgf_def, mgf, ← Real.exp_nat_mul]
  congr 1
  funext ω
  rw [Nat.cast_comm, mul_comm]

/-- For a finite measure, the integrand of a probability-generating function is integrable on the
closed unit interval. -/
theorem integrable_pow_of_abs_le_one [IsFiniteMeasure μ] {X : Ω → ℕ} (hX : AEMeasurable X μ)
    {t : ℝ} (ht : |t| ≤ 1) : Integrable (fun ω => t ^ X ω) μ := by
  refine (integrable_const (1 : ℝ)).mono' (hX.const_pow t).aestronglyMeasurable ?_
  filter_upwards with ω
  simpa only [Real.norm_eq_abs, abs_pow, norm_one] using pow_le_one₀ (abs_nonneg t) ht

/-- The probability-generating function of a sum of two independent natural-number-valued random
variables is the product of their generating functions. -/
theorem IndepFun.pgf_add {X Y : Ω → ℕ} (hXY : IndepFun X Y μ) (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (t : ℝ) :
    pgf (X + Y) μ t = pgf X μ t * pgf Y μ t := by
  have hindep : IndepFun (fun ω => t ^ X ω) (fun ω => t ^ Y ω) μ :=
    hXY.comp (measurable_id.const_pow t) (measurable_id.const_pow t)
  simp_rw [pgf_def, Pi.add_apply, pow_add]
  exact hindep.integral_mul_eq_mul_integral (hX.const_pow t).aestronglyMeasurable
    (hY.const_pow t).aestronglyMeasurable

/-- A probability-generating function turns a finite sum of independent random variables into the
product of their generating functions. -/
theorem iIndepFun.pgf_sum {ι : Type*} {X : ι → Ω → ℕ} (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, AEMeasurable (X i) μ) (s : Finset ι) (t : ℝ) :
    pgf (∑ i ∈ s, X i) μ t = ∏ i ∈ s, pgf (X i) μ t := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  classical
  induction s using Finset.induction_on with
  | empty => simp [pgf_def]
  | insert i s hi hrec =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        IndepFun.pgf_add (h_indep.indepFun_finsetSum_of_notMem₀ h_meas hi).symm (h_meas i)
          (Finset.aemeasurable_sum s fun j _ => h_meas j) t, hrec]

section NamedDistributions

open scoped NNReal ProbabilityTheory unitInterval

/-- The probability-generating function of a Bernoulli distribution. -/
theorem pgf_bernoulliMeasure (p : unitInterval) (t : ℝ) :
    pgf id Ber((1 : ℕ), 0, p) t = 1 - (p : ℝ) + (p : ℝ) * t := by
  rw [pgf_def, integral_bernoulliMeasure]
  simp
  ring

/-- The probability-generating function of a binomial distribution. -/
theorem pgf_binomial (n : ℕ) (p : unitInterval) (t : ℝ) :
    pgf id (binomial n p) t = (1 - (p : ℝ) + (p : ℝ) * t) ^ n := by
  -- `add_pow` expands `(x + y) ^ n` with the binomial weights attached to `x`, so the base has to
  -- be reordered to put the factor `p * t` first.
  have hbase : 1 - (p : ℝ) + (p : ℝ) * t = (p : ℝ) * t + (1 - (p : ℝ)) := add_comm _ _
  rw [pgf_def, integral_binomial, ← Nat.range_succ_eq_Iic, hbase, add_pow]
  simp only [smul_eq_mul, id_eq]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The probability-generating function of a Poisson distribution. -/
theorem pgf_poissonMeasure (r : ℝ≥0) (t : ℝ) :
    pgf id (poissonMeasure r) t = Real.exp ((r : ℝ) * (t - 1)) := by
  rw [pgf_def, integral_poissonMeasure]
  simp only [smul_eq_mul, id_eq]
  calc
    ∑' n : ℕ, (Real.exp (-r) * (r : ℝ) ^ n / n.factorial) * t ^ n =
        Real.exp (-r) * ∑' n : ℕ, (((r : ℝ) * t) ^ n / n.factorial) := by
      rw [← tsum_mul_left]
      congr with n
      rw [mul_pow]
      ring
    _ = Real.exp (-r) * Real.exp ((r : ℝ) * t) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * t)).tsum_eq, Real.exp_eq_exp_ℝ]
    _ = Real.exp ((r : ℝ) * (t - 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- At the zero parameter, Mathlib's geometric distribution is a Dirac mass at zero, so its
probability-generating function is identically one. -/
@[simp]
theorem pgf_geometricMeasure_zero (t : ℝ) : pgf id (geometricMeasure 0) t = 1 := by
  simp [pgf_def, geometricMeasure]

/-- For a nonzero success probability, the geometric probability-generating-function integrand
is integrable exactly on the open interval determined by the geometric-series ratio. -/
theorem integrable_pow_geometricMeasure_iff {p : unitInterval} (hp : p ≠ 0) (t : ℝ) :
    Integrable (fun n : ℕ => t ^ n) (geometricMeasure p) ↔
      |(1 - (p : ℝ)) * t| < 1 := by
  rw [integrable_geometricMeasure_iff hp]
  have hp0 : (p : ℝ) ≠ 0 := by simpa using hp
  have hfun : (fun n : ℕ => (1 - (p : ℝ)) ^ n * p * ‖t ^ n‖) =
      fun n : ℕ => ((1 - (p : ℝ)) * |t|) ^ n * p := by
    funext n
    rw [Real.norm_eq_abs, abs_pow, mul_pow]
    ring
  rw [hfun, summable_mul_right_iff hp0, summable_geometric_iff_norm_lt_one,
    Real.norm_eq_abs]
  simp only [abs_mul, abs_abs, abs_of_nonneg (by grind : 0 ≤ 1 - (p : ℝ))]

/-- The probability-generating function of a geometric distribution with nonzero parameter, on its
exact integrability domain.  The boundary case `p = 1`, whose law is a Dirac mass at zero, is
included. -/
theorem pgf_geometricMeasure {p : unitInterval} (hp : p ≠ 0) {t : ℝ}
    (ht : |(1 - (p : ℝ)) * t| < 1) :
    pgf id (geometricMeasure p) t = (p : ℝ) / (1 - (1 - (p : ℝ)) * t) := by
  rw [pgf_def, integral_geometricMeasure hp]
  simp only [smul_eq_mul, id_eq]
  calc
    ∑' n : ℕ, ((1 - (p : ℝ)) ^ n * p) * t ^ n =
        (p : ℝ) * ∑' n : ℕ, ((1 - (p : ℝ)) * t) ^ n := by
      rw [← tsum_mul_left]
      congr with n
      rw [mul_pow]
      ring
    _ = (p : ℝ) * (1 - (1 - (p : ℝ)) * t)⁻¹ := by
      rw [tsum_geometric_of_norm_lt_one]
      simpa only [Real.norm_eq_abs] using ht
    _ = (p : ℝ) / (1 - (1 - (p : ℝ)) * t) := by rw [div_eq_mul_inv]

end NamedDistributions

end Probability

end TauCeti
