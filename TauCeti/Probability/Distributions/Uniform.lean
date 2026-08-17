/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The uniform distribution on an interval

`uniformMeasure a b` is normalized Lebesgue measure on `Set.Ioc a b`, defined as
`ProbabilityTheory.cond volume (Set.Ioc a b)`.

**Why `cond` and not a fresh normalization.** Mathlib defines `MeasureTheory.pdf.IsUniform X s ℙ μ`
as `μ.map X = ProbabilityTheory.cond μ s`. Defining the measure by the same `cond` makes the bridge
`isUniform_of_hasLaw_uniformMeasure` hold definitionally, so no second normalization convention
enters the library and nothing has to be reconciled later.

**Boundary.** For `b ≤ a` the interval is empty and `uniformMeasure a b` is the zero measure
(`uniformMeasure_of_le`), not a probability measure. Every quantitative statement below therefore
takes `a < b` as a hypothesis rather than assuming it silently.

## Main definitions

* `TauCeti.Probability.uniformMeasure` — the uniform law on `Set.Ioc a b`.

## Main results

* `isProbabilityMeasure_uniformMeasure` — it is a probability measure when `a < b`;
* `uniformMeasure_eq_smul`, `uniformMeasure_apply` — its `withDensity`-free description as a
  rescaled restriction, and evaluation on a measurable set;
* `isUniform_of_hasLaw_uniformMeasure` — a variable with this law is uniform in Mathlib's sense;
* `integral_id_uniformMeasure` — the mean is `(a + b) / 2`;
* `variance_id_uniformMeasure` — the variance is `(b - a) ^ 2 / 12`.

## Implementation

`uniformMeasure_eq_smul` rewrites `cond` into `(ENNReal.ofReal (b - a))⁻¹ • volume.restrict …` by
computing `volume (Set.Ioc a b)`; every integral below is then an interval integral times a scalar.
The variance goes through `ProbabilityTheory.variance_eq_integral`, which asks only for
`AEMeasurable`, rather than through the second-moment formula, which would need an `MemLp _ 2`
side condition.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 0, item 3. The probability
  density function, cdf, moment generating function, characteristic function, the affine transport
  `(uniformMeasure 0 1).map (fun x => a + (b - a) * x) = uniformMeasure a b`, and parameter
  measurability are further targets of that item and are not built here.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2, 2nd ed.,
  Wiley (1995), ch. 26.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

/-- The uniform probability measure on the interval `Set.Ioc a b`.

This is normalized Lebesgue measure on `Set.Ioc a b` when `a < b`, and the zero measure when
`b ≤ a`. Phrasing it through `ProbabilityTheory.cond` is what makes it agree definitionally with
Mathlib's `MeasureTheory.pdf.IsUniform`. -/
def uniformMeasure (a b : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Ioc a b)

/-- On a degenerate interval the uniform measure is the zero measure, not a probability measure. -/
theorem uniformMeasure_of_le {a b : ℝ} (hba : b ≤ a) : uniformMeasure a b = 0 := by
  rw [uniformMeasure, Set.Ioc_eq_empty (by simpa using hba)]
  simp [ProbabilityTheory.cond]

/-- The uniform measure is Lebesgue measure restricted to `Set.Ioc a b` and rescaled by the
interval length. -/
theorem uniformMeasure_eq_smul {a b : ℝ} :
    uniformMeasure a b = (ENNReal.ofReal (b - a))⁻¹ • volume.restrict (Set.Ioc a b) := by
  rw [uniformMeasure, ProbabilityTheory.cond, Real.volume_Ioc]

/-- Evaluation of the uniform measure on a measurable set. -/
theorem uniformMeasure_apply {a b : ℝ} {s : Set ℝ} (hs : MeasurableSet s) :
    uniformMeasure a b s = (ENNReal.ofReal (b - a))⁻¹ * volume (s ∩ Set.Ioc a b) := by
  rw [uniformMeasure_eq_smul, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs]

/-- On a nondegenerate interval the uniform measure is a probability measure. -/
theorem isProbabilityMeasure_uniformMeasure {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (uniformMeasure a b) :=
  cond_isProbabilityMeasure_of_finite
    (by rw [Real.volume_Ioc]; simpa using hab)
    (by rw [Real.volume_Ioc]; simp)

/-- A random variable with the uniform law is uniform in Mathlib's sense.

This holds by definition: both sides are `ProbabilityTheory.cond volume (Set.Ioc a b)`. -/
theorem isUniform_of_hasLaw_uniformMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {a b : ℝ} (hX : HasLaw X (uniformMeasure a b) P) :
    pdf.IsUniform X (Set.Ioc a b) P volume :=
  hX.map_eq

/-- The mean of the uniform distribution on `Set.Ioc a b` is the midpoint `(a + b) / 2`. -/
theorem integral_id_uniformMeasure {a b : ℝ} (hab : a < b) :
    ∫ x, x ∂uniformMeasure a b = (a + b) / 2 := by
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  rw [uniformMeasure_eq_smul, integral_smul_measure,
    ← intervalIntegral.integral_of_le hab.le]
  simp only [integral_id]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hba.le, smul_eq_mul]
  field_simp
  ring

/-- The variance of the uniform distribution on `Set.Ioc a b` is `(b - a) ^ 2 / 12`. -/
theorem variance_id_uniformMeasure {a b : ℝ} (hab : a < b) :
    variance id (uniformMeasure a b) = (b - a) ^ 2 / 12 := by
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  rw [variance_eq_integral measurable_id.aemeasurable]
  simp only [id_eq]
  rw [integral_id_uniformMeasure hab, uniformMeasure_eq_smul, integral_smul_measure,
    ← intervalIntegral.integral_of_le hab.le,
    intervalIntegral.integral_comp_sub_right (fun x => x ^ 2) ((a + b) / 2)]
  simp only [integral_pow]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hba.le, smul_eq_mul]
  field_simp
  ring

end Probability

end TauCeti
