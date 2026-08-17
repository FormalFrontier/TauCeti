/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Density
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
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
(`uniformMeasure_eq_zero_of_le`), not a probability measure. Every quantitative statement below
therefore takes `a < b` as a hypothesis rather than assuming it silently.

## Main definitions

* `TauCeti.Probability.uniformMeasure` — the uniform law on `Set.Ioc a b`;
* `TauCeti.Probability.uniformPDFReal` — the real-valued density. The `ℝ≥0∞`-valued density is
  Mathlib's `MeasureTheory.pdf.uniformPDF`, reused rather than redefined.

## Main results

* `isProbabilityMeasure_uniformMeasure` — it is a probability measure when `a < b`;
* `uniformMeasure_eq_smul`, `uniformMeasure_apply` — its description as a rescaled restriction, and
  evaluation on a measurable set;
* `isUniform_of_hasLaw_uniformMeasure` — a variable with this law is uniform in Mathlib's sense;
* `uniformMeasure_eq_withDensity` and `rnDeriv_uniformMeasure` — Mathlib's `pdf.uniformPDF` is the
  density of this measure, as a `withDensity` and as the Radon–Nikodym derivative;
* `hasPDF_of_hasLaw_uniformMeasure` — a variable with this law satisfies `HasPDF`, i.e. its law is
  absolutely continuous; the density itself is identified by the two results above;
* `uniformPDF_eq_ofReal_uniformPDFReal` — the bridge between that density and the real-valued one;
* `cdf_uniformMeasure` — the cdf is `0` below `a`, `1` above `b`, and `(x - a) / (b - a)` between;
* `integral_id_uniformMeasure` — the mean is `(a + b) / 2`;
* `variance_id_uniformMeasure` — the variance is `(b - a) ^ 2 / 12`.

## Implementation

`uniformMeasure_eq_smul` rewrites `cond` into `(ENNReal.ofReal (b - a))⁻¹ • volume.restrict …` by
computing `volume (Set.Ioc a b)`; every integral below is then an interval integral times a scalar.
The variance goes through `ProbabilityTheory.variance_eq_integral`, which asks only for
`AEMeasurable`, rather than through the second-moment formula, which would need an `MemLp _ 2`
side condition.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 0, item 3. The remaining
  targets of that item — `integrableExpSet`, the moment generating and cumulant generating
  functions, the characteristic function, the affine transport
  `(uniformMeasure 0 1).map (fun x => a + (b - a) * x) = uniformMeasure a b`, and parameter
  measurability — are not built here.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2, 2nd ed.,
  Wiley (1995), ch. 26.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

/-- The uniform probability measure on the interval `Set.Ioc a b`.

This is normalized Lebesgue measure on `Set.Ioc a b` when `a < b`, and the zero measure when
`b ≤ a`. Phrasing it through `ProbabilityTheory.cond` is what makes it agree definitionally with
Mathlib's `MeasureTheory.pdf.IsUniform`. -/
def uniformMeasure (a b : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Ioc a b)

/-- On a degenerate interval the uniform measure is the zero measure, not a probability measure. -/
@[simp]
theorem uniformMeasure_eq_zero_of_le {a b : ℝ} (hba : b ≤ a) : uniformMeasure a b = 0 := by
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

/-! ### The probability density function

Mathlib already supplies the `ℝ≥0∞`-valued density of a uniform law as
`MeasureTheory.pdf.uniformPDF s x μ = s.indicator ((μ s)⁻¹ • 1) x`, so none is introduced here —
the roadmap is explicit that no second pdf abstraction should enter the library. What is missing is
the real-valued form and the interval-specific identifications, which is what this section adds. -/

/-- The real-valued density of the uniform distribution on `Set.Ioc a b`.

Mathlib's `MeasureTheory.pdf.uniformPDF` is `ℝ≥0∞`-valued; this is the real-valued companion, and
`uniformPDF_eq_ofReal_uniformPDFReal` relates the two. -/
def uniformPDFReal (a b x : ℝ) : ℝ := if x ∈ Set.Ioc a b then (b - a)⁻¹ else 0

@[simp]
theorem uniformPDFReal_of_mem {a b x : ℝ} (hx : x ∈ Set.Ioc a b) :
    uniformPDFReal a b x = (b - a)⁻¹ := by simp [uniformPDFReal, hx]

@[simp]
theorem uniformPDFReal_of_notMem {a b x : ℝ} (hx : x ∉ Set.Ioc a b) :
    uniformPDFReal a b x = 0 := by simp [uniformPDFReal, hx]

theorem measurable_uniformPDFReal {a b : ℝ} : Measurable (uniformPDFReal a b) := by
  unfold uniformPDFReal
  exact measurable_const.ite measurableSet_Ioc measurable_const

/-- Mathlib's uniform density is the real one pushed into `ℝ≥0∞`.

No nondegeneracy hypothesis: inside the interval membership already forces `a < b`, and outside
both sides vanish. -/
theorem uniformPDF_eq_ofReal_uniformPDFReal {a b : ℝ} (x : ℝ) :
    pdf.uniformPDF (Set.Ioc a b) x volume = ENNReal.ofReal (uniformPDFReal a b x) := by
  rw [pdf.uniformPDF_ite, Real.volume_Ioc]
  by_cases hx : x ∈ Set.Ioc a b
  · have hab : a < b := lt_of_lt_of_le hx.1 hx.2
    rw [uniformPDFReal_of_mem hx, ENNReal.ofReal_inv_of_pos (sub_pos.mpr hab)]
    simp [hx]
  · rw [uniformPDFReal_of_notMem hx, ENNReal.ofReal_zero]
    simp [hx]

theorem measurable_uniformPDF_Ioc_volume {a b : ℝ} :
    Measurable fun x => pdf.uniformPDF (Set.Ioc a b) x volume := by
  unfold pdf.uniformPDF
  exact (measurable_const.smul measurable_const).indicator measurableSet_Ioc

/-- The uniform measure is Lebesgue measure weighted by Mathlib's uniform density.

No `a < b` hypothesis is needed: on a degenerate interval both sides are the zero measure. -/
theorem uniformMeasure_eq_withDensity {a b : ℝ} :
    uniformMeasure a b = volume.withDensity (fun x => pdf.uniformPDF (Set.Ioc a b) x volume) := by
  unfold pdf.uniformPDF
  rw [withDensity_indicator measurableSet_Ioc]
  simp only [Pi.smul_def, smul_eq_mul, Pi.one_apply, mul_one]
  rw [withDensity_const, uniformMeasure_eq_smul, Real.volume_Ioc]

/-- A random variable with the uniform law admits a density: its law is absolutely continuous with
respect to Lebesgue measure.

This gives `HasPDF` only. *Which* density it is, is `uniformMeasure_eq_withDensity`; on a degenerate
interval the law is the zero measure, so no probability-measure claim is made here. -/
theorem hasPDF_of_hasLaw_uniformMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {a b : ℝ} (hX : HasLaw X (uniformMeasure a b) P) :
    HasPDF X P :=
  hasPDF_of_map_eq_withDensity hX.aemeasurable _ measurable_uniformPDF_Ioc_volume.aemeasurable
    (by rw [hX.map_eq, uniformMeasure_eq_withDensity])

/-- The Radon-Nikodym derivative of the uniform measure against Lebesgue measure is its density. -/
theorem rnDeriv_uniformMeasure {a b : ℝ} :
    (uniformMeasure a b).rnDeriv volume
      =ᵐ[volume] fun x => pdf.uniformPDF (Set.Ioc a b) x volume := by
  rw [uniformMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity volume measurable_uniformPDF_Ioc_volume

/-! ### The cumulative distribution function, mean and variance -/

/-- The cumulative distribution function of the uniform distribution rises linearly across the
interval and is constant outside it. -/
theorem cdf_uniformMeasure {a b : ℝ} (hab : a < b) (x : ℝ) :
    cdf (uniformMeasure a b) x =
      if x ≤ a then 0 else if b ≤ x then 1 else (x - a) / (b - a) := by
  have := isProbabilityMeasure_uniformMeasure hab
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hne : ENNReal.ofReal (b - a) ≠ 0 := by simpa using hab
  have htop : ENNReal.ofReal (b - a) ≠ ⊤ := by simp
  have hset : Set.Iic x ∩ Set.Ioc a b = Set.Ioc a (min b x) := by
    ext y; simp [Set.mem_Iic, Set.mem_Ioc, and_comm]; tauto
  rw [cdf_eq_real, Measure.real, uniformMeasure_apply measurableSet_Iic, hset, Real.volume_Ioc]
  split_ifs with h1 h2
  · -- below the interval: the truncated interval is empty
    have hxb : x ≤ b := le_trans h1 hab.le
    have hxa : x - a ≤ 0 := by linarith
    have hzero : ENNReal.ofReal (x - a) = 0 := ENNReal.ofReal_eq_zero.mpr hxa
    rw [min_eq_right hxb, hzero, mul_zero, ENNReal.toReal_zero]
  · -- above the interval: the normalization cancels
    rw [min_eq_left h2, ENNReal.inv_mul_cancel hne htop, ENNReal.toReal_one]
  · -- inside: the linear rise
    have hax : a < x := lt_of_not_ge h1
    have hxb : x ≤ b := (not_le.mp h2).le
    rw [min_eq_right hxb, ← ENNReal.ofReal_inv_of_pos hba,
      ← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal (by positivity)]
    field_simp

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

/-! ### Exponential transforms

The uniform law has bounded support, so *every* exponential moment exists and the moment generating
function is finite on all of `ℝ`. The formulas split at `t = 0`: the quotient
`(exp (t * b) - exp (t * a)) / ((b - a) * t)` has a removable singularity there, and rather than
push a proof through it the value `1` is given directly. -/

/-- The uniform law is carried by its interval. -/
theorem ae_mem_Ioc_uniformMeasure {a b : ℝ} : ∀ᵐ x ∂uniformMeasure a b, x ∈ Set.Ioc a b := by
  rw [uniformMeasure_eq_smul]
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioc) _

/-- The uniform law is finite for every pair of endpoints: a probability measure when `a < b`, and
the zero measure otherwise. -/
instance isFiniteMeasure_uniformMeasure {a b : ℝ} : IsFiniteMeasure (uniformMeasure a b) := by
  rcases lt_or_ge a b with hab | hba
  · have : IsProbabilityMeasure (uniformMeasure a b) := isProbabilityMeasure_uniformMeasure hab
    infer_instance
  · rw [uniformMeasure_eq_zero_of_le hba]
    infer_instance

/-- **Every exponential moment of the uniform law exists.**

The support is bounded, so `exp (t * x)` is bounded above by `exp (|t| * max |a| |b|)` almost
everywhere, and the measure is finite. No hypothesis on the endpoints is needed. -/
@[simp]
theorem integrableExpSet_id_uniformMeasure {a b : ℝ} :
    integrableExpSet id (uniformMeasure a b) = Set.univ := by
  ext t
  simp only [Set.mem_univ, iff_true, integrableExpSet, Set.mem_ofPred_eq, id_eq]
  refine Integrable.mono' (integrable_const (Real.exp (|t| * max |a| |b|)))
    (Continuous.aestronglyMeasurable (by continuity)) ?_
  filter_upwards [ae_mem_Ioc_uniformMeasure (a := a) (b := b)] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ?_
  have hxb : |x| ≤ max |a| |b| := by
    rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]
      exact le_trans hx.2 (le_trans (le_abs_self b) (le_max_right _ _))
    · rw [h1]
      have h2 : -x ≤ -a := by linarith [hx.1]
      exact le_trans h2 (le_trans (neg_le_abs a) (le_max_left _ _))
  calc t * x ≤ |t * x| := le_abs_self _
    _ = |t| * |x| := abs_mul t x
    _ ≤ |t| * max |a| |b| := mul_le_mul_of_nonneg_left hxb (abs_nonneg t)

/-- The moment generating function of the uniform law at `0` is `1`.

Deliberately not `@[simp]`: `simp` already rewrites `mgf id μ 0` to `μ.real Set.univ`, so this
left-hand side is not in normal form and the repo's simpNF linter rejects the annotation. For a
probability measure `simp` then closes the goal on its own, which makes the annotation redundant as
well as ill-formed. -/
theorem mgf_id_uniformMeasure_zero {a b : ℝ} (hab : a < b) :
    mgf id (uniformMeasure a b) 0 = 1 := by
  have := isProbabilityMeasure_uniformMeasure hab
  simp [mgf]

/-- **The moment generating function of the uniform law**, away from the removable singularity. -/
theorem mgf_id_uniformMeasure {a b t : ℝ} (hab : a < b) (ht : t ≠ 0) :
    mgf id (uniformMeasure a b) t =
      (Real.exp (t * b) - Real.exp (t * a)) / ((b - a) * t) := by
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hint : ∫ x in Set.Ioc a b, Real.exp (t * x)
      = (Real.exp (t * b) - Real.exp (t * a)) / t := by
    rw [← intervalIntegral.integral_of_le hab.le,
      intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) ht]
    simp [integral_exp]
    field_simp
  rw [mgf, uniformMeasure_eq_smul, integral_smul_measure]
  simp only [id_eq]
  rw [hint, ENNReal.toReal_inv, ENNReal.toReal_ofReal hba.le, smul_eq_mul]
  field_simp

end Probability

end TauCeti
