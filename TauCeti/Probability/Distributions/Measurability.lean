/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.Distributions.Cauchy
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.Probability.Distributions.Pareto
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Measurability of the standard families in their parameters

A distribution is a family of measures indexed by its parameters, and `MeasureTheory.Measure α`
carries the Giry measurable structure. This file proves parameter measurability for Mathlib's
Gamma, exponential, Beta, Pareto, Gaussian, Cauchy, Poisson, geometric, Bernoulli and binomial
scalar laws, which is exactly what a consumer needs in order to package them as
`ProbabilityTheory.Kernel`s.

## Two mechanisms

The absolutely continuous families are all `volume.withDensity` of their density, so they are
handled once and for all by Mathlib's `MeasureTheory.measurable_withDensity`: it is enough
to know that the density is measurable **jointly** in the parameters and the point. That is the
content of the `measurable_uncurry_...` lemmas below, and it is a genuinely stronger statement than
the per-parameter measurability Mathlib already provides -- `Real.Gamma` and
`ProbabilityTheory.beta` now vary too, which is why `Real.measurable_Gamma` is needed.

The discrete families are weighted sums of Dirac measures, and are handled by the shared
`measurable_sum_smul_dirac`, which evaluates such a measure on a set as a `tsum` of the weights.
The binomial law is the finite such sum `ProbabilityTheory.binomial_eq_sum_dirac`, and is evaluated
directly.

Three families are defined by a case split at a degenerate parameter — `gaussianReal μ 0` and
`cauchyMeasure x₀ 0` are Dirac measures, `geometricMeasure 0` is `Measure.dirac 0` — and their
proofs go through `Measurable.ite`: the degenerate parameter set is closed, and `Measure.dirac` is
itself measurable.

## Main results

* `measurable_gammaMeasure`, `measurable_expMeasure`, `measurable_betaMeasure`,
  `measurable_paretoMeasure`, `measurable_gaussianReal`, `measurable_cauchyMeasure` — the six
  continuous families of `TauCeti/Probability/Distributions/PDFInstances.lean`;
* `measurable_poissonMeasure`, `measurable_geometricMeasure`, `measurable_bernoulliMeasure`,
  `measurable_binomial` — the discrete families;
* `measurable_beta` — the Beta normalizing constant `ProbabilityTheory.beta`, needed on the way and
  of independent interest;
* `measurable_sum_smul_dirac` — the shared bridge for weighted sums of Dirac measures.

The parameter measurability of `uniformMeasure` is `TauCeti.Probability.measurable_uniformMeasure`,
in `TauCeti/Probability/Distributions/Uniform.lean`, next to that family's other results.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 0, item 4 — parameter
  measurability, with `measurable_gammaMeasure` and `measurable_poissonMeasure` as the named
  targets. Item 2 of the same layer, the Radon-Nikodym derivatives, is a separate target and is not
  built here.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

namespace TauCeti

namespace Probability

/-! ### The Beta normalizing constant -/

/-- `ProbabilityTheory.beta` is measurable in its two parameters.

It is `Real.Gamma α * Real.Gamma β / Real.Gamma (α + β)`, so this is `Real.measurable_Gamma` three
times. No positivity is assumed: measurability is a statement about the total function, junk values
at the poles of `Real.Gamma` included. -/
@[fun_prop]
theorem measurable_beta : Measurable fun p : ℝ × ℝ => beta p.1 p.2 := by
  unfold beta
  fun_prop

/-! ### Joint measurability of the continuous densities

Each lemma says that the density is measurable as a function of the pair (parameters, point). This
is what `MeasureTheory.measurable_withDensity` consumes; Mathlib's `measurable_gammaPDFReal`
and its analogues fix the parameters and are therefore too weak. -/

/-- The Gamma density is measurable jointly in its shape, its rate and the point. -/
@[fun_prop]
theorem measurable_uncurry_gammaPDF :
    Measurable fun q : (ℝ × ℝ) × ℝ => gammaPDF q.1.1 q.1.2 q.2 := by
  simp only [gammaPDF, gammaPDFReal]
  exact (Measurable.ite (measurableSet_le measurable_const measurable_snd)
    (by fun_prop) measurable_const).ennreal_ofReal

/-- The Beta density is measurable jointly in its two shapes and the point. -/
@[fun_prop]
theorem measurable_uncurry_betaPDF :
    Measurable fun q : (ℝ × ℝ) × ℝ => betaPDF q.1.1 q.1.2 q.2 := by
  simp only [betaPDF, betaPDFReal]
  refine (Measurable.ite ?_ (by fun_prop) measurable_const).ennreal_ofReal
  exact (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd measurable_const)

/-- The Pareto density is measurable jointly in its threshold, its shape and the point. -/
@[fun_prop]
theorem measurable_uncurry_paretoPDF :
    Measurable fun q : (ℝ × ℝ) × ℝ => paretoPDF q.1.1 q.1.2 q.2 := by
  simp only [paretoPDF, paretoPDFReal]
  exact (Measurable.ite (measurableSet_le measurable_fst.fst measurable_snd)
    (by fun_prop) measurable_const).ennreal_ofReal

/-- The Gaussian density is measurable jointly in its mean, its variance and the point.

At `v = 0` the formula returns `0`, which is the junk value of `gaussianPDF`; the measure
`gaussianReal μ 0` is a Dirac measure and is handled separately in `measurable_gaussianReal`. -/
@[fun_prop]
theorem measurable_uncurry_gaussianPDF :
    Measurable fun q : (ℝ × ℝ≥0) × ℝ => gaussianPDF q.1.1 q.1.2 q.2 := by
  simp only [gaussianPDF, gaussianPDFReal]
  fun_prop

/-- The Cauchy density is measurable jointly in its location, its scale and the point. -/
@[fun_prop]
theorem measurable_uncurry_cauchyPDF :
    Measurable fun q : (ℝ × ℝ≥0) × ℝ => cauchyPDF q.1.1 q.1.2 q.2 := by
  simp only [cauchyPDF, cauchyPDFReal]
  fun_prop

/-! ### The continuous families -/

/-- **The Gamma family is measurable in its parameters.** -/
@[fun_prop]
theorem measurable_gammaMeasure : Measurable fun p : ℝ × ℝ => gammaMeasure p.1 p.2 :=
  measurable_withDensity (μ := volume) measurable_uncurry_gammaPDF

/-- **The exponential family is measurable in its rate.**

`expMeasure r` is `gammaMeasure 1 r`, so this is `measurable_gammaMeasure` along the line `a = 1`.
-/
@[fun_prop]
theorem measurable_expMeasure : Measurable fun r : ℝ => expMeasure r := by
  have h : (fun r : ℝ => expMeasure r)
      = (fun p : ℝ × ℝ => gammaMeasure p.1 p.2) ∘ fun r : ℝ => ((1 : ℝ), r) := rfl
  rw [h]
  exact measurable_gammaMeasure.comp (by fun_prop)

/-- **The Beta family is measurable in its parameters.** -/
@[fun_prop]
theorem measurable_betaMeasure : Measurable fun p : ℝ × ℝ => betaMeasure p.1 p.2 :=
  measurable_withDensity (μ := volume) measurable_uncurry_betaPDF

/-- **The Pareto family is measurable in its parameters.** -/
@[fun_prop]
theorem measurable_paretoMeasure : Measurable fun p : ℝ × ℝ => paretoMeasure p.1 p.2 :=
  measurable_withDensity (μ := volume) measurable_uncurry_paretoPDF

/-- **The real Gaussian family is measurable in its mean and variance.**

The variance `0` fibre is a Dirac measure rather than a `withDensity` measure, so the proof splits
along the measurable set `{p | p.2 = 0}` and uses `MeasureTheory.Measure.measurable_dirac` there. -/
@[fun_prop]
theorem measurable_gaussianReal : Measurable fun p : ℝ × ℝ≥0 => gaussianReal p.1 p.2 := by
  simp only [gaussianReal]
  refine Measurable.ite ?_ (Measure.measurable_dirac.comp measurable_fst)
    (measurable_withDensity (μ := volume) measurable_uncurry_gaussianPDF)
  exact measurable_snd (measurableSet_singleton 0)

/-- **The Cauchy family is measurable in its location and scale.**

As for the Gaussian, the zero-scale fibre is a Dirac measure and is split off. -/
@[fun_prop]
theorem measurable_cauchyMeasure : Measurable fun p : ℝ × ℝ≥0 => cauchyMeasure p.1 p.2 := by
  simp only [cauchyMeasure]
  refine Measurable.ite ?_ (Measure.measurable_dirac.comp measurable_fst)
    (measurable_withDensity (μ := volume) measurable_uncurry_cauchyPDF)
  exact measurable_snd (measurableSet_singleton 0)

/-! ### The discrete families -/

/-- A countable mixture of Dirac measures at fixed atoms `g i` is measurable in the weights.

This is the discrete counterpart of `MeasureTheory.measurable_withDensity`: evaluating on a
measurable set turns the measure into the sum `∑' i, f b i * 1_{g i ∈ s}`, and a `tsum` of
measurable functions is measurable. The atoms are indexed by a countable type of their own, so the
ambient space `α` may be uncountable. -/
theorem measurable_sum_smul_dirac {β ι α : Type*} [MeasurableSpace β] [MeasurableSpace α]
    [Countable ι] {f : β → ι → ℝ≥0∞} {g : ι → α}
    (hf : ∀ i, Measurable fun b => f b i) :
    Measurable fun b => Measure.sum fun i => f b i • Measure.dirac (g i) := by
  refine Measure.measurable_measure.2 fun s hs => ?_
  simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
  exact Measurable.tsum fun i => (hf i).mul_const _

/-- **The Poisson family is measurable in its rate.**

The roadmap's Layer 4 composes this with `Real.toNNReal` to build the Gamma-mixed Poisson kernel. -/
@[fun_prop]
theorem measurable_poissonMeasure : Measurable fun r : ℝ≥0 => poissonMeasure r := by
  simp only [poissonMeasure]
  exact measurable_sum_smul_dirac fun n => by fun_prop

/-- **The geometric family is measurable in its success probability.**

At `p = 0` the law is `Measure.dirac 0` rather than a weighted sum, so the proof splits along the
measurable set `{p | p ≠ 0}` of the unit interval. -/
@[fun_prop]
theorem measurable_geometricMeasure : Measurable fun p : unitInterval => geometricMeasure p := by
  simp only [geometricMeasure]
  refine Measurable.ite ?_ (measurable_sum_smul_dirac fun n => by fun_prop) measurable_const
  exact (measurableSet_singleton (0 : unitInterval)).compl

/-- **The Bernoulli family is measurable in its success probability.** -/
@[fun_prop]
theorem measurable_bernoulliMeasure {X : Type*} [MeasurableSpace X] (x y : X) :
    Measurable fun p : unitInterval => bernoulliMeasure x y p := by
  simp only [bernoulliMeasure]
  fun_prop

/-- **The binomial family is measurable in its number of trials and its success probability.**

`ProbabilityTheory.binomial_eq_sum_dirac` writes `Bin(n, p)` as a finite weighted sum of Dirac
measures whose weights are polynomial in `p`, so each fibre `n` is measurable in `p`, and `ℕ` is
countable and discrete. -/
@[fun_prop]
theorem measurable_binomial : Measurable fun q : ℕ × unitInterval => binomial q.1 q.2 := by
  refine measurable_from_prod_countable_right fun n => Measure.measurable_measure.2 fun s hs => ?_
  simp only [binomial_eq_sum_dirac, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs]
  exact Finset.measurable_sum _ fun k _ => (by fun_prop : Measurable _).mul_const _

end Probability

end TauCeti
