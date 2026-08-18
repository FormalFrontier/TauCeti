/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Density
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.Distributions.Pareto
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Cauchy

/-!
# `HasPDF` instances for Mathlib's continuous families

Several of Mathlib's continuous scalar laws can be presented as `withDensity` measures, but none is
connected to `MeasureTheory.HasPDF`. This file supplies that bridge for the six such families, and
identifies the resulting density. How each is presented differs: `gammaMeasure`, `betaMeasure` and
`paretoMeasure` are `withDensity` by definition, `expMeasure` through `gammaMeasure`, and
`gaussianReal` and `cauchyMeasure` only away from zero spread.

**One helper, six families, two conclusions each.** The bridges themselves live in
`TauCeti/Probability/Density.lean`, which mentions no particular distribution:
`hasPDF_of_hasLaw_withDensity` gives `HasPDF` and `pdf_eq_of_hasLaw_withDensity` identifies the
density. Keeping them there lets `Distributions/Uniform.lean` reuse the same bridges without
importing Gamma, Beta, Pareto, Gaussian and Cauchy along with them. Nothing here recomputes a
density — Mathlib already proved each defining `withDensity` equality, and this file packages those
facts.

**Where the spread may vanish.** `gaussianReal m v` and `cauchyMeasure x₀ γ` are defined by a case
split: at `v = 0` and `γ = 0` they are Dirac measures, which are singular with respect to `volume`
and have no density at all. Those two bridges therefore carry `v ≠ 0` and `γ ≠ 0` — not as
convenience hypotheses but because the statement is false without them.

`gammaMeasure`, `betaMeasure`, `expMeasure` and `paretoMeasure` need no such hypothesis: each is
`volume.withDensity` of its density **for every parameter**, so each is absolutely continuous
throughout. That is a separate question from whether the result is a *probability* measure, which
does constrain the parameters (`isProbabilityMeasure_gammaMeasure` and its analogues); absolute
continuity is all these bridges need.

## Main results

* `hasPDF_of_hasLaw_gammaMeasure` and its five siblings, each paired with a `pdf_..._eq`
  a.e.-identification. The two shared bridges they are built from are in
  `TauCeti.Probability.Density`.

Three `ℝ≥0∞`-valued measurability lemmas (`measurable_gammaPDF`, `measurable_betaPDF`,
`measurable_paretoPDF`) are supplied because Mathlib exposes only the real-valued forms for those
families; the Gaussian and Cauchy `ℝ≥0∞` versions already exist and are reused.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 0, item 1 — connecting Mathlib's
  continuous families to `HasPDF` and identifying `pdf X P`. Item 2 (the Radon–Nikodym derivatives)
  is a separate target and is not built here; item 4 (parameter measurability) is
  `TauCeti/Probability/Distributions/Measurability.lean`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

namespace TauCeti

namespace Probability


/-! ### `ℝ≥0∞`-valued measurability for the families that lack it

Mathlib exposes `measurable_gammaPDFReal`, `measurable_betaPDFReal` and `measurable_paretoPDFReal`
but not their `ℝ≥0∞` companions. Each density is `ENNReal.ofReal` of the real one; the `unfold`
names that reduction rather than leaving it to elaboration. -/

/-- The `ℝ≥0∞`-valued Gamma density is measurable. -/
theorem measurable_gammaPDF (a r : ℝ) : Measurable (gammaPDF a r) := by
  unfold gammaPDF
  exact (measurable_gammaPDFReal a r).ennreal_ofReal

/-- The `ℝ≥0∞`-valued Beta density is measurable. -/
theorem measurable_betaPDF (α β : ℝ) : Measurable (betaPDF α β) := by
  unfold betaPDF
  exact (measurable_betaPDFReal α β).ennreal_ofReal

/-- The `ℝ≥0∞`-valued Pareto density is measurable. -/
theorem measurable_paretoPDF (t r : ℝ) : Measurable (paretoPDF t r) := by
  unfold paretoPDF
  exact (measurable_paretoPDFReal t r).ennreal_ofReal

/-! ### The six families

Each family gets both conclusions: that a variable with the law has a density, and what that
density is. The `simpa only [...]` steps name the measure definitions being reduced instead of
letting elaboration unfold them silently. -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A variable with a Gamma law has a density. -/
theorem hasPDF_of_hasLaw_gammaMeasure {a r : ℝ} (hX : HasLaw X (gammaMeasure a r) P) :
    HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_gammaPDF a r).aemeasurable
    (by simpa only [gammaMeasure] using hX)

/-- The density of a Gamma law is `gammaPDF`. -/
theorem pdf_eq_gammaPDF_of_hasLaw_gammaMeasure {a r : ℝ} (hX : HasLaw X (gammaMeasure a r) P) :
    pdf X P =ᵐ[volume] gammaPDF a r :=
  pdf_eq_of_hasLaw_withDensity (measurable_gammaPDF a r).aemeasurable
    (by simpa only [gammaMeasure] using hX)

/-- A variable with a Beta law has a density. -/
theorem hasPDF_of_hasLaw_betaMeasure {α β : ℝ} (hX : HasLaw X (betaMeasure α β) P) :
    HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_betaPDF α β).aemeasurable
    (by simpa only [betaMeasure] using hX)

/-- The density of a Beta law is `betaPDF`. -/
theorem pdf_eq_betaPDF_of_hasLaw_betaMeasure {α β : ℝ} (hX : HasLaw X (betaMeasure α β) P) :
    pdf X P =ᵐ[volume] betaPDF α β :=
  pdf_eq_of_hasLaw_withDensity (measurable_betaPDF α β).aemeasurable
    (by simpa only [betaMeasure] using hX)

/-- A variable with an exponential law has a density. -/
theorem hasPDF_of_hasLaw_expMeasure {r : ℝ} (hX : HasLaw X (expMeasure r) P) :
    HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_gammaPDF 1 r).aemeasurable
    (by simpa only [expMeasure, gammaMeasure] using hX)

/-- The density of an exponential law is `exponentialPDF`.

`exponentialPDFReal` is *defined* as `gammaPDFReal 1`, so the two densities agree definitionally;
the `unfold` names that rather than leaving it to elaboration. -/
theorem pdf_eq_exponentialPDF_of_hasLaw_expMeasure {r : ℝ} (hX : HasLaw X (expMeasure r) P) :
    pdf X P =ᵐ[volume] exponentialPDF r := by
  have h : pdf X P =ᵐ[volume] gammaPDF 1 r :=
    pdf_eq_of_hasLaw_withDensity (measurable_gammaPDF 1 r).aemeasurable
      (by simpa only [expMeasure, gammaMeasure] using hX)
  unfold exponentialPDF exponentialPDFReal
  exact h

/-- A variable with a Pareto law has a density. -/
theorem hasPDF_of_hasLaw_paretoMeasure {t r : ℝ} (hX : HasLaw X (paretoMeasure t r) P) :
    HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_paretoPDF t r).aemeasurable
    (by simpa only [paretoMeasure] using hX)

/-- The density of a Pareto law is `paretoPDF`. -/
theorem pdf_eq_paretoPDF_of_hasLaw_paretoMeasure {t r : ℝ}
    (hX : HasLaw X (paretoMeasure t r) P) : pdf X P =ᵐ[volume] paretoPDF t r :=
  pdf_eq_of_hasLaw_withDensity (measurable_paretoPDF t r).aemeasurable
    (by simpa only [paretoMeasure] using hX)

/-- A variable with a nondegenerate Gaussian law has a density.

`v ≠ 0` is required, not merely convenient: `gaussianReal m 0` is `Measure.dirac m`, which is
singular with respect to `volume`. -/
theorem hasPDF_of_hasLaw_gaussianReal {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX : HasLaw X (gaussianReal m v) P) : HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_gaussianPDF m v).aemeasurable
    (by rwa [gaussianReal_of_var_ne_zero _ hv] at hX)

/-- The density of a nondegenerate Gaussian law is `gaussianPDF`. -/
theorem pdf_eq_gaussianPDF_of_hasLaw_gaussianReal {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX : HasLaw X (gaussianReal m v) P) : pdf X P =ᵐ[volume] gaussianPDF m v :=
  pdf_eq_of_hasLaw_withDensity (measurable_gaussianPDF m v).aemeasurable
    (by rwa [gaussianReal_of_var_ne_zero _ hv] at hX)

/-- A variable with a nondegenerate Cauchy law has a density.

`γ ≠ 0` is required, not merely convenient: `cauchyMeasure x₀ 0` is `Measure.dirac x₀`, which is
singular with respect to `volume`. -/
theorem hasPDF_of_hasLaw_cauchyMeasure {x₀ : ℝ} {γ : ℝ≥0} (hγ : γ ≠ 0)
    (hX : HasLaw X (cauchyMeasure x₀ γ) P) : HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_cauchyPDF x₀ γ).aemeasurable
    (by rwa [cauchyMeasure_of_scale_ne_zero _ hγ] at hX)

/-- The density of a nondegenerate Cauchy law is `cauchyPDF`. -/
theorem pdf_eq_cauchyPDF_of_hasLaw_cauchyMeasure {x₀ : ℝ} {γ : ℝ≥0} (hγ : γ ≠ 0)
    (hX : HasLaw X (cauchyMeasure x₀ γ) P) : pdf X P =ᵐ[volume] cauchyPDF x₀ γ :=
  pdf_eq_of_hasLaw_withDensity (measurable_cauchyPDF x₀ γ).aemeasurable
    (by rwa [cauchyMeasure_of_scale_ne_zero _ hγ] at hX)

end Probability

end TauCeti
