/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.Distributions.Pareto
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Cauchy
public import Mathlib.Probability.Density
public import Mathlib.Probability.HasLaw

/-!
# `HasPDF` instances for Mathlib's continuous families

Mathlib defines its continuous scalar laws as `withDensity` measures but does not connect them to
`MeasureTheory.HasPDF`. This file supplies that bridge for the six families that have one, so a
random variable known to *have* one of these laws is known to have a density.

**One helper, six applications.** `hasPDF_of_hasLaw_withDensity` does all the work: a law presented
as `volume.withDensity f` with `f` measurable yields `HasPDF` directly. Nothing here recomputes a
density — Mathlib already proved each defining `withDensity` equality, and this file packages those
facts rather than repeating them.

**Where the spread may vanish.** `gaussianReal m v` and `cauchyMeasure x₀ γ` are defined by a case
split: at `v = 0` and `γ = 0` they are Dirac measures, which are singular with respect to `volume`
and have no density at all. Those two bridges therefore carry `v ≠ 0` and `γ ≠ 0` — not as
convenience hypotheses but because the statement is false without them.

The other four families need no such hypothesis: `gammaMeasure`, `betaMeasure`, `expMeasure` and
`paretoMeasure` are `withDensity` measures for every parameter, and degenerate parameters make the
density zero rather than the measure singular.

## Main results

* `hasPDF_of_hasLaw_withDensity` — the shared bridge;
* `hasPDF_of_hasLaw_gammaMeasure`, `_betaMeasure`, `_expMeasure`, `_paretoMeasure`,
  `_gaussianReal`, `_cauchyMeasure` — its six instantiations.

Three `ℝ≥0∞`-valued measurability lemmas (`measurable_gammaPDF`, `measurable_betaPDF`,
`measurable_paretoPDF`) are supplied here because Mathlib exposes only the real-valued forms for
those families; the Gaussian and Cauchy `ℝ≥0∞` versions already exist and are reused.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 0, item 1 — connecting Mathlib's
  continuous families to `HasPDF`. Item 2 (identifying the Radon–Nikodym derivatives) and item 4
  (parameter measurability) are separate targets and are not built here.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- **The shared bridge.** A law presented as `volume.withDensity f`, with `f` measurable, gives
`HasPDF`.

Every family below is an instance of this; nothing recomputes a density. -/
theorem hasPDF_of_hasLaw_withDensity {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hX : HasLaw X (volume.withDensity f) P) : HasPDF X P :=
  hasPDF_of_map_eq_withDensity hX.aemeasurable f hf.aemeasurable hX.map_eq

/-! ### `ℝ≥0∞`-valued measurability for the families that lack it

Mathlib exposes `measurable_gammaPDFReal`, `measurable_betaPDFReal` and `measurable_paretoPDFReal`
but not their `ℝ≥0∞` companions. Each density is `ENNReal.ofReal` of the real one, so the missing
lemma is one composition. -/

theorem measurable_gammaPDF (a r : ℝ) : Measurable (gammaPDF a r) :=
  (measurable_gammaPDFReal a r).ennreal_ofReal

theorem measurable_betaPDF (α β : ℝ) : Measurable (betaPDF α β) :=
  (measurable_betaPDFReal α β).ennreal_ofReal

theorem measurable_paretoPDF (t r : ℝ) : Measurable (paretoPDF t r) :=
  (measurable_paretoPDFReal t r).ennreal_ofReal

/-! ### The six bridges -/

/-- A variable with a Gamma law has a density. -/
theorem hasPDF_of_hasLaw_gammaMeasure {a r : ℝ} (hX : HasLaw X (gammaMeasure a r) P) :
    HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_gammaPDF a r) hX

/-- A variable with a Beta law has a density. -/
theorem hasPDF_of_hasLaw_betaMeasure {α β : ℝ} (hX : HasLaw X (betaMeasure α β) P) :
    HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_betaPDF α β) hX

/-- A variable with an exponential law has a density.

`expMeasure r` is `gammaMeasure 1 r`, so its density is `gammaPDF 1 r`. -/
theorem hasPDF_of_hasLaw_expMeasure {r : ℝ} (hX : HasLaw X (expMeasure r) P) :
    HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_gammaPDF 1 r) hX

/-- A variable with a Pareto law has a density. -/
theorem hasPDF_of_hasLaw_paretoMeasure {t r : ℝ} (hX : HasLaw X (paretoMeasure t r) P) :
    HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_paretoPDF t r) hX

/-- A variable with a nondegenerate Gaussian law has a density.

`v ≠ 0` is required, not merely convenient: `gaussianReal m 0` is `Measure.dirac m`, which is
singular with respect to `volume`. -/
theorem hasPDF_of_hasLaw_gaussianReal {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX : HasLaw X (gaussianReal m v) P) : HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_gaussianPDF m v)
    (by rwa [gaussianReal_of_var_ne_zero _ hv] at hX)

/-- A variable with a nondegenerate Cauchy law has a density.

`γ ≠ 0` is required, not merely convenient: `cauchyMeasure x₀ 0` is `Measure.dirac x₀`, which is
singular with respect to `volume`. -/
theorem hasPDF_of_hasLaw_cauchyMeasure {x₀ : ℝ} {γ : ℝ≥0} (hγ : γ ≠ 0)
    (hX : HasLaw X (cauchyMeasure x₀ γ) P) : HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_cauchyPDF x₀ γ)
    (by rwa [cauchyMeasure_of_scale_ne_zero _ hγ] at hX)

end Probability

end TauCeti
