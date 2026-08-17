/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.PiWithDensity
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The standard Gaussian measure on a finite product

The product measure `γ^ι = Measure.pi (fun _ : ι => gaussianReal 0 1)` is Lebesgue measure on
`ℝ^ι` weighted by the joint density `x ↦ ∏ i, gaussianPDFReal 0 1 (x i)`. That identification is
what lets a weight-in-the-measure statement about `γ^ι` be read as a weight-in-the-function
statement about `volume^ι`, via `TauCeti.weightL2Isometry`.

Like `TauCeti.gaussianPDFReal_zero_one`, these are statements about the Gaussian distribution
alone (no orthogonal family appears), so they live here rather than with the multi-index Hermite
basis that consumes them.

## Main statements

* `TauCeti.pi_gaussianReal_eq_withDensity`: `γ^ι = volume^ι` weighted by the joint density.
* `TauCeti.pi_volume_absolutelyContinuous_pi_gaussianReal`: the joint density never vanishes, so
  `volume^ι`-null sets are exactly `γ^ι`-null sets in the direction one needs to move an
  almost-everywhere statement from `γ^ι` to `volume^ι`.
-/

public section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace TauCeti

variable (ι : Type*) [Fintype ι]

/-- The joint standard Gaussian density on `ℝ^ι` is everywhere positive. -/
theorem prod_gaussianPDFReal_pos (x : ι → ℝ) : 0 < ∏ i, gaussianPDFReal 0 1 (x i) :=
  Finset.prod_pos fun i _ => gaussianPDFReal_pos 0 1 (x i) one_ne_zero

/-- The joint standard Gaussian density on `ℝ^ι` is measurable. -/
theorem measurable_prod_gaussianPDFReal :
    Measurable fun x : ι → ℝ => ∏ i, gaussianPDFReal 0 1 (x i) :=
  Finset.measurable_prod _ fun i _ =>
    (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i)

/-- **The standard Gaussian on `ℝ^ι` is `volume^ι` weighted by the joint density.** Each factor is
`volume` weighted by `gaussianPDFReal 0 1` (`ProbabilityTheory.gaussianReal_of_var_ne_zero`), and
coordinatewise densities multiply (`TauCeti.pi_withDensity`). -/
theorem pi_gaussianReal_eq_withDensity :
    (Measure.pi fun _ : ι => (gaussianReal 0 1 : Measure ℝ))
      = (Measure.pi fun _ : ι => (volume : Measure ℝ)).withDensity
        fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i)) := by
  have hγ : (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x))
      = (gaussianReal 0 1 : Measure ℝ) := by
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, gaussianPDF_def]
  have : IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)) := by
    rw [hγ]; infer_instance
  have hfam : (fun _ : ι => (gaussianReal 0 1 : Measure ℝ))
      = fun _ : ι => volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x) :=
    funext fun _ => hγ.symm
  rw [hfam, pi_withDensity (fun _ : ι => (volume : Measure ℝ)) fun _ =>
      (measurable_gaussianPDFReal 0 1).ennreal_ofReal]
  exact withDensity_congr_ae (Filter.Eventually.of_forall fun x =>
    (ENNReal.ofReal_prod_of_nonneg fun i _ =>
      (gaussianPDFReal_pos 0 1 (x i) one_ne_zero).le).symm)

/-- **`volume^ι` is absolutely continuous with respect to `γ^ι`.** The joint density is everywhere
positive, so weighting by it kills no set of positive measure. This is what moves an
almost-everywhere identification of a `L²(γ^ι)` representative to one holding `volume^ι`-almost
everywhere, where the `√`-density envelope lives. -/
theorem pi_volume_absolutelyContinuous_pi_gaussianReal :
    (Measure.pi fun _ : ι => (volume : Measure ℝ))
      ≪ Measure.pi fun _ : ι => (gaussianReal 0 1 : Measure ℝ) := by
  rw [pi_gaussianReal_eq_withDensity]
  exact withDensity_absolutelyContinuous'
    (measurable_prod_gaussianPDFReal ι).ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun x =>
      (ENNReal.ofReal_pos.2 (prod_gaussianPDFReal_pos ι x)).ne')

end TauCeti
