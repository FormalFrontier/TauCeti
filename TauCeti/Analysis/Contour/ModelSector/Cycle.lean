/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cycle.Basic
public import TauCeti.Analysis.Contour.ModelSector.Closed

/-!
# Model sectors as contour cycles

Hungerbühler--Wasem Proposition 2.2 decomposes a closed immersed curve, as a contour cycle, into
a cycle avoiding the distinguished point and one model-sector cycle for each crossing.  The raw
model sector, its piecewise-`C¹` regularity, and its winding number are constructed in
`ModelSector.Closed`; this file packages it as the closed-curve generator that the cycle
decomposition uses.

## Main definitions

* `Contour.modelSectorCurve` -- the model sector as a closed piecewise-`C¹` curve.
* `Contour.modelSectorCycle` -- the corresponding one-generator contour cycle.

## Main results

* `Contour.Cycle.integral_modelSectorCycle` -- its cycle integral is the raw contour integral.
* `Contour.Cycle.windingNumber_modelSectorCycle_eq_raw` -- its cycle winding number is the raw
  winding number.
* `Contour.Cycle.windingNumber_modelSectorCycle` -- at the sector center its winding number is
  `α / 2π`.

## References

* N. Hungerbühler and M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), equation (2.4) and Proposition 2.2.
-/

public section

noncomputable section

open Set

namespace TauCeti.Contour

/-- The model sector bundled as a closed piecewise-`C¹` curve. -/
def modelSectorCurve (z₀ : ℂ) (r φ α : ℝ) (hr : 0 ≤ r) (hα : 0 ≤ α) :
    PiecewiseC1ClosedCurve :=
  PiecewiseC1ClosedCurve.of (modelSector z₀ r φ α)
    (isPiecewiseC1On_modelSector hr φ α) (modelSector_closed z₀ hr φ hα)

/-- The model sector as a one-generator contour cycle. -/
def modelSectorCycle (z₀ : ℂ) (r φ α : ℝ) (hr : 0 ≤ r) (hα : 0 ≤ α) : Cycle :=
  FreeAbelianGroup.of (modelSectorCurve z₀ r φ α hr hα)

/-- The bundled model sector starts at `-r`. -/
@[simp]
theorem modelSectorCurve_a (z₀ : ℂ) (r φ α : ℝ) (hr : 0 ≤ r) (hα : 0 ≤ α) :
    (modelSectorCurve z₀ r φ α hr hα).a = -r := by
  rw [modelSectorCurve, PiecewiseC1ClosedCurve.of_a]

/-- The bundled model sector ends at `r + α`. -/
@[simp]
theorem modelSectorCurve_b (z₀ : ℂ) (r φ α : ℝ) (hr : 0 ≤ r) (hα : 0 ≤ α) :
    (modelSectorCurve z₀ r φ α hr hα).b = r + α := by
  rw [modelSectorCurve, PiecewiseC1ClosedCurve.of_b]

/-- On its parameter interval, the bundled model sector agrees with the raw model sector. -/
@[simp]
theorem modelSectorCurve_apply {z₀ : ℂ} {r φ α t : ℝ} (hr : 0 ≤ r) (hα : 0 ≤ α)
    (ht : t ∈ uIcc (-r) (r + α)) :
    modelSectorCurve z₀ r φ α hr hα t = modelSector z₀ r φ α t := by
  rw [modelSectorCurve]
  exact PiecewiseC1ClosedCurve.of_apply _ _ _ ht

/-- The trace of the model-sector cycle is the image of its raw parametrization. -/
@[simp]
theorem Cycle.trace_modelSectorCycle (z₀ : ℂ) (r φ α : ℝ) (hr : 0 ≤ r) (hα : 0 ≤ α) :
    Cycle.trace (modelSectorCycle z₀ r φ α hr hα) =
      modelSector z₀ r φ α '' uIcc (-r) (r + α) := by
  rw [modelSectorCycle, modelSectorCurve]
  exact Cycle.trace_of_raw _ _ _

namespace Cycle

/-- Integrating over the model-sector cycle gives the raw contour integral over the model sector. -/
@[simp]
theorem integral_modelSectorCycle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (z₀ : ℂ) (r φ α : ℝ) (hr : 0 ≤ r) (hα : 0 ≤ α) :
    integral f (modelSectorCycle z₀ r φ α hr hα) =
      ∫ t in -r..r + α, deriv (modelSector z₀ r φ α) t • f (modelSector z₀ r φ α t) := by
  rw [modelSectorCycle, modelSectorCurve, integral_of_raw]

/-- The winding number of the model-sector cycle is the winding number of its raw
parametrization. -/
@[simp]
theorem windingNumber_modelSectorCycle_eq_raw (z z₀ : ℂ) (r φ α : ℝ) (hr : 0 ≤ r)
    (hα : 0 ≤ α) :
    windingNumber z (modelSectorCycle z₀ r φ α hr hα) =
      Contour.windingNumber (modelSector z₀ r φ α) (-r) (r + α) z := by
  rw [modelSectorCycle, modelSectorCurve, windingNumber_of_raw]

/-- **The model-sector cycle has winding number `α / 2π` about its corner.** This is the cycle
form of `Contour.windingNumber_closedModelSector`, ready to be summed in the finite crossing
decomposition of Hungerbühler--Wasem Proposition 2.2. -/
theorem windingNumber_modelSectorCycle {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (φ : ℝ) {α : ℝ}
    (hα : 0 ≤ α) :
    windingNumber z₀ (modelSectorCycle z₀ r φ α hr.le hα) =
      (α : ℂ) / (2 * (Real.pi : ℂ)) := by
  rw [windingNumber_modelSectorCycle_eq_raw,
    windingNumber_closedModelSector hr φ hα]

end Cycle

end TauCeti.Contour

end
