/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Additive Haar measures and continuous linear equivalences

A continuous linear equivalence between finite-dimensional real normed spaces is nonsingular for
any additive Haar measures chosen on its source and target: null sets correspond to null sets
under it, whatever the normalizations. This is uniqueness of additive Haar measure, in the form
`MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure`, applied to the pushforward measure,
which is again an additive Haar measure.

## Main results

* `TauCeti.ContinuousLinearEquiv.quasiMeasurePreserving_addHaar`: a continuous linear equivalence
  is quasi measure preserving for additive Haar measures on its source and target.
-/

public section

open MeasureTheory MeasureTheory.Measure

namespace TauCeti

/-- A continuous linear equivalence is nonsingular for any additive Haar measures on its source
and target. -/
theorem ContinuousLinearEquiv.quasiMeasurePreserving_addHaar {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μ : Measure E) (ν : Measure F) [IsAddHaarMeasure μ] [IsAddHaarMeasure ν]
    (e : E ≃L[ℝ] F) : QuasiMeasurePreserving e μ ν :=
  ⟨e.continuous.measurable, absolutelyContinuous_isAddHaarMeasure (μ.map e) ν⟩

end TauCeti

end
