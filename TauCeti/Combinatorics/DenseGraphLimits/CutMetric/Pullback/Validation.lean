/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

import Mathlib.Probability.Distributions.Bernoulli
import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Pullback.Basic

/-!
# Atomic regressions for the map form of the cut distance

The harder direction of `cutDist_eq_cutDistPullback` applies Janson's Thm A.9 to the *coupling*, so
the atomic cases to check are atomic couplings. These three elaboration checks run the equivalence
at a point-mass coupling, at a finitely atomic one, and at one mixing an atomic with a continuous
direction. Each fails to typecheck for any formulation that assumes the carriers, or the coupling,
atomless.

Keeping these roadmap design-validation checks separate avoids adding their Bernoulli dependency
to the canonical `CutMetric.Pullback.Basic` API module. The repository build includes this module,
so the regressions remain part of the build gate for the contract they test.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, the Layer-5 design-validation milestone
  requiring Dirac, finite-atomic, and mixed regressions against `cutDist_eq_cutDistPullback`.
-/

noncomputable section

open MeasureTheory

open scoped unitInterval

namespace TauCeti

namespace DenseGraphLimits

-- Regression: both carriers are point masses, so every coupling of them is a point mass.
@[expose] public section

example (U : Graphon ℝ (Measure.dirac 0)) (W : Graphon ℝ (Measure.dirac 1)) :
    cutDist U W = cutDistPullback U W :=
  cutDist_eq_cutDistPullback U W

-- Regression: both carriers are Bernoulli laws, carried by at most two atoms — an endpoint
-- parameter collapses one to a point mass — so every coupling of them is finitely atomic.
example {p q : I} (U : Graphon ℝ (ProbabilityTheory.bernoulliMeasure 0 1 p))
    (W : Graphon ℝ (ProbabilityTheory.bernoulliMeasure 0 1 q)) :
    cutDist U W = cutDistPullback U W :=
  cutDist_eq_cutDistPullback U W

-- Regression: one carrier is atomic — at most two atoms, one if `p` is an endpoint — and the
-- other is `(I, volume)`, so a coupling of them has an atomic and a continuous direction at once.
example {p : I} (U : Graphon ℝ (ProbabilityTheory.bernoulliMeasure 0 1 p))
    (W : Graphon I volume) : cutDist U W = cutDistPullback U W :=
  cutDist_eq_cutDistPullback U W

end

end DenseGraphLimits

end TauCeti
