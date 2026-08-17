/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Convex combinations of probability measures

`ProbabilityMeasure α` carries no addition and no scalar action: it is a subtype of `Measure α`,
and neither `P + Q` nor `c • P` is a probability measure. What it does carry is a convex structure,
and this file names it. For weights `a + b = 1`, `a • P + b • Q` is again a probability measure, and
`ProbabilityMeasure.convexCombo` is that combination, bundled.

Naming the bundled combination is what lets a statement about a map out of `ProbabilityMeasure α`
say "affine" without coercing to `Measure α` and rebuilding the probability-measure structure at
every step.

## Main results

* `isProbabilityMeasure_smul_add_smul` — the unbundled fact about total mass.
* `ProbabilityMeasure.convexCombo` — the bundled combination, with `toMeasure_convexCombo`
  exposing its underlying measure.

`convexCombo` and its two lemmas are declared in the root `MeasureTheory.ProbabilityMeasure`
namespace rather than under `TauCeti`, since the type is Mathlib's; that is what lets
`P.convexCombo` be written as dot notation.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- **A convex combination of probability measures is a probability measure.** The weights are
arbitrary elements of `ℝ≥0∞` summing to `1`; no separate nonnegativity condition is needed, since
`ℝ≥0∞` has none to impose. -/
theorem isProbabilityMeasure_smul_add_smul {a b : ℝ≥0∞} (hab : a + b = 1) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : IsProbabilityMeasure (a • μ + b • ν) :=
  ⟨by simp [hab]⟩

end MeasureTheory

end TauCeti

/-! ### The bundled combination

`ProbabilityMeasure` is Mathlib's type, so its namespace is Mathlib's: these three declarations sit
in the root `MeasureTheory.ProbabilityMeasure`, not under `TauCeti`, which is what makes
`P.convexCombo hab Q` elaborate as dot notation. -/

namespace MeasureTheory

namespace ProbabilityMeasure

variable {α : Type*} [MeasurableSpace α]

/-- The **convex combination** `a • P + b • Q` of two probability measures, for weights summing
to `1`, bundled as a `ProbabilityMeasure`.

Exposed: this is a bundling, with no content beyond `toMeasure_convexCombo`, and callers
constructing subtypes of `ProbabilityMeasure` need the underlying measure definitionally. -/
@[expose]
def convexCombo {a b : ℝ≥0∞} (hab : a + b = 1) (P Q : ProbabilityMeasure α) :
    ProbabilityMeasure α :=
  ⟨a • (P : Measure α) + b • (Q : Measure α),
    TauCeti.MeasureTheory.isProbabilityMeasure_smul_add_smul hab _ _⟩

/-- The underlying measure of a convex combination is the combination of the underlying
measures. -/
@[simp]
theorem toMeasure_convexCombo {a b : ℝ≥0∞} (hab : a + b = 1) (P Q : ProbabilityMeasure α) :
    (convexCombo hab P Q : Measure α) = a • (P : Measure α) + b • (Q : Measure α) :=
  (rfl)

end ProbabilityMeasure

end MeasureTheory
