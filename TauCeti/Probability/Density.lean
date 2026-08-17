/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Density
public import Mathlib.Probability.HasLaw

/-!
# Densities from laws presented as `withDensity`

Two bridges from a law given as `μ.withDensity f` to Mathlib's `MeasureTheory.HasPDF` and `pdf`.

Several of Mathlib's continuous scalar families can be *presented* as `withDensity` measures — some
by definition, others only away from a degenerate parameter — and so can laws Tau Ceti builds on top
of them, but none of them is connected to `HasPDF`. These two theorems make
that connection once, so no individual family has to repeat the
`hasPDF_of_map_eq_withDensity hX.aemeasurable … hX.map_eq` plumbing.

The file is deliberately neutral: it mentions no particular distribution, so a module defining one
family can import it without acquiring the others.

## Main results

* `hasPDF_of_hasLaw_withDensity` — a law presented as `μ.withDensity f` gives `HasPDF`;
* `pdf_eq_of_hasLaw_withDensity` — and its density is `f`.

Both are stated for an arbitrary codomain and codomain measure, since neither proof uses anything
about `ℝ` or `volume`, and both ask only for `AEMeasurable f μ`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {P : Measure Ω} {μ : Measure E}
  {X : Ω → E} {f : E → ℝ≥0∞}

/-- **The shared bridge.** A law presented as `μ.withDensity f`, with `f` a.e. measurable, gives
`HasPDF`. -/
theorem hasPDF_of_hasLaw_withDensity (hf : AEMeasurable f μ)
    (hX : HasLaw X (μ.withDensity f) P) : HasPDF X P μ :=
  hasPDF_of_map_eq_withDensity hX.aemeasurable f hf hX.map_eq

/-- The density supplied by `hasPDF_of_hasLaw_withDensity` is the one the law was presented with.

Needs `[SigmaFinite μ]` on the *codomain* measure — satisfied by `volume` — and nothing on the
source measure. -/
theorem pdf_eq_of_hasLaw_withDensity [SigmaFinite μ] (hf : AEMeasurable f μ)
    (hX : HasLaw X (μ.withDensity f) P) : pdf X P μ =ᵐ[μ] f := by
  have : HasPDF X P μ := hasPDF_of_hasLaw_withDensity hf hX
  exact (pdf.eq_of_map_eq_withDensity' f hf).mp hX.map_eq

end Probability

end TauCeti
