/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Markov kernels, bundled fibrewise

`IsMarkovKernel κ` says exactly that every fibre of `κ : Kernel β Ω` is a probability measure.
Consumers that want a *random probability measure* — a `β → ProbabilityMeasure Ω`, the shape
predicates like `MixedIIDWith` and `ConditionallyIIDWith` take as their witness — must pair each
fibre with that instance by hand. `Kernel.probabilityMeasure` does it once.

The bundling is canonical: there is no choice to make, and correspondingly no probability-measure
lemma here, since the type already carries it.

## Main results

* `Kernel.probabilityMeasure` — the bundled kernel;
* `Kernel.probabilityMeasure_toMeasure` — its underlying measure is the kernel's fibre, and the
  abstraction boundary for importing modules;
* `Kernel.measurable_probabilityMeasure` — measurability into `ProbabilityMeasure Ω`.

Stated for an arbitrary Markov kernel rather than for any particular construction. The regular
conditional distribution `ProbabilityTheory.condDistrib` is one instance; conditioning on a
sub-σ-algebra is that instance with the conditioning map `id`, which is how the de Finetti
directing measures arise.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {β Ω : Type*} [MeasurableSpace Ω] [mβ : MeasurableSpace β]

/-- A Markov kernel with each fibre bundled as a `ProbabilityMeasure`.

Note this lives in `TauCeti.Probability.Kernel`, not Mathlib's `ProbabilityTheory.Kernel`, so it is
spelled `Kernel.probabilityMeasure κ` rather than by dot notation on `κ`. -/
def Kernel.probabilityMeasure (κ : Kernel β Ω) [IsMarkovKernel κ] (b : β) : ProbabilityMeasure Ω :=
  ⟨κ b, inferInstance⟩

/-- The underlying measure of a bundled fibre is the kernel's fibre.

This is the abstraction boundary: importing modules should reason through this lemma rather than
unfold `Kernel.probabilityMeasure`, which is why the definition is not `@[expose]`. -/
@[simp]
theorem Kernel.probabilityMeasure_toMeasure (κ : Kernel β Ω) [IsMarkovKernel κ] (b : β) :
    (Kernel.probabilityMeasure κ b : Measure Ω) = κ b := by
  simp only [Kernel.probabilityMeasure, ProbabilityMeasure.coe_mk]

/-- The bundled kernel is measurable into `ProbabilityMeasure Ω`. -/
@[fun_prop]
theorem Kernel.measurable_probabilityMeasure (κ : Kernel β Ω) [IsMarkovKernel κ] :
    Measurable (Kernel.probabilityMeasure κ) := by
  refine Measurable.subtype_mk ?_
  exact Measure.measurable_of_measurable_coe _ fun s hs => Kernel.measurable_coe _ hs

end Probability

end TauCeti
