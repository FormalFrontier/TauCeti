/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The regular conditional distribution, bundled fibrewise

Mathlib's `ProbabilityTheory.condDistrib Y X μ` is a `Kernel β Ω`, and is already known to be a
Markov kernel. Consumers that want a *random probability measure* — a `β → ProbabilityMeasure Ω`,
the shape predicates like `MixedIIDWith` and `ConditionallyIIDWith` take as their witness — must
bundle each fibre with that instance by hand.

`condDistribProbabilityMeasure` does it once. The bundling is canonical: there is no choice to
make, since `IsMarkovKernel (condDistrib Y X μ)` is exactly the statement that every fibre is a
probability measure. Correspondingly there is no separate probability-measure lemma here; the
type already carries it.

## Main results

* `condDistribProbabilityMeasure` — the bundled conditional distribution;
* `condDistribProbabilityMeasure_toMeasure` — its underlying measure is the kernel's fibre;
* `measurable_condDistribProbabilityMeasure` — measurability into `ProbabilityMeasure Ω`;
* `condDistribProbabilityMeasure_comp_ae_eq_condExp` — the characteristic property, the bundled
  form of `condDistrib_ae_eq_condExp`.

This is deliberately stated at `condDistrib`'s own generality — an arbitrary observed map `Y` and
conditioning map `X` — rather than around a sub-σ-algebra parameter. Conditioning on a
sub-σ-algebra `m` is the special case `X := id` with `id` read as `Ω → Ω` carrying `m` on the
codomain, which is how both de Finetti directing measures arise.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {α β Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  {mα : MeasurableSpace α} [mβ : MeasurableSpace β] {μ : Measure α} [IsFiniteMeasure μ]
  {X : α → β} {Y : α → Ω}

/-- The regular conditional distribution of `Y` given `X`, with each fibre bundled as a
`ProbabilityMeasure` using `IsMarkovKernel (condDistrib Y X μ)`. -/
def condDistribProbabilityMeasure (Y : α → Ω) (X : α → β) (μ : Measure α) [IsFiniteMeasure μ]
    (b : β) : ProbabilityMeasure Ω :=
  ⟨condDistrib Y X μ b, inferInstance⟩

/-- The underlying measure of the bundled conditional distribution is the kernel's fibre. -/
@[simp]
theorem condDistribProbabilityMeasure_toMeasure (b : β) :
    (condDistribProbabilityMeasure Y X μ b : Measure Ω) = condDistrib Y X μ b := by
  simp only [condDistribProbabilityMeasure, ProbabilityMeasure.coe_mk]

/-- The bundled conditional distribution is measurable into `ProbabilityMeasure Ω`. -/
@[fun_prop]
theorem measurable_condDistribProbabilityMeasure :
    Measurable (condDistribProbabilityMeasure Y X μ) := by
  refine Measurable.subtype_mk ?_
  exact Measure.measurable_of_measurable_coe _ fun s hs => Kernel.measurable_coe _ hs

/-- **Characteristic property.** Evaluated along `X`, the bundled conditional distribution of a
measurable set is a version of the conditional expectation of that set's indicator given `X`.

The bundled form of `condDistrib_ae_eq_condExp`. -/
theorem condDistribProbabilityMeasure_comp_ae_eq_condExp (hX : Measurable X) (hY : Measurable Y)
    {s : Set Ω} (hs : MeasurableSet s) :
    (fun a => (condDistribProbabilityMeasure Y X μ (X a)).toMeasure.real s)
      =ᵐ[μ] μ⟦Y ⁻¹' s | MeasurableSpace.comap X inferInstance⟧ :=
  condDistrib_ae_eq_condExp hX hY hs

end Probability

end TauCeti
