/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Coordinate marginals of a probability measure on a product

`Mathlib` pushes a `MeasureTheory.ProbabilityMeasure` forward along a measurable map with
`MeasureTheory.ProbabilityMeasure.map`, whose a.e.-measurability hypothesis is measured against the
measure being pushed. For the evaluation maps of a product that hypothesis is uniform, so the
pushforward is a function of the measure alone; `TauCeti.MeasureTheory.coordMarginal` fixes that
choice and records its measurability in the Giry σ-algebra.

The measurability is what a random probability measure on a product needs: a witness of a shape
like `TauCeti.Probability.MixedIIDWith` carries `Measurable ν` for `ν : Ω → ProbabilityMeasure`,
and a consumer that wants the individual coordinate laws as a random probability measure — for
instance the transition matrix of a mixture of Markov chains — has to know that taking a marginal
preserves that measurability.

## Main definitions

* `TauCeti.MeasureTheory.coordMarginal` — the law of one coordinate under a probability measure on
  a product.

## Main results

* `TauCeti.MeasureTheory.coordMarginal_apply` — its value on a measurable set, as the mass of the
  corresponding coordinate event.
* `TauCeti.MeasureTheory.measurable_coordMarginal` — measurability in the Giry σ-algebra.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace MeasureTheory

variable {ι : Type*} {π : ι → Type*} [∀ i, MeasurableSpace (π i)]

/-- The law of the `a`-th coordinate under a probability measure on the product `∀ i, π i`. -/
def coordMarginal (P : ProbabilityMeasure (∀ i, π i)) (a : ι) : ProbabilityMeasure (π a) :=
  P.map (measurable_pi_apply a).aemeasurable

-- The parentheses in `(rfl)` opt out of the exported-theorem exposure check, so that the
-- underlying-measure equation can be stated without exposing the body of `coordMarginal`.
@[simp]
theorem coordMarginal_toMeasure (P : ProbabilityMeasure (∀ i, π i)) (a : ι) :
    (coordMarginal P a : Measure (π a)) = (P : Measure (∀ i, π i)).map fun x => x a :=
  (rfl)

/-- A coordinate marginal evaluated on a measurable set is the mass of the coordinate event. -/
theorem coordMarginal_apply (P : ProbabilityMeasure (∀ i, π i)) (a : ι) {s : Set (π a)}
    (hs : MeasurableSet s) :
    (coordMarginal P a : Measure (π a)) s = (P : Measure (∀ i, π i)) {x | x a ∈ s} := by
  rw [coordMarginal_toMeasure, Measure.map_apply (measurable_pi_apply a) hs]
  rfl

/-- Taking a coordinate marginal is measurable for the Giry σ-algebras. -/
@[fun_prop]
theorem measurable_coordMarginal (a : ι) :
    Measurable fun P : ProbabilityMeasure (∀ i, π i) => coordMarginal P a := by
  refine Measurable.subtype_mk ?_
  exact (Measure.measurable_map _ (measurable_pi_apply a)).comp measurable_subtype_coe

end MeasureTheory

end TauCeti

end

end
