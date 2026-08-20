/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Evaluating a measurable family at a measurable index

Mathlib's `Measurable.eval` evaluates a measurable map into a product at a **fixed** coordinate.
This file records the variant where the coordinate is itself a measurable function of the point,
which is what a recursion whose next index is read off the current state needs.

The hypotheses on the index type are the usual ones for such a statement: countably many
coordinates, each of them a measurable set, so that the fibres of the index map cut the domain into
countably many measurable pieces on which the evaluation is an ordinary coordinate projection.
Both are necessary — for an uncountable index type the diagonal `fun (x, i) => x i` is already not
measurable for the product σ-algebra.

## Main results

* `TauCeti.MeasureTheory.measurable_eval_index`: measurability of `fun b => g b (f b)`.
-/

public section

namespace TauCeti

namespace MeasureTheory

/-- **A measurable family evaluated at a measurable index is measurable.** Over a countable index
type with measurable points, `fun b => g b (f b)` is measurable as soon as the family `g` and the
index `f` are: the fibres of `f` are countably many measurable sets, and on each of them the
evaluation is a coordinate projection of `g`. -/
theorem measurable_eval_index {β ι γ : Type*} [MeasurableSpace β] [MeasurableSpace ι]
    [MeasurableSpace γ] [Countable ι] [MeasurableSingletonClass ι] {g : β → ι → γ} {f : β → ι}
    (hg : Measurable g) (hf : Measurable f) : Measurable fun b => g b (f b) :=
  (measurable_from_prod_countable_left (f := fun p : (ι → γ) × ι => p.1 p.2)
    fun i => measurable_pi_apply i).comp (hg.prodMk hf)

end MeasureTheory

end TauCeti
