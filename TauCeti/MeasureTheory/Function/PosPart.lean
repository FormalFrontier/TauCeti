/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Order.Lattice
public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Measurability of positive and negative parts

`f⁺ = f ⊔ 0` and `f⁻ = (-f) ⊔ 0` are measurable when `f` is, in any lattice-ordered group whose
join and negation are measurable. Mathlib supplies the algebra (`posPart_def`, `negPart_def`,
`posPart_sub_negPart`, `posPart_nonneg`, `negPart_nonneg`); these are the two measurability facts.
-/

public section

namespace TauCeti

variable {α M : Type*} [MeasurableSpace α] [MeasurableSpace M] [Lattice M] [AddGroup M]
  [MeasurableSup₂ M] {f : α → M}

/-- The positive part of a measurable function is measurable. -/
theorem _root_.Measurable.posPart (hf : Measurable f) : Measurable f⁺ := by
  rw [posPart_def]; exact hf.sup measurable_const

/-- The negative part of a measurable function is measurable. -/
theorem _root_.Measurable.negPart [MeasurableNeg M] (hf : Measurable f) : Measurable f⁻ := by
  rw [negPart_def]; exact hf.neg.sup measurable_const

end TauCeti
