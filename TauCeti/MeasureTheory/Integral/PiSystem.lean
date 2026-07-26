module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.PiSystem

/-!
# A Dynkin (π-λ) step for Bochner integrals

If a function's integral vanishes on the whole space and on every member of a π-system generating
the σ-algebra, then it vanishes on every measurable set.

This is the Bochner counterpart of Mathlib's `ℝ≥0∞`-valued
`MeasureTheory.lintegral_eq_lintegral_of_isPiSystem`. Stating it for an arbitrary π-system rather
than for a specific one (rectangles, boxes) lets a single theorem serve every product-measure
arity.
-/

public section

namespace TauCeti

open MeasureTheory

/-- **The Dynkin (π-λ) step for Bochner integrals.** A function whose integral vanishes on the
whole space and on every member of a generating π-system has vanishing integral on every
measurable set. -/
theorem setIntegral_eq_zero_of_isPiSystem {X E : Type*} {m0 : MeasurableSpace X}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {ρ : Measure X} {S : Set (Set X)}
    (hgen : m0 = MeasurableSpace.generateFrom S) (hpi : IsPiSystem S) {f : X → E}
    (hf : Integrable f ρ) (huniv : ∫ x, f x ∂ρ = 0) (hS : ∀ s ∈ S, ∫ x in s, f x ∂ρ = 0) :
    ∀ u, MeasurableSet u → ∫ x in u, f x ∂ρ = 0 := by
  refine MeasurableSpace.induction_on_inter (C := fun u _ => ∫ x in u, f x ∂ρ = 0) hgen hpi ?_ hS
    ?_ ?_
  · simp
  · intro u hu ih
    rw [setIntegral_compl hu hf, huniv, ih, sub_zero]
  · intro u hd hm ih
    rw [integral_iUnion hm hd hf.integrableOn]
    simp [ih]

end TauCeti
