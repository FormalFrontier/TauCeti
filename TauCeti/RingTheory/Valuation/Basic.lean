/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Basic

/-!
# Basic valuation inequalities

This file records general-purpose variants of the ultrametric triangle inequality.
-/

public section

namespace Valuation

variable {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]

/-- The ultrametric triangle inequality in comparison form: `v x` is at most the larger of
`v y` and the displacement `v (x - y)`. -/
theorem le_max_sub (v : Valuation R Γ₀) (x y : R) :
    v x ≤ max (v y) (v (x - y)) := by
  have he : y + (x - y) = x := by simp [sub_eq_add_neg]
  calc v x = v (y + (x - y)) := by rw [he]
    _ ≤ max (v y) (v (x - y)) := v.map_add _ _

end Valuation

end
