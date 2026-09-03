/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.EReal.Operations

/-!
# Operations on extended real numbers

This file supplements Mathlib's API for arithmetic operations on `EReal`.

## Main results

* `EReal.iInf_sub_coe` — subtracting a real constant commutes with an infimum in `EReal`.
-/

public section

noncomputable section

namespace TauCeti

/-- Subtracting a real constant commutes with an infimum in `EReal`; both sides are `⊤` when the
index type is empty. -/
theorem _root_.EReal.iInf_sub_coe {ι : Sort*} (f : ι → EReal) (a : ℝ) :
    (⨅ i, (f i - (a : EReal))) = (⨅ i, f i) - (a : EReal) := by
  refine le_antisymm ?_ (le_iInf fun i => EReal.sub_le_sub (iInf_le f i) le_rfl)
  rw [EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot a)) (.inl (EReal.coe_ne_top a))]
  exact le_iInf fun i => EReal.add_le_of_le_sub (iInf_le _ i)

end TauCeti

end

end
