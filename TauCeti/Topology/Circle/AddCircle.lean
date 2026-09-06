/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The additive circle and the complex unit circle

For a nonzero real period `T`, Mathlib's `AddCircle.homeomorphCircle` identifies `AddCircle T`
with the complex unit circle `Circle`. This file records where that identification sends the
distinguished points: `0 : AddCircle T` is the point `1 : Circle`, so the inverse homeomorphism
carries `1` back to `0`.

## Main results

* `AddCircle.homeomorphCircle_symm_one` — the inverse circle homeomorphism sends `1` to `0` for
  every nonzero real period.
-/

public section

namespace AddCircle

/-- The inverse homeomorphism `AddCircle.homeomorphCircle.symm` carries `1 : Circle` to `0`. -/
@[simp]
theorem homeomorphCircle_symm_one {T : ℝ} (hT : T ≠ 0) :
    (AddCircle.homeomorphCircle hT).symm 1 = 0 := by
  rw [Homeomorph.symm_apply_eq, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_zero]

end AddCircle
