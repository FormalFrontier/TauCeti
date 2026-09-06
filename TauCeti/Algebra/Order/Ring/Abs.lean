/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Products of nearby reals

If two nonnegative reals are each within `e` of `q`, their product is within `e (2q + e)` of
`q²`: the quantitative form of continuity of multiplication used when a measure is compared with
its own square.
-/

public section

namespace TauCeti

/-- `|x y - q²| ≤ e (2q + e)` when `x` and `y` are within `e` of `q ≥ 0` and `y ≥ 0`. -/
theorem abs_mul_sub_mul_self_le {x y q e : ℝ} (hx : |x - q| ≤ e) (hy : |y - q| ≤ e)
    (hy0 : 0 ≤ y) (hq0 : 0 ≤ q) (he : 0 ≤ e) :
    |x * y - q * q| ≤ e * (2 * q + e) := by
  have heq : x * y - q * q = (x - q) * y + q * (y - q) := by ring
  have hyq : y ≤ q + e := by linarith [(abs_le.1 hy).2]
  calc |x * y - q * q| ≤ |(x - q) * y| + |q * (y - q)| := by
        rw [heq]; exact abs_add_le _ _
    _ = |x - q| * y + q * |y - q| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hy0, abs_of_nonneg hq0]
    _ ≤ e * (q + e) + q * e := by gcongr
    _ = e * (2 * q + e) := by ring

end TauCeti
