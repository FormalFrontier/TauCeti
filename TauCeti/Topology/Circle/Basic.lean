/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# A point of the circle and its inverse

Mathlib's `Circle` is the unit circle of `ℂ` as a group. This file records when a point of it is
separated from its inverse: `z - z⁻¹` vanishes exactly at the two square roots of `1`, the points
`z = ±1`. The chord and arc geometry of the circle is
`TauCeti/Topology/Circle/Metric.lean`; this is the algebraic fact that precedes it.

## Main results

* `TauCeti.circle_sub_inv_ne_zero` — `z - z⁻¹ ≠ 0` for a point `z` of the circle with `z² ≠ 1`.
-/

public section

namespace TauCeti

/-- **A point of the circle is separated from its inverse once `z² ≠ 1`**: `z - z⁻¹` vanishes only
at the two points `z = ±1` of the circle. -/
theorem circle_sub_inv_ne_zero {z : Circle} (hz : (z : ℂ) ^ 2 ≠ 1) :
    (z : ℂ) - ((z : ℂ))⁻¹ ≠ 0 := by
  intro hc
  refine hz ?_
  rw [sub_eq_zero] at hc
  calc (z : ℂ) ^ 2 = (z : ℂ) * ((z : ℂ))⁻¹ := by rw [← hc, sq]
    _ = 1 := mul_inv_cancel₀ z.coe_ne_zero

end TauCeti
