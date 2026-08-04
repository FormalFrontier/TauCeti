/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Ring.Units
import Mathlib.Tactic.NoncommRing

/-!
# `1 + a * b` is a unit exactly when `1 + b * a` is

In a ring, possibly noncommutative, the two products `a * b` and `b * a` are generally unrelated,
but `1 + a * b` and `1 + b * a` are invertible together: if `v` inverts `1 + a * b`, then
`1 - b * v * a` inverts `1 + b * a`. This is the elementwise shadow of the fact that `a * b` and
`b * a` have the same spectrum away from `0`, and it is the mechanism behind the left-right
symmetry of the Jacobson radical.

Mathlib carries this computation only as an unnamed step inside the proof of
`spectrum.unit_mem_mul_comm`; here it is stated on its own.

## Main results

* `TauCeti.isUnit_one_add_mul_comm`: `IsUnit (1 + a * b) ↔ IsUnit (1 + b * a)`.
* `TauCeti.isUnit_one_sub_mul_comm`: `IsUnit (1 - a * b) ↔ IsUnit (1 - b * a)`.
-/

public section

namespace TauCeti

variable {R : Type*} [Ring R]

/-- If `1 + a * b` is a unit then so is `1 + b * a`: an explicit inverse is `1 - b * v * a`,
where `v` inverts `1 + a * b`. -/
theorem isUnit_one_add_mul_swap {a b : R} (h : IsUnit (1 + a * b)) : IsUnit (1 + b * a) := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨v, hv, hv'⟩ : ∃ v : R, (1 + a * b) * v = 1 ∧ v * (1 + a * b) = 1 :=
    ⟨((u⁻¹ : Rˣ) : R), by rw [← hu, u.mul_inv], by rw [← hu, u.inv_mul]⟩
  refine ⟨⟨1 + b * a, 1 - b * v * a, ?_, ?_⟩, rfl⟩
  · calc (1 + b * a) * (1 - b * v * a)
        = 1 + b * a - b * ((1 + a * b) * v) * a := by noncomm_ring
      _ = 1 := by rw [hv]; noncomm_ring
  · calc (1 - b * v * a) * (1 + b * a)
        = 1 + b * a - b * (v * (1 + a * b)) * a := by noncomm_ring
      _ = 1 := by rw [hv']; noncomm_ring

/-- `1 + a * b` is a unit exactly when `1 + b * a` is. -/
theorem isUnit_one_add_mul_comm {a b : R} : IsUnit (1 + a * b) ↔ IsUnit (1 + b * a) :=
  ⟨isUnit_one_add_mul_swap, isUnit_one_add_mul_swap⟩

/-- `1 - a * b` is a unit exactly when `1 - b * a` is. -/
theorem isUnit_one_sub_mul_comm {a b : R} : IsUnit (1 - a * b) ↔ IsUnit (1 - b * a) := by
  simpa [sub_eq_add_neg] using isUnit_one_add_mul_comm (a := -a) (b := b)

end TauCeti
