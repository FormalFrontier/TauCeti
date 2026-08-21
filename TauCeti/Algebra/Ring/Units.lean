/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Basic

/-!
# `1 + a * b` is a unit exactly when `1 + b * a` is

In a ring, possibly noncommutative, the two products `a * b` and `b * a` are generally unrelated,
but `1 + a * b` and `1 + b * a` are invertible together. This is the elementwise shadow of the
fact that `a * b` and `b * a` have the same spectrum away from `0`, and it is the mechanism behind
the left-right symmetry of the Jacobson radical.

Mathlib records the spectral statement as `spectrum.unit_mem_mul_comm`. The elementwise form is
that statement for the base ring `ℤ`, read at the unit `1`, and that is how it is obtained here.

## Main results

* `TauCeti.isUnit_one_sub_mul_comm`: `IsUnit (1 - a * b) ↔ IsUnit (1 - b * a)`.
* `TauCeti.isUnit_one_add_mul_comm`: `IsUnit (1 + a * b) ↔ IsUnit (1 + b * a)`.
-/

public section

namespace TauCeti

variable {R : Type*} [Ring R]

/-- `1 - a * b` is a unit exactly when `1 - b * a` is.

This is `spectrum.unit_mem_mul_comm` over the base ring `ℤ`, at the unit `1`. -/
theorem isUnit_one_sub_mul_comm {a b : R} : IsUnit (1 - a * b) ↔ IsUnit (1 - b * a) := by
  have h := spectrum.unit_mem_mul_comm (R := ℤ) (a := a) (b := b) (r := 1)
  simpa only [spectrum.mem_iff, Units.val_one, map_one, not_iff_not] using h

/-- `1 + a * b` is a unit exactly when `1 + b * a` is. -/
theorem isUnit_one_add_mul_comm {a b : R} : IsUnit (1 + a * b) ↔ IsUnit (1 + b * a) := by
  simpa only [neg_mul, mul_neg, sub_neg_eq_add] using isUnit_one_sub_mul_comm (a := -a) (b := b)

end TauCeti
