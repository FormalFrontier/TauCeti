/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Basic

/-!
# Reading a four-factor product identity as a quotient

A relation `a * b * k = c * d` in a group can be read as a statement about the quotient
`a⁻¹ * c`: it says that quotient is `b * k * d⁻¹`. That is the form wanted whenever two
factorisations of the same element are compared and one asks how far apart their left-hand
factors are, the answer being an expression in the right-hand ones.

## Main results

* `inv_mul_eq_mul_mul_inv_of_mul_mul_eq_mul`: from `a * b * k = c * d` it follows that
  `a⁻¹ * c = b * k * d⁻¹`.
-/

public section

/-- From `a * b * k = c * d`, the quotient `a⁻¹ * c` of the two left-hand factors is
`b * k * d⁻¹`. Cancelling `a` on the left and `d` on the right turns the goal back into the
hypothesis. -/
@[to_additive /-- From `a + b + k = c + d`, the difference `-a + c` of the two left-hand
summands is `b + k + -d`. -/]
lemma inv_mul_eq_mul_mul_inv_of_mul_mul_eq_mul {G : Type*} [Group G] {a b k c d : G}
    (h : a * b * k = c * d) : a⁻¹ * c = b * k * d⁻¹ := by
  apply mul_left_cancel (a := a)
  apply mul_right_cancel (b := d)
  simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel, mul_one]
  simp only [mul_assoc] at h
  exact h.symm

end
