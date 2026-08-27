/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# The resultant against a reversed linear factor

Mathlib evaluates the resultant against the linear polynomial `X - C x` on either side
(`Polynomial.resultant_X_sub_C_left`, `Polynomial.resultant_X_sub_C_right`). This file records the
companion for the *reversed* polynomial `C x - X`, which is the shape that arises as `x - θ` in
`AdjoinRoot f`: the answer is `f.eval x`, with **no sign**.

That absence is the point. `C x - X` is `C (-1) * (X - C x)`, which contributes `(-1) ^ m`, and
`resultant_X_sub_C_right` contributes another `(-1) ^ m`, so the two cancel.

## Main results

* `Polynomial.resultant_C_sub_X_right`

## Provenance

Adapted from Michael Stoll's `EllipticCurves`
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0) at commit
`66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, `EllipticCurves/Mathlib/Basic.lean` line 615, where
it is a Mathlib-bound prerequisite of the explicit `2`-descent.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- The resultant of `f` with the reversed linear polynomial `C x - X` is `f.eval x`. Note the
absence of a sign: `C x - X` is `-(X - C x)`, and the two signs cancel. -/
@[simp]
theorem resultant_C_sub_X_right (f : R[X]) (x : R) (m : ℕ) (hm : f.natDegree ≤ m) :
    f.resultant (C x - X) m 1 = f.eval x := by
  -- `C x - X` is `X - C x` scaled by the constant `-1`
  have hneg : C x - X = C (-1 : R) * (X - C x) := by simp
  rw [hneg, resultant_C_mul_right, resultant_X_sub_C_right f m x hm, ← mul_assoc, ← pow_add,
    ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

end Polynomial
