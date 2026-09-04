/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Algebra.Module.Defs

/-!
# Powers of negative one in a ground ring

This file provides the cast to a ground ring of Mathlib's unit-valued sign character
`Int.negOnePow : ℤ → ℤˣ`; the cast factors through `ℤ`.

## Main definitions

* `TauCeti.negOnePowCast`: the scalar `(-1) ^ e` in a ground ring.
-/

public section

universe uR uA

namespace TauCeti

section NegOnePowCast

variable {R : Type uR} [Ring R]

variable (R) in
/-- The scalar `(-1) ^ e` in a ground ring. -/
def negOnePowCast (e : ℤ) : R := ((e.negOnePow : ℤ) : R)

/-- The ground-ring sign is the cast of Mathlib's `Int.negOnePow`. -/
theorem negOnePowCast_eq_intCast (e : ℤ) : negOnePowCast R e = ((e.negOnePow : ℤ) : R) :=
  (rfl)

@[simp]
theorem negOnePowCast_zero : negOnePowCast R 0 = 1 := by simp [negOnePowCast]

@[simp]
theorem negOnePowCast_one : negOnePowCast R 1 = -1 := by simp [negOnePowCast]

@[simp]
theorem negOnePowCast_neg (a : ℤ) : negOnePowCast R (-a) = negOnePowCast R a := by
  simp [negOnePowCast]

theorem negOnePowCast_add (a b : ℤ) :
    negOnePowCast R (a + b) = negOnePowCast R a * negOnePowCast R b := by
  simp [negOnePowCast, Int.negOnePow_add]

@[simp]
theorem negOnePowCast_two_mul (a : ℤ) : negOnePowCast R (2 * a) = 1 := by
  simp [negOnePowCast]

theorem negOnePowCast_even {e : ℤ} (he : Even e) : negOnePowCast R e = 1 := by
  simp [negOnePowCast, Int.negOnePow_even _ he]

theorem negOnePowCast_odd {e : ℤ} (he : Odd e) : negOnePowCast R e = -1 := by
  simp [negOnePowCast, Int.negOnePow_odd _ he]

variable {A : Type uA} [AddCommMonoid A] [Module R A]

/-- The scalar `(-1) ^ e` acts as an involution. -/
@[simp]
theorem negOnePowCast_smul_negOnePowCast_smul (e : ℤ) (a : A) :
    negOnePowCast R e • (negOnePowCast R e • a) = a := by
  rw [smul_smul, ← negOnePowCast_add, ← two_mul, negOnePowCast_two_mul, one_smul]

@[simp]
theorem negOnePowCast_smul_eq_zero_iff (e : ℤ) (a : A) :
    negOnePowCast R e • a = 0 ↔ a = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rw [← negOnePowCast_smul_negOnePowCast_smul (R := R) e a, h, smul_zero]

end NegOnePowCast

end TauCeti
