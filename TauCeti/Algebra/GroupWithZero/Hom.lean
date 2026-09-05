/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.GroupWithZero.Defs

/-!
# Unitality of a multiplicative map

A multiplicative map need not preserve `1`, and the zero map shows it need not. Where
multiplication in the codomain is left-cancellative away from zero there is nothing in between:
such a map is identically zero or unital, the zero map being the only non-unital one. A unital
one is promoted to a bundled unital map by `AlgHom.ofLinearMap` or `RingHom.mk'`.

This is the dichotomy that lets a type of multiplicative maps carry a zero without adjoining one.

## Main results

* `MulHomClass.forall_apply_eq_zero_or_map_one`: such a map vanishes identically or sends `1`
  to `1`.

## Implementation notes

The statement is class-general, over `MulHomClass`, so it holds of every bundled multiplicative
map type — `MonoidHom`, `RingHom`, `NonUnitalAlgHom` — without a specialisation for each. Its
vanishing alternative is pointwise, `∀ x, p x = 0`, rather than `p = 0`, because the class
carries no `Zero` on the map type.
-/

public section

variable {A B G : Type*} [MulOneClass A] [MulZeroOneClass B] [IsLeftCancelMulZero B]
  [FunLike G A B] [MulHomClass G A B]

namespace MulHomClass

/-- **A multiplicative map vanishes identically or is unital.** -/
-- Both branches are one rewrite: at `p 1 = 0` every `x = x * 1` is killed, and otherwise `p 1`
-- cancels from `p 1 * p 1 = p 1 * 1`.
theorem forall_apply_eq_zero_or_map_one (p : G) : (∀ x, p x = 0) ∨ p 1 = 1 := by
  by_cases h1 : p 1 = 0
  · exact Or.inl fun x => by rw [← mul_one x, map_mul, h1, mul_zero]
  · refine Or.inr (mul_left_cancel₀ h1 ?_)
    rw [← map_mul, mul_one, mul_one]

/-- **A multiplicative map that is somewhere nonzero is unital.** -/
theorem map_one_of_exists_apply_ne_zero {p : G} (hp : ∃ x, p x ≠ 0) : p 1 = 1 :=
  (forall_apply_eq_zero_or_map_one p).resolve_left fun h => by
    obtain ⟨x, hx⟩ := hp
    exact hx (h x)

end MulHomClass

end
