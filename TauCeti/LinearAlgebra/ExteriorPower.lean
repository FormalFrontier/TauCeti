/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Vanishing of exterior powers above the rank

This file records that the `d`th exterior power of a finite free module over a nontrivial
commutative ring vanishes as soon as `d` exceeds the rank of the module.

## Main results

* `exteriorPower.eq_zero_of_finrank_lt` states that every element of `⋀[R]^d M` is zero when
  `Module.finrank R M < d`.

## References

The proof reads the statement off Mathlib's exterior-power dimension formula
`exteriorPower.finrank_eq`, from `Mathlib.LinearAlgebra.ExteriorPower.Basis`, by Sophie Morel
and Daniel Morrison.
-/

public section

universe u w

variable {R : Type u} {M : Type w}

namespace exteriorPower

variable [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]

/-- An exterior power above the rank of a finite free module is zero. -/
theorem eq_zero_of_finrank_lt (d : ℕ) (h : Module.finrank R M < d) (x : ⋀[R]^d M) :
    x = 0 := by
  have : Subsingleton (⋀[R]^d M) := by
    rw [← Module.finrank_eq_zero_iff_of_free R, finrank_eq, Nat.choose_eq_zero_iff]
    exact h
  exact Subsingleton.elim x 0

end exteriorPower
