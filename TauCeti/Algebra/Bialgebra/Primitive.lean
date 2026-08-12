/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Primitive elements in a bialgebra

This file records the binomial formula for the comultiplication of a power of a primitive
element in an arbitrary bialgebra. The two tensor factors commute even when the bialgebra itself
is noncommutative.

## Main results

* `TauCeti.Bialgebra.comul_pow_of_primitive`: the comultiplication of a power of a primitive
  element is its binomial expansion.
-/

public section

open scoped TensorProduct

namespace TauCeti.Bialgebra

universe u w

/-- The comultiplication of a power of a primitive element is its binomial expansion. -/
theorem comul_pow_of_primitive
    {R : Type u} {A : Type w} [CommSemiring R] [Semiring A] [Bialgebra R A]
    (a : A) (h : Coalgebra.comul a = a ⊗ₜ[R] 1 + 1 ⊗ₜ[R] a) (n : ℕ) :
    (Coalgebra.comul (R := R)) (a ^ n) =
      ∑ mn ∈ Finset.antidiagonal n, n.choose mn.1 •
        ((a ^ mn.1) ⊗ₜ[R] (a ^ mn.2)) := by
  rw [Bialgebra.comul_pow, h]
  have hcomm : Commute (a ⊗ₜ[R] 1) (1 ⊗ₜ[R] a) :=
    (Commute.one_right _).tmul (Commute.one_left _)
  rw [hcomm.add_pow']
  simp only [Algebra.TensorProduct.tmul_pow, one_pow,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end TauCeti.Bialgebra
