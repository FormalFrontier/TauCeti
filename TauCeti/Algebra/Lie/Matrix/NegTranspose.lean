/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.Matrix

/-!
# Negative transpose as a Lie algebra automorphism

Transposition reverses multiplication of square matrices. Consequently negative transposition,
`X ↦ -Xᵀ`, preserves the commutator bracket and is an involutive Lie algebra automorphism. This
file packages that standard construction as `Matrix.negTransposeLieEquiv`.

The negative sign is essential: transposition alone is a Lie algebra anti-automorphism. The
result is the linear-algebra input to graph automorphisms of classical Lie algebras, especially
the type-`A` diagram reversal on `sl_n`.

## Main declarations

* `Matrix.negTransposeLieEquiv`: the involutive Lie algebra automorphism `X ↦ -Xᵀ`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Section 14.
* R. W. Carter, *Simple Groups of Lie Type*, Section 12.2.
-/

public section

namespace Matrix

universe u v

variable (n : Type u) (R : Type v)
variable [Fintype n] [DecidableEq n] [CommRing R]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Negative transposition `X ↦ -Xᵀ` is an involutive automorphism of the matrix Lie algebra.

Transposition reverses an associative product, while the negative sign reverses the resulting
commutator once more. -/
def negTransposeLieEquiv : Matrix n n R ≃ₗ⁅R⁆ Matrix n n R where
  __ := (transposeLinearEquiv n n R R).trans (LinearEquiv.neg R)
  map_lie' {X Y} := by
    simp only [LieRing.of_associative_ring_bracket]
    simp

/-- Negative transposition evaluates as `-Xᵀ`. -/
@[simp]
theorem negTransposeLieEquiv_apply (X : Matrix n n R) :
    negTransposeLieEquiv n R X = -Xᵀ := (rfl)

/-- The inverse of negative transposition is negative transposition itself. -/
@[simp]
theorem negTransposeLieEquiv_symm :
    (negTransposeLieEquiv n R).symm = negTransposeLieEquiv n R := (rfl)

end Matrix
