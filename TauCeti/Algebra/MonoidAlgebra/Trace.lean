/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Algebra.MonoidAlgebra.Basis

/-!
# The trace of multiplication by an element of a finite monoid algebra

For a finite monoid `G` the monoid algebra `k[G]` is free on the monoid elements, so multiplication
by a fixed element `x` is an endomorphism of a finite free module and has a trace. In the basis of
monoid elements the matrix of *right* multiplication by `x` has `g`-th diagonal entry `x_1`,
because `g * h = g` forces `h = 1` as soon as `G` cancels on the left; the trace is therefore
`|G| * x_1`, and it sees nothing of `x` beyond its coefficient at the identity. The same count on
the left needs cancellation on the right and gives the same answer, in the matrix form
`TauCeti.trace_leftMulMatrix_monoidAlgebra` that the character-table files consume. A group cancels
on both sides, so all three statements apply to a finite group algebra.

The special case `x = g` recovers the character of the regular representation, but the general
statement is what identifies the scalar in an essential idempotence `c * c = a • c`, by pairing
with `TauCeti.LinearMap.trace_eq_mul_finrank_range`.

## Main statements

* `TauCeti.trace_leftMulMatrix_monoidAlgebra`: the matrix form, the trace of the left regular
  matrix of `x` is `|G| * x_1`.
* `TauCeti.MonoidAlgebra.trace_mulRight`: the trace of right multiplication by `x` on `k[G]` is
  `|G| * x_1`.
* `TauCeti.MonoidAlgebra.trace_mulLeft`: the same for left multiplication.
-/

public section

open MonoidAlgebra

namespace TauCeti

/-- **The regular trace reads off the coefficient at the identity.** Every diagonal entry of the
left regular matrix of `x` is the coefficient of `x` at `1`, so the trace is `|G|` times it. -/
@[simp]
theorem trace_leftMulMatrix_monoidAlgebra {k G : Type*} [CommSemiring k] [Monoid G]
    [IsRightCancelMul G] [Fintype G] [DecidableEq G] (x : MonoidAlgebra k G) :
    Matrix.trace (Algebra.leftMulMatrix (MonoidAlgebra.basis G k) x) =
      (Fintype.card G : k) * x.coeff 1 := by
  have hdiag : ∀ g : G, (x * MonoidAlgebra.single g (1 : k)).coeff g = x.coeff 1 := fun g => by
    simpa using x.coeff_mul_single_eq_coeff_mul (m₁ := g) (r := 1) 1 (by simp)
  simp [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, hdiag, Finset.card_univ]

/-- **The trace of right multiplication on a finite monoid algebra.** Multiplication on the right
by `x` has trace `|G| * x_1`. -/
@[simp]
theorem MonoidAlgebra.trace_mulRight {k G : Type*} [CommSemiring k] [Monoid G]
    [IsLeftCancelMul G] [Finite G] (x : MonoidAlgebra k G) :
    LinearMap.trace k (MonoidAlgebra k G) (LinearMap.mulRight k x) =
      (Nat.card G : k) * x.coeff 1 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hdiag : ∀ g : G, (MonoidAlgebra.single g (1 : k) * x).coeff g = x.coeff 1 := fun g => by
    simpa using x.coeff_single_mul_eq_mul_coeff (m₁ := g) (r := 1) 1 (by simp)
  rw [LinearMap.trace_eq_matrix_trace k (MonoidAlgebra.basis G k), Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply,
    MonoidAlgebra.basis_repr, LinearMap.mulRight_apply, hdiag,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Nat.card_eq_fintype_card]

/-- **The trace of left multiplication on a finite monoid algebra.** Multiplication on the left by
`x` has trace `|G| * x_1`, the same as multiplication on the right. -/
@[simp]
theorem MonoidAlgebra.trace_mulLeft {k G : Type*} [CommSemiring k] [Monoid G]
    [IsRightCancelMul G] [Finite G] (x : MonoidAlgebra k G) :
    LinearMap.trace k (MonoidAlgebra k G) (LinearMap.mulLeft k x) =
      (Nat.card G : k) * x.coeff 1 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  rw [LinearMap.trace_eq_matrix_trace k (MonoidAlgebra.basis G k), Algebra.toMatrix_lmul_eq,
    trace_leftMulMatrix_monoidAlgebra, Nat.card_eq_fintype_card]

end TauCeti
