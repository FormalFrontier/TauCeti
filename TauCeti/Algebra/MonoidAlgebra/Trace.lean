/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Algebra.MonoidAlgebra.Basis

/-!
# The trace of multiplication by an element of a finite group algebra

For a finite group `G` the group algebra `k[G]` is free on the group elements, so multiplication
by a fixed element `x` is an endomorphism of a finite free module and has a trace. In the basis of
group elements the matrix of *right* multiplication by `x` has `g`-th diagonal entry `x_1`,
because `g * h = g` forces `h = 1`; the trace is therefore `|G| * x_1`, and it sees nothing of `x`
beyond its coefficient at the identity. The same count on the left gives the same answer.

The special case `x = g` recovers the character of the regular representation, but the general
statement is what identifies the scalar in an essential idempotence `c * c = a • c`, by pairing
with `TauCeti.LinearMap.trace_eq_mul_finrank_range`.

## Main statements

* `TauCeti.MonoidAlgebra.trace_mulRight`: the trace of right multiplication by `x` on `k[G]` is
  `|G| * x_1`.
* `TauCeti.MonoidAlgebra.trace_mulLeft`: the same for left multiplication.
-/

public section

open MonoidAlgebra

namespace TauCeti

/-- **The trace of right multiplication on a finite group algebra.** Multiplication on the right
by `x` has trace `|G| * x_1`. -/
theorem MonoidAlgebra.trace_mulRight {k G : Type*} [CommRing k] [Group G] [Finite G]
    (x : MonoidAlgebra k G) :
    LinearMap.trace k (MonoidAlgebra k G) (LinearMap.mulRight k x) =
      (Nat.card G : k) * x.coeff 1 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  rw [LinearMap.trace_eq_matrix_trace k (MonoidAlgebra.basis G k), Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply,
    MonoidAlgebra.basis_repr, LinearMap.mulRight_apply,
    MonoidAlgebra.coeff_single_mul_apply, one_mul, inv_mul_cancel,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Nat.card_eq_fintype_card]

/-- **The trace of left multiplication on a finite group algebra.** Multiplication on the left by
`x` has trace `|G| * x_1`, the same as multiplication on the right. -/
theorem MonoidAlgebra.trace_mulLeft {k G : Type*} [CommRing k] [Group G] [Finite G]
    (x : MonoidAlgebra k G) :
    LinearMap.trace k (MonoidAlgebra k G) (LinearMap.mulLeft k x) =
      (Nat.card G : k) * x.coeff 1 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  rw [LinearMap.trace_eq_matrix_trace k (MonoidAlgebra.basis G k), Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply,
    MonoidAlgebra.basis_repr, LinearMap.mulLeft_apply,
    MonoidAlgebra.coeff_mul_single_apply, mul_one, mul_inv_cancel,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Nat.card_eq_fintype_card]

end TauCeti
