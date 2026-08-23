/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Smeval

public section

/-!
# Scalar-multiple polynomial evaluation in an opposite monoid

`Polynomial.smeval` evaluates a polynomial at an element of an additive commutative monoid with
natural number powers and an action of the coefficient semiring. All three of those structures
are inherited by the opposite monoid, and `MulOpposite.unop` respects each of them, so evaluation
commutes with `MulOpposite.unop`.

This is what transports a statement proved through an antihomomorphism -- a homomorphism to the
opposite ring -- back to the ring itself, in the situation where only powers of a single element
occur and multiplication is therefore never actually reversed. The antipode of a universal
enveloping algebra applied to a generalized binomial coefficient is such a situation, since
`Ring.choose` is a rational multiple of the value of `descPochhammer` at one element.

## Main results

* `TauCeti.Polynomial.unop_smeval`: `MulOpposite.unop` commutes with `Polynomial.smeval`.
-/

namespace TauCeti.Polynomial

/-- Evaluating a polynomial at an element of an opposite monoid and then taking
`MulOpposite.unop` is the same as evaluating at the `MulOpposite.unop` of that element. -/
@[simp]
theorem unop_smeval {R A : Type*} [Semiring R] [Monoid A] [AddCommMonoid A] [Module R A]
    (p : _root_.Polynomial R) (a : Aᵐᵒᵖ) :
    (p.smeval a).unop = p.smeval a.unop := by
  induction p using _root_.Polynomial.induction_on' with
  | add p q hp hq =>
    rw [_root_.Polynomial.smeval_add, MulOpposite.unop_add, hp, hq,
      _root_.Polynomial.smeval_add]
  | monomial n c =>
    rw [_root_.Polynomial.smeval_monomial, MulOpposite.unop_smul, MulOpposite.unop_pow,
      _root_.Polynomial.smeval_monomial]

end TauCeti.Polynomial
