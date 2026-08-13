/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RingTheory.Nilpotent.Exp
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# Conjugation as the exponential of the adjoint action

`TauCeti/RingTheory/Nilpotent/Exp.lean` shows that for a nilpotent element `a` of an associative
`ℚ`-algebra `A` the exponential of the commutator endomorphism `b ↦ a * b - b * a` is conjugation
by the unit `exp a`. This file restates that identity for the adjoint action of the Lie algebra
underlying `A`:

```text
exp (ad a) b = exp a * b * exp (-a).
```

Mathlib already knows that the exponential of a nilpotent derivation is a Lie algebra automorphism
(`LieDerivation.exp`); what is added here is that for an *inner* derivation that automorphism is an
explicit conjugation. This is the identity that rewrites a conjugate of a root subgroup element of
a Chevalley--Demazure group scheme as another exponential, so it is the algebraic source of the
Chevalley commutator relations.

The Lie ring structure on an associative ring is only a local instance in Mathlib
(`LieRing.ofAssociativeRing`), so a consumer of these lemmas has to make it local too; the
instance-free spelling `TauCeti.exp_mulLeft_sub_mulRight_apply` stays available for consumers that
would rather not.

## Main results

* `TauCeti.exp_ad_apply`: `exp (ad a)` is conjugation by `exp a`.
* `TauCeti.exp_mul_eq_exp_ad_apply_mul`: moving `exp a` past a ring element rewrites it through
  the adjoint action.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* R. W. Carter, *Simple Groups of Lie Type*, §4.
-/

public section

namespace TauCeti

open IsNilpotent

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- **Conjugation is the exponential of the adjoint action.** For a nilpotent `a`, the automorphism
`exp (ad a)` of the Lie algebra underlying `A` is conjugation by the unit `exp a`. -/
theorem exp_ad_apply {a : A} (ha : IsNilpotent a) (b : A) :
    exp (LieAlgebra.ad ℚ A a) b = exp a * b * exp (-a) := by
  rw [congrFun (LieAlgebra.ad_eq_lmul_left_sub_lmul_right (R := ℚ) A) a]
  simp only [Pi.sub_apply]
  exact exp_mulLeft_sub_mulRight_apply ha b

/-- Moving an exponential of a nilpotent element past a ring element rewrites it through the
adjoint action. -/
theorem exp_mul_eq_exp_ad_apply_mul {a : A} (ha : IsNilpotent a) (b : A) :
    exp a * b = exp (LieAlgebra.ad ℚ A a) b * exp a := by
  rw [exp_ad_apply ha, mul_assoc, exp_neg_mul_exp_self ha, mul_one]

end TauCeti
