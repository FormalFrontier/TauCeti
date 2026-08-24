/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Ring.Idempotent

import Mathlib.Tactic.Abel

/-!
# The idempotents cut out by a square root of one

Let `A` be an algebra over a commutative ring `R` in which `2` is invertible, and let `ω : A`. The
element

`TauCeti.halfOneAdd R ω = ½ (1 + ω)`

and its companion `TauCeti.halfOneAdd R (-ω) = ½ (1 - ω)` always add up to `1`
(`TauCeti.halfOneAdd_add_halfOneAdd_neg`) and always differ by `ω`
(`TauCeti.halfOneAdd_sub_halfOneAdd_neg`). As soon as `ω * ω = 1` they are moreover orthogonal
(`TauCeti.halfOneAdd_mul_halfOneAdd_neg`) and therefore idempotent
(`TauCeti.isIdempotentElem_halfOneAdd`): a square root of one always cuts out a **complementary
orthogonal pair** of idempotents. The right ideals `e₊ A` and `e₋ A` are two-sided, and the
resulting decomposition is one of rings, only when the idempotents are central, which is more than
this file assumes. If `ω` commutes with a given element then so do both idempotents
(`TauCeti.commute_halfOneAdd`), and elements written in the form `e₊ a + e₋ b` then multiply
componentwise (`TauCeti.halfOneAdd_mul_add_mul`).

Nothing here is specific to any one algebra:
`TauCeti/LinearAlgebra/CliffordAlgebra/OddSplitting.lean` runs it on a central odd square root of
one in a Clifford algebra, where the two blocks turn out to be copies of the even subalgebra.

Mathlib has `IsIdempotentElem` and its complement API
(`IsIdempotentElem.of_mul_add`, `IsIdempotentElem.one_sub_mul_self`), which is what the proofs below
consume, but not the passage from a square root of one to the idempotent pair.

## Main definitions

* `TauCeti.halfOneAdd`: the element `½ (1 + ω)`. No property of `ω` is built into it, so that the
  complementary idempotent is literally the same construction applied to `-ω`.

## Main results

* `TauCeti.halfOneAdd_add_halfOneAdd_neg`, `TauCeti.halfOneAdd_sub_halfOneAdd_neg`: the pair is
  complementary, and its difference recovers `ω`.
* `TauCeti.halfOneAdd_mul_halfOneAdd_neg`, `TauCeti.isIdempotentElem_halfOneAdd`: for a square root
  of one the pair is orthogonal and idempotent.
* `TauCeti.halfOneAdd_mul_add_mul`: **the multiplication rule** `(e₊ a + e₋ b) (e₊ c + e₋ d)
  = e₊ (a c) + e₋ (b d)`, for `a` and `b` commuting with `ω`.
-/

public section

namespace TauCeti

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Algebra R A] [Invertible (2 : R)]

/-- The element `½ (1 + ω)` of an `R`-algebra, for `2` invertible in `R`.

It is idempotent when `ω * ω = 1` (`TauCeti.isIdempotentElem_halfOneAdd`), and then
`halfOneAdd R (-ω) = ½ (1 - ω)` is the complementary idempotent. No property of `ω` is built into
the definition, so that the two idempotents are literally the same construction applied to `ω` and
to `-ω`. -/
noncomputable def halfOneAdd (ω : A) : A := (⅟2 : R) • (1 + ω)

/-- The defining formula for `TauCeti.halfOneAdd`. -/
theorem halfOneAdd_def (ω : A) : halfOneAdd R ω = (⅟2 : R) • (1 + ω) := (rfl)

/-- **The pair is complementary**: `½ (1 + ω) + ½ (1 - ω) = 1`. -/
@[simp]
theorem halfOneAdd_add_halfOneAdd_neg (ω : A) : halfOneAdd R ω + halfOneAdd R (-ω) = 1 := by
  rw [halfOneAdd_def, halfOneAdd_def, ← smul_add]
  have h : (1 + ω) + (1 + -ω) = (2 : R) • (1 : A) := by rw [two_smul]; abel
  rw [h, invOf_smul_smul]

/-- **The difference of the pair is `ω`**: `½ (1 + ω) - ½ (1 - ω) = ω`. This is what makes `ω`
recoverable from the splitting it induces. -/
@[simp]
theorem halfOneAdd_sub_halfOneAdd_neg (ω : A) : halfOneAdd R ω - halfOneAdd R (-ω) = ω := by
  rw [halfOneAdd_def, halfOneAdd_def, ← smul_sub]
  have h : (1 + ω) - (1 + -ω) = (2 : R) • ω := by rw [two_smul]; abel
  rw [h, invOf_smul_smul]

/-- The companion element is the complement `1 - ½ (1 + ω)`, the form in which Mathlib's
`IsIdempotentElem` API talks about it. -/
theorem halfOneAdd_neg_eq_one_sub (ω : A) : halfOneAdd R (-ω) = 1 - halfOneAdd R ω :=
  eq_sub_of_add_eq' (halfOneAdd_add_halfOneAdd_neg R ω)

variable {ω : A}

/-- **The pair is orthogonal** when `ω` squares to `1`: `½ (1 + ω) · ½ (1 - ω) = 0`. -/
theorem halfOneAdd_mul_halfOneAdd_neg (hsq : ω * ω = 1) :
    halfOneAdd R ω * halfOneAdd R (-ω) = 0 := by
  have h : (1 + ω) * (1 + -ω) = 0 := by
    rw [add_mul, one_mul, mul_add, mul_one, mul_neg, hsq]
    abel
  rw [halfOneAdd_def, halfOneAdd_def, smul_mul_assoc, mul_smul_comm, h, smul_zero, smul_zero]

/-- **`½ (1 + ω)` is idempotent** when `ω` squares to `1`. -/
theorem isIdempotentElem_halfOneAdd (hsq : ω * ω = 1) : IsIdempotentElem (halfOneAdd R ω) :=
  (IsIdempotentElem.of_mul_add (halfOneAdd_mul_halfOneAdd_neg R hsq)
    (halfOneAdd_add_halfOneAdd_neg R ω)).1

/-- **`½ (1 - ω)` is idempotent** when `ω` squares to `1`; it is the complementary idempotent. -/
theorem isIdempotentElem_halfOneAdd_neg (hsq : ω * ω = 1) :
    IsIdempotentElem (halfOneAdd R (-ω)) :=
  (IsIdempotentElem.of_mul_add (halfOneAdd_mul_halfOneAdd_neg R hsq)
    (halfOneAdd_add_halfOneAdd_neg R ω)).2

/-- The reverse orthogonality `½ (1 - ω) · ½ (1 + ω) = 0`, read off the complement. -/
theorem halfOneAdd_neg_mul_halfOneAdd (hsq : ω * ω = 1) :
    halfOneAdd R (-ω) * halfOneAdd R ω = 0 := by
  rw [halfOneAdd_neg_eq_one_sub]
  exact (isIdempotentElem_halfOneAdd R hsq).one_sub_mul_self

/-- **The pair inherits commutation from `ω`.** Only commutation with the element at hand is
needed, so a central `ω` gives a central pair. -/
theorem commute_halfOneAdd {x : A} (h : Commute ω x) : Commute (halfOneAdd R ω) x := by
  rw [halfOneAdd_def]
  exact Commute.smul_left ((Commute.one_left x).add_left h) _

/-- **The multiplication rule a splitting rests on**: the pair being orthogonal, idempotent and
commuting with `a` and `b`, elements of the form `e₊ a + e₋ b` multiply componentwise. -/
theorem halfOneAdd_mul_add_mul (hsq : ω * ω = 1) {a b : A} (ha : Commute ω a) (hb : Commute ω b)
    (c d : A) :
    (halfOneAdd R ω * a + halfOneAdd R (-ω) * b) *
        (halfOneAdd R ω * c + halfOneAdd R (-ω) * d)
      = halfOneAdd R ω * (a * c) + halfOneAdd R (-ω) * (b * d) := by
  have hee := (isIdempotentElem_halfOneAdd R hsq).eq
  have hff := (isIdempotentElem_halfOneAdd_neg R hsq).eq
  have hef := halfOneAdd_mul_halfOneAdd_neg R hsq
  have hfe := halfOneAdd_neg_mul_halfOneAdd R hsq
  have hae : Commute a (halfOneAdd R ω) := (commute_halfOneAdd R ha).symm
  have haf : Commute a (halfOneAdd R (-ω)) := (commute_halfOneAdd R ha.neg_left).symm
  have hbe : Commute b (halfOneAdd R ω) := (commute_halfOneAdd R hb).symm
  have hbf : Commute b (halfOneAdd R (-ω)) := (commute_halfOneAdd R hb.neg_left).symm
  calc (halfOneAdd R ω * a + halfOneAdd R (-ω) * b) *
        (halfOneAdd R ω * c + halfOneAdd R (-ω) * d)
      = halfOneAdd R ω * a * (halfOneAdd R ω * c)
          + halfOneAdd R ω * a * (halfOneAdd R (-ω) * d)
          + (halfOneAdd R (-ω) * b * (halfOneAdd R ω * c)
            + halfOneAdd R (-ω) * b * (halfOneAdd R (-ω) * d)) := by
        rw [add_mul, mul_add, mul_add]
    _ = halfOneAdd R ω * halfOneAdd R ω * (a * c)
          + halfOneAdd R ω * halfOneAdd R (-ω) * (a * d)
          + (halfOneAdd R (-ω) * halfOneAdd R ω * (b * c)
            + halfOneAdd R (-ω) * halfOneAdd R (-ω) * (b * d)) := by
        rw [hae.mul_mul_mul_comm _ c, haf.mul_mul_mul_comm _ d, hbe.mul_mul_mul_comm _ c,
          hbf.mul_mul_mul_comm _ d]
    _ = halfOneAdd R ω * (a * c) + halfOneAdd R (-ω) * (b * d) := by
        rw [hee, hff, hef, hfe, zero_mul, zero_mul, add_zero, zero_add]

end TauCeti
