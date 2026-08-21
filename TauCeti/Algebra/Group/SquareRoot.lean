/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Square roots in a group

The **square roots** of an element `x` of a group `G` are the `g` with `g * g = x`. Conjugation
carries them bijectively onto the square roots of a conjugate of `x`
(`TauCeti.squareRootConjEquiv`), so their number depends only on the conjugacy class of `x`
(`TauCeti.card_squareRoot_conj`). That is what makes the square-root count a class function, and
hence expandable in the basis of irreducible characters.

## Main statements

* `TauCeti.squareRootConjEquiv`: conjugation is a bijection between the square roots of `x` and
  those of `h * x * h⁻¹`.
* `TauCeti.card_squareRoot_conj`: conjugate elements have equally many square roots.

## Implementation notes

`Nat.card` is used for the count, so no finiteness or decidability assumption is needed to state
the result.  It follows the usual junk-value convention: on a group in which some element has
infinitely many square roots, `Nat.card` returns `0` at that element rather than a cardinal, so the
count below is a genuine number of square roots only when that subtype is finite — as it is for a
finite group.  The statements are unaffected either way, since conjugation is a bijection whether
or not the two sides are finite.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- **Conjugation permutes square roots**: `g ↦ h * g * h⁻¹` is a bijection from the square roots
of `x` onto the square roots of `h * x * h⁻¹`.  It is the conjugation automorphism
`MulAut.conj h` restricted to the square roots, being multiplicative and injective. -/
def squareRootConjEquiv (x h : G) :
    {g : G // g * g = x} ≃ {g : G // g * g = h * x * h⁻¹} :=
  Equiv.subtypeEquiv (MulAut.conj h) fun g => by
    rw [MulEquiv.coe_toEquiv, ← map_mul, ← MulAut.conj_apply h x, EmbeddingLike.apply_eq_iff_eq]

/-- Conjugation of square roots is conjugation of group elements.

The definition is not `@[expose]`d, so this is how it applies outside this file: the generic
`Equiv.subtypeEquiv_apply` cannot fire on the opaque `TauCeti.squareRootConjEquiv`. -/
@[simp]
theorem squareRootConjEquiv_apply_coe (x h : G) (g : {g : G // g * g = x}) :
    (squareRootConjEquiv x h g : G) = h * (g : G) * h⁻¹ :=
  (rfl)

/-- The inverse of `TauCeti.squareRootConjEquiv` is conjugation by `h⁻¹`; as with
`TauCeti.squareRootConjEquiv_apply_coe`, this is what the opaque definition needs in place of
`Equiv.subtypeEquiv_symm`. -/
@[simp]
theorem squareRootConjEquiv_symm_apply_coe (x h : G) (g : {g : G // g * g = h * x * h⁻¹}) :
    ((squareRootConjEquiv x h).symm g : G) = h⁻¹ * (g : G) * h :=
  (rfl)

/-- **The number of square roots is a class function of the group element**: `x` and its
conjugate `h * x * h⁻¹` have equally many square roots.  The counts are `Nat.card`s, hence both
`0` in the degenerate case of infinitely many square roots. -/
theorem card_squareRoot_conj (x h : G) :
    Nat.card {g : G // g * g = h * x * h⁻¹} = Nat.card {g : G // g * g = x} :=
  Nat.card_congr (squareRootConjEquiv x h).symm

end TauCeti
