/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.CentralIdempotent
public import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# The number of blocks of a Wedderburn presentation is an invariant

Artin--Wedderburn presents a semisimple ring `R` as a finite product of matrix algebras over
division rings,

`R ≃+* ∏ᵢ Matₙᵢ(Dᵢ)`,

and Mathlib supplies such a presentation but says nothing about how much of it is determined by
`R`.  This file proves the first uniqueness statement: **the number of blocks is the same for any
two presentations** (`TauCeti.card_blocks_eq`).

The invariant that sees the block count is the set of central idempotents.  A ring isomorphism
carries central idempotents to central idempotents, they are computed coordinatewise on a product,
and a simple ring has exactly two of them; so a product of `m` simple rings has exactly `2 ^ m`
central idempotents, and `m` is recovered from `R`.  Those three ingredients are supplied by
`TauCeti/RingTheory/CentralIdempotent.lean`; this file combines them, first in the natural
generality of a product of arbitrary simple rings
(`TauCeti.card_eq_of_ringEquiv_pi_of_isSimpleRing`) and then for a Wedderburn presentation, whose
matrix blocks are simple rings by `IsSimpleRing.matrix`.

Positivity of the block sizes is essential and not decoration: `Matₒ(D)` is the trivial ring, which
is not simple, and a presentation could be padded with any number of such blocks without changing
`R`.  This is the same `NeZero` hypothesis that
`IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing` produces.  Semisimplicity of `R` is *not*
needed anywhere: the count is an invariant of any ring admitting such a presentation, and
semisimplicity is what guarantees a presentation exists in the first place.

What is *not* proved here is the finer uniqueness — that the multiset of degrees `nᵢ` and the
division rings `Dᵢ` are determined too — which needs the identification of the blocks with the
isomorphism classes of simple `R`-modules rather than a mere count.  That identification is
`TauCeti.blocks_equiv_simpleModules` in
`TauCeti/RingTheory/Semisimple/Wedderburn/Blocks.lean`, which recovers the count below as a count of
simple modules but still says nothing about the degrees or the division rings.  For a *single*
block those two are settled by `TauCeti.wedderburn_data_unique` in
`TauCeti/RingTheory/Semisimple/MatrixDivisionRing.lean`; what remains open is the matching of the
blocks of two presentations of a product.

## Main results

* `TauCeti.card_eq_of_ringEquiv_pi_of_isSimpleRing`: two presentations of a ring as a finite
  product of simple rings have the same number of factors.
* `TauCeti.card_blocks_eq`: **the number of blocks of a Wedderburn presentation is an invariant of
  the ring.**

## References

This implements the Layer 2 target `card_blocks_eq` ("invariance of the block count") of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See T. Y. Lam, *A First Course in Noncommutative Rings*, §3, or C. W. Curtis and I. Reiner,
*Representation Theory of Finite Groups and Associative Algebras*, §25.
-/

public section

namespace TauCeti

section Simple

variable {R : Type*} [Ring R] {ι : Type*} {A : ι → Type*} [∀ i, Ring (A i)]
  [∀ i, IsSimpleRing (A i)]

/-- **Two presentations of a ring as a finite product of simple rings have the same number of
factors.**  Both counts are read off the number of central idempotents of `R`, which is
`2 ^ (number of factors)`. -/
theorem card_eq_of_ringEquiv_pi_of_isSimpleRing [Finite ι] {κ : Type*} [Finite κ]
    {B : κ → Type*} [∀ j, Ring (B j)] [∀ j, IsSimpleRing (B j)]
    (f : R ≃+* ∀ i, A i) (g : R ≃+* ∀ j, B j) : Nat.card ι = Nat.card κ := by
  have h : (2 : ℕ) ^ Nat.card ι = 2 ^ Nat.card κ := by
    rw [← card_centralIdempotents_pi_of_isSimpleRing A,
      ← card_centralIdempotents_pi_of_isSimpleRing B,
      ← card_centralIdempotents_congr f, ← card_centralIdempotents_congr g]
  exact Nat.pow_right_injective le_rfl h

end Simple

/-- **Invariance of the block count.** Two Wedderburn presentations of the same ring have the same
number of blocks.

The `NeZero` hypotheses on the block sizes are essential, exactly as in Mathlib's
`IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing`: a block of size `0` is the trivial
ring, so without them any presentation could be padded with empty blocks and the count would not be
an invariant.  Semisimplicity of `R` is not needed — it is what makes a presentation exist, not
what makes the count well defined. -/
theorem card_blocks_eq {R : Type*} [Ring R] {m n : ℕ} {D : Fin m → Type*} {D' : Fin n → Type*}
    [∀ i, DivisionRing (D i)] [∀ i, DivisionRing (D' i)] {d : Fin m → ℕ} {d' : Fin n → ℕ}
    [∀ i, NeZero (d i)] [∀ i, NeZero (d' i)]
    (f : R ≃+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i))
    (g : R ≃+* ∀ i, Matrix (Fin (d' i)) (Fin (d' i)) (D' i)) : m = n := by
  have hd : ∀ i, Nonempty (Fin (d i)) := fun i => ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (d i))⟩⟩
  have hd' : ∀ i, Nonempty (Fin (d' i)) := fun i => ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (d' i))⟩⟩
  simpa using card_eq_of_ringEquiv_pi_of_isSimpleRing f g

end TauCeti
