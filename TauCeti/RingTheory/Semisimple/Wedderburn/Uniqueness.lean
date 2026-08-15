/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Semisimple.MatrixDivisionRing
import TauCeti.RingTheory.Semisimple.BlockCount

/-!
# Uniqueness of Wedderburn blocks

Artin--Wedderburn presents a semisimple ring as a finite product of matrix rings over division
rings.  `TauCeti.card_blocks_eq` proves that two such presentations have equally many blocks, and
`TauCeti.wedderburn_data_unique` proves that the size and coefficient division ring of a *single*
matrix block are intrinsic.  The generic factor matching in
`TauCeti.exists_equiv_factors_of_ringEquiv_pi` permutes the factors of the two products; this file
applies the single-block result to each matched pair and concludes that two Wedderburn
presentations have the same matrix sizes and division rings after one permutation of the blocks.

## Main results

* `TauCeti.wedderburn_blocks_unique`: two Wedderburn presentations have matching degrees and
  coefficient division rings after a permutation of their blocks.

## References

This proves the two-presentation block-multiset consequence of the Layer 2 uniqueness target in the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See T. Y. Lam, *A First Course in Noncommutative Rings*, GTM 131, section 3, or C. W. Curtis and
I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*, section 26.
-/

public section

namespace TauCeti

universe u v w

/-- **Uniqueness of every block in a Wedderburn presentation.** Two presentations of a ring as a
finite product of positive-size matrix rings over division rings differ only by a permutation of
the blocks: corresponding matrix sizes agree and their coefficient division rings are isomorphic.

The positivity hypotheses are essential.  A zero-size matrix ring is trivial and can be inserted
with arbitrary coefficients without changing the product. -/
theorem wedderburn_blocks_unique {R : Type u} [Ring R]
    {m n : ℕ} {D : Fin m → Type v} {E : Fin n → Type w}
    [∀ i, DivisionRing (D i)] [∀ j, DivisionRing (E j)]
    {d : Fin m → ℕ} {e : Fin n → ℕ} [∀ i, NeZero (d i)] [∀ j, NeZero (e j)]
    (f : R ≃+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i))
    (g : R ≃+* ∀ j, Matrix (Fin (e j)) (Fin (e j)) (E j)) :
    ∃ σ : Fin m ≃ Fin n, ∀ i, d i = e (σ i) ∧ Nonempty (D i ≃+* E (σ i)) := by
  classical
  have hd : ∀ i, Nonempty (Fin (d i)) := fun i ↦
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (d i))⟩⟩
  have he : ∀ j, Nonempty (Fin (e j)) := fun j ↦
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (e j))⟩⟩
  obtain ⟨σ, hσ⟩ := exists_equiv_factors_of_ringEquiv_pi (f.symm.trans g)
  refine ⟨σ, fun i ↦ ?_⟩
  obtain ⟨hblock, -⟩ := hσ i
  exact wedderburn_data_unique (.refl _) hblock

end TauCeti
