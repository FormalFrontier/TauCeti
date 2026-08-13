/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.CentralIdempotent
public import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Block counts and factor matching for products of simple rings

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
generality of products of arbitrary simple rings and then for a Wedderburn presentation, whose
matrix blocks are simple rings by `IsSimpleRing.matrix`.  It also strengthens the count for an
isomorphism between two products: the coordinate central idempotents determine a permutation of
the factors, and the original isomorphism restricts to an isomorphism on every matched pair.

Positivity of the block sizes is essential and not decoration: `Matₒ(D)` is the trivial ring, which
is not simple, and a presentation could be padded with any number of such blocks without changing
`R`.  This is the same `NeZero` hypothesis that
`IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing` produces.  Semisimplicity of `R` is *not*
needed anywhere: the count is an invariant of any ring admitting such a presentation, and
semisimplicity is what guarantees a presentation exists in the first place.

The finer uniqueness — that the degrees `nᵢ` and division rings `Dᵢ` match after a permutation — is
`TauCeti.wedderburn_blocks_unique` in
`TauCeti/RingTheory/Semisimple/Wedderburn/Uniqueness.lean`.  It upgrades the counting argument here:
the coordinate central idempotents themselves determine the factor permutation, after which
`TauCeti.wedderburn_data_unique` identifies each corresponding pair of matrix blocks.

## Main results

* `TauCeti.card_eq_of_ringEquiv_pi_of_isSimpleRing`: two presentations of a ring as a finite
  product of simple rings have the same number of factors.
* `TauCeti.exists_equiv_factors_of_ringEquiv_pi`: an isomorphism between finite products of simple
  rings induces a permutation and compatible isomorphisms of the matched factors.
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

universe u v w x

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

section Products

variable {ι : Type u} {κ : Type v} [Finite ι] [Finite κ]
  {A : ι → Type w} {B : κ → Type x}
  [∀ i, Ring (A i)] [∀ i, IsSimpleRing (A i)]
  [∀ j, Ring (B j)] [∀ j, IsSimpleRing (B j)]

attribute [local instance] Fintype.ofFinite Classical.decEq

omit [Finite ι] in
private theorem single_one_ne_zero (i : ι) : Pi.single i (1 : A i) ≠ 0 := by
  classical
  intro h
  have := congrFun h i
  simp at this

omit [Finite ι] [∀ i, IsSimpleRing (A i)] in
private theorem single_one_mem_centralIdempotents (i : ι) :
    Pi.single i (1 : A i) ∈ centralIdempotents (∀ i, A i) := by
  classical
  rw [mem_centralIdempotents_pi]
  intro j
  by_cases h : j = i
  · subst j
    rw [Pi.single_eq_same]
    exact one_mem_centralIdempotents
  · rw [Pi.single_eq_of_ne h]
    exact zero_mem_centralIdempotents

variable (f : (∀ i, A i) ≃+* (∀ j, B j))

omit [Finite ι] [Finite κ] [∀ i, IsSimpleRing (A i)] in
private theorem image_coordinate_eq_zero_or_one (i : ι) (j : κ) :
    f (Pi.single i (1 : A i)) j = 0 ∨ f (Pi.single i (1 : A i)) j = 1 := by
  have hmem : f (Pi.single i (1 : A i)) j ∈ centralIdempotents (B j) :=
    (mem_centralIdempotents_pi B).mp
      (map_mem_centralIdempotents f (single_one_mem_centralIdempotents i)) j
  rw [centralIdempotents_eq_pair (B j)] at hmem
  simpa [eq_comm] using hmem

omit [Finite κ] [∀ i, IsSimpleRing (A i)] in
private theorem existsUnique_image_coordinate_eq_one (j : κ) :
    ∃! i : ι, f (Pi.single i (1 : A i)) j = 1 := by
  classical
  have hsum : ∑ i : ι, f (Pi.single i (1 : A i)) j = 1 := by
    rw [← Finset.sum_apply, ← map_sum, (CompleteOrthogonalIdempotents.single A).complete, map_one]
    rfl
  have hex : ∃ i : ι, f (Pi.single i (1 : A i)) j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    simp [h] at hsum
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, (image_coordinate_eq_zero_or_one f i j).resolve_left hi, ?_⟩
  intro i' hi'
  by_contra hne
  have hmul : Pi.single i (1 : A i) * Pi.single i' (1 : A i') = 0 :=
    (CompleteOrthogonalIdempotents.single A).ortho (Ne.symm hne)
  have := congrFun (congrArg f hmul) j
  simp [map_mul, hi', (image_coordinate_eq_zero_or_one f i j).resolve_left hi] at this

private noncomputable def sourceIndex (j : κ) : ι :=
  (existsUnique_image_coordinate_eq_one f j).choose

omit [Finite κ] [∀ i, IsSimpleRing (A i)] in
private theorem image_coordinate_sourceIndex (j : κ) :
    f (Pi.single (sourceIndex f j) (1 : A (sourceIndex f j))) j = 1 :=
  (existsUnique_image_coordinate_eq_one f j).choose_spec.1

omit [Finite κ] [∀ i, IsSimpleRing (A i)] in
private theorem sourceIndex_eq_of_image_coordinate_eq_one {i : ι} {j : κ}
    (h : f (Pi.single i (1 : A i)) j = 1) : sourceIndex f j = i :=
  ((existsUnique_image_coordinate_eq_one f j).choose_spec.2 i h).symm

omit [Finite κ] in
private theorem sourceIndex_surjective : Function.Surjective (sourceIndex f) := by
  intro i
  have himage : f (Pi.single i (1 : A i)) ≠ 0 := by
    rw [← map_zero f]
    exact f.injective.ne (single_one_ne_zero i)
  obtain ⟨j, hj⟩ : ∃ j, f (Pi.single i (1 : A i)) j ≠ 0 := by
    exact Function.ne_iff.mp himage
  exact ⟨j, sourceIndex_eq_of_image_coordinate_eq_one f
    ((image_coordinate_eq_zero_or_one f i j).resolve_left hj)⟩

private theorem sourceIndex_bijective : Function.Bijective (sourceIndex f) := by
  apply (Nat.bijective_iff_surjective_and_card (sourceIndex f)).mpr
  exact ⟨sourceIndex_surjective f, card_eq_of_ringEquiv_pi_of_isSimpleRing f (.refl _)⟩

private noncomputable def blockEquiv : ι ≃ κ :=
  (Equiv.ofBijective (sourceIndex f) (sourceIndex_bijective f)).symm

private theorem sourceIndex_blockEquiv (i : ι) : sourceIndex f (blockEquiv f i) = i :=
  (Equiv.ofBijective (sourceIndex f) (sourceIndex_bijective f)).apply_symm_apply i

private theorem image_coordinate_blockEquiv (i : ι) :
    f (Pi.single i (1 : A i)) (blockEquiv f i) = 1 := by
  have h := image_coordinate_sourceIndex f (blockEquiv f i)
  rwa [sourceIndex_blockEquiv f i] at h

private theorem image_coordinate_eq_zero_of_ne (i : ι) {j : κ} (h : j ≠ blockEquiv f i) :
    f (Pi.single i (1 : A i)) j = 0 := by
  rcases image_coordinate_eq_zero_or_one f i j with hz | ho
  · exact hz
  · have hs : sourceIndex f j = i := sourceIndex_eq_of_image_coordinate_eq_one f ho
    have hb : blockEquiv f (sourceIndex f j) = j :=
      (Equiv.ofBijective (sourceIndex f) (sourceIndex_bijective f)).symm_apply_apply j
    exact absurd (hb ▸ congrArg (blockEquiv f) hs) h

private theorem map_single_eq_single (i : ι) (x : A i) :
    f (Pi.single i x) =
      Pi.single (blockEquiv f i) (f (Pi.single i x) (blockEquiv f i)) := by
  classical
  ext j
  by_cases h : j = blockEquiv f i
  · subst j
    rw [Pi.single_eq_same]
  · have hzero := image_coordinate_eq_zero_of_ne f i h
    have hsingle : Pi.single i (1 : A i) * Pi.single i x = Pi.single i x := by
      rw [← Pi.single_mul, one_mul]
    have hmul := congrFun (congrArg f hsingle) j
    rw [map_mul, Pi.mul_apply, hzero, zero_mul] at hmul
    rw [Pi.single_eq_of_ne h]
    exact hmul.symm

private theorem symm_map_single_eq_single (i : ι) (y : B (blockEquiv f i)) :
    f.symm (Pi.single (blockEquiv f i) y) =
      Pi.single i (f.symm (Pi.single (blockEquiv f i) y) i) := by
  classical
  have hcoord : f (Pi.single i (1 : A i)) =
      Pi.single (blockEquiv f i) (1 : B (blockEquiv f i)) := by
    rw [map_single_eq_single, image_coordinate_blockEquiv]
  ext k
  by_cases h : k = i
  · subst k
    rw [Pi.single_eq_same]
  · have hzero : Pi.single i (1 : A i) k = 0 := Pi.single_eq_of_ne h 1
    have hmul : Pi.single (blockEquiv f i) (1 : B (blockEquiv f i)) *
        Pi.single (blockEquiv f i) y = Pi.single (blockEquiv f i) y := by
      rw [← Pi.single_mul, one_mul]
    have := congrFun (congrArg f.symm hmul) k
    rw [map_mul, ← hcoord, f.symm_apply_apply] at this
    rw [Pi.mul_apply, hzero, zero_mul] at this
    rw [Pi.single_eq_of_ne h]
    exact this.symm

private noncomputable def factorRingEquiv (i : ι) : A i ≃+* B (blockEquiv f i) where
  toFun x := f (Pi.single i x) (blockEquiv f i)
  invFun y := f.symm (Pi.single (blockEquiv f i) y) i
  map_add' x y := by rw [Pi.single_add, map_add]; rfl
  map_mul' x y := by rw [Pi.single_mul, map_mul]; rfl
  left_inv x := by
    have h := congrFun (congrArg f.symm (map_single_eq_single f i x)) i
    rw [f.symm_apply_apply, Pi.single_eq_same] at h
    exact h.symm
  right_inv y := by
    have h := congrFun (congrArg f (symm_map_single_eq_single f i y)) (blockEquiv f i)
    rw [f.apply_symm_apply, Pi.single_eq_same] at h
    exact h.symm

/-- **A ring isomorphism between finite products of simple rings permutes their factors.**

The returned factor isomorphisms are restrictions of the original isomorphism: mapping an element
supported at `i` gives the corresponding element supported at `σ i`.  The permutation need not be
canonical when some factors are isomorphic. -/
theorem exists_equiv_factors_of_ringEquiv_pi
    (f : (∀ i, A i) ≃+* (∀ j, B j)) :
    ∃ σ : ι ≃ κ, ∀ i, ∃ e : A i ≃+* B (σ i),
      ∀ x, f (Pi.single i x) = Pi.single (σ i) (e x) :=
  ⟨blockEquiv f, fun i ↦ ⟨factorRingEquiv f i, map_single_eq_single f i⟩⟩

end Products

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
