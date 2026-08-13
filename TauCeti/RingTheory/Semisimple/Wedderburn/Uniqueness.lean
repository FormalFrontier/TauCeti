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
matrix block are intrinsic.  This file joins those results: a ring isomorphism between two finite
products of simple rings permutes their factors, and hence two Wedderburn presentations have the
same matrix sizes and division rings after one permutation of the blocks.

The factor permutation is recovered from the coordinate central idempotents.  If
`e_i = Pi.single i 1`, the images of the `e_i` are nonzero orthogonal central idempotents summing
to `1`.  In a simple target factor every central idempotent is `0` or `1`, so each target coordinate
belongs to exactly one image.  This gives a surjection from target factors to source factors;
`TauCeti.card_eq_of_ringEquiv_pi_of_isSimpleRing` makes it bijective.  Restricting the original
isomorphism to the corresponding coordinates then gives an isomorphism of each pair of factors.

## Main results

* `TauCeti.exists_equiv_factors_of_ringEquiv_pi`: an isomorphism between finite products of
  simple rings induces a permutation matching isomorphic factors.
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

universe u v w x

section Products

variable {ι : Type u} {κ : Type v} [Finite ι] [Finite κ]
  {A : ι → Type w} {B : κ → Type x}
  [∀ i, Ring (A i)] [∀ i, IsSimpleRing (A i)]
  [∀ j, Ring (B j)] [∀ j, IsSimpleRing (B j)]

attribute [local instance] Fintype.ofFinite
noncomputable local instance : DecidableEq ι := Classical.decEq ι
noncomputable local instance : DecidableEq κ := Classical.decEq κ

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
    have hmul := congrFun (congrArg f (show Pi.single i (1 : A i) * Pi.single i x =
        Pi.single i x by rw [← Pi.single_mul, one_mul])) j
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

The returned equivalence matches every source factor with an isomorphic target factor.  It is not
claimed to be canonical: repeated isomorphic factors can be permuted in more than one way. -/
theorem exists_equiv_factors_of_ringEquiv_pi
    (f : (∀ i, A i) ≃+* (∀ j, B j)) :
    ∃ σ : ι ≃ κ, ∀ i, Nonempty (A i ≃+* B (σ i)) :=
  ⟨blockEquiv f, fun i ↦ ⟨factorRingEquiv f i⟩⟩

end Products

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
  obtain ⟨hblock⟩ := hσ i
  exact wedderburn_data_unique (.refl _) hblock

end TauCeti
