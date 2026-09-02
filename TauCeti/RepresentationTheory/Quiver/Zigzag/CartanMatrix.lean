/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Grading
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective
public import TauCeti.RingTheory.Idempotents.Corner

/-!
# The graded Cartan matrix of a zigzag algebra

For a finite simple graph without isolated vertices, the vertex idempotents `e_i` of the zigzag
relation quotient `Z` are primitive, so `Z e_i` is the indecomposable projective at `i` and the
corner `e_i Z e_j` records the homomorphisms from `Z e_i` to `Z e_j`.  This file computes those
corners degree by degree for the path-length grading and assembles the resulting graded Cartan
matrix.

The three nonzero graded corners are read off the vertex-arrow-volume basis: the vertex
idempotent `e_i` spans the degree-zero corner at `(i, i)`, the arrow of the dart from `j` to `i`
spans the degree-one corner at `(i, j)`, and the volume class `x_i` spans the degree-two corner
at `(i, i)`.  Everything else vanishes, so

```text
C_G(q) = (1 + q²) I + q A_G,
```

with `A_G` the adjacency matrix of the graph.  At `q = 1` this is the ungraded Cartan matrix
`2I + A_G`, whose column sums are the dimensions of the vertex projectives; at `q = -1` it is the
generalized Cartan matrix `2I - A_G` of the graph.

## Main definitions

* `TauCeti.zigzagCorner`: the corner `e_i Z e_j`, as a `k`-submodule of the relation quotient.
* `TauCeti.zigzagGradedCorner`: its degree-`n` piece for the path-length grading.
* `TauCeti.zigzagGradedCartanMatrix`: the matrix of graded dimensions of the corners, a matrix of
  polynomials in `q`.

## Main results

* `TauCeti.restrictScalars_zigzagProjective_eq_iSup_zigzagCorner`: the vertex projective `Z e_j`
  is the sum of the corners `e_i Z e_j`.
* `TauCeti.zigzagGradedCorner_zero_self_eq_span`,
  `TauCeti.zigzagGradedCorner_one_eq_span_of_adj` and
  `TauCeti.zigzagGradedCorner_two_self_eq_span`: the three nonvanishing graded corners, each
  spanned by a single basis vector, together with the vanishing of all the others.
* `TauCeti.zigzagGradedCartanMatrix_apply`: **the entrywise graded Cartan formula.**
* `TauCeti.zigzagGradedCartanMatrix_eq`: the same formula in matrix notation,
  `C_G(q) = (1 + q²) I + q A_G`.
* `TauCeti.zigzagGradedCartanMatrix_map_eval_one` and
  `TauCeti.zigzagGradedCartanMatrix_map_eval_neg_one`: the two specializations `2I + A_G` and
  `2I - A_G`.
* `TauCeti.sum_eval_one_zigzagGradedCartanMatrix_eq_finrank_zigzagProjective`: the column sums at
  `q = 1` are the dimensions of the vertex projectives.

## Implementation notes

The graded Cartan entry is defined as the truncated sum `∑_{n < 3} dim (e_i Z e_j)_n q^n` rather
than as a sum over all degrees.  The truncation loses nothing:
`TauCeti.finrank_zigzagGradedCorner_of_three_le` proves that every corner of degree at least three
vanishes, because the whole degree-`n` piece of the zigzag quotient does.

The corners here are the graded homomorphism spaces of the vertex projectives only through the
standard dictionary `Hom_Z(Z e_i, Z e_j) ≅ e_i Z e_j`, which this file does not construct; what it
does prove about the projectives themselves is
`TauCeti.restrictScalars_zigzagProjective_eq_iSup_zigzagCorner`, that `Z e_j` is the sum of the
corners `e_i Z e_j` over `i`, together with the resulting numerical comparison
`TauCeti.sum_eval_one_zigzagGradedCartanMatrix_eq_finrank_zigzagProjective`.

## References

This is the graded Cartan matrix of Layer 3 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`.  See Huerfano--Khovanov, *A category for the
adjoint representation*, Section 3, and Ehrig--Tubbenhauer, *Algebraic properties of zigzag
algebras*, Section 2.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver Polynomial

universe u w

variable (k : Type w) [Field k] {V : Type u} (G : SimpleGraph V) [Finite V]

/-! ### The corners of a zigzag algebra -/

/-- Cutting an element of the zigzag relation quotient down to the corner at `(i, j)`, that is,
multiplying it by `e_i` on the left and by `e_j` on the right. -/
noncomputable def zigzagCornerMap (i j : V) :
    nonisolatedZigzagQuotient k G →ₗ[k] nonisolatedZigzagQuotient k G :=
  cornerMap k (zigzagVertexIdempotent k G i) (zigzagVertexIdempotent k G j)

@[simp]
theorem zigzagCornerMap_apply (i j : V) (x : nonisolatedZigzagQuotient k G) :
    zigzagCornerMap k G i j x =
      zigzagVertexIdempotent k G i * x * zigzagVertexIdempotent k G j :=
  cornerMap_apply k _ _ x

/-- **The corner `e_i Z e_j` of a zigzag algebra**, as a `k`-submodule of the relation quotient:
the elements which `e_i` fixes on the left and `e_j` fixes on the right. -/
noncomputable def zigzagCorner (i j : V) :
    Submodule k (nonisolatedZigzagQuotient k G) :=
  cornerSubmodule k (zigzagVertexIdempotent k G i) (zigzagVertexIdempotent k G j)

/-- Membership in the corner `e_i Z e_j`: an element belongs to it exactly when multiplying it by
`e_i` on the left and by `e_j` on the right fixes it. -/
@[simp]
theorem mem_zigzagCorner_iff {i j : V} {x : nonisolatedZigzagQuotient k G} :
    x ∈ zigzagCorner k G i j ↔
      zigzagVertexIdempotent k G i * x * zigzagVertexIdempotent k G j = x :=
  mem_cornerSubmodule_iff k (zigzagMk_vertexIdempotent_mul_self k G i)
    (zigzagMk_vertexIdempotent_mul_self k G j)

/-- The corner `e_i Z e_j` sits inside the vertex projective `Z e_j`. -/
theorem mem_zigzagProjective_of_mem_zigzagCorner {i j : V}
    {x : nonisolatedZigzagQuotient k G} (hx : x ∈ zigzagCorner k G i j) :
    x ∈ zigzagProjective k G j := by
  rw [mem_zigzagProjective_iff]
  conv_lhs => rw [← (mem_zigzagCorner_iff k G).1 hx]
  rw [mul_assoc, zigzagMk_vertexIdempotent_mul_self]
  exact (mem_zigzagCorner_iff k G).1 hx

/-- The vertex idempotent at `i` lies in the corner at `(i, i)`. -/
theorem zigzagVertexIdempotent_mem_zigzagCorner (i : V) :
    zigzagVertexIdempotent k G i ∈ zigzagCorner k G i i := by
  rw [mem_zigzagCorner_iff]
  simp only [zigzagVertexIdempotent, zigzagMk_vertexIdempotent_mul_self]

/-- The arrow of a dart lies in the corner at `(head, tail)`: in the later-factor-first convention
the arrow of `d` is fixed on the left by the idempotent at the head of `d` and on the right by the
idempotent at its tail. -/
theorem zigzagMk_ofArrow_mem_zigzagCorner (d : G.Dart) :
    zigzagMk k G (ofArrow (arrow G d.adj)) ∈ zigzagCorner k G d.snd d.fst := by
  rw [mem_zigzagCorner_iff]
  simp only [zigzagVertexIdempotent, zigzagMk_vertexIdempotent_mul_ofArrow,
    zigzagMk_ofArrow_mul_vertexIdempotent]

/-- The volume class at `i` lies in the corner at `(i, i)`. -/
theorem zigzagVolume_mem_zigzagCorner (i : V) :
    zigzagVolume k G i ∈ zigzagCorner k G i i := by
  rw [mem_zigzagCorner_iff]
  simp only [zigzagVertexIdempotent, zigzagMk_vertexIdempotent_mul_zigzagVolume,
    zigzagVolume_mul_zigzagMk_vertexIdempotent]

/-- **The vertex projective `Z e_j` is the sum of the corners `e_i Z e_j`.** Cutting the
vertex-arrow-volume basis down by `e_j` leaves the idempotent `e_j`, the arrows leaving `j`, and
the volume class `x_j`, and each of them lies in one corner. -/
theorem restrictScalars_zigzagProjective_eq_iSup_zigzagCorner (j : V) :
    Submodule.restrictScalars k (zigzagProjective k G j) = ⨆ i, zigzagCorner k G i j := by
  refine le_antisymm (fun x hx => ?_) (iSup_le fun i _ hy =>
    mem_zigzagProjective_of_mem_zigzagCorner k G hy)
  have himage : Submodule.map (LinearMap.mulRight k (zigzagVertexIdempotent k G j))
      (Submodule.span k (Set.range (zigzagBasisFun k G))) ≤ ⨆ i, zigzagCorner k G i j := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mulRight_apply]
    rcases b with v | d | v
    · rcases eq_or_ne v j with rfl | hv
      · rw [zigzagBasisFun_inl]
        simp only [zigzagVertexIdempotent, zigzagMk_vertexIdempotent_mul_self]
        exact le_iSup (fun i => zigzagCorner k G i v) v
            (zigzagVertexIdempotent_mem_zigzagCorner k G v)
      · rw [zigzagBasisFun_inl]
        simp only [zigzagVertexIdempotent,
          zigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne k G hv]
        exact Submodule.zero_mem _
    · rcases eq_or_ne j d.fst with rfl | hd
      · rw [zigzagBasisFun_inr_inl]
        simp only [zigzagVertexIdempotent, zigzagMk_ofArrow_mul_vertexIdempotent]
        exact le_iSup (fun i => zigzagCorner k G i d.fst) d.snd
            (zigzagMk_ofArrow_mem_zigzagCorner k G d)
      · rw [zigzagBasisFun_inr_inl]
        simp only [zigzagVertexIdempotent, zigzagMk_ofArrow_mul_vertexIdempotent_of_ne k G d hd]
        exact Submodule.zero_mem _
    · rcases eq_or_ne v j with rfl | hv
      · rw [zigzagBasisFun_inr_inr]
        simp only [zigzagVertexIdempotent, zigzagVolume_mul_zigzagMk_vertexIdempotent]
        exact le_iSup (fun i => zigzagCorner k G i v) v (zigzagVolume_mem_zigzagCorner k G v)
      · rw [zigzagBasisFun_inr_inr]
        simp only [zigzagVertexIdempotent,
          zigzagVolume_mul_zigzagMk_vertexIdempotent_of_ne k G (Ne.symm hv)]
        exact Submodule.zero_mem _
  have hx' : x * zigzagVertexIdempotent k G j = x := (mem_zigzagProjective_iff k G).1 hx
  have hspan : x ∈ Submodule.span k (Set.range (zigzagBasisFun k G)) := by
    rw [span_range_zigzagBasisFun_eq_top]
    exact Submodule.mem_top
  have hmem := himage (Submodule.mem_map_of_mem
    (f := LinearMap.mulRight k (zigzagVertexIdempotent k G j)) hspan)
  rwa [LinearMap.mulRight_apply, hx'] at hmem

/-! ### The graded corners -/

/-- **The degree-`n` part of the corner `e_i Z e_j`** for the path-length grading of the zigzag
relation quotient. -/
noncomputable def zigzagGradedCorner (i j : V) (n : ℕ) :
    Submodule k (nonisolatedZigzagQuotient k G) :=
  zigzagCorner k G i j ⊓ zigzagGrade k G n

/-- Membership in a graded corner: an element belongs to it exactly when it lies in the corner and
is homogeneous of that degree. -/
@[simp]
theorem mem_zigzagGradedCorner_iff {i j : V} {n : ℕ} {x : nonisolatedZigzagQuotient k G} :
    x ∈ zigzagGradedCorner k G i j n ↔ x ∈ zigzagCorner k G i j ∧ x ∈ zigzagGrade k G n :=
  Iff.rfl

/-- A graded corner sits inside the corner it grades. -/
theorem zigzagGradedCorner_le_zigzagCorner (i j : V) (n : ℕ) :
    zigzagGradedCorner k G i j n ≤ zigzagCorner k G i j :=
  fun _ hx => ((mem_zigzagGradedCorner_iff k G).1 hx).1

/-- An element of a graded corner is cut out by the corner map from a spanning family of its
degree.  This is the shape in which each of the three degrees below is computed: it reduces the
graded corner to the span of the corner map applied to the vertex idempotents, the arrows, or the
volume classes. -/
private theorem zigzagGradedCorner_le_span_image {i j : V} {n : ℕ}
    {s : Set (nonisolatedZigzagQuotient k G)} (hs : zigzagGrade k G n = Submodule.span k s) :
    zigzagGradedCorner k G i j n ≤ Submodule.span k (⇑(zigzagCornerMap k G i j) '' s) := by
  rintro x ⟨hcorner, hgrade⟩
  have hx : zigzagCornerMap k G i j x = x := by
    rw [zigzagCornerMap_apply]
    exact (mem_zigzagCorner_iff k G).1 hcorner
  rw [hs] at hgrade
  rw [← hx, ← Submodule.map_span]
  exact Submodule.mem_map_of_mem hgrade

/-- **The degree-zero corner at a vertex is spanned by its idempotent.** -/
theorem zigzagGradedCorner_zero_self_eq_span (i : V) :
    zigzagGradedCorner k G i i 0 = Submodule.span k {zigzagVertexIdempotent k G i} := by
  refine le_antisymm ?_ ?_
  · refine le_trans (zigzagGradedCorner_le_span_image k G
      (zigzagGrade_zero_eq_span_range_vertexIdempotent k G)) (Submodule.span_le.2 ?_)
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    rcases eq_or_ne v i with rfl | hv
    · rw [zigzagCornerMap_apply]
      simp only [zigzagVertexIdempotent, zigzagMk_vertexIdempotent_mul_self]
      exact Submodule.subset_span rfl
    · rw [zigzagCornerMap_apply]
      simp only [zigzagVertexIdempotent,
        zigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne k G (Ne.symm hv), zero_mul]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨zigzagVertexIdempotent_mem_zigzagCorner k G i,
      zigzagMk_mem_zigzagGrade k G (PathAlgebra.vertexIdempotent_mem_grade_zero _)⟩

/-- **The degree-zero corner between distinct vertices vanishes.** -/
theorem zigzagGradedCorner_zero_eq_bot_of_ne {i j : V} (h : i ≠ j) :
    zigzagGradedCorner k G i j 0 = ⊥ := by
  refine le_antisymm ?_ bot_le
  refine le_trans (zigzagGradedCorner_le_span_image k G
    (zigzagGrade_zero_eq_span_range_vertexIdempotent k G)) (Submodule.span_le.2 ?_)
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  rw [zigzagCornerMap_apply]
  rcases eq_or_ne v i with rfl | hv
  · simp only [zigzagVertexIdempotent, zigzagMk_vertexIdempotent_mul_self,
      zigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne k G h]
    exact Submodule.zero_mem _
  · simp only [zigzagVertexIdempotent,
      zigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne k G (Ne.symm hv), zero_mul]
    exact Submodule.zero_mem _

/-- **The degree-one corner over an edge is spanned by the arrow crossing it.** The corner at
`(i, j)` sees the arrow which starts at `j` and ends at `i`. -/
theorem zigzagGradedCorner_one_eq_span_of_adj {i j : V} (h : G.Adj j i) :
    zigzagGradedCorner k G i j 1 = Submodule.span k {zigzagMk k G (ofArrow (arrow G h))} := by
  refine le_antisymm ?_ ?_
  · refine le_trans (zigzagGradedCorner_le_span_image k G
      (zigzagGrade_one_eq_span_range_ofArrow k G)) (Submodule.span_le.2 ?_)
    rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩
    rw [zigzagCornerMap_apply]
    rcases eq_or_ne i e.snd with rfl | hi
    · rcases eq_or_ne j e.fst with rfl | hj
      · simp only [zigzagVertexIdempotent, zigzagMk_vertexIdempotent_mul_ofArrow,
          zigzagMk_ofArrow_mul_vertexIdempotent]
        exact Submodule.subset_span rfl
      · simp only [zigzagVertexIdempotent, zigzagMk_vertexIdempotent_mul_ofArrow,
          zigzagMk_ofArrow_mul_vertexIdempotent_of_ne k G e hj]
        exact Submodule.zero_mem _
    · simp only [zigzagVertexIdempotent,
        zigzagMk_vertexIdempotent_mul_ofArrow_of_ne k G e hi, zero_mul]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨zigzagMk_ofArrow_mem_zigzagCorner k G ⟨(j, i), h⟩,
      zigzagMk_mem_zigzagGrade k G (PathAlgebra.ofArrow_mem_grade_one _)⟩

/-- **The degree-one corner over a nonedge vanishes.** -/
theorem zigzagGradedCorner_one_eq_bot_of_not_adj {i j : V} (h : ¬G.Adj j i) :
    zigzagGradedCorner k G i j 1 = ⊥ := by
  refine le_antisymm ?_ bot_le
  refine le_trans (zigzagGradedCorner_le_span_image k G
    (zigzagGrade_one_eq_span_range_ofArrow k G)) (Submodule.span_le.2 ?_)
  rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩
  rw [zigzagCornerMap_apply]
  rcases eq_or_ne i e.snd with rfl | hi
  · have hj : j ≠ e.fst := fun hje => h (hje ▸ e.adj)
    simp only [zigzagVertexIdempotent, zigzagMk_vertexIdempotent_mul_ofArrow,
      zigzagMk_ofArrow_mul_vertexIdempotent_of_ne k G e hj]
    exact Submodule.zero_mem _
  · simp only [zigzagVertexIdempotent,
      zigzagMk_vertexIdempotent_mul_ofArrow_of_ne k G e hi, zero_mul]
    exact Submodule.zero_mem _

/-- **The degree-two corner at a vertex is spanned by its volume class.** -/
theorem zigzagGradedCorner_two_self_eq_span (i : V) :
    zigzagGradedCorner k G i i 2 = Submodule.span k {zigzagVolume k G i} := by
  refine le_antisymm ?_ ?_
  · refine le_trans (zigzagGradedCorner_le_span_image k G
      (zigzagGrade_two_eq_span_range_zigzagVolume k G)) (Submodule.span_le.2 ?_)
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    rw [zigzagCornerMap_apply]
    rcases eq_or_ne v i with rfl | hv
    · simp only [zigzagVertexIdempotent, zigzagMk_vertexIdempotent_mul_zigzagVolume,
        zigzagVolume_mul_zigzagMk_vertexIdempotent]
      exact Submodule.subset_span rfl
    · simp only [zigzagVertexIdempotent,
        zigzagMk_vertexIdempotent_mul_zigzagVolume_of_ne k G (Ne.symm hv), zero_mul]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    refine ⟨zigzagVolume_mem_zigzagCorner k G i, ?_⟩
    rw [zigzagGrade_two_eq_span_range_zigzagVolume]
    exact Submodule.subset_span ⟨i, rfl⟩

/-- **The degree-two corner between distinct vertices vanishes.** -/
theorem zigzagGradedCorner_two_eq_bot_of_ne {i j : V} (h : i ≠ j) :
    zigzagGradedCorner k G i j 2 = ⊥ := by
  refine le_antisymm ?_ bot_le
  refine le_trans (zigzagGradedCorner_le_span_image k G
    (zigzagGrade_two_eq_span_range_zigzagVolume k G)) (Submodule.span_le.2 ?_)
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  rw [zigzagCornerMap_apply]
  rcases eq_or_ne v i with rfl | hv
  · simp only [zigzagVertexIdempotent, zigzagMk_vertexIdempotent_mul_zigzagVolume,
      zigzagVolume_mul_zigzagMk_vertexIdempotent_of_ne k G (Ne.symm h)]
    exact Submodule.zero_mem _
  · simp only [zigzagVertexIdempotent,
      zigzagMk_vertexIdempotent_mul_zigzagVolume_of_ne k G (Ne.symm hv), zero_mul]
    exact Submodule.zero_mem _

/-- **Every corner of degree at least three vanishes**, because the whole degree-`n` piece does. -/
theorem zigzagGradedCorner_eq_bot_of_three_le (i j : V) {n : ℕ} (hn : 3 ≤ n) :
    zigzagGradedCorner k G i j n = ⊥ := by
  rw [zigzagGradedCorner, zigzagGrade_eq_bot_of_three_le k G hn, inf_bot_eq]

/-! ### The dimensions of the graded corners -/


/-- The degree-zero corner at a vertex is one-dimensional. -/
theorem finrank_zigzagGradedCorner_zero_self (i : V) :
    Module.finrank k (zigzagGradedCorner k G i i 0) = 1 := by
  rw [zigzagGradedCorner_zero_self_eq_span]
  exact finrank_span_singleton (zigzagVertexIdempotent_ne_zero k G i)

/-- The degree-zero corner between distinct vertices has dimension zero. -/
theorem finrank_zigzagGradedCorner_zero_of_ne {i j : V} (h : i ≠ j) :
    Module.finrank k (zigzagGradedCorner k G i j 0) = 0 := by
  rw [zigzagGradedCorner_zero_eq_bot_of_ne k G h, finrank_bot]

/-- The degree-one corner over a nonedge has dimension zero. -/
theorem finrank_zigzagGradedCorner_one_of_not_adj {i j : V} (h : ¬G.Adj j i) :
    Module.finrank k (zigzagGradedCorner k G i j 1) = 0 := by
  rw [zigzagGradedCorner_one_eq_bot_of_not_adj k G h, finrank_bot]

/-- The degree-two corner between distinct vertices has dimension zero. -/
theorem finrank_zigzagGradedCorner_two_of_ne {i j : V} (h : i ≠ j) :
    Module.finrank k (zigzagGradedCorner k G i j 2) = 0 := by
  rw [zigzagGradedCorner_two_eq_bot_of_ne k G h, finrank_bot]

/-- **The graded Cartan entries vanish in every degree at least three**: this is what makes the
truncated sum defining `TauCeti.zigzagGradedCartanMatrix` lose nothing. -/
theorem finrank_zigzagGradedCorner_of_three_le (i j : V) {n : ℕ} (hn : 3 ≤ n) :
    Module.finrank k (zigzagGradedCorner k G i j n) = 0 := by
  rw [zigzagGradedCorner_eq_bot_of_three_le k G i j hn, finrank_bot]

/-- The degree-one corner over an edge is one-dimensional: the arrow crossing the edge is nonzero
because traversing it and returning is the nonzero volume class at its head. -/
theorem finrank_zigzagGradedCorner_one_of_adj {i j : V} (h : G.Adj j i) :
    Module.finrank k (zigzagGradedCorner k G i j 1) = 1 := by
  rw [zigzagGradedCorner_one_eq_span_of_adj k G h]
  refine finrank_span_singleton fun harrow => ?_
  have hvol := zigzagMk_ofArrow_mul_ofArrow_symm k G (⟨(j, i), h⟩ : G.Dart)
  rw [harrow, zero_mul] at hvol
  exact zigzagVolume_ne_zero k G h.symm hvol.symm

/-- The degree-two corner at a vertex with a neighbour is one-dimensional. -/
theorem finrank_zigzagGradedCorner_two_self_of_adj {i j : V} (h : G.Adj i j) :
    Module.finrank k (zigzagGradedCorner k G i i 2) = 1 := by
  rw [zigzagGradedCorner_two_self_eq_span]
  exact finrank_span_singleton (zigzagVolume_ne_zero k G h)

/-! ### The graded Cartan matrix -/

/-- **The graded Cartan matrix of a zigzag algebra**: the entry at `(i, j)` is the graded dimension
`∑_n dim_k (e_i Z e_j)_n q^n` of the corner at `(i, j)`, a polynomial in the internal degree `q`.
The sum is truncated below degree three, which by
`TauCeti.finrank_zigzagGradedCorner_of_three_le` discards only zeros. -/
noncomputable def zigzagGradedCartanMatrix : Matrix V V ℤ[X] :=
  Matrix.of fun i j =>
    ∑ n ∈ Finset.range 3, (Module.finrank k (zigzagGradedCorner k G i j n) : ℤ[X]) * X ^ n

theorem zigzagGradedCartanMatrix_apply_eq_sum (i j : V) :
    zigzagGradedCartanMatrix k G i j =
      (Module.finrank k (zigzagGradedCorner k G i j 0) : ℤ[X]) +
        (Module.finrank k (zigzagGradedCorner k G i j 1) : ℤ[X]) * X +
        (Module.finrank k (zigzagGradedCorner k G i j 2) : ℤ[X]) * X ^ 2 := by
  rw [zigzagGradedCartanMatrix, Matrix.of_apply, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, pow_zero, mul_one, pow_one]

/-- **The graded Cartan entry away from the diagonal and from the edges vanishes.** -/
theorem zigzagGradedCartanMatrix_apply_of_ne_of_not_adj {i j : V} (hne : i ≠ j)
    (h : ¬G.Adj i j) : zigzagGradedCartanMatrix k G i j = 0 := by
  rw [zigzagGradedCartanMatrix_apply_eq_sum, finrank_zigzagGradedCorner_zero_of_ne k G hne,
    finrank_zigzagGradedCorner_one_of_not_adj k G fun hji => h hji.symm,
    finrank_zigzagGradedCorner_two_of_ne k G hne]
  push_cast
  ring

/-- **The diagonal graded Cartan entry at a vertex with a neighbour is `1 + q²`**: the vertex
idempotent in degree zero and the volume class in degree two. -/
theorem zigzagGradedCartanMatrix_apply_self_of_adj {i j : V} (h : G.Adj i j) :
    zigzagGradedCartanMatrix k G i i = 1 + X ^ 2 := by
  rw [zigzagGradedCartanMatrix_apply_eq_sum, finrank_zigzagGradedCorner_zero_self,
    finrank_zigzagGradedCorner_one_of_not_adj k G (G.irrefl (v := i)),
    finrank_zigzagGradedCorner_two_self_of_adj k G h]
  push_cast
  ring

/-- **The graded Cartan entry over an edge is `q`**: the single arrow crossing it. -/
theorem zigzagGradedCartanMatrix_apply_of_adj {i j : V} (h : G.Adj i j) :
    zigzagGradedCartanMatrix k G i j = X := by
  have hne : i ≠ j := G.ne_of_adj h
  rw [zigzagGradedCartanMatrix_apply_eq_sum, finrank_zigzagGradedCorner_zero_of_ne k G hne,
    finrank_zigzagGradedCorner_one_of_adj k G h.symm,
    finrank_zigzagGradedCorner_two_of_ne k G hne]
  push_cast
  ring

/-- The graded Cartan matrix is symmetric: the graph is undirected. -/
theorem isSymm_zigzagGradedCartanMatrix : (zigzagGradedCartanMatrix k G).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rcases eq_or_ne i j with rfl | hne
  · rfl
  · by_cases h : G.Adj i j
    · rw [zigzagGradedCartanMatrix_apply_of_adj k G h.symm,
        zigzagGradedCartanMatrix_apply_of_adj k G h]
    · rw [zigzagGradedCartanMatrix_apply_of_ne_of_not_adj k G (Ne.symm hne)
        fun hji => h hji.symm,
        zigzagGradedCartanMatrix_apply_of_ne_of_not_adj k G hne h]

section Nonisolated

variable (hns : ∀ i : V, ∃ j, G.Adj i j)
include hns

section Decidable

variable [DecidableEq V] [DecidableRel G.Adj]

/-- **The entrywise graded Cartan formula.** The diagonal entries are `1 + q²`, the entries over an
edge are `q`, and all the others vanish. -/
theorem zigzagGradedCartanMatrix_apply (i j : V) :
    zigzagGradedCartanMatrix k G i j =
      (if i = j then 1 + X ^ 2 else 0) + if G.Adj i j then X else 0 := by
  rcases eq_or_ne i j with rfl | hne
  · obtain ⟨j, hj⟩ := hns i
    rw [zigzagGradedCartanMatrix_apply_self_of_adj k G hj, ite_eq_left rfl,
      ite_eq_right (G.irrefl (v := i)), add_zero]
  · rw [ite_eq_right hne, zero_add]
    by_cases h : G.Adj i j
    · rw [zigzagGradedCartanMatrix_apply_of_adj k G h, ite_eq_left h]
    · rw [zigzagGradedCartanMatrix_apply_of_ne_of_not_adj k G hne h, ite_eq_right h]

/-- **The graded Cartan matrix of a zigzag algebra is `(1 + q²) I + q A_G`.** -/
theorem zigzagGradedCartanMatrix_eq :
    zigzagGradedCartanMatrix k G =
      (1 + X ^ 2 : ℤ[X]) • (1 : Matrix V V ℤ[X]) + (X : ℤ[X]) • G.adjMatrix ℤ[X] := by
  ext i j
  rw [zigzagGradedCartanMatrix_apply k G hns, Matrix.add_apply, Matrix.smul_apply,
    Matrix.smul_apply, Matrix.one_apply, SimpleGraph.adjMatrix_apply]
  split_ifs <;> simp

/-- **At `q = 1` the graded Cartan matrix is the ungraded one**, `2I + A_G`. -/
theorem zigzagGradedCartanMatrix_map_eval_one :
    (zigzagGradedCartanMatrix k G).map (eval 1) =
      (2 : ℤ) • (1 : Matrix V V ℤ) + G.adjMatrix ℤ := by
  ext i j
  rw [Matrix.map_apply, zigzagGradedCartanMatrix_apply k G hns, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, SimpleGraph.adjMatrix_apply]
  split_ifs <;> simp

/-- **At `q = -1` the graded Cartan matrix is the generalized Cartan matrix `2I - A_G`** of the
graph. -/
theorem zigzagGradedCartanMatrix_map_eval_neg_one :
    (zigzagGradedCartanMatrix k G).map (eval (-1)) =
      (2 : ℤ) • (1 : Matrix V V ℤ) - G.adjMatrix ℤ := by
  ext i j
  rw [Matrix.map_apply, zigzagGradedCartanMatrix_apply k G hns, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, SimpleGraph.adjMatrix_apply]
  split_ifs <;> simp

end Decidable

section Sum

variable [Fintype V]

/-- **The column sums of the ungraded Cartan matrix are `2 + deg(j)`.** -/
theorem sum_eval_one_zigzagGradedCartanMatrix [DecidableRel G.Adj] (j : V) :
    ∑ i, eval 1 (zigzagGradedCartanMatrix k G i j) = 2 + (G.degree j : ℤ) := by
  classical
  have hentry : ∀ i, eval 1 (zigzagGradedCartanMatrix k G i j) =
      (if i = j then (2 : ℤ) else 0) + if G.Adj i j then 1 else 0 := by
    intro i
    rw [zigzagGradedCartanMatrix_apply k G hns]
    split_ifs <;> simp
  have hdeg : ∑ i, (if G.Adj i j then (1 : ℤ) else 0) = (G.degree j : ℤ) := by
    rw [← Finset.sum_filter]
    have hfilter : {i ∈ (Finset.univ : Finset V) | G.Adj i j} = G.neighborFinset j := by
      ext i
      simp [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm]
    rw [hfilter, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul,
      mul_one]
  rw [Finset.sum_congr rfl fun i _ => hentry i, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.univ : Finset V) j fun _ => (2 : ℤ), hdeg,
    ite_eq_left (Finset.mem_univ j)]

/-- **The column sums of the ungraded Cartan matrix are the dimensions of the vertex
projectives.** The vertex projective `Z e_j` is the sum of the corners `e_i Z e_j` over the
vertices `i`, and this is that decomposition read in dimensions. -/
theorem sum_eval_one_zigzagGradedCartanMatrix_eq_finrank_zigzagProjective (j : V) :
    ∑ i, eval 1 (zigzagGradedCartanMatrix k G i j) =
      (Module.finrank k (zigzagProjective k G j) : ℤ) := by
  classical
  rw [sum_eval_one_zigzagGradedCartanMatrix k G hns, finrank_zigzagProjective k G hns]
  push_cast
  ring

end Sum

end Nonisolated

end TauCeti
