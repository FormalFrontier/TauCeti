/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.PosDef
public import TauCeti.LinearAlgebra.RootSystem.DynkinType

public section

/-!
# Cartan matrices of finite type

The Cartan-Killing classification is, at bottom, a statement about integer matrices: the Cartan
matrix of a finite crystallographic root system is a generalized Cartan matrix that is
*symmetrizable with positive definite symmetrization*, and only finitely many combinatorial shapes
of such a matrix exist. This file introduces the matrix-level condition, `TauCeti.IsFiniteType`,
develops the tools that eliminate diagrams from the list, and proves that the Cartan matrix of a
base of a finite crystallographic root system satisfies it.

Positive definiteness is asked for over `ℚ`, not over `ℤ`.
`TauCeti.Matrix.posDef_map_intCast` shows that positive definiteness over `ℤ` implies positive
definiteness over `ℚ`, and the rational form is the one downstream arguments use, since a test
vector produced by a diagram computation need not have integer entries. The symmetrizer `d` is
likewise rational: it is the vector of inverse root lengths, which is integral only after clearing
denominators. The symmetrization itself is not redone here: Mathlib packages it over `ℤ` as
`RootPairing.Base.exists_cartanMatrix_diagaonal_mul_posDef`, resting on
`RootPairing.posRootForm_rootFormIn_posDef`.

## Main definitions

* `TauCeti.IsFiniteType`: an integer matrix is a generalized Cartan matrix admitting a positive
  rational symmetrizer whose symmetrization is positive definite.

## Main results

* `TauCeti.isFiniteType_of`: a constructor that does not ask for the symmetric vanishing pattern,
  which the symmetrizer already forces.
* `TauCeti.isFiniteType_of_conjTranspose_mul_self_of_det_ne_zero`: the constructor used for a
  matrix presented by its entries. Positive definiteness of the symmetrization is certified by an
  explicit Gram model `Cᴴ * C` together with nonsingularity, both of which are finite
  computations. `TauCeti.Matrix.det_mul_intCast` is the determinant of the symmetrization that
  such a computation meets.
* `TauCeti.IsFiniteType.submatrix`: principal submatrices of a finite-type matrix are of finite
  type. This is what lets a forbidden subdiagram rule out a diagram containing it.
* `TauCeti.IsFiniteType.transpose`: finite type is invariant under matrix transposition.
* `TauCeti.IsFiniteType.sum_apply_mul_apply_lt_four`: the star bound. The Cartan products joining
  an index to pairwise non-adjacent neighbours sum to less than `4`. This is the first of the two
  positive-definiteness estimates behind the local shape of a finite-type diagram.
* `TauCeti.IsFiniteType.apply_mul_apply_mem_of_ne`: the rank-two bound. For `i ≠ j` the Cartan
  product `A i j * A j i` lies in `{0, 1, 2, 3}`, so every edge of the diagram is single, double or
  triple.
* `TauCeti.IsFiniteType.isSimplyLaced_iff`: **a finite-type matrix is simply laced exactly when
  none of its edges is multiple**, that is, when no Cartan product of two distinct indices exceeds
  `1`. Together with the rank-two bound this is how the classification enters its simply-laced
  branch, having excluded the Cartan products `2` and `3`.
* `TauCeti.IsFiniteType.exists_apply_succ_eq_zero`: **a finite-type diagram carries no cycle**. A
  cyclic list of at least three distinct indices has a missing edge. This is the second estimate:
  the test vector is supported on the indices of the putative cycle, its coordinate at each of them
  being the reciprocal of the symmetrizer, and each edge of the cycle then cancels the diagonal
  contribution of one of its ends.
* `TauCeti.IsFiniteType.apply_eq_zero_of_apply_ne_zero`: **a finite-type diagram carries no
  triangle**, the three-index case of the previous item: two distinct neighbours of an index are
  never adjacent to one another. `TauCeti.IsFiniteType.pairwise_apply_eq_zero` is the same statement
  for a whole neighbourhood, in the shape the star bound consumes.

The star bound selects its neighbours through a pairwise non-adjacency hypothesis; with the triangle
excluded that hypothesis comes for free, and the consequences below are the unconditional graph
statements the classification runs on.

* `TauCeti.IsFiniteType.card_le_three_of_forall_apply_ne_zero`: **the degree bound**. No index has
  four neighbours; the affine type `D̃₄` is ruled out in `TauCeti.not_isFiniteType_affineD₄`.
* `TauCeti.IsFiniteType.apply_mul_apply_le_one_of_two_le`: **at most one edge at an index is
  multiple**.
* `TauCeti.IsFiniteType.apply_eq_zero_of_apply_mul_apply_eq_three`: **a triple edge is isolated**,
  so it is a connected component of the diagram; this is why `G₂` has rank `2`.
* `TauCeti.IsFiniteType.apply_mul_apply_eq_one_of_three_le_card`: **a branch vertex is simply
  laced**. Three neighbours of an index are each joined to it by a single edge.
* `TauCeti.IsFiniteType.det_ne_zero`: a finite-type matrix is nonsingular. Since the extended
  Dynkin diagrams have singular Cartan matrices, this is the third elimination tool; the affine
  type `Ã₂` is ruled out in `TauCeti.not_isFiniteType_affineA₂`. It does not subsume the
  no-triangle theorem: `TauCeti.not_isFiniteType_doubleEdgeTriangle` exhibits a nonsingular
  triangle.
* `TauCeti.IsFiniteType.eq_zero_of_forall_mul_sum_apply_mul_nonpos`: **a finite-type matrix has no
  nonzero subdominant vector**, one with `xᵢ · (A x)ᵢ ≤ 0` at every index. This is the fourth
  elimination tool, and unlike `TauCeti.IsFiniteType.det_ne_zero` it does not ask the certificate to
  be a null vector, only to point away from the positive cone coordinatewise, so a single vector can
  rule out a whole family of diagrams.
* `TauCeti.isFiniteType_cartanMatrix`: **the Cartan matrix of a base of a finite crystallographic
  root system is of finite type**, and `TauCeti.HasCartanType.isFiniteType`: so is the standard
  Cartan matrix of any Dynkin type realized by such a base.

## References

This file implements the "finite-type condition" item of Layer 5 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, following the target signature
`isFiniteType_cartanMatrix` in that roadmap's `Suggested.lean`. See V. G. Kac, *Infinite
Dimensional Lie Algebras*, 3rd ed., Chapter 4, for the finite/affine/indefinite trichotomy of
generalized Cartan matrices, and Humphreys, *Introduction to Lie Algebras and Representation
Theory*, Chapter 11, for the classification of the finite-type case.
-/

open scoped Matrix

namespace TauCeti

namespace Matrix

/-- **The determinant of a symmetrization.** Scaling the rows of an integer matrix `M` by a
rational vector `d` multiplies the determinant by `∏ i, d i`. This is `Matrix.det_mul_column`, which
does the row scaling, composed with `Int.cast_det`, which turns the determinant of the cast matrix
into the cast of the integral determinant; the composite is the shape in which the symmetrization
of `TauCeti.IsFiniteType` is met. -/
theorem det_mul_intCast {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℚ) (M : _root_.Matrix n n ℤ) :
    (_root_.Matrix.of fun i j ↦ d i * (M i j : ℚ)).det = (∏ i, d i) * (M.det : ℚ) := by
  have hmap : (_root_.Matrix.of fun i j ↦ d i * (M i j : ℚ))
      = _root_.Matrix.of fun i j ↦ d i * M.map (fun x : ℤ ↦ (x : ℚ)) i j := by
    ext i j
    simp
  rw [hmap, _root_.Matrix.det_mul_column, ← Int.cast_det]

end Matrix

variable {B : Type*} {A : Matrix B B ℤ}

/-- A finite square integer matrix is **of finite type** when it is a generalized Cartan matrix -
diagonal entries `2`, nonpositive off-diagonal entries, and a symmetric vanishing pattern - which
is symmetrizable with positive definite symmetrization: there is a positive rational vector `d`
making `fun i j ↦ d i * A i j` positive definite (in particular symmetric).

The Cartan matrices of finite root systems are exactly the matrices of this kind, up to
irreducibility; `TauCeti.isFiniteType_cartanMatrix` proves one direction. -/
def IsFiniteType [Fintype B] (A : Matrix B B ℤ) : Prop :=
  (∀ i, A i i = 2) ∧ (∀ i j, i ≠ j → A i j ≤ 0) ∧ (∀ i j, A i j = 0 → A j i = 0) ∧
    ∃ d : B → ℚ, (∀ i, 0 < d i) ∧ (Matrix.of fun i j ↦ d i * (A i j : ℚ)).PosDef

variable [Fintype B]

/-- **Building a finite-type matrix.** The symmetric vanishing pattern demanded by
`TauCeti.IsFiniteType` need not be checked: a positive symmetrizer already forces
`d j * A j i = d i * A i j`, so one entry of a transposed pair vanishes exactly when the other
does. The clause is kept in the definition because it is one of the defining axioms of a
generalized Cartan matrix. -/
theorem isFiniteType_of (h2 : ∀ i, A i i = 2) (hle : ∀ i j, i ≠ j → A i j ≤ 0) {d : B → ℚ}
    (hd : ∀ i, 0 < d i) (hpd : (Matrix.of fun i j ↦ d i * (A i j : ℚ)).PosDef) :
    IsFiniteType A := by
  refine ⟨h2, hle, fun i j hij ↦ ?_, d, hd, hpd⟩
  have hsymm := hpd.isHermitian.apply i j
  simp only [Matrix.of_apply, star_trivial] at hsymm
  rw [hij] at hsymm
  have : ((A j i : ℤ) : ℚ) = 0 := by simpa [(hd j).ne'] using hsymm
  exact_mod_cast this

/-- **A nonsingular generalized Cartan matrix with a rational Gram model is of finite type.** This
is the working form of `TauCeti.isFiniteType_of` for a matrix given by an explicit list of entries:
positive definiteness of the symmetrization is certified by exhibiting it as `Cᴴ * C` for a matrix
`C` of coordinates - the columns of `C` being simple coroots, in the intended application - which
makes it positive *semi*definite, with nonsingularity of `A` upgrading that to positive
definiteness. -/
theorem isFiniteType_of_conjTranspose_mul_self_of_det_ne_zero [DecidableEq B] {m : Type*}
    [Fintype m] (h2 : ∀ i, A i i = 2) (hle : ∀ i j, i ≠ j → A i j ≤ 0) {d : B → ℚ}
    (hd : ∀ i, 0 < d i) {C : Matrix m B ℚ}
    (hgram : Matrix.of (fun i j ↦ d i * (A i j : ℚ)) = Cᴴ * C) (hdet : A.det ≠ 0) :
    IsFiniteType A := by
  refine isFiniteType_of h2 hle hd ?_
  have hunit : IsUnit (Matrix.of fun i j ↦ d i * (A i j : ℚ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_mul_intCast]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ ↦ (hd i).ne')
      (Int.cast_ne_zero.mpr hdet)
  rw [hgram] at hunit ⊢
  exact Matrix.posDef_conjTranspose_mul_self_of_isUnit C hunit

namespace IsFiniteType

/-- The diagonal entries of a finite-type matrix are `2`. -/
lemma apply_self (h : IsFiniteType A) (i : B) : A i i = 2 := h.1 i

/-- The off-diagonal entries of a finite-type matrix are nonpositive. -/
lemma apply_le_zero_of_ne (h : IsFiniteType A) {i j : B} (hij : i ≠ j) : A i j ≤ 0 := h.2.1 i j hij

/-- The vanishing pattern of a finite-type matrix is symmetric. -/
lemma apply_eq_zero_symm (h : IsFiniteType A) {i j : B} (hij : A i j = 0) : A j i = 0 :=
  h.2.2.1 i j hij

/-- An entry of a finite-type matrix vanishes exactly when its transpose does. -/
lemma apply_eq_zero_iff (h : IsFiniteType A) {i j : B} : A i j = 0 ↔ A j i = 0 :=
  ⟨h.apply_eq_zero_symm, h.apply_eq_zero_symm⟩

/-- The symmetrizer of a finite-type matrix, together with its defining properties. -/
lemma exists_symmetrizer (h : IsFiniteType A) :
    ∃ d : B → ℚ, (∀ i, 0 < d i) ∧ (Matrix.of fun i j ↦ d i * (A i j : ℚ)).PosDef := h.2.2.2

omit [Fintype B] in
/-- **The symmetrizer intertwines the two entries of a transposed pair.** The symmetrization is
symmetric, being positive definite, and this is what that says entrywise. -/
private theorem symmetrization_apply_comm {d : B → ℚ}
    (hpd : (Matrix.of fun i j ↦ d i * (A i j : ℚ)).PosDef) (p q : B) :
    d q * (A q p : ℚ) = d p * (A p q : ℚ) := by
  simpa using hpd.isHermitian.apply p q

/-- **A principal submatrix of a finite-type matrix is of finite type.** This is the form in which
a forbidden subdiagram excludes every diagram containing it. -/
theorem submatrix {C : Type*} [Fintype C] (h : IsFiniteType A) {e : C → B}
    (he : Function.Injective e) :
    IsFiniteType (A.submatrix e e) := by
  -- Restricting the symmetrizer along the same injection restricts the symmetrization, and
  -- positive definiteness passes to principal submatrices.
  obtain ⟨d, hd, hpd⟩ := h.exists_symmetrizer
  refine ⟨fun i ↦ h.apply_self _, fun i j hij ↦ h.apply_le_zero_of_ne fun hc ↦ hij (he hc),
    fun i j hij ↦ h.apply_eq_zero_symm hij, d ∘ e, fun i ↦ hd _, ?_⟩
  exact hpd.submatrix he

/-- **Finite type is invariant under transposition.** The reciprocal vector is a symmetrizer for
the transpose. Its symmetrization is obtained from the original one by conjugating with the
invertible diagonal matrix whose entries are those reciprocals. -/
theorem transpose (h : IsFiniteType A) : IsFiniteType A.transpose := by
  classical
  obtain ⟨d, hd, hpd⟩ := h.exists_symmetrizer
  refine isFiniteType_of (fun i ↦ h.apply_self i)
    (fun i j hij ↦ h.apply_le_zero_of_ne hij.symm) (d := fun i ↦ (d i)⁻¹)
    (fun i ↦ inv_pos.mpr (hd i)) ?_
  have hdiag : Function.Injective (Matrix.diagonal fun i ↦ (d i)⁻¹).mulVec := by
    intro x y hxy
    funext i
    apply mul_left_cancel₀ (inv_ne_zero (hd i).ne')
    simpa only [Matrix.mulVec_diagonal] using congrFun hxy i
  have hconj := hpd.conjTranspose_mul_mul_same hdiag
  convert hconj using 1
  ext i j
  have hsymm := hpd.isHermitian.apply i j
  simp only [Matrix.of_apply, Matrix.transpose_apply, Matrix.diagonal_conjTranspose, star_trivial,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Matrix.of_apply, star_trivial] at hsymm
  field_simp [(hd i).ne', (hd j).ne']
  linarith

/-- **A nonzero entry has Cartan product at least `1`.** Off the diagonal both entries of such a
transposed pair are at most `-1`: they are nonpositive, and neither vanishes, because the vanishing
pattern is symmetric. On the diagonal the product is `2 * 2`. -/
theorem one_le_apply_mul_apply (h : IsFiniteType A) {i j : B} (hne : A i j ≠ 0) :
    1 ≤ A i j * A j i := by
  rcases eq_or_ne i j with rfl | hij
  · rw [h.apply_self]; norm_num
  have hi : A i j ≤ -1 := by have := h.apply_le_zero_of_ne hij; omega
  have hj : A j i ≤ -1 := by
    have hle := h.apply_le_zero_of_ne hij.symm
    have hne' : A j i ≠ 0 := fun hc ↦ hne (h.apply_eq_zero_symm hc)
    omega
  nlinarith

omit [Fintype B] in
/-- **A pairwise non-adjacent block of the symmetrization is diagonal.** Along a set of indices
that are pairwise non-adjacent, the `l`-th column of the symmetrization `fun p q ↦ d p * A p q`
meets only the index `l` itself, so the sum collapses to that one term. This is what makes the
coordinates of a pairwise non-adjacent star independent of one another, so that each can be chosen
to minimize the quadratic form separately. -/
private theorem sum_mul_symmetrization_mul_eq_of_pairwise_apply_eq_zero {d x : B → ℚ}
    {s : Finset B} (hs : (s : Set B).Pairwise fun j k ↦ A j k = 0) {l : B} (hl : l ∈ s) :
    ∑ k ∈ s, x k * (d k * (A k l : ℚ)) * x l = x l * (d l * (A l l : ℚ)) * x l :=
  Finset.sum_eq_single_of_mem l hl fun k hk hkl ↦ by
    simp [hs (by exact_mod_cast hk) (by exact_mod_cast hl) hkl]

/-- **The value of the symmetrized quadratic form at the test vector of a non-adjacent star.** For
`i` outside a pairwise non-adjacent `s`, any vector taking the value `1` at `i`, the value
`-dᵢAᵢₖ / 2dₖ` at each `k ∈ s` and `0` at every other index evaluates the form at
`2dᵢ - (dᵢ/2) ∑ⱼ AᵢⱼAⱼᵢ`. When the symmetrizer is positive, as it is at the one call site below,
that value at `k ∈ s` is the one minimizing the `k`-th coordinate of the form — a legitimate choice
one coordinate at a time because `s` is pairwise non-adjacent. The evaluation itself needs no sign
condition, only `dₖ ≠ 0`.

Of the matrix data only the nonvanishing of the symmetrizer on `s`, the diagonal entries at `i` and
on `s`, and the symmetrization identity `dⱼAⱼᵢ = dᵢAᵢⱼ` for `j ∈ s` are used; positive definiteness
enters in `TauCeti.IsFiniteType.sum_apply_mul_apply_lt_four`, which is what turns this value into a
bound. -/
private theorem dotProduct_mulVec_symmetrization_eq_of_pairwise_apply_eq_zero
    {d : B → ℚ} {i : B} {s : Finset B} (hd : ∀ p ∈ s, d p ≠ 0) (h2i : A i i = 2)
    (h2s : ∀ p ∈ s, A p p = 2)
    (hsymm : ∀ p ∈ s, d p * (A p i : ℚ) = d i * (A i p : ℚ)) (his : i ∉ s)
    (hs : (s : Set B).Pairwise fun j k ↦ A j k = 0) {x : B → ℚ} (hxi : x i = 1)
    (hxs : ∀ k ∈ s, x k = -(d i * (A i k : ℚ)) / (2 * d k))
    (hxz : ∀ k, k ≠ i → k ∉ s → x k = 0) :
    x ⬝ᵥ ((Matrix.of fun p q ↦ d p * (A p q : ℚ)) *ᵥ x)
      = 2 * d i - d i / 2 * ∑ j ∈ s, (A i j : ℚ) * (A j i : ℚ) := by
  classical
  -- Only the indices of `insert i s` contribute to the quadratic form.
  have hxz' : ∀ k ∉ insert i s, x k = 0 := fun k hk ↦
    hxz k (fun hc ↦ hk (hc ▸ Finset.mem_insert_self i s)) fun hc ↦ hk (Finset.mem_insert_of_mem hc)
  have hrow : ∀ l : B, ∑ k, x k * (d k * (A k l : ℚ)) * x l
      = ∑ k ∈ insert i s, x k * (d k * (A k l : ℚ)) * x l := fun l ↦
    (Finset.sum_subset (Finset.subset_univ _) fun k _ hk ↦ by simp [hxz' k hk]).symm
  have hsum : x ⬝ᵥ ((Matrix.of fun p q ↦ d p * (A p q : ℚ)) *ᵥ x)
      = ∑ l ∈ insert i s, ∑ k ∈ insert i s, x k * (d k * (A k l : ℚ)) * x l := by
    rw [Matrix.dot_mulVec_eq_sum_sum]
    simp only [Matrix.of_apply, hrow]
    exact (Finset.sum_subset (Finset.subset_univ _) fun l _ hl ↦ by simp [hxz' l hl]).symm
  rw [hsum, sub_eq_add_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  simp only [Finset.sum_insert his]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  · rw [hxi, h2i]
    push_cast
    ring
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hji : (A j i : ℚ) = d i * (A i j : ℚ) / d j := by
      field_simp [hd j hj]
      linarith [hsymm j hj]
    rw [sum_mul_symmetrization_mul_eq_of_pairwise_apply_eq_zero hs hj, h2s j hj, hxi, hxs j hj, hji]
    field_simp [hd j hj]
    ring

/-- **The star bound.** If `i` is distinct from every index of `s` and the indices of `s` are
pairwise non-adjacent, then the Cartan products of `i` with the indices of `s` sum to less than
`4`.

This is the first of the two positive-definiteness estimates behind the local shape of a finite-type
diagram: inside a pairwise non-adjacent star at `i` there are at most three neighbours, at most one
of the edges to them is multiple, and a triple edge among them stands alone. The second,
`TauCeti.IsFiniteType.apply_eq_zero_of_apply_ne_zero`, removes the pairwise hypothesis. -/
theorem sum_apply_mul_apply_lt_four (h : IsFiniteType A) {i : B} {s : Finset B} (his : i ∉ s)
    (hs : (s : Set B).Pairwise fun j k ↦ A j k = 0) :
    ∑ j ∈ s, A i j * A j i < 4 := by
  classical
  obtain ⟨d, hd, hpd⟩ := h.exists_symmetrizer
  have hsymm := symmetrization_apply_comm hpd
  -- The test vector: `1` at `i`, the value minimizing the `k`-th coordinate of the form at each
  -- `k ∈ s`, and `0` elsewhere.
  set x : B → ℚ := fun k ↦ if k = i then 1 else
    if k ∈ s then -(d i * (A i k : ℚ)) / (2 * d k) else 0 with hx
  have hxi : x i = 1 := by simp [hx]
  have hxs : ∀ k ∈ s, x k = -(d i * (A i k : ℚ)) / (2 * d k) := fun k hk ↦ by
    have hki : k ≠ i := fun hc ↦ his (hc ▸ hk)
    simp [hx, hki, hk]
  have hq := hpd.dotProduct_mulVec_pos (x := x) fun hc ↦ by simpa [hxi] using congrFun hc i
  rw [star_trivial, dotProduct_mulVec_symmetrization_eq_of_pairwise_apply_eq_zero
    (fun p _ ↦ (hd p).ne') (h.apply_self i) (fun p _ ↦ h.apply_self p) (fun p _ ↦ hsymm i p) his
    hs hxi hxs fun k hki hks ↦ by simp [hx, hki, hks]] at hq
  -- Positive definiteness now reads off the bound, the factor `dᵢ` being positive.
  have hcast : ((∑ j ∈ s, A i j * A j i : ℤ) : ℚ) < 4 := by
    push_cast
    nlinarith [hd i]
  exact_mod_cast hcast

/-- **The Cartan product of two distinct indices of a finite-type matrix is `0`, `1`, `2` or `3`.**
These are exactly the values that name the orders `2, 3, 4, 6` of a product of two simple
reflections. -/
theorem apply_mul_apply_mem_of_ne (h : IsFiniteType A) {i j : B} (hij : i ≠ j) :
    A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ) := by
  -- Nonnegativity is the product of two nonpositive entries; the upper bound is the star bound for
  -- the single-element star `{j}`.
  have hlt := h.sum_apply_mul_apply_lt_four (i := i) (s := {j}) (by simpa using hij)
    (by simp [Set.pairwise_singleton])
  rw [Finset.sum_singleton] at hlt
  have hnonneg : 0 ≤ A i j * A j i :=
    mul_nonneg_of_nonpos_of_nonpos (h.apply_le_zero_of_ne hij) (h.apply_le_zero_of_ne hij.symm)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- **A finite-type matrix is simply laced exactly when none of its edges is multiple.** The Cartan
product `A i j * A j i` is the multiplicity of the edge joining `i` and `j`, so the condition on the
right says that every edge is single: no double edge, and no triple edge.

Only the off-diagonal entries are constrained, one entry of a transposed pair at a time, and that
is enough because the entries of such a pair vanish together and a product of two nonpositive
integers is `1` only when both are `-1`. -/
theorem isSimplyLaced_iff (h : IsFiniteType A) :
    A.IsSimplyLaced ↔ ∀ i j, i ≠ j → A i j * A j i ≤ 1 := by
  constructor
  · intro hsl i j hij
    rcases hsl hij with hij' | hij' <;> rcases hsl hij.symm with hji | hji <;> simp [hij', hji]
  · intro hle i j hij
    have hbound := hle i j hij
    have hnonneg : 0 ≤ A i j * A j i :=
      mul_nonneg_of_nonpos_of_nonpos (h.apply_le_zero_of_ne hij) (h.apply_le_zero_of_ne hij.symm)
    rcases (by omega : A i j * A j i = 0 ∨ A i j * A j i = 1) with hzero | hone
    · rcases mul_eq_zero.mp hzero with hij' | hji
      · exact Or.inl hij'
      · exact Or.inl (h.apply_eq_zero_symm hji)
    · rcases Int.eq_one_or_neg_one_of_mul_eq_one' hone with ⟨hij', -⟩ | ⟨hij', -⟩
      · have := h.apply_le_zero_of_ne hij
        omega
      · exact Or.inr hij'

/-- **On a cycle of length at least three an index and its two cyclic neighbours are pairwise
distinct.** Successor and predecessor are the cyclic ones, taken in the additive group `Fin m`.
Three is the exact threshold: on `Fin 2` an index has a single neighbour, `i + 1 = i - 1`. -/
private theorem cyclic_neighbors_pairwise_ne {m : ℕ} [NeZero m] (hm : 3 ≤ m) (i : Fin m) :
    i + 1 ≠ i ∧ i - 1 ≠ i ∧ i + 1 ≠ i - 1 := by
  have hval1 : ((1 : Fin m) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have hone : (1 : Fin m) ≠ 0 := fun hc ↦ by
    have hval := congrArg Fin.val hc
    rw [hval1, Fin.val_zero] at hval
    omega
  have htwo : (1 : Fin m) + 1 ≠ 0 := fun hc ↦ by
    have hval2 : (((1 : Fin m) + 1 : Fin m) : ℕ) = 2 := by
      rw [Fin.val_add, hval1, Nat.mod_eq_of_lt (by omega)]
    have hval := congrArg Fin.val hc
    rw [hval2, Fin.val_zero] at hval
    omega
  have hsucc : i + 1 ≠ i := fun hc ↦ hone (add_left_cancel (hc.trans (add_zero i).symm))
  refine ⟨hsucc, fun hc ↦ ?_, fun hc ↦ ?_⟩
  · have h1 : i - 1 + 1 = i + 1 := by rw [hc]
    rw [sub_add_cancel] at h1
    exact hsucc h1.symm
  · refine htwo (add_left_cancel (a := i) ?_)
    rw [← add_assoc, hc, sub_add_cancel, add_zero]

/-- **A symmetric cycle form with the given diagonal and edge bounds has rows summing to a
difference of reciprocals.** For `f` symmetric with `f i i = 2 / dᵢ`, nonpositive off the diagonal
and at most `-1/dᵢ` along each cycle edge, the `i`th row sums to at most `1/dᵢ - 1/dᵢ₋₁`. Summing
this over the cycle makes the right-hand side telescope to zero. -/
private theorem sum_le_inv_sub_inv {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    {d : Fin m → ℚ} {f : Fin m → Fin m → ℚ} (hfsymm : ∀ i j, f i j = f j i)
    (hdiag : ∀ i, f i i = 2 / d i) (hnonpos : ∀ i j : Fin m, j ≠ i → f i j ≤ 0)
    (hedge : ∀ i : Fin m, f i (i + 1) ≤ -(d i)⁻¹) (i : Fin m) :
    ∑ j, f i j ≤ (d i)⁻¹ - (d (i - 1))⁻¹ := by
  obtain ⟨hsucc, hpred, hsp⟩ := cyclic_neighbors_pairwise_ne hm i
  rw [← Finset.sum_sdiff (Finset.subset_univ ({i, i + 1, i - 1} : Finset (Fin m)))]
  have hrest : ∑ j ∈ Finset.univ \ ({i, i + 1, i - 1} : Finset (Fin m)), f i j ≤ 0 := by
    refine Finset.sum_nonpos fun j hj ↦ hnonpos i j ?_
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    tauto
  have hthree : ∑ j ∈ ({i, i + 1, i - 1} : Finset (Fin m)), f i j
      = f i i + f i (i + 1) + f i (i - 1) := by
    rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hsucc.symm, hpred.symm⟩),
      Finset.sum_insert (by simpa using hsp), Finset.sum_singleton, add_assoc]
  have hlast : f i (i - 1) ≤ -(d (i - 1))⁻¹ := by
    have hshift := hedge (i - 1)
    rwa [sub_add_cancel, hfsymm] at hshift
  have hhalf : (2 : ℚ) / d i = (d i)⁻¹ + (d i)⁻¹ := by
    rw [div_eq_mul_inv]; ring
  have hii := hdiag i
  have hnext := hedge i
  rw [hthree]
  linarith

/-- **A cyclic diagram is not of finite type.** On an index type of size at least three, no
finite-type matrix joins every index to its cyclic successor: some `Tₖ,ₖ₊₁` vanishes.

This is the positive-definiteness estimate behind the acyclicity of a finite-type diagram, and the
test vector is the reciprocal `xᵢ = 1/dᵢ` of the symmetrizer. At it the symmetrized form
`∑ᵢⱼ xᵢ dᵢTᵢⱼ xⱼ` collects `2/dᵢ` from each diagonal entry and `Tᵢⱼ/dⱼ` from each off-diagonal one,
and the latter is nonpositive throughout. The two entries of the pair `{k, k+1}` contribute equally,
each `Tₖ₊₁,ₖ/dₖ ≤ -1/dₖ`, since the symmetrization identity `dₖTₖ,ₖ₊₁ = dₖ₊₁Tₖ₊₁,ₖ` is exactly what
makes `Tᵢⱼ/dⱼ` symmetric in `i` and `j`. So the value is at most `∑ₖ 2/dₖ - 2∑ₖ 1/dₖ = 0`, which
positive definiteness forbids. Edges off the cycle only lower the value further, so the cycle need
not be chordless, and the scaling by the symmetrizer is what keeps the test vector rational: the
geometric argument takes unit vectors along the coroots and needs their square roots.

The affine diagrams `Ãₙ` for `n ≥ 2`, the ones whose diagrams are cycles, are what this excludes,
and at three indices every triangle: `TauCeti.IsFiniteType.apply_eq_zero_of_apply_ne_zero` is the
case `m = 3`. The remaining affine diagram `Ã₁` is a double edge on two indices rather than a cycle,
and is excluded instead by the rank-two bound `TauCeti.IsFiniteType.apply_mul_apply_mem_of_ne`. -/
private theorem exists_apply_succ_eq_zero_fin {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    {T : Matrix (Fin m) (Fin m) ℤ} (h : IsFiniteType T) :
    ∃ k, T k (k + 1) = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨d, hd, hpd⟩ := h.exists_symmetrizer
  have hsymm := symmetrization_apply_comm hpd
  -- `f i j` is the contribution of the pair `(i, j)` to the form at the test vector; it is
  -- symmetric, and nonpositive off the diagonal.
  obtain ⟨f, hf⟩ : ∃ f : Fin m → Fin m → ℚ, ∀ i j, f i j = (T i j : ℚ) / d j := ⟨_, fun _ _ ↦ rfl⟩
  have hfsymm : ∀ i j, f i j = f j i := by
    intro i j
    rw [hf, hf, div_eq_div_iff (hd j).ne' (hd i).ne']
    linear_combination -hsymm i j
  have hdiag : ∀ i, f i i = 2 / d i := by
    intro i
    rw [hf, h.apply_self]
    norm_num
  have hnonpos : ∀ i j : Fin m, j ≠ i → f i j ≤ 0 := by
    intro i j hji
    have h1 : ((T i j : ℤ) : ℚ) ≤ 0 := by exact_mod_cast h.apply_le_zero_of_ne (Ne.symm hji)
    rw [hf, div_eq_mul_inv]
    simpa using mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr (hd j).le)
  -- Along an edge of the cycle the contribution is at most `-1/dᵢ`, at either of its two entries.
  have hedge : ∀ i : Fin m, f i (i + 1) ≤ -(d i)⁻¹ := by
    intro i
    have h0 : T (i + 1) i ≠ 0 := fun hc ↦ hcon i (h.apply_eq_zero_symm hc)
    have hle : T (i + 1) i ≤ -1 := by
      have := h.apply_le_zero_of_ne (cyclic_neighbors_pairwise_ne hm i).1
      omega
    have hcast : ((T (i + 1) i : ℤ) : ℚ) ≤ -1 := by exact_mod_cast hle
    calc f i (i + 1) = (T (i + 1) i : ℚ) * (d i)⁻¹ := by rw [hfsymm, hf, div_eq_mul_inv]
      _ ≤ (-1 : ℚ) * (d i)⁻¹ := mul_le_mul_of_nonneg_right hcast (inv_nonneg.mpr (hd i).le)
      _ = -(d i)⁻¹ := by ring
  -- Positive definiteness at the test vector.
  have hx : (fun k : Fin m ↦ (d k)⁻¹) ≠ 0 := fun hc ↦ by
    simpa [(hd (0 : Fin m)).ne'] using congrFun hc 0
  have hq := hpd.dotProduct_mulVec_pos hx
  rw [star_trivial, Matrix.dot_mulVec_eq_sum_sum] at hq
  simp only [Matrix.of_apply] at hq
  have hq' : (0 : ℚ) < ∑ i, ∑ j, f i j := by
    rw [Finset.sum_comm]
    refine lt_of_lt_of_le hq (le_of_eq (Finset.sum_congr rfl fun j _ ↦
      Finset.sum_congr rfl fun i _ ↦ ?_))
    rw [hf, inv_mul_cancel_left₀ (hd i).ne', div_eq_mul_inv]
  -- Each index contributes at most `1/dᵢ - 1/dᵢ₋₁`, and those differences telescope around the
  -- cycle to `0`.
  have hbound : ∀ i : Fin m, ∑ j, f i j ≤ (d i)⁻¹ - (d (i - 1))⁻¹ :=
    sum_le_inv_sub_inv hm hfsymm hdiag hnonpos hedge
  have hshift : ∑ i : Fin m, (d (i - 1))⁻¹ = ∑ i : Fin m, (d i)⁻¹ :=
    Fintype.sum_equiv (Equiv.subRight (1 : Fin m)) _ _ fun _ ↦ rfl
  have hle := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) ↦ hbound i
  rw [Finset.sum_sub_distrib, hshift, sub_self] at hle
  linarith

/-- **A finite-type diagram carries no cycle.** A cyclic list of at least three distinct indices
has a missing edge: some index of the cycle is not joined to its successor. The cycle is not
required to be chordless, and no edge of it is required to be simple.

Only the principal submatrix on the indices of the cycle is involved, so this is
`TauCeti.IsFiniteType.exists_apply_succ_eq_zero_fin` transported along the injection.
`TauCeti.IsFiniteType.isAcyclic_diagramGraph` is the same statement in the language of graphs. -/
theorem exists_apply_succ_eq_zero (h : IsFiniteType A) {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    {v : Fin m → B} (hv : Function.Injective v) :
    ∃ k, A (v k) (v (k + 1)) = 0 := by
  obtain ⟨k, hk⟩ := exists_apply_succ_eq_zero_fin hm (h.submatrix hv)
  exact ⟨k, hk⟩

/-- **A finite-type diagram carries no triangle.** Two distinct neighbours of an index are never
adjacent to one another, so the neighbourhood of an index is pairwise non-adjacent and the star
bound applies to it with no side condition.

This is the three-index case of `TauCeti.IsFiniteType.exists_apply_succ_eq_zero`, and it is what
turns the conditional consequences of the star bound into graph statements: the degree bound
`TauCeti.IsFiniteType.card_le_three_of_forall_apply_ne_zero`, the fact that at most one edge at an
index is multiple, and the isolation of a triple edge. -/
theorem apply_eq_zero_of_apply_ne_zero (h : IsFiniteType A) {i j k : B} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hj : A i j ≠ 0) (hk : A i k ≠ 0) :
    A j k = 0 := by
  by_contra hjk0
  -- Were the three indices pairwise joined they would close up into a cycle of length three.
  have hki : A k i ≠ 0 := fun hc ↦ hk (h.apply_eq_zero_symm hc)
  have hv : Function.Injective ![i, j, k] := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all
  obtain ⟨t, ht⟩ := h.exists_apply_succ_eq_zero (m := 3) (by norm_num) hv
  fin_cases t
  · exact hj (by simpa using ht)
  · exact hjk0 (by simpa using ht)
  · exact hki (by simpa using ht)

/-- **The neighbourhood of an index is pairwise non-adjacent.** This is the no-triangle theorem in
the form the star bound consumes: a set of neighbours of `i`, none of them `i` itself, satisfies the
pairwise hypothesis of `TauCeti.IsFiniteType.sum_apply_mul_apply_lt_four` for free. -/
theorem pairwise_apply_eq_zero (h : IsFiniteType A) {i : B} {s : Finset B} (his : i ∉ s)
    (hadj : ∀ j ∈ s, A i j ≠ 0) :
    (s : Set B).Pairwise fun j k ↦ A j k = 0 := by
  intro j hj k hk hjk
  simp only [Finset.mem_coe] at hj hk
  refine h.apply_eq_zero_of_apply_ne_zero ?_ ?_ hjk (hadj j hj) (hadj k hk)
  · rintro rfl; exact his hj
  · rintro rfl; exact his hk

/-- **The two-index case of the star bound.** Three pairwise distinct indices `i`, `j`, `k` are such
that the Cartan products of `i` with `j` and with `k` sum to less than `4`; neither `j` nor `k` is
required to be a neighbour of `i`, an absent edge contributing `0`. No non-adjacency of `j` and `k`
is assumed: if both are neighbours of `i` the no-triangle theorem supplies it, and otherwise the
rank-two bound alone already caps the sum at `3`. -/
theorem apply_mul_apply_add_apply_mul_apply_lt_four (h : IsFiniteType A) {i j k : B} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) :
    A i j * A j i + A i k * A k i < 4 := by
  classical
  -- If either of `j`, `k` misses `i`, the rank-two bound on the other edge is already enough.
  have hmemj := h.apply_mul_apply_mem_of_ne hij
  have hmemk := h.apply_mul_apply_mem_of_ne hik
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmemj hmemk
  rcases eq_or_ne (A i j) 0 with hzj | hnej
  · simp only [hzj, zero_mul, zero_add]
    omega
  rcases eq_or_ne (A i k) 0 with hzk | hnek
  · simp only [hzk, zero_mul, add_zero]
    omega
  -- Otherwise `j` and `k` are both neighbours of `i`, so the no-triangle theorem separates them and
  -- the star bound applies to the star `{j, k}`.
  have h0 : A j k = 0 := h.apply_eq_zero_of_apply_ne_zero hij hik hjk hnej hnek
  have hkj : A k j = 0 := h.apply_eq_zero_symm h0
  have hi : i ∉ ({j, k} : Finset B) := by simp [hij, hik]
  have hp : ((({j, k} : Finset B) : Set B)).Pairwise fun p q ↦ A p q = 0 := by
    intro p hp' q hq' hpq
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hp' hq'
    rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl <;> simp_all
  have hlt := h.sum_apply_mul_apply_lt_four hi hp
  rwa [Finset.sum_insert (by simpa using hjk), Finset.sum_singleton] at hlt

/-- **At most one edge at an index is multiple.** An index carrying a multiple edge to `j` is
joined to every index other than `j` by at most a single edge. No non-adjacency of the far ends is
assumed: the no-triangle theorem supplies it. -/
theorem apply_mul_apply_le_one_of_two_le (h : IsFiniteType A) {i j k : B} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hj : 2 ≤ A i j * A j i) :
    A i k * A k i ≤ 1 := by
  -- The two-index case of the star bound leaves less than `2` for the edge to `k`.
  have := h.apply_mul_apply_add_apply_mul_apply_lt_four hij hik hjk
  omega

/-- **A triple edge is isolated.** An index joined to `j` by a triple edge is joined to no index
other than `j` at all; applied at both ends of the edge this says that a triple edge is a connected
component of the diagram, which is why `G₂` has rank `2`. Here `i ≠ j` need not be assumed: it
follows from the Cartan product being `3` rather than the diagonal value `4`. -/
theorem apply_eq_zero_of_apply_mul_apply_eq_three (h : IsFiniteType A) {i j k : B} (hik : i ≠ k)
    (hjk : j ≠ k) (hj : A i j * A j i = 3) :
    A i k = 0 := by
  have hij : i ≠ j := by
    rintro rfl
    rw [h.apply_self] at hj
    omega
  -- A triple edge already exhausts the two-index case of the star bound, leaving no room for `k`.
  by_contra h0
  have h1 := h.one_le_apply_mul_apply h0
  have := h.apply_mul_apply_add_apply_mul_apply_lt_four hij hik hjk
  omega

/-- **The degree bound: an index of a finite-type matrix has at most three neighbours**, so a
finite-type diagram branches into at most three arms. By the no-triangle theorem the neighbours are
automatically pairwise non-adjacent, so the star bound applies to them directly. -/
theorem card_le_three_of_forall_apply_ne_zero (h : IsFiniteType A) {i : B} {s : Finset B}
    (his : i ∉ s) (hadj : ∀ j ∈ s, A i j ≠ 0) :
    s.card ≤ 3 := by
  have hone : ∀ j ∈ s, (1 : ℤ) ≤ A i j * A j i := fun j hj ↦
    h.one_le_apply_mul_apply (hadj j hj)
  have hcard : (s.card : ℤ) ≤ ∑ j ∈ s, A i j * A j i := by
    calc (s.card : ℤ) = ∑ _j ∈ s, (1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum hone
  have := h.sum_apply_mul_apply_lt_four his (h.pairwise_apply_eq_zero his hadj)
  omega

/-- **A three-armed star of a finite-type matrix is simply laced.** An index with three neighbours
meets each of them along a single edge, since three Cartan products of value at least `1` already
exhaust the star bound. Together with `TauCeti.IsFiniteType.card_le_three_of_forall_apply_ne_zero`
this says that a branch vertex of a finite-type diagram carries exactly three simple edges. -/
theorem apply_mul_apply_eq_one_of_three_le_card (h : IsFiniteType A) {i : B} {s : Finset B}
    (his : i ∉ s) (hadj : ∀ j ∈ s, A i j ≠ 0) (hcard : 3 ≤ s.card) {j : B} (hj : j ∈ s) :
    A i j * A j i = 1 := by
  classical
  have hs : (s : Set B).Pairwise fun j k ↦ A j k = 0 := h.pairwise_apply_eq_zero his hadj
  have hone : ∀ k ∈ s, (1 : ℤ) ≤ A i k * A k i := fun k hk ↦
    h.one_le_apply_mul_apply (hadj k hk)
  have hsplit : ∑ k ∈ s, A i k * A k i
      = A i j * A j i + ∑ k ∈ s.erase j, A i k * A k i := (Finset.add_sum_erase _ _ hj).symm
  have herase : ((s.erase j).card : ℤ) ≤ ∑ k ∈ s.erase j, A i k * A k i := by
    calc ((s.erase j).card : ℤ) = ∑ _k ∈ s.erase j, (1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun k hk ↦ hone k (Finset.mem_of_mem_erase hk)
  have hcard' : (s.erase j).card = s.card - 1 := Finset.card_erase_of_mem hj
  have hlt := h.sum_apply_mul_apply_lt_four his hs
  have hj1 := hone j hj
  omega

/-- **A finite-type matrix is nonsingular.** This is the elimination tool for the extended Dynkin
diagrams, whose Cartan matrices are singular. -/
theorem det_ne_zero [DecidableEq B] (h : IsFiniteType A) : A.det ≠ 0 := by
  -- The symmetrization is a positive definite matrix over a field, hence invertible, and the
  -- symmetrizer contributes only a nonzero diagonal factor.
  obtain ⟨d, -, hpd⟩ := h.exists_symmetrizer
  have hu := hpd.isUnit
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul_intCast] at hu
  intro hdet
  rw [hdet] at hu
  simp at hu

/-- **A finite-type matrix admits no nonzero subdominant vector.** Call a rational vector `x`
*subdominant* for `A` when `xᵢ · (A x)ᵢ ≤ 0` at every index `i`; then `x = 0`.

The symmetrized quadratic form of `A` at `x` is `∑ᵢ dᵢ · xᵢ · (A x)ᵢ`, because scaling the `i`-th
row by `dᵢ` scales the `i`-th summand by `dᵢ`, and the symmetrizer is positive. So a subdominant
vector makes the form nonpositive, which positive definiteness allows only at `0`.

This is the elimination tool for a diagram carrying an explicit certificate. It is weaker than
asking for a null vector, as `TauCeti.IsFiniteType.det_ne_zero` does: the certificate is allowed to
be strictly subdominant at some indices, which is what lets a single vector rule out a whole family
of diagrams rather than only the critical ones. -/
theorem eq_zero_of_forall_mul_sum_apply_mul_nonpos (h : IsFiniteType A) {x : B → ℚ}
    (hx : ∀ i, x i * ∑ j, (A i j : ℚ) * x j ≤ 0) : x = 0 := by
  by_contra hne
  obtain ⟨d, hd, hpd⟩ := h.exists_symmetrizer
  have hpos := hpd.dotProduct_mulVec_pos hne
  rw [star_trivial, Matrix.dot_mulVec_eq_sum_sum] at hpos
  simp only [Matrix.of_apply] at hpos
  rw [Finset.sum_comm] at hpos
  refine absurd hpos (not_lt.2 (Finset.sum_nonpos fun i _ ↦ ?_))
  have hrow : ∑ j, x i * (d i * (A i j : ℚ)) * x j = d i * (x i * ∑ j, (A i j : ℚ) * x j) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hrow]
  simpa using mul_le_mul_of_nonneg_left (hx i) (hd i).le

end IsFiniteType

/-- **The Cartan matrix of the affine diagram `Ã₂` is not of finite type.** The three-cycle is a
genuine generalized Cartan matrix, symmetric with every Cartan product equal to `1`, so neither the
combinatorial axioms nor the rank-two bound exclude it; it is positive *semi*definite. The proof
below rules it out by `TauCeti.IsFiniteType.det_ne_zero`, which is merely the tool it uses: being a
triangle, `Ã₂` is excluded by `TauCeti.IsFiniteType.apply_eq_zero_of_apply_ne_zero` as well, and it
is exactly the equality case of that estimate. -/
theorem not_isFiniteType_affineA₂ :
    ¬ IsFiniteType (!![2, -1, -1; -1, 2, -1; -1, -1, 2] : Matrix (Fin 3) (Fin 3) ℤ) := by
  intro h
  refine h.det_ne_zero ?_
  norm_num [Matrix.det_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

/-- **The Cartan matrix of the affine diagram `D̃₄` is not of finite type.** The four-armed star is
the smallest diagram excluded by the degree bound; unlike `Ã₂` it needs no determinant, since
`TauCeti.IsFiniteType.card_le_three_of_forall_apply_ne_zero` applies to the central index
directly. -/
theorem not_isFiniteType_affineD₄ :
    ¬ IsFiniteType (!![2, -1, -1, -1, -1;
                      -1, 2, 0, 0, 0;
                      -1, 0, 2, 0, 0;
                      -1, 0, 0, 2, 0;
                      -1, 0, 0, 0, 2] : Matrix (Fin 5) (Fin 5) ℤ) := by
  intro h
  have hcard := h.card_le_three_of_forall_apply_ne_zero (i := 0) (s := {1, 2, 3, 4})
    (by decide) (by decide)
  revert hcard
  decide

/-- **A triangle carrying double edges is not of finite type.** This matrix is a generalized Cartan
matrix; it is symmetrizable, by `d = (1, 2, 1)`; its Cartan products `2`, `1`, `2` all lie in the
rank-two range; and it is nonsingular, with determinant `-6`. So neither the combinatorial axioms,
nor `TauCeti.IsFiniteType.apply_mul_apply_mem_of_ne`, nor `TauCeti.IsFiniteType.det_ne_zero`
excludes it. Neither does the star bound: no two of the three indices are non-adjacent, so the only
neighbour sets meeting its pairwise non-adjacency hypothesis are the empty and the singleton ones,
whose Cartan products sum to at most `2` and so stay clear of the bound. It is
`TauCeti.IsFiniteType.apply_eq_zero_of_apply_ne_zero` that rules it out. -/
theorem not_isFiniteType_doubleEdgeTriangle :
    ¬ IsFiniteType (!![2, -2, -1; -1, 2, -1; -1, -2, 2] : Matrix (Fin 3) (Fin 3) ℤ) := by
  intro h
  have h12 := h.apply_eq_zero_of_apply_ne_zero (i := 0) (j := 1) (k := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  revert h12
  decide

section RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- **The Cartan matrix of a base of a finite crystallographic root system is of finite type.** The
symmetrizer is the vector of inverse root lengths for the canonical form.

Reducedness is not assumed: positive definiteness of the canonical form does not need it. -/
theorem isFiniteType_cartanMatrix [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] [P.IsCrystallographic] (b : P.Base) :
    IsFiniteType b.cartanMatrix := by
  classical
  -- Mathlib packages the positive definite symmetrization over `ℤ`, and
  -- `TauCeti.Matrix.posDef_map_intCast` carries it over `ℚ`.
  obtain ⟨d, hd, hpd⟩ := b.exists_cartanMatrix_diagaonal_mul_posDef
  refine isFiniteType_of (fun i ↦ b.cartanMatrix_apply_same i)
    (fun i j hij ↦ b.cartanMatrix_le_zero_of_ne i j hij)
    (d := fun i ↦ (d i : ℚ)) (fun i ↦ by exact_mod_cast hd i) ?_
  convert Matrix.posDef_map_intCast hpd using 1
  ext i j
  simp [Matrix.diagonal_mul]

/-- **The standard Cartan matrix of a Dynkin type realized by a base is of finite type.** This is
the shape in which the finite-type condition eliminates candidate Dynkin types. -/
theorem HasCartanType.isFiniteType [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] [P.IsCrystallographic] {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) : IsFiniteType t.cartanMatrix := by
  -- Relabelling by the inverse of the matching turns the standard matrix into a principal
  -- submatrix - indeed a reindexing - of the Cartan matrix of the base.
  obtain ⟨e, he⟩ := (hasCartanType_iff_reindex b t).mp h
  rw [← he]
  exact (isFiniteType_cartanMatrix b).submatrix e.symm.injective

end RootPairing

end TauCeti
