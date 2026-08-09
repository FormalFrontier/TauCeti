/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
* `TauCeti.IsFiniteType.submatrix`: principal submatrices of a finite-type matrix are of finite
  type. This is what lets a forbidden subdiagram rule out a diagram containing it.
* `TauCeti.IsFiniteType.sum_apply_mul_apply_lt_four`: the star bound. The Cartan products joining
  an index to pairwise non-adjacent neighbours sum to less than `4`. This is the first of the two
  positive-definiteness estimates behind the local shape of a finite-type diagram.
* `TauCeti.IsFiniteType.apply_mul_apply_mem_of_ne`: the rank-two bound. For `i ≠ j` the Cartan
  product `A i j * A j i` lies in `{0, 1, 2, 3}`, so every edge of the diagram is single, double or
  triple.
* `TauCeti.IsFiniteType.apply_eq_zero_of_apply_ne_zero`: **a finite-type diagram carries no
  triangle**. Two distinct neighbours of an index are never adjacent to one another. This is the
  second estimate: the test vector is supported on the three indices of the putative triangle, its
  coordinate at each of them being the weight of the opposite edge, and the rank-two bound then
  makes the symmetrized form nonpositive there. `TauCeti.IsFiniteType.pairwise_apply_eq_zero` is the
  same statement for a whole neighbourhood, in the shape the star bound consumes.

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

omit [Fintype B] in
/-- **The square of an edge weight of the symmetrization is a scaled Cartan product.** The weight
`dₚAₚq` squares to `dₚdq · AₚqAqₚ`, the two symmetrizer values times the Cartan product of the
edge. This is what lets the triangle estimate be run over `ℚ`: the square roots of the geometric
argument never appear. -/
private theorem sq_symmetrization_apply {d : B → ℚ} {p q : B}
    (hsymm : d q * (A q p : ℚ) = d p * (A p q : ℚ)) :
    (d p * (A p q : ℚ)) ^ 2 = d p * d q * ((A p q : ℚ) * (A q p : ℚ)) := by
  linear_combination (-(d p * (A p q : ℚ))) * hsymm

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

/-- **Three Cartan products in the rank-two range satisfy `(α + β + γ) ^ 2 ≤ 9αβγ`.** This is the
arithmetic behind the exclusion of triangles. The three edges of a triangle carry Cartan products
between `1` and `3`, and the inequality then says that the test vector built from those three
products does not see a positive value of the symmetrized form. Equality holds exactly at
`α = β = γ = 1`, the simply laced triangle, which is the affine diagram `Ã₂`. -/
private theorem add_sq_le_nine_mul {α β γ : ℤ} (hα : 1 ≤ α) (hα' : α ≤ 3) (hβ : 1 ≤ β)
    (hβ' : β ≤ 3) (hγ : 1 ≤ γ) (hγ' : γ ≤ 3) :
    (α + β + γ) ^ 2 ≤ 9 * (α * β * γ) := by
  interval_cases α <;> interval_cases β <;> interval_cases γ <;> norm_num

/-- **The endgame of the triangle exclusion.** If `m` is positive with `m² = P²αβγ` and the three
Cartan products satisfy the bound of `TauCeti.IsFiniteType.add_sq_le_nine_mul`, then `3m` is not
below `P(α + β + γ)`: squaring the strict inequality would make `9P²αβγ` smaller than itself.

At the call site `P` is the product of the three symmetrizer values, `α`, `β`, `γ` are the Cartan
products along the three edges of the triangle, and `m` is the product of the three edge weights of
the symmetrization, up to sign; the value of the symmetrized form at the test vector is
`2P(α + β + γ) - 6m`, so positive definiteness is exactly the inequality refuted here. -/
private theorem not_three_mul_lt {P m α β γ : ℚ} (hP : 0 < P) (hm : 0 < m)
    (hm2 : m ^ 2 = P ^ 2 * (α * β * γ)) (hb : (α + β + γ) ^ 2 ≤ 9 * (α * β * γ)) :
    ¬ 3 * m < P * (α + β + γ) := fun hlt ↦ by
  nlinarith [mul_le_mul_of_nonneg_left hb (mul_pos hP hP).le, sq_nonneg (P * (α + β + γ) - 3 * m)]

/-- **The three-index core of the no-triangle theorem.** A finite-type matrix on three indices has
a missing edge: if the first index is joined to the other two, those two are not joined to each
other.

The proof is the second, and last, positive-definiteness estimate of this file, and it is a
different one from the star bound: the test vector is supported on *all three* indices, and at each
of them its coordinate is the weight, in the symmetrization, of the *opposite* edge. Writing
`a`, `b`, `c` for the three edge weights - each negative, since the off-diagonal entries are - the
symmetrized form evaluates at that vector to `2(d₀c² + d₁b² + d₂a²) + 6abc`, and the identity
`a² = d₀d₁·(A₀₁A₁₀)` turns this into `2P(α + β + γ) - 6m` in the notation of
`TauCeti.IsFiniteType.not_three_mul_lt`. -/
private theorem apply_eq_zero_fin_three {T : Matrix (Fin 3) (Fin 3) ℤ} (h : IsFiniteType T)
    (h01 : T 0 1 ≠ 0) (h02 : T 0 2 ≠ 0) :
    T 1 2 = 0 := by
  by_contra h12
  obtain ⟨d, hd, hpd⟩ := h.exists_symmetrizer
  have hsymm := symmetrization_apply_comm hpd
  -- Each of the three edges is present, so each edge weight of the symmetrization is negative.
  have hT01 : T 0 1 < 0 := lt_of_le_of_ne (h.apply_le_zero_of_ne (by decide)) h01
  have hT02 : T 0 2 < 0 := lt_of_le_of_ne (h.apply_le_zero_of_ne (by decide)) h02
  have hT12 : T 1 2 < 0 := lt_of_le_of_ne (h.apply_le_zero_of_ne (by decide)) h12
  have ha : d 0 * ((T 0 1 : ℤ) : ℚ) < 0 := mul_neg_of_pos_of_neg (hd 0) (by exact_mod_cast hT01)
  have hb : d 0 * ((T 0 2 : ℤ) : ℚ) < 0 := mul_neg_of_pos_of_neg (hd 0) (by exact_mod_cast hT02)
  have hc : d 1 * ((T 1 2 : ℤ) : ℚ) < 0 := mul_neg_of_pos_of_neg (hd 1) (by exact_mod_cast hT12)
  -- The test vector: at each index, the weight of the opposite edge.
  have hq := hpd.dotProduct_mulVec_pos
    (x := ![-(d 1 * ((T 1 2 : ℤ) : ℚ)), -(d 0 * ((T 0 2 : ℤ) : ℚ)), -(d 0 * ((T 0 1 : ℤ) : ℚ))])
    (fun hcon ↦ by
      have h0 := congrFun hcon 0
      simp only [Matrix.cons_val_zero, Pi.zero_apply, neg_eq_zero] at h0
      linarith)
  rw [star_trivial, Matrix.dot_mulVec_eq_sum_sum] at hq
  simp only [Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hq
  rw [h.apply_self 0, h.apply_self 1, h.apply_self 2, hsymm 0 1, hsymm 0 2, hsymm 1 2] at hq
  push_cast at hq
  -- The square of an edge weight is the Cartan product of that edge, scaled by two symmetrizers.
  have ea := sq_symmetrization_apply (hsymm 0 1)
  have eb := sq_symmetrization_apply (hsymm 0 2)
  have ec := sq_symmetrization_apply (hsymm 1 2)
  -- Package the three edges as the data the arithmetic endgame consumes.
  refine not_three_mul_lt (P := d 0 * d 1 * d 2)
    (m := -(d 0 * ((T 0 1 : ℤ) : ℚ) * (d 0 * ((T 0 2 : ℤ) : ℚ)) * (d 1 * ((T 1 2 : ℤ) : ℚ))))
    (α := ((T 0 1 : ℤ) : ℚ) * ((T 1 0 : ℤ) : ℚ)) (β := ((T 0 2 : ℤ) : ℚ) * ((T 2 0 : ℤ) : ℚ))
    (γ := ((T 1 2 : ℤ) : ℚ) * ((T 2 1 : ℤ) : ℚ))
    (mul_pos (mul_pos (hd 0) (hd 1)) (hd 2))
    (neg_pos.mpr (mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg ha hb) hc)) ?_ ?_ ?_
  · -- `m² = P²αβγ`, by multiplying the three edge identities.
    have : (-(d 0 * ((T 0 1 : ℤ) : ℚ) * (d 0 * ((T 0 2 : ℤ) : ℚ)) * (d 1 * ((T 1 2 : ℤ) : ℚ)))) ^ 2
        = (d 0 * ((T 0 1 : ℤ) : ℚ)) ^ 2 * (d 0 * ((T 0 2 : ℤ) : ℚ)) ^ 2 *
          (d 1 * ((T 1 2 : ℤ) : ℚ)) ^ 2 := by ring
    rw [this, ea, eb, ec]
    ring
  · -- The rank-two bound on each of the three edges feeds the arithmetic inequality.
    have hα := h.one_le_apply_mul_apply h01
    have hβ := h.one_le_apply_mul_apply h02
    have hγ := h.one_le_apply_mul_apply h12
    have hα' := h.apply_mul_apply_mem_of_ne (i := 0) (j := 1) (by decide)
    have hβ' := h.apply_mul_apply_mem_of_ne (i := 0) (j := 2) (by decide)
    have hγ' := h.apply_mul_apply_mem_of_ne (i := 1) (j := 2) (by decide)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα' hβ' hγ'
    have := add_sq_le_nine_mul hα (by omega) hβ (by omega) hγ (by omega)
    exact_mod_cast this
  · -- Positive definiteness at the test vector, rewritten through the three edge identities: each
    -- diagonal contribution is twice `P` times the Cartan product of the opposite edge.
    have ea' : 2 * d 2 * (d 0 * ((T 0 1 : ℤ) : ℚ)) ^ 2
        = 2 * (d 0 * d 1 * d 2) * (((T 0 1 : ℤ) : ℚ) * ((T 1 0 : ℤ) : ℚ)) := by rw [ea]; ring
    have eb' : 2 * d 1 * (d 0 * ((T 0 2 : ℤ) : ℚ)) ^ 2
        = 2 * (d 0 * d 1 * d 2) * (((T 0 2 : ℤ) : ℚ) * ((T 2 0 : ℤ) : ℚ)) := by rw [eb]; ring
    have ec' : 2 * d 0 * (d 1 * ((T 1 2 : ℤ) : ℚ)) ^ 2
        = 2 * (d 0 * d 1 * d 2) * (((T 1 2 : ℤ) : ℚ) * ((T 2 1 : ℤ) : ℚ)) := by rw [ec]; ring
    linarith [hq, ea', eb', ec']

/-- **A finite-type diagram carries no triangle.** Two distinct neighbours of an index are never
adjacent to one another, so the neighbourhood of an index is pairwise non-adjacent and the star
bound applies to it with no side condition.

This is what turns the conditional consequences of the star bound into graph statements: the degree
bound `TauCeti.IsFiniteType.card_le_three_of_forall_apply_ne_zero`, the fact that at most one edge
at an index is multiple, and the isolation of a triple edge. -/
theorem apply_eq_zero_of_apply_ne_zero (h : IsFiniteType A) {i j k : B} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hj : A i j ≠ 0) (hk : A i k ≠ 0) :
    A j k = 0 := by
  -- Restrict to the principal submatrix on the three indices and apply the three-index core.
  have he : Function.Injective ![i, j, k] := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all
  have h' := h.submatrix he
  have e01 : (A.submatrix ![i, j, k] ![i, j, k]) 0 1 = A i j := by simp
  have e02 : (A.submatrix ![i, j, k] ![i, j, k]) 0 2 = A i k := by simp
  have e12 : (A.submatrix ![i, j, k] ![i, j, k]) 1 2 = A j k := by simp
  have := apply_eq_zero_fin_three h' (e01 ▸ hj) (e02 ▸ hk)
  rwa [e12] at this

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
  have hu : IsUnit (Matrix.diagonal d * A.map (Int.cast : ℤ → ℚ)) := by
    apply Matrix.PosDef.isUnit
    convert hpd using 1
    ext i j
    simp [Matrix.diagonal_mul]
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.det_diagonal] at hu
  intro hdet
  have hzero : (A.map (Int.cast : ℤ → ℚ)).det = 0 := by
    rw [← Int.cast_det A, hdet, Int.cast_zero]
  rw [hzero, mul_zero] at hu
  simp at hu

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
