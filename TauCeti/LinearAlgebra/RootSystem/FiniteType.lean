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
  an index to pairwise non-adjacent neighbours sum to less than `4`. This is the one
  positive-definiteness estimate behind the local shape of a finite-type diagram, and the results
  below are its corollaries.
* `TauCeti.IsFiniteType.apply_mul_apply_mem_of_ne`: the rank-two bound. For `i ≠ j` the Cartan
  product `A i j * A j i` lies in `{0, 1, 2, 3}`, so every edge of the diagram is single, double or
  triple.
* `TauCeti.IsFiniteType.card_le_three_of_pairwise_apply_eq_zero`: the degree bound for a
  non-adjacent star. No index has four pairwise non-adjacent neighbours; the affine type `D̃₄` is
  ruled out in `TauCeti.not_isFiniteType_affineD₄`.
* `TauCeti.IsFiniteType.apply_mul_apply_le_one_of_two_le` and
  `TauCeti.IsFiniteType.apply_eq_zero_of_apply_mul_apply_eq_three`: of two edges at an index whose
  far ends are non-adjacent at most one is multiple, and an index carrying a triple edge is joined
  to no further index non-adjacent to the far end of that edge.
* `TauCeti.IsFiniteType.apply_mul_apply_eq_one_of_three_le_card`: three pairwise non-adjacent
  neighbours of an index are each joined to it by a single edge.

Each of these consequences selects its neighbours through a pairwise non-adjacency hypothesis,
which is what the star bound asks for. Turning them into the unconditional graph statements the
classification runs on - degree at most three, at most one multiple edge at a vertex, an isolated
triple edge, a simply laced branch vertex - needs in addition that distinct neighbours of an index
are never adjacent, that is, that a finite-type diagram carries no triangle. That exclusion is not
proved here.
* `TauCeti.IsFiniteType.det_ne_zero`: a finite-type matrix is nonsingular. Since the extended
  Dynkin diagrams have singular Cartan matrices, this is the second elimination tool; the affine
  type `Ã₂` is ruled out in `TauCeti.not_isFiniteType_affineA₂`.
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

This is the single positive-definiteness estimate behind the local shape of a finite-type diagram:
inside a pairwise non-adjacent star at `i` there are at most three neighbours, at most one of the
edges to them is multiple, and a triple edge among them stands alone. -/
theorem sum_apply_mul_apply_lt_four (h : IsFiniteType A) {i : B} {s : Finset B} (his : i ∉ s)
    (hs : (s : Set B).Pairwise fun j k ↦ A j k = 0) :
    ∑ j ∈ s, A i j * A j i < 4 := by
  classical
  obtain ⟨d, hd, hpd⟩ := h.exists_symmetrizer
  -- The symmetrizer intertwines the two entries of a transposed pair.
  have hsymm : ∀ p q : B, d q * (A q p : ℚ) = d p * (A p q : ℚ) := fun p q ↦ by
    simpa using hpd.isHermitian.apply p q
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

/-- **The two-index case of the star bound.** Two non-adjacent indices `j` and `k`, both distinct
from `i`, carry Cartan products with `i` summing to less than `4`; neither is required to be a
neighbour of `i`, an absent edge contributing `0`. Here `j ≠ k` need not be assumed: it follows
from `A j k = 0`, since the diagonal entries are `2`. -/
theorem apply_mul_apply_add_apply_mul_apply_lt_four (h : IsFiniteType A) {i j k : B} (hij : i ≠ j)
    (hik : i ≠ k) (h0 : A j k = 0) :
    A i j * A j i + A i k * A k i < 4 := by
  classical
  have hjk : j ≠ k := fun hc ↦ by rw [hc, h.apply_self k] at h0; omega
  have hkj : A k j = 0 := h.apply_eq_zero_symm h0
  have hi : i ∉ ({j, k} : Finset B) := by simp [hij, hik]
  have hp : ((({j, k} : Finset B) : Set B)).Pairwise fun p q ↦ A p q = 0 := by
    intro p hp' q hq' hpq
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hp' hq'
    rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl <;> simp_all
  have hlt := h.sum_apply_mul_apply_lt_four hi hp
  rwa [Finset.sum_insert (by simpa using hjk), Finset.sum_singleton] at hlt

/-- **At most one edge of a non-adjacent pair at an index is multiple.** If the edge from `i` to
`j` is multiple, then `i` is joined to every index non-adjacent to `j` by at most a single edge. -/
theorem apply_mul_apply_le_one_of_two_le (h : IsFiniteType A) {i j k : B} (h0 : A j k = 0)
    (hj : 2 ≤ A i j * A j i) :
    A i k * A k i ≤ 1 := by
  -- A multiple edge at `i` makes `i ≠ j`, and were `i` equal to `k` that edge would be absent.
  rcases eq_or_ne i j with rfl | hij
  · simp [h0]
  have hik : i ≠ k := by
    rintro rfl
    rw [h.apply_eq_zero_symm h0] at hj
    simp at hj
  have := h.apply_mul_apply_add_apply_mul_apply_lt_four hij hik h0
  omega

/-- **A triple edge is isolated among the neighbours non-adjacent to its far end.** An index joined
to `j` by a triple edge is joined to no further index non-adjacent to `j`. This is the local step
behind `G₂` being the only finite-type diagram carrying a triple edge. -/
theorem apply_eq_zero_of_apply_mul_apply_eq_three (h : IsFiniteType A) {i j k : B} (h0 : A j k = 0)
    (hj : A i j * A j i = 3) :
    A i k = 0 := by
  -- A Cartan product of `3` is neither the diagonal value `4` nor the absent edge from `k` to `j`.
  have hij : i ≠ j := by
    rintro rfl
    rw [h.apply_self] at hj
    omega
  have hik : i ≠ k := by
    rintro rfl
    rw [h.apply_eq_zero_symm h0] at hj
    simp at hj
  by_contra hne
  have h1 := h.one_le_apply_mul_apply hne
  have := h.apply_mul_apply_add_apply_mul_apply_lt_four hij hik h0
  omega

/-- **An index of a finite-type matrix has at most three pairwise non-adjacent neighbours**, so a
finite-type diagram branches into at most three pairwise unjoined arms. The unconditional degree
bound asks in addition that distinct neighbours of an index are non-adjacent, which is not proved
here. -/
theorem card_le_three_of_pairwise_apply_eq_zero (h : IsFiniteType A) {i : B} {s : Finset B}
    (his : i ∉ s) (hadj : ∀ j ∈ s, A i j ≠ 0)
    (hs : (s : Set B).Pairwise fun j k ↦ A j k = 0) :
    s.card ≤ 3 := by
  have hone : ∀ j ∈ s, (1 : ℤ) ≤ A i j * A j i := fun j hj ↦
    h.one_le_apply_mul_apply (hadj j hj)
  have hcard : (s.card : ℤ) ≤ ∑ j ∈ s, A i j * A j i := by
    calc (s.card : ℤ) = ∑ _j ∈ s, (1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum hone
  have := h.sum_apply_mul_apply_lt_four his hs
  omega

/-- **A three-armed non-adjacent star of a finite-type matrix is simply laced.** An index with
three pairwise non-adjacent neighbours meets each of them along a single edge, since three Cartan
products of value at least `1` already exhaust the star bound. -/
theorem apply_mul_apply_eq_one_of_three_le_card (h : IsFiniteType A) {i : B} {s : Finset B}
    (his : i ∉ s) (hadj : ∀ j ∈ s, A i j ≠ 0)
    (hs : (s : Set B).Pairwise fun j k ↦ A j k = 0) (hcard : 3 ≤ s.card) {j : B} (hj : j ∈ s) :
    A i j * A j i = 1 := by
  classical
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
combinatorial axioms nor the rank-two bound exclude it; it is positive *semi*definite, and it is
`TauCeti.IsFiniteType.det_ne_zero` that rules it out. -/
theorem not_isFiniteType_affineA₂ :
    ¬ IsFiniteType (!![2, -1, -1; -1, 2, -1; -1, -1, 2] : Matrix (Fin 3) (Fin 3) ℤ) := by
  intro h
  refine h.det_ne_zero ?_
  norm_num [Matrix.det_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

/-- **The Cartan matrix of the affine diagram `D̃₄` is not of finite type.** The four-armed star is
the smallest diagram excluded by the degree bound; unlike `Ã₂` it needs no determinant, since
`TauCeti.IsFiniteType.card_le_three_of_pairwise_apply_eq_zero` applies to the central index
directly. -/
theorem not_isFiniteType_affineD₄ :
    ¬ IsFiniteType (!![2, -1, -1, -1, -1;
                      -1, 2, 0, 0, 0;
                      -1, 0, 2, 0, 0;
                      -1, 0, 0, 2, 0;
                      -1, 0, 0, 0, 2] : Matrix (Fin 5) (Fin 5) ℤ) := by
  intro h
  have hcard := h.card_le_three_of_pairwise_apply_eq_zero (i := 0) (s := {1, 2, 3, 4})
    (by decide) (by decide) (by
      intro p hp q hq hpq
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hp hq
      rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
        revert hpq <;> decide)
  revert hcard
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
