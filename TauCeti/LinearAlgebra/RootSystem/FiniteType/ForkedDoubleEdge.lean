/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical

public section

/-!
# A branch vertex and a double edge cannot coexist in a finite-type diagram

A connected finite-type diagram is a tree of maximal degree three, and the constraints of the
Cartan-Killing classification that remain concern where a branch vertex and a multiple edge may
sit. The fork bound
(`TauCeti.eq_zero_or_eq_one_one_or_eq_one_two_le_four_of_isFiniteType_star_three`) settles the
simply-laced branchings, and the rank-two estimates of
`TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic` settle a multiple edge locally. Neither says
anything about a diagram carrying *both* a branch vertex and a double edge, and the list
`Aₙ, Bₙ, Cₙ, Dₙ, E₆, E₇, E₈, F₄, G₂` has no such member. This file supplies that step.

The obstruction is the extended Dynkin diagram `B̃ₗ`, which is exactly the diagram of `Bₗ` with one
further vertex joined to the second vertex of its chain: a fork at one end, a chain, and the double
edge of `Bₗ` at the other end. Adjoining a pendant vertex is the general operation
`TauCeti.adjoinPendant`, and `TauCeti.affineBCartanMatrix n` is `Bₙ₊₃` with a pendant vertex
adjoined at the index `1`, so that the number of vertices separating the fork from the double edge
is arbitrary. An acyclic diagram whose only multiple edge is a double edge, and which has a branch
vertex, carries one of these or one of their transposes: keep the path joining the branch vertex to
the double edge, two further neighbours of the branch vertex, and nothing else. Carrying that
extraction out is left to the step that assembles the classification; what this file provides is
the exclusion it needs, in the form `TauCeti.IsFiniteType.submatrix` consumes.

The certificate is the vector of **marks** `TauCeti.affineBMark`: the value `1` at the two vertices
of the fork and at the short vertex beyond the double edge, and `2` at every vertex in between. The
Cartan matrix annihilates them, so they are a nonzero subdominant vector and
`TauCeti.IsFiniteType.eq_zero_of_forall_mul_sum_apply_mul_nonpos` excludes the diagram. The
transposed family, `Cₙ₊₃` with the same pendant vertex adjoined, is the twisted affine diagram
`A⁽²⁾₂ₗ₋₁`, and it is excluded through `TauCeti.IsFiniteType.transpose`.

The exclusion is sharp in the only direction available to it: deleting the pendant vertex leaves
`CartanMatrix.B (n + 3)`, which `TauCeti.isFiniteType_cartanMatrix_B` proves to be of finite type,
so it is the fork, and not the double edge, that these diagrams die of.

## Main definitions

* `TauCeti.adjoinPendant`: the diagram of a matrix with one further vertex adjoined, joined by a
  single edge to a chosen vertex.
* `TauCeti.affineBCartanMatrix`: the Cartan matrix of the extended Dynkin diagram `B̃ₗ`, for
  `ℓ = n + 3`.
* `TauCeti.affineBMark`: its marks, the test vector the exclusion is proved with.

## Main results

* `TauCeti.sum_affineBCartanMatrix_mul_affineBMark_none` and
  `TauCeti.sum_affineBCartanMatrix_mul_affineBMark_some`: the marks are a null vector.
* `TauCeti.not_isFiniteType_affineBCartanMatrix` and
  `TauCeti.not_isFiniteType_affineBCartanMatrix_transpose`: neither orientation of a fork joined by
  a chain to a double edge is of finite type.

## References

This file continues the "chain/fork length constraints" step of the classification of finite-type
Cartan matrices, Layer 5 of `TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. The
diagram is the affine type `B⁽¹⁾ₗ` of V. G. Kac, *Infinite Dimensional Lie Algebras*, 3rd ed.,
Ch. 4 and Table Aff 1. Kac writes `aᵢⱼ = ⟨αⱼ, αᵢ^∨⟩`, the transpose of the convention
`cartanMatrix i j = ⟨αᵢ, αⱼ^∨⟩` used here, so the null vector below is his vector of comarks. See
also J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §11.4, where the
same configuration is excluded.
-/

open scoped Matrix

namespace TauCeti

variable {α : Type*} [DecidableEq α] {M : Matrix α α ℤ} {i : α}

/-- **Adjoining a pendant vertex.** The diagram of `TauCeti.adjoinPendant M i` is the diagram of
`M` together with one further vertex, written `none`, joined to the vertex `i` by a single edge and
to nothing else. -/
def adjoinPendant (M : Matrix α α ℤ) (i : α) : Matrix (Option α) (Option α) ℤ :=
  Matrix.of fun v w ↦
    match v, w with
    | none, none => 2
    | none, some w => if w = i then -1 else 0
    | some v, none => if v = i then -1 else 0
    | some v, some w => M v w

-- `(rfl)`, not `rfl`: the bodies of the definitions in this file are deliberately left unexposed,
-- and the parenthesised form keeps these equations out of the exported definitional-equality check.
@[simp] lemma adjoinPendant_none_none : adjoinPendant M i none none = 2 := (rfl)

/-- The pendant vertex is joined to `i` alone. -/
@[simp] lemma adjoinPendant_none_some (j : α) :
    adjoinPendant M i none (some j) = if j = i then -1 else 0 := (rfl)

/-- The pendant vertex is joined to `i` alone. -/
@[simp] lemma adjoinPendant_some_none (j : α) :
    adjoinPendant M i (some j) none = if j = i then -1 else 0 := (rfl)

/-- Adjoining a vertex changes no entry of the original matrix. -/
@[simp] lemma adjoinPendant_some_some (j k : α) :
    adjoinPendant M i (some j) (some k) = M j k := (rfl)

/-- Deleting the pendant vertex again recovers the original matrix. -/
@[simp] lemma adjoinPendant_submatrix_some :
    (adjoinPendant M i).submatrix some some = M := (rfl)

/-- The pendant edge is a single edge, so transposition leaves it alone and reverses only the
edges of `M`. -/
@[simp] lemma adjoinPendant_transpose : (adjoinPendant M i)ᵀ = adjoinPendant Mᵀ i := by
  ext v w
  rcases v with _ | v <;> rcases w with _ | w <;> rfl

/-- Adjoining a pendant vertex keeps the diagonal entries equal to `2`, as a generalized Cartan
matrix needs them. -/
lemma adjoinPendant_diag (hM : ∀ j, M j j = 2) (v : Option α) : adjoinPendant M i v v = 2 := by
  cases v with
  | none => exact adjoinPendant_none_none
  | some j => exact hM j

/-- Adjoining a pendant vertex keeps the off-diagonal entries nonpositive. -/
lemma adjoinPendant_apply_le_zero_of_ne (hM : ∀ j k, j ≠ k → M j k ≤ 0) {v w : Option α}
    (hvw : v ≠ w) : adjoinPendant M i v w ≤ 0 := by
  rcases v with _ | v <;> rcases w with _ | w
  · exact absurd rfl hvw
  · rw [adjoinPendant_none_some]; split_ifs <;> norm_num
  · rw [adjoinPendant_some_none]; split_ifs <;> norm_num
  · exact hM v w fun h ↦ hvw (congrArg some h)

/-! ### The affine diagram `B̃ₗ` -/

/-- **The Cartan matrix of the extended Dynkin diagram `B̃ₗ`**, for `ℓ = n + 3`: the chain of `Bₗ`,
whose last edge is double, with one further vertex joined to its second vertex. That second vertex
is then joined to three others, and the double edge stands at the far end of the chain, at an
arbitrary distance from it - at `n = 0` the branch vertex carries the double edge itself. -/
def affineBCartanMatrix (n : ℕ) :
    Matrix (Option (Fin (n + 3))) (Option (Fin (n + 3))) ℤ :=
  adjoinPendant (CartanMatrix.B (n + 3)) ⟨1, by omega⟩

/-- Deleting the pendant vertex of `B̃ₗ` leaves `Bₗ`, which is of finite type. -/
@[simp] lemma affineBCartanMatrix_submatrix_some (n : ℕ) :
    (affineBCartanMatrix n).submatrix some some = CartanMatrix.B (n + 3) :=
  adjoinPendant_submatrix_some

/-- **Reversing the double edge of `B̃ₗ` gives `Cₗ` with the same pendant vertex**, the twisted
affine diagram `A⁽²⁾₂ₗ₋₁`. -/
lemma affineBCartanMatrix_transpose (n : ℕ) :
    (affineBCartanMatrix n)ᵀ = adjoinPendant (CartanMatrix.C (n + 3)) ⟨1, by omega⟩ := by
  rw [affineBCartanMatrix, adjoinPendant_transpose, CartanMatrix.B_transpose]

/-- `B̃ₗ` is a generalized Cartan matrix: its diagonal is `2`. -/
@[simp] lemma affineBCartanMatrix_diag (n : ℕ) (v : Option (Fin (n + 3))) :
    affineBCartanMatrix n v v = 2 :=
  adjoinPendant_diag (fun j ↦ CartanMatrix.B_diag (n + 3) j) v

/-- `B̃ₗ` is a generalized Cartan matrix: its off-diagonal entries are nonpositive. -/
lemma affineBCartanMatrix_apply_le_zero_of_ne (n : ℕ) {v w : Option (Fin (n + 3))} (hvw : v ≠ w) :
    affineBCartanMatrix n v w ≤ 0 :=
  adjoinPendant_apply_le_zero_of_ne
    (fun j k hjk ↦ CartanMatrix.B_off_diag_nonpos (n + 3) j k hjk) hvw

/-! ### The rows of `B̃ₗ` at its marks -/

/-- The Cartan-matrix entry of a chain of type `B` between the positions `s` and `t`, the last
position being `L`: `2` on the diagonal, `-1` between consecutive positions, and `-2` from the
position before the last one to the last one, whose root is the short one.

`TauCeti.LinearAlgebra.RootSystem.FiniteType.Star` carries a simply-laced analogue for the arms of
a star. That one is private to its file, and it describes no double edge, so it cannot serve the
chain of type `B` here. -/
private def bEntry (L s t : ℕ) : ℤ :=
  if s = t then 2 else if s + 1 = t then (if t = L then -2 else -1)
  else if t + 1 = s then -1 else 0

/-- Mathlib's Cartan matrix of type `B`, in the chain coordinates of `TauCeti.bEntry`. -/
private lemma cartanMatrix_B_apply {m : ℕ} (i j : Fin m) :
    CartanMatrix.B m i j = bEntry (m - 1) i j := by
  simp only [CartanMatrix.B, bEntry, Matrix.of_apply, Fin.ext_iff]

/-- **A row of a chain of type `B`, against an arbitrary weighting of its positions.** The row `a`
collects `2 g a`, the value at the position before it - absent at the head of the chain - and the
value at the position after it, doubled when that position is the short end and absent when the row
is the short end itself. -/
private theorem sum_range_bEntry_mul {L m a : ℕ} (ha : a < m) (g : ℕ → ℚ) :
    ∑ s ∈ Finset.range m, (bEntry L a s : ℚ) * g s
      = 2 * g a - (if a = 0 then 0 else g (a - 1))
        - (if a + 1 = m then 0 else (if a + 1 = L then 2 else 1) * g (a + 1)) := by
  have key : ∀ s ∈ Finset.range m, ((bEntry L a s : ℤ) : ℚ) * g s
      = (if s = a then 2 * g a else 0) + (if s + 1 = a then -g s else 0)
        + (if s = a + 1 then -((if a + 1 = L then 2 else 1) * g (a + 1)) else 0) := by
    intro s _
    rcases eq_or_ne s a with rfl | h1
    · simp [bEntry]
    rcases eq_or_ne (s + 1) a with rfl | h2
    · have e1 : ¬ (s + 1 + 1 = s) := by omega
      have e2 : ¬ (s = s + 1 + 1) := by omega
      simp [bEntry, e1, e2]
    rcases eq_or_ne s (a + 1) with rfl | h3
    · have e3 : ¬ (a + 1 + 1 = a) := by omega
      simp [bEntry, e3]
      split_ifs <;> ring
    · simp [bEntry, h1, h2, h3, Ne.symm h1, Ne.symm h3]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h1 : ∑ s ∈ Finset.range m, (if s = a then 2 * g a else 0) = 2 * g a := by
    rw [Finset.sum_ite_eq' (Finset.range m) a fun _ ↦ 2 * g a]
    simp [Finset.mem_range, ha]
  have h3 : ∑ s ∈ Finset.range m,
      (if s = a + 1 then -((if a + 1 = L then 2 else 1) * g (a + 1)) else 0)
      = -(if a + 1 = m then 0 else (if a + 1 = L then 2 else 1) * g (a + 1)) := by
    rw [Finset.sum_ite_eq' (Finset.range m) (a + 1)
      fun _ ↦ -((if a + 1 = L then 2 else 1) * g (a + 1))]
    by_cases hm : a + 1 = m
    · simp [Finset.mem_range, hm]
    · rw [ite_eq_left (Finset.mem_range.2 (by omega)), ite_eq_right hm]
  have h2 : ∑ s ∈ Finset.range m, (if s + 1 = a then -g s else 0)
      = -(if a = 0 then 0 else g (a - 1)) := by
    match a with
    | 0 => simp
    | k + 1 =>
      have hcongr : ∀ s ∈ Finset.range m, (if s + 1 = k + 1 then -g s else 0)
          = (if s = k then -g k else 0) := by
        intro s _
        by_cases h : s = k <;> simp [h]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq' (Finset.range m) k fun _ ↦ -g k,
        ite_eq_left (Finset.mem_range.2 (by omega)), ite_eq_right (Nat.succ_ne_zero k)]
      norm_num
  rw [h1, h2, h3]
  ring

/-- The **marks** of `B̃ₗ`: the value `1` at the two vertices of the fork and at the short vertex
beyond the double edge, and `2` at every vertex of the chain in between.

Along the chain these are the coefficients of the highest root of `Bₗ` in the basis of simple
coroots, `θ^∨ = α₁^∨ + 2 α₂^∨ + ⋯ + 2 α_{ℓ-1}^∨ + α_ℓ^∨`, and the pendant vertex carries `1`: they
are the comarks of the affine type `B⁽¹⁾ₗ`, which is what a null vector of the Cartan matrix is in
the convention `cartanMatrix i j = ⟨αᵢ, αⱼ^∨⟩` used here. -/
def affineBMark (n : ℕ) : Option (Fin (n + 3)) → ℚ
  | none => 1
  | some j => if (j : ℕ) = 0 ∨ (j : ℕ) = n + 2 then 1 else 2

@[simp] lemma affineBMark_none (n : ℕ) : affineBMark n none = 1 := (rfl)

@[simp] lemma affineBMark_some (n : ℕ) (j : Fin (n + 3)) :
    affineBMark n (some j) = if (j : ℕ) = 0 ∨ (j : ℕ) = n + 2 then 1 else 2 := (rfl)

/-- The marks are positive; in particular they are not the zero vector. -/
lemma affineBMark_pos (n : ℕ) (v : Option (Fin (n + 3))) : 0 < affineBMark n v := by
  cases v with
  | none => rw [affineBMark_none]; norm_num
  | some j => rw [affineBMark_some]; split_ifs <;> norm_num

/-- The chain of `B̃ₗ` weighted by the marks: its row `a` sums to `1` at the branch vertex, where
the pendant edge will contribute the missing `-1`, and to `0` at every other vertex. -/
private theorem sum_range_bEntry_mul_affineBMark (n : ℕ) {a : ℕ} (ha : a < n + 3) :
    ∑ s ∈ Finset.range (n + 3),
        (bEntry (n + 2) a s : ℚ) * (if s = 0 ∨ s = n + 2 then 1 else 2)
      = if a = 1 then 1 else 0 := by
  rw [sum_range_bEntry_mul ha]
  match a with
  | 0 =>
    rw [ite_eq_left rfl, ite_eq_left (Or.inl rfl), ite_eq_right (by omega : ¬ (0 + 1 = n + 3)),
      ite_eq_right (by omega : ¬ (0 + 1 = n + 2)),
      ite_eq_right (by omega : ¬ (0 + 1 = 0 ∨ 0 + 1 = n + 2)),
      ite_eq_right (by omega : ¬ ((0 : ℕ) = 1))]
    norm_num
  | 1 =>
    rw [ite_eq_right (by omega : ¬ (1 = 0 ∨ 1 = n + 2)), ite_eq_right (by omega : ¬ ((1 : ℕ) = 0)),
      ite_eq_left (by omega : 1 - 1 = 0 ∨ 1 - 1 = n + 2),
      ite_eq_right (by omega : ¬ (1 + 1 = n + 3)), ite_eq_left rfl]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [ite_eq_left (by omega : 1 + 1 = 0 + 2),
        ite_eq_left (by omega : 1 + 1 = 0 ∨ 1 + 1 = 0 + 2)]
      norm_num
    · rw [ite_eq_right (by omega : ¬ (1 + 1 = n + 2)),
        ite_eq_right (by omega : ¬ (1 + 1 = 0 ∨ 1 + 1 = n + 2))]
      norm_num
  | k + 2 =>
    rw [ite_eq_right (by omega : ¬ (k + 2 = 0)), ite_eq_right (by omega : ¬ (k + 2 = 1)),
      ite_eq_right (by omega : ¬ (k + 2 - 1 = 0 ∨ k + 2 - 1 = n + 2))]
    rcases eq_or_lt_of_le (by omega : k + 2 ≤ n + 2) with hk | hk
    · rw [ite_eq_left (Or.inr hk), ite_eq_left (by omega : k + 2 + 1 = n + 3)]
      norm_num
    · rw [ite_eq_right (by omega : ¬ (k + 2 = 0 ∨ k + 2 = n + 2)),
        ite_eq_right (by omega : ¬ (k + 2 + 1 = n + 3))]
      rcases eq_or_lt_of_le (by omega : k + 3 ≤ n + 2) with hk' | hk'
      · rw [ite_eq_left (by omega : k + 2 + 1 = n + 2),
          ite_eq_left (by omega : k + 3 = 0 ∨ k + 3 = n + 2)]
        norm_num
      · rw [ite_eq_right (by omega : ¬ (k + 2 + 1 = n + 2)),
          ite_eq_right (by omega : ¬ (k + 3 = 0 ∨ k + 3 = n + 2))]
        norm_num

/-- The chain row of `B̃ₗ` at a chain vertex, before the pendant edge is added. -/
private theorem sum_cartanMatrix_B_mul_affineBMark (n : ℕ) (j : Fin (n + 3)) :
    ∑ k : Fin (n + 3), (CartanMatrix.B (n + 3) j k : ℚ) * affineBMark n (some k)
      = if (j : ℕ) = 1 then 1 else 0 := by
  have hcast : ∀ k : Fin (n + 3), ((CartanMatrix.B (n + 3) j k : ℤ) : ℚ) * affineBMark n (some k)
      = (bEntry (n + 2) (j : ℕ) (k : ℕ) : ℚ)
        * (if (k : ℕ) = 0 ∨ (k : ℕ) = n + 2 then 1 else 2) := by
    intro k
    rw [cartanMatrix_B_apply, affineBMark_some]
    norm_num
  rw [Finset.sum_congr rfl fun k _ ↦ hcast k,
    Fin.sum_univ_eq_sum_range
      (fun s ↦ (bEntry (n + 2) (j : ℕ) s : ℚ) * (if s = 0 ∨ s = n + 2 then 1 else 2)) (n + 3)]
  exact sum_range_bEntry_mul_affineBMark n j.isLt

/-- **The row of `B̃ₗ` at the pendant vertex annihilates the marks**: that vertex carries the mark
`1`, and its single neighbour, the branch vertex, carries the mark `2`.

This is not a `simp` lemma, and neither is its companion
`TauCeti.sum_affineBCartanMatrix_mul_affineBMark_some`: `Fintype.sum_option` and the entry lemmas
above dismantle the left-hand side before this equation could fire, so the attribute would report
only as a `simpNF` violation. Both rows are stated in the shape
`TauCeti.IsFiniteType.eq_zero_of_forall_mul_sum_apply_mul_nonpos` consumes, and their call site
reaches them by `rw`. -/
theorem sum_affineBCartanMatrix_mul_affineBMark_none (n : ℕ) :
    ∑ w, (affineBCartanMatrix n none w : ℚ) * affineBMark n w = 0 := by
  rw [Fintype.sum_option]
  have hchain : ∀ k : Fin (n + 3),
      ((affineBCartanMatrix n none (some k) : ℤ) : ℚ) * affineBMark n (some k)
        = if k = (⟨1, by omega⟩ : Fin (n + 3)) then -2 else 0 := by
    intro k
    rw [affineBCartanMatrix, adjoinPendant_none_some, affineBMark_some]
    by_cases hk : k = (⟨1, by omega⟩ : Fin (n + 3))
    · subst hk
      rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right (by omega : ¬ ((1 : ℕ) = 0 ∨ 1 = n + 2))]
      norm_num
    · rw [ite_eq_right hk, ite_eq_right hk]
      norm_num
  rw [Finset.sum_congr rfl fun k _ ↦ hchain k,
    Finset.sum_ite_eq' Finset.univ (⟨1, by omega⟩ : Fin (n + 3)) fun _ ↦ (-2 : ℚ),
    ite_eq_left (Finset.mem_univ _), affineBCartanMatrix, adjoinPendant_none_none,
    affineBMark_none]
  norm_num

/-- **The rows of `B̃ₗ` at a chain vertex annihilate the marks.** Away from the branch vertex the
chain of `Bₗ` does it alone; at the branch vertex the chain leaves `1`, which the pendant edge
cancels.

Not a `simp` lemma, for the reason given at
`TauCeti.sum_affineBCartanMatrix_mul_affineBMark_none`. -/
theorem sum_affineBCartanMatrix_mul_affineBMark_some (n : ℕ) (j : Fin (n + 3)) :
    ∑ w, (affineBCartanMatrix n (some j) w : ℚ) * affineBMark n w = 0 := by
  rw [Fintype.sum_option, affineBCartanMatrix, adjoinPendant_some_none, affineBMark_none]
  have hchain : ∀ k : Fin (n + 3),
      ((adjoinPendant (CartanMatrix.B (n + 3)) (⟨1, by omega⟩ : Fin (n + 3))
          (some j) (some k) : ℤ) : ℚ) * affineBMark n (some k)
        = ((CartanMatrix.B (n + 3) j k : ℤ) : ℚ) * affineBMark n (some k) := by
    intro k
    rw [adjoinPendant_some_some]
  rw [Finset.sum_congr rfl fun k _ ↦ hchain k, sum_cartanMatrix_B_mul_affineBMark]
  have hj : (j = (⟨1, by omega⟩ : Fin (n + 3))) ↔ ((j : ℕ) = 1) := Fin.ext_iff
  by_cases h : (j : ℕ) = 1
  · rw [ite_eq_left (hj.mpr h), ite_eq_left h]
    norm_num
  · rw [ite_eq_right (fun hc ↦ h (hj.mp hc)), ite_eq_right h]
    norm_num

/-- **A fork joined by a chain to a double edge is not of finite type.** The diagram is `Bₗ` with
one further vertex adjoined to the second vertex of its chain, the extended Dynkin diagram `B̃ₗ`;
its marks are a nonzero subdominant vector, indeed a null vector, so
`TauCeti.IsFiniteType.eq_zero_of_forall_mul_sum_apply_mul_nonpos` excludes it.

None of the earlier eliminations reaches it. It is a genuine generalized Cartan matrix, its branch
vertex has degree three, its one double edge is the only multiple edge and has Cartan product `2`,
which the rank-two estimates allow, and the fork bound applies to simply-laced stars only. -/
theorem not_isFiniteType_affineBCartanMatrix (n : ℕ) :
    ¬ IsFiniteType (affineBCartanMatrix n) := by
  intro h
  have hzero := h.eq_zero_of_forall_mul_sum_apply_mul_nonpos (x := affineBMark n) fun v ↦ by
    cases v with
    | none => rw [sum_affineBCartanMatrix_mul_affineBMark_none]; norm_num
    | some j => rw [sum_affineBCartanMatrix_mul_affineBMark_some]; norm_num
  exact absurd (congrFun hzero none) (affineBMark_pos n none).ne'

/-- **The same diagram with its double edge reversed is not of finite type either.** Transposing
`B̃ₗ` reverses every edge, so it fixes the pendant edge and the chain and turns the double edge of
`Bₗ` into that of `Cₗ`, giving the twisted affine diagram `A⁽²⁾₂ₗ₋₁`. The two orientations are the
two ways a double edge can face a branch vertex, so together with
`TauCeti.not_isFiniteType_affineBCartanMatrix` this rules out both. -/
theorem not_isFiniteType_affineBCartanMatrix_transpose (n : ℕ) :
    ¬ IsFiniteType (affineBCartanMatrix n)ᵀ := by
  intro h
  refine not_isFiniteType_affineBCartanMatrix n ?_
  rw [← Matrix.transpose_transpose (affineBCartanMatrix n)]
  exact h.transpose

end TauCeti
