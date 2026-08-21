/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic
public import TauCeti.LinearAlgebra.RootSystem.Chain
public import TauCeti.LinearAlgebra.RootSystem.AdjoinPendant

public section

/-!
# The affine diagrams `B̃ₗ` and `A⁽²⁾₂ₗ₋₁` are not of finite type

A connected finite-type diagram is a tree of maximal degree three, and the constraints of the
Cartan-Killing classification that remain concern where a branch vertex and a multiple edge may
sit. The fork bound
(`TauCeti.eq_zero_or_eq_one_one_or_eq_one_two_le_four_of_isFiniteType_star_three`) settles the
simply-laced branchings; the rank-two estimates of
`TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic` settle a multiple edge locally; and
`TauCeti.IsFiniteType.apply_mul_apply_eq_one_of_three_le_card` already excludes a multiple edge
*incident to* a branch vertex, since a vertex of degree three meets each of its neighbours along a
single edge. What none of them reaches is a double edge at a positive distance from a branch
vertex, and the list `Aₙ, Bₙ, Cₙ, Dₙ, E₆, E₇, E₈, F₄, G₂` has no such member. This file supplies
that step.

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

The certificate is the vector of **comarks** `TauCeti.affineBComark`: the value `1` at the two
vertices of the fork and at the short vertex beyond the double edge, and `2` at every vertex in
between. The Cartan matrix annihilates them, so they are a nonzero subdominant vector and
`TauCeti.IsFiniteType.eq_zero_of_forall_mul_sum_apply_mul_nonpos` excludes the diagram. The
transposed family, `Cₙ₊₃` with the same pendant vertex adjoined, is the twisted affine diagram
`A⁽²⁾₂ₗ₋₁`, and it is excluded through `TauCeti.IsFiniteType.transpose`. The rows of the chain are
evaluated with `TauCeti.sum_range_chainBEntry_mul`. Its simply-laced specialization is
`TauCeti.sum_range_chainEntry_mul`, used by
`TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.Basic`.

The exclusion is sharp in the only direction available to it: deleting the pendant vertex leaves
`CartanMatrix.B (n + 3)`, which `TauCeti.isFiniteType_cartanMatrix_B` proves to be of finite type,
so it is the fork, and not the double edge, that these diagrams die of.

## Main definitions

* `TauCeti.affineBCartanMatrix`: the Cartan matrix of the extended Dynkin diagram `B̃ₗ`, for
  `ℓ = n + 3`.
* `TauCeti.affineBComark`: its comarks, the test vector the exclusion is proved with.

## Main results

* `TauCeti.sum_affineBCartanMatrix_mul_affineBComark_eq_zero`: the comarks are a null vector of the
  Cartan matrix.
* `TauCeti.not_isFiniteType_affineBCartanMatrix` and
  `TauCeti.not_isFiniteType_affineBCartanMatrix_transpose`: `affineBCartanMatrix n` and its
  transpose, the affine diagrams `B̃ₗ` and `A⁽²⁾₂ₗ₋₁`, are not of finite type.

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

/-! ### The affine diagram `B̃ₗ` -/

/-- **The Cartan matrix of the extended Dynkin diagram `B̃ₗ`**, for `ℓ = n + 3`: the chain of `Bₗ`,
whose last edge is double, with one further vertex joined to its second vertex. That second vertex
is then joined to three others, and the double edge stands at the far end of the chain, at an
arbitrary distance from it - at `n = 0` the branch vertex carries the double edge itself. -/
def affineBCartanMatrix (n : ℕ) :
    Matrix (Option (Fin (n + 3))) (Option (Fin (n + 3))) ℤ :=
  adjoinPendant (CartanMatrix.B (n + 3)) ⟨1, by omega⟩

/-- `B̃ₗ` as a pendant vertex adjoined to `Bₗ`. This is not a `simp` lemma: it would dismantle the
left-hand sides of the entry lemmas below, which state the entries of `B̃ₗ` in its own terms. It is
what identifies a diagram extracted from a larger one with this family, together with the entry
lemmas. -/
lemma affineBCartanMatrix_def (n : ℕ) :
    affineBCartanMatrix n = adjoinPendant (CartanMatrix.B (n + 3)) ⟨1, by omega⟩ := (rfl)

/-- The pendant vertex of `B̃ₗ` is joined to the vertex `1` of the chain alone. -/
@[simp] lemma affineBCartanMatrix_none_some (n : ℕ) (j : Fin (n + 3)) :
    affineBCartanMatrix n none (some j) = if (j : ℕ) = 1 then -1 else 0 := by
  rw [affineBCartanMatrix_def, adjoinPendant_none_some]
  simp [Fin.ext_iff]

/-- The pendant vertex of `B̃ₗ` is joined to the vertex `1` of the chain alone. -/
@[simp] lemma affineBCartanMatrix_some_none (n : ℕ) (j : Fin (n + 3)) :
    affineBCartanMatrix n (some j) none = if (j : ℕ) = 1 then -1 else 0 := by
  rw [affineBCartanMatrix_def, adjoinPendant_some_none]
  simp [Fin.ext_iff]

/-- Adjoining the pendant vertex changes no entry of the chain of `Bₗ`. -/
@[simp] lemma affineBCartanMatrix_some_some (n : ℕ) (j k : Fin (n + 3)) :
    affineBCartanMatrix n (some j) (some k) = CartanMatrix.B (n + 3) j k := by
  rw [affineBCartanMatrix_def, adjoinPendant_some_some]

/-- Deleting the pendant vertex of `B̃ₗ` leaves `Bₗ`, which is of finite type. -/
@[simp] lemma affineBCartanMatrix_submatrix_some (n : ℕ) :
    (affineBCartanMatrix n).submatrix some some = CartanMatrix.B (n + 3) := by
  rw [affineBCartanMatrix_def, adjoinPendant_submatrix_some]

/-- **Reversing the double edge of `B̃ₗ` gives `Cₗ` with the same pendant vertex**, the twisted
affine diagram `A⁽²⁾₂ₗ₋₁`. -/
@[simp] lemma affineBCartanMatrix_transpose (n : ℕ) :
    (affineBCartanMatrix n)ᵀ = adjoinPendant (CartanMatrix.C (n + 3)) ⟨1, by omega⟩ := by
  rw [affineBCartanMatrix_def, adjoinPendant_transpose, CartanMatrix.B_transpose]

/-- `B̃ₗ` is a generalized Cartan matrix: its diagonal is `2`. -/
@[simp] lemma affineBCartanMatrix_diag (n : ℕ) (v : Option (Fin (n + 3))) :
    affineBCartanMatrix n v v = 2 := by
  rw [affineBCartanMatrix_def]
  exact adjoinPendant_diag (fun j ↦ CartanMatrix.B_diag (n + 3) j) v

/-- `B̃ₗ` is a generalized Cartan matrix: its off-diagonal entries are nonpositive. -/
lemma affineBCartanMatrix_apply_le_zero_of_ne (n : ℕ) {v w : Option (Fin (n + 3))} (hvw : v ≠ w) :
    affineBCartanMatrix n v w ≤ 0 := by
  rw [affineBCartanMatrix_def]
  exact adjoinPendant_apply_le_zero_of_ne
    (fun j k hjk ↦ CartanMatrix.B_off_diag_nonpos (n + 3) j k hjk) hvw

/-! ### The rows of `B̃ₗ` at its comarks -/

/-- The **comarks** of `B̃ₗ`: the value `1` at the two vertices of the fork and at the short vertex
beyond the double edge, and `2` at every vertex of the chain in between.

Along the chain these are the coefficients of the highest root of `Bₗ` in the basis of simple
coroots, `θ^∨ = α₁^∨ + 2 α₂^∨ + ⋯ + 2 α_{ℓ-1}^∨ + α_ℓ^∨`, and the pendant vertex carries `1`: they
are the comarks of the affine type `B⁽¹⁾ₗ`, which is what a null vector of the Cartan matrix is in
the convention `cartanMatrix i j = ⟨αᵢ, αⱼ^∨⟩` used here. -/
def affineBComark (n : ℕ) : Option (Fin (n + 3)) → ℚ
  | none => 1
  | some j => if (j : ℕ) = 0 ∨ (j : ℕ) = n + 2 then 1 else 2

@[simp] lemma affineBComark_none (n : ℕ) : affineBComark n none = 1 := (rfl)

@[simp] lemma affineBComark_some (n : ℕ) (j : Fin (n + 3)) :
    affineBComark n (some j) = if (j : ℕ) = 0 ∨ (j : ℕ) = n + 2 then 1 else 2 := (rfl)

/-- The comarks are positive; in particular they are not the zero vector. -/
lemma affineBComark_pos (n : ℕ) (v : Option (Fin (n + 3))) : 0 < affineBComark n v := by
  cases v with
  | none => rw [affineBComark_none]; norm_num
  | some j => rw [affineBComark_some]; split_ifs <;> norm_num

/-- The chain of `B̃ₗ` weighted by the comarks: its row `a` sums to `1` at the branch vertex, where
the pendant edge will contribute the missing `-1`, and to `0` at every other vertex. -/
private theorem sum_range_chainBEntry_mul_affineBComark (n : ℕ) {a : ℕ} (ha : a < n + 3) :
    ∑ s ∈ Finset.range (n + 3),
        (chainBEntry (n + 2) a s : ℚ) * (if s = 0 ∨ s = n + 2 then 1 else 2)
      = if a = 1 then 1 else 0 := by
  rw [sum_range_chainBEntry_mul ha]
  match a with
  | 0 => split_ifs <;> grind
  | 1 => split_ifs <;> grind
  | k + 2 => split_ifs <;> grind

/-- The chain row of `B̃ₗ` at a chain vertex, before the pendant edge is added. -/
private theorem sum_cartanMatrix_B_mul_affineBComark (n : ℕ) (j : Fin (n + 3)) :
    ∑ k : Fin (n + 3), (CartanMatrix.B (n + 3) j k : ℚ) * affineBComark n (some k)
      = if (j : ℕ) = 1 then 1 else 0 := by
  have hcast : ∀ k : Fin (n + 3), ((CartanMatrix.B (n + 3) j k : ℤ) : ℚ) * affineBComark n (some k)
      = (chainBEntry (n + 2) (j : ℕ) (k : ℕ) : ℚ)
        * (if (k : ℕ) = 0 ∨ (k : ℕ) = n + 2 then 1 else 2) := by
    intro k
    rw [← chainBEntry_eq_cartanMatrix_B, affineBComark_some]
    norm_num
  rw [Finset.sum_congr rfl fun k _ ↦ hcast k,
    Fin.sum_univ_eq_sum_range
      (fun s ↦ (chainBEntry (n + 2) (j : ℕ) s : ℚ) * (if s = 0 ∨ s = n + 2 then 1 else 2)) (n + 3)]
  exact sum_range_chainBEntry_mul_affineBComark n j.isLt

/-- **The row of `B̃ₗ` at the pendant vertex annihilates the comarks**: that vertex carries the
comark `1`, and its single neighbour, the branch vertex, carries the comark `2`.

This row and its companion below are the two halves of
`TauCeti.sum_affineBCartanMatrix_mul_affineBComark_eq_zero`, which states them uniformly and is the
form a consumer wants; they are private. -/
private theorem sum_affineBCartanMatrix_mul_affineBComark_none_eq_zero (n : ℕ) :
    ∑ w, (affineBCartanMatrix n none w : ℚ) * affineBComark n w = 0 := by
  rw [Fintype.sum_option]
  have hchain : ∀ k : Fin (n + 3),
      ((affineBCartanMatrix n none (some k) : ℤ) : ℚ) * affineBComark n (some k)
        = if k = (⟨1, by omega⟩ : Fin (n + 3)) then -2 else 0 := by
    intro k
    have hk : (k = (⟨1, by omega⟩ : Fin (n + 3))) ↔ ((k : ℕ) = 1) := Fin.ext_iff
    rw [affineBCartanMatrix_none_some, affineBComark_some]
    simp only [hk]
    split_ifs <;> grind
  rw [Finset.sum_congr rfl fun k _ ↦ hchain k,
    Finset.sum_ite_eq' Finset.univ (⟨1, by omega⟩ : Fin (n + 3)) fun _ ↦ (-2 : ℚ),
    ite_eq_left (Finset.mem_univ _), affineBCartanMatrix_diag, affineBComark_none]
  norm_num

/-- **The rows of `B̃ₗ` at a chain vertex annihilate the comarks.** Away from the branch vertex the
chain of `Bₗ` does it alone; at the branch vertex the chain leaves `1`, which the pendant edge
cancels.

Private, for the reason given at
`TauCeti.sum_affineBCartanMatrix_mul_affineBComark_none_eq_zero`. -/
private theorem sum_affineBCartanMatrix_mul_affineBComark_some_eq_zero (n : ℕ) (j : Fin (n + 3)) :
    ∑ w, (affineBCartanMatrix n (some j) w : ℚ) * affineBComark n w = 0 := by
  rw [Fintype.sum_option, affineBCartanMatrix_some_none, affineBComark_none]
  have hchain : ∀ k : Fin (n + 3),
      ((affineBCartanMatrix n (some j) (some k) : ℤ) : ℚ) * affineBComark n (some k)
        = ((CartanMatrix.B (n + 3) j k : ℤ) : ℚ) * affineBComark n (some k) := by
    intro k
    rw [affineBCartanMatrix_some_some]
  rw [Finset.sum_congr rfl fun k _ ↦ hchain k, sum_cartanMatrix_B_mul_affineBComark]
  split_ifs <;> grind

/-- **The comarks of `B̃ₗ` are a null vector of its Cartan matrix.** This is the certificate the
exclusion runs on, stated in the shape
`TauCeti.IsFiniteType.eq_zero_of_forall_mul_sum_apply_mul_nonpos` consumes.

This is not a `simp` lemma: `Fintype.sum_option` and the entry lemmas above dismantle the left-hand
side before the equation could fire, so the attribute would report only as a `simpNF` violation. -/
theorem sum_affineBCartanMatrix_mul_affineBComark_eq_zero (n : ℕ) (v : Option (Fin (n + 3))) :
    ∑ w, (affineBCartanMatrix n v w : ℚ) * affineBComark n w = 0 := by
  cases v with
  | none => exact sum_affineBCartanMatrix_mul_affineBComark_none_eq_zero n
  | some j => exact sum_affineBCartanMatrix_mul_affineBComark_some_eq_zero n j

/-- **The affine diagram `B̃ₗ` is not of finite type.** It is `Bₗ` with one further vertex adjoined
to the second vertex of its chain, so a fork joined by a chain to a double edge; its comarks are a
nonzero subdominant vector, indeed a null vector, so
`TauCeti.IsFiniteType.eq_zero_of_forall_mul_sum_apply_mul_nonpos` excludes it.

For `n ≥ 1` no earlier elimination reaches it: it is a genuine generalized Cartan matrix, its
branch vertex has degree three, its one double edge is the only multiple edge and has Cartan
product `2`, which the rank-two estimates allow, and the fork bound applies to simply-laced stars
only. At `n = 0` the branch vertex carries the double edge itself, and
`TauCeti.IsFiniteType.apply_mul_apply_eq_one_of_three_le_card` - a branch vertex is simply laced -
already excludes that member. -/
theorem not_isFiniteType_affineBCartanMatrix (n : ℕ) :
    ¬ IsFiniteType (affineBCartanMatrix n) := by
  intro h
  have hzero := h.eq_zero_of_forall_mul_sum_apply_mul_nonpos (x := affineBComark n) fun v ↦ by
    rw [sum_affineBCartanMatrix_mul_affineBComark_eq_zero]
    norm_num
  exact absurd (congrFun hzero none) (affineBComark_pos n none).ne'

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
