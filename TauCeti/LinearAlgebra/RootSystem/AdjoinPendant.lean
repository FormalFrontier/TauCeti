/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NormNum

public section

/-!
# Adjoining a pendant vertex to a matrix

This file defines the matrix obtained by adjoining one further vertex, joined by a single edge to a
chosen vertex of an integer matrix. The construction is independent of finite type and is used to
assemble Cartan matrices of diagrams with a pendant vertex.

## Main definitions

* `TauCeti.adjoinPendant`: adjoin a new vertex, indexed by `none`, to a chosen vertex of a matrix.

## Main results

* `TauCeti.adjoinPendant_submatrix_some`: deleting the new vertex recovers the original matrix.
* `TauCeti.adjoinPendant_transpose`: adjoining a pendant vertex commutes with transposition.
* `TauCeti.adjoinPendant_diag` and `TauCeti.adjoinPendant_apply_le_zero_of_ne`: adjoining a pendant
  vertex preserves the diagonal and off-diagonal sign conditions of a generalized Cartan matrix.
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

-- `(rfl)`, not `rfl`: the body of `TauCeti.adjoinPendant` is deliberately left unexposed, and the
-- parenthesised form keeps these equations out of the exported definitional-equality check.
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
  | some j => rw [adjoinPendant_some_some]; exact hM j

/-- Adjoining a pendant vertex keeps the off-diagonal entries nonpositive. -/
lemma adjoinPendant_apply_le_zero_of_ne (hM : ∀ j k, j ≠ k → M j k ≤ 0) {v w : Option α}
    (hvw : v ≠ w) : adjoinPendant M i v w ≤ 0 := by
  rcases v with _ | v <;> rcases w with _ | w
  · exact absurd rfl hvw
  · rw [adjoinPendant_none_some]; split_ifs <;> norm_num
  · rw [adjoinPendant_some_none]; split_ifs <;> norm_num
  · rw [adjoinPendant_some_some]; exact hM v w fun h ↦ hvw (congrArg some h)

end TauCeti
