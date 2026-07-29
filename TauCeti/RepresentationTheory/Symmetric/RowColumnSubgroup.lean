/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Combinatorics.Young.YoungTableau
public import TauCeti.GroupTheory.Perm.FiberSubgroup

/-!
# The row and column groups of a Young tableau

A `μ`-tableau `t` is the datum a Young symmetrizer is built from: the row symmetrizer sums over
the permutations of the labels that stay inside their row of `t`, and the column antisymmetrizer
sums with signs over those that stay inside their column.

This file defines the two subgroups `YoungTableau.rowSubgroup t` and `YoungTableau.colSubgroup t`
of `Equiv.Perm (Fin μ.card)` cut out by those conditions, and proves the two facts the symmetrizer
theory rests on: the row and column groups meet trivially, because a cell is determined by its row
together with its column; and each of them is the product of the symmetric groups of the rows,
respectively columns, of `μ`.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 7.1.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layers 0 and 2.
-/

public section

namespace TauCeti

namespace YoungTableau

variable {μ : YoungDiagram}

/-- The **row group** of a `μ`-tableau: the permutations of the labels that keep every label in
its own row of `t`. -/
@[expose] def rowSubgroup (t : YoungTableau μ) : Subgroup (Equiv.Perm (Fin μ.card)) :=
  fiberSubgroup (rowIndex t)

/-- The **column group** of a `μ`-tableau: the permutations of the labels that keep every label in
its own column of `t`. -/
@[expose] def colSubgroup (t : YoungTableau μ) : Subgroup (Equiv.Perm (Fin μ.card)) :=
  fiberSubgroup (colIndex t)

@[simp]
theorem mem_rowSubgroup {t : YoungTableau μ} {σ : Equiv.Perm (Fin μ.card)} :
    σ ∈ rowSubgroup t ↔ ∀ k, rowIndex t (σ k) = rowIndex t k :=
  mem_fiberSubgroup

@[simp]
theorem mem_colSubgroup {t : YoungTableau μ} {σ : Equiv.Perm (Fin μ.card)} :
    σ ∈ colSubgroup t ↔ ∀ k, colIndex t (σ k) = colIndex t k :=
  mem_fiberSubgroup

/-- The row and column groups of a `μ`-tableau meet only in the identity: a permutation of the
labels that stays inside the rows and inside the columns fixes every cell. -/
theorem rowSubgroup_inf_colSubgroup_eq_bot (t : YoungTableau μ) :
    rowSubgroup t ⊓ colSubgroup t = ⊥ := by
  rw [rowSubgroup, colSubgroup, fiberSubgroup_inf]
  exact fiberSubgroup_eq_bot_of_injective (rowIndex_colIndex_injective t)

/-- The row and column groups of a `μ`-tableau are disjoint subgroups of the symmetric group on
the labels. -/
theorem disjoint_rowSubgroup_colSubgroup (t : YoungTableau μ) :
    Disjoint (rowSubgroup t) (colSubgroup t) :=
  disjoint_iff.mpr (rowSubgroup_inf_colSubgroup_eq_bot t)

/-- The row group of a `μ`-tableau is the product, over the rows of `μ`, of the symmetric groups
of the rows.  Rows beyond the last one of `μ` are empty and contribute trivial factors. -/
@[expose] def rowSubgroupMulEquiv (t : YoungTableau μ) :
    rowSubgroup t ≃* ∀ i, Equiv.Perm ↥(μ.row i) :=
  (fiberSubgroupMulEquivPiPerm (rowIndex t)).trans
    (MulEquiv.piCongrRight fun i => (rowFiberEquiv t i).permCongrHom)

/-- The column group of a `μ`-tableau is the product, over the columns of `μ`, of the symmetric
groups of the columns. -/
@[expose] def colSubgroupMulEquiv (t : YoungTableau μ) :
    colSubgroup t ≃* ∀ j, Equiv.Perm ↥(μ.col j) :=
  (fiberSubgroupMulEquivPiPerm (colIndex t)).trans
    (MulEquiv.piCongrRight fun j => (colFiberEquiv t j).permCongrHom)

/-- The `i`-th component of `rowSubgroupMulEquiv t σ` moves the cell carrying the label `k` to the
cell carrying the label `σ k`. -/
@[simp]
theorem rowSubgroupMulEquiv_apply_coe (t : YoungTableau μ) (σ : rowSubgroup t) (i : ℕ)
    (k : {k : Fin μ.card // rowIndex t k = i}) :
    (rowSubgroupMulEquiv t σ i (rowFiberEquiv t i k) : ℕ × ℕ) =
      (t.symm ((σ : Equiv.Perm (Fin μ.card)) k) : ℕ × ℕ) := by
  have key : rowSubgroupMulEquiv t σ i =
      (rowFiberEquiv t i).permCongr (fiberSubgroupMulEquivPiPerm (rowIndex t) σ i) := rfl
  simp [key]

/-- The `j`-th component of `colSubgroupMulEquiv t σ` moves the cell carrying the label `k` to the
cell carrying the label `σ k`. -/
@[simp]
theorem colSubgroupMulEquiv_apply_coe (t : YoungTableau μ) (σ : colSubgroup t) (j : ℕ)
    (k : {k : Fin μ.card // colIndex t k = j}) :
    (colSubgroupMulEquiv t σ j (colFiberEquiv t j k) : ℕ × ℕ) =
      (t.symm ((σ : Equiv.Perm (Fin μ.card)) k) : ℕ × ℕ) := by
  have key : colSubgroupMulEquiv t σ j =
      (colFiberEquiv t j).permCongr (fiberSubgroupMulEquivPiPerm (colIndex t) σ j) := rfl
  simp [key]

end YoungTableau

end TauCeti
