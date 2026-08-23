/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Map
public import TauCeti.Combinatorics.Young.Tableau
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
respectively columns, of `μ`.  It also records the transpositions that the two groups contain:
swapping two labels of a common row lies in the row group, and swapping two labels of a common
column lies in the column group.  Finally it recognises the two extreme shapes: the row group is
everything exactly when the diagram has at most one row, the column group is everything exactly
when it has at most one column, and either of those forces the other group to be trivial.

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
def rowSubgroup (t : YoungTableau μ) : Subgroup (Equiv.Perm (Fin μ.card)) :=
  fiberSubgroup (rowIndex t)

/-- The **column group** of a `μ`-tableau: the permutations of the labels that keep every label in
its own column of `t`. -/
def colSubgroup (t : YoungTableau μ) : Subgroup (Equiv.Perm (Fin μ.card)) :=
  fiberSubgroup (colIndex t)

@[simp]
theorem mem_rowSubgroup {t : YoungTableau μ} {σ : Equiv.Perm (Fin μ.card)} :
    σ ∈ rowSubgroup t ↔ ∀ k, rowIndex t (σ k) = rowIndex t k :=
  mem_fiberSubgroup

@[simp]
theorem mem_colSubgroup {t : YoungTableau μ} {σ : Equiv.Perm (Fin μ.card)} :
    σ ∈ colSubgroup t ↔ ∀ k, colIndex t (σ k) = colIndex t k :=
  mem_fiberSubgroup

/-- The row group of `t` is the group of permutations preserving the fibers of `rowIndex t`. -/
theorem rowSubgroup_def (t : YoungTableau μ) :
    rowSubgroup t = fiberSubgroup (rowIndex t) := by
  ext σ
  rw [mem_rowSubgroup, mem_fiberSubgroup]

/-- The column group of `t` is the group of permutations preserving the fibers of `colIndex t`. -/
theorem colSubgroup_def (t : YoungTableau μ) :
    colSubgroup t = fiberSubgroup (colIndex t) := by
  ext σ
  rw [mem_colSubgroup, mem_fiberSubgroup]

/-- The transposition of two labels lying in a common row of `t` belongs to the row group. -/
theorem swap_mem_rowSubgroup {t : YoungTableau μ} {x y : Fin μ.card}
    (h : rowIndex t x = rowIndex t y) : Equiv.swap x y ∈ rowSubgroup t := by
  rw [rowSubgroup_def]
  exact swap_mem_fiberSubgroup h

/-- The transposition of two labels lying in a common column of `t` belongs to the column
group. -/
theorem swap_mem_colSubgroup {t : YoungTableau μ} {x y : Fin μ.card}
    (h : colIndex t x = colIndex t y) : Equiv.swap x y ∈ colSubgroup t := by
  rw [colSubgroup_def]
  exact swap_mem_fiberSubgroup h

/-- The row and column groups of a `μ`-tableau meet only in the identity: a permutation of the
labels that stays inside the rows and inside the columns fixes every cell. -/
theorem rowSubgroup_inf_colSubgroup_eq_bot (t : YoungTableau μ) :
    rowSubgroup t ⊓ colSubgroup t = ⊥ := by
  rw [rowSubgroup_def, colSubgroup_def, fiberSubgroup_inf]
  exact fiberSubgroup_eq_bot_of_injective (rowIndex_colIndex_injective t)

/-- The row and column groups of a `μ`-tableau are disjoint subgroups of the symmetric group on
the labels. -/
theorem disjoint_rowSubgroup_colSubgroup (t : YoungTableau μ) :
    Disjoint (rowSubgroup t) (colSubgroup t) :=
  disjoint_iff.mpr (rowSubgroup_inf_colSubgroup_eq_bot t)

/-- The row group of a `μ`-tableau is the product, over the rows of `μ`, of the symmetric groups
of the rows.  Rows beyond the last one of `μ` are empty and contribute trivial factors. -/
def rowSubgroupMulEquiv (t : YoungTableau μ) :
    rowSubgroup t ≃* ∀ i, Equiv.Perm ↥(μ.row i) :=
  (MulEquiv.subgroupCongr (rowSubgroup_def t)).trans <|
    (fiberSubgroupMulEquivPiPerm (rowIndex t)).trans
      (MulEquiv.piCongrRight fun i => (rowFiberEquiv t i).permCongrHom)

/-- The column group of a `μ`-tableau is the product, over the columns of `μ`, of the symmetric
groups of the columns. -/
def colSubgroupMulEquiv (t : YoungTableau μ) :
    colSubgroup t ≃* ∀ j, Equiv.Perm ↥(μ.col j) :=
  (MulEquiv.subgroupCongr (colSubgroup_def t)).trans <|
    (fiberSubgroupMulEquivPiPerm (colIndex t)).trans
      (MulEquiv.piCongrRight fun j => (colFiberEquiv t j).permCongrHom)

/-- The `i`-th component of `rowSubgroupMulEquiv t σ` moves the cell carrying the label `k` to the
cell carrying the label `σ k`. -/
@[simp]
theorem rowSubgroupMulEquiv_apply_coe (t : YoungTableau μ) (σ : rowSubgroup t) (i : ℕ)
    (k : {k : Fin μ.card // rowIndex t k = i}) :
    (rowSubgroupMulEquiv t σ i (rowFiberEquiv t i k) : ℕ × ℕ) =
      (t.symm ((σ : Equiv.Perm (Fin μ.card)) k) : ℕ × ℕ) := by
  rw [rowSubgroupMulEquiv, MulEquiv.trans_apply,
    fiberSubgroupMulEquivPiPerm_trans_piCongrRight_apply, rowFiberEquiv_apply_coe]
  simp only [MulEquiv.subgroupCongr_apply]

/-- The `j`-th component of `colSubgroupMulEquiv t σ` moves the cell carrying the label `k` to the
cell carrying the label `σ k`. -/
@[simp]
theorem colSubgroupMulEquiv_apply_coe (t : YoungTableau μ) (σ : colSubgroup t) (j : ℕ)
    (k : {k : Fin μ.card // colIndex t k = j}) :
    (colSubgroupMulEquiv t σ j (colFiberEquiv t j k) : ℕ × ℕ) =
      (t.symm ((σ : Equiv.Perm (Fin μ.card)) k) : ℕ × ℕ) := by
  rw [colSubgroupMulEquiv, MulEquiv.trans_apply,
    fiberSubgroupMulEquivPiPerm_trans_piCongrRight_apply, colFiberEquiv_apply_coe]
  simp only [MulEquiv.subgroupCongr_apply]

/-- The permutation of the labels assembled from a family of permutations of the rows of `μ` moves
each label by the permutation of its own row. -/
@[simp]
theorem rowSubgroupMulEquiv_symm_apply (t : YoungTableau μ) (σ : ∀ i, Equiv.Perm ↥(μ.row i))
    (k : Fin μ.card) :
    (((rowSubgroupMulEquiv t).symm σ : Equiv.Perm (Fin μ.card)) k : Fin μ.card) =
      ((rowFiberEquiv t (rowIndex t k)).symm
        (σ (rowIndex t k) (rowFiberEquiv t (rowIndex t k) ⟨k, rfl⟩)) : Fin μ.card) := by
  rw [rowSubgroupMulEquiv, MulEquiv.symm_trans_apply, MulEquiv.subgroupCongr_symm_apply,
    fiberSubgroupMulEquivPiPerm_trans_piCongrRight_symm_apply]

/-- The permutation of the labels assembled from a family of permutations of the columns of `μ`
moves each label by the permutation of its own column. -/
@[simp]
theorem colSubgroupMulEquiv_symm_apply (t : YoungTableau μ) (σ : ∀ j, Equiv.Perm ↥(μ.col j))
    (k : Fin μ.card) :
    (((colSubgroupMulEquiv t).symm σ : Equiv.Perm (Fin μ.card)) k : Fin μ.card) =
      ((colFiberEquiv t (colIndex t k)).symm
        (σ (colIndex t k) (colFiberEquiv t (colIndex t k) ⟨k, rfl⟩)) : Fin μ.card) := by
  rw [colSubgroupMulEquiv, MulEquiv.symm_trans_apply, MulEquiv.subgroupCongr_symm_apply,
    fiberSubgroupMulEquivPiPerm_trans_piCongrRight_symm_apply]

/-! ### The extreme shapes -/

/-- A diagram whose zeroth column has at most one cell has only one row, so every label of a
tableau on it lies in row `0`. -/
theorem rowIndex_eq_zero_of_colLen_le_one (t : YoungTableau μ) (h : μ.colLen 0 ≤ 1)
    (k : Fin μ.card) : rowIndex t k = 0 := by
  have hmem : (t.symm k : ℕ × ℕ) ∈ μ := (YoungDiagram.mem_cells _).mp (t.symm k).2
  have hlt : (t.symm k : ℕ × ℕ).1 < μ.colLen (t.symm k : ℕ × ℕ).2 :=
    YoungDiagram.mem_iff_lt_colLen.mp hmem
  have hle : μ.colLen (t.symm k : ℕ × ℕ).2 ≤ μ.colLen 0 := μ.colLen_anti 0 _ (Nat.zero_le _)
  rw [rowIndex_def]
  omega

/-- A diagram whose zeroth row has at most one cell has only one column, so every label of a
tableau on it lies in column `0`. -/
theorem colIndex_eq_zero_of_rowLen_le_one (t : YoungTableau μ) (h : μ.rowLen 0 ≤ 1)
    (k : Fin μ.card) : colIndex t k = 0 := by
  have hmem : (t.symm k : ℕ × ℕ) ∈ μ := (YoungDiagram.mem_cells _).mp (t.symm k).2
  have hlt : (t.symm k : ℕ × ℕ).2 < μ.rowLen (t.symm k : ℕ × ℕ).1 :=
    YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have hle : μ.rowLen (t.symm k : ℕ × ℕ).1 ≤ μ.rowLen 0 := μ.rowLen_anti 0 _ (Nat.zero_le _)
  rw [colIndex_def]
  omega

/-- The row group of a tableau is everything exactly when its shape has at most one row: with a
single row every permutation of the labels preserves it, while two rows are separated by a
transposition. -/
@[simp]
theorem rowSubgroup_eq_top_iff (t : YoungTableau μ) : rowSubgroup t = ⊤ ↔ μ.colLen 0 ≤ 1 := by
  refine ⟨fun h => ?_, fun h => by ext σ; simp [rowIndex_eq_zero_of_colLen_le_one t h]⟩
  by_contra hc
  obtain ⟨k, hk⟩ : ∃ k : Fin μ.card, rowIndex t k = 0 :=
    ⟨t ⟨(0, 0), (YoungDiagram.mem_cells _).mpr
      (YoungDiagram.mem_iff_lt_colLen.mpr (by omega))⟩, rowIndex_apply t _⟩
  obtain ⟨l, hl⟩ : ∃ l : Fin μ.card, rowIndex t l = 1 :=
    ⟨t ⟨(1, 0), (YoungDiagram.mem_cells _).mpr
      (YoungDiagram.mem_iff_lt_colLen.mpr (by omega))⟩, rowIndex_apply t _⟩
  have hswap := mem_rowSubgroup.mp (by rw [h]; exact Subgroup.mem_top (Equiv.swap k l)) k
  rw [Equiv.swap_apply_left, hk, hl] at hswap
  omega

/-- The column group of a tableau is everything exactly when its shape has at most one column:
with a single column every permutation of the labels preserves it, while two columns are
separated by a transposition. -/
@[simp]
theorem colSubgroup_eq_top_iff (t : YoungTableau μ) : colSubgroup t = ⊤ ↔ μ.rowLen 0 ≤ 1 := by
  refine ⟨fun h => ?_, fun h => by ext σ; simp [colIndex_eq_zero_of_rowLen_le_one t h]⟩
  by_contra hc
  obtain ⟨k, hk⟩ : ∃ k : Fin μ.card, colIndex t k = 0 :=
    ⟨t ⟨(0, 0), (YoungDiagram.mem_cells _).mpr
      (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))⟩, colIndex_apply t _⟩
  obtain ⟨l, hl⟩ : ∃ l : Fin μ.card, colIndex t l = 1 :=
    ⟨t ⟨(0, 1), (YoungDiagram.mem_cells _).mpr
      (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))⟩, colIndex_apply t _⟩
  have hswap := mem_colSubgroup.mp (by rw [h]; exact Subgroup.mem_top (Equiv.swap k l)) k
  rw [Equiv.swap_apply_left, hk, hl] at hswap
  omega

/-- The row and column groups meet trivially, so a full row group forces a trivial column
group. -/
theorem colSubgroup_eq_bot_of_rowSubgroup_eq_top (t : YoungTableau μ) (h : rowSubgroup t = ⊤) :
    colSubgroup t = ⊥ := by
  have hinf := rowSubgroup_inf_colSubgroup_eq_bot t
  rwa [h, top_inf_eq] at hinf

/-- The row and column groups meet trivially, so a full column group forces a trivial row
group. -/
theorem rowSubgroup_eq_bot_of_colSubgroup_eq_top (t : YoungTableau μ) (h : colSubgroup t = ⊤) :
    rowSubgroup t = ⊥ := by
  have hinf := rowSubgroup_inf_colSubgroup_eq_bot t
  rwa [h, inf_top_eq] at hinf

end YoungTableau

end TauCeti
