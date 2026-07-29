/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.Young.YoungDiagram
public import TauCeti.GroupTheory.Perm.FiberSubgroup

/-!
# Young tableaux and their row and column groups

A `μ`-tableau is a bijective filling `t : ↥μ.cells ≃ Fin μ.card` of the cells of a Young diagram
`μ` by the labels `Fin μ.card`.  It is the datum a Young symmetrizer is built from: the row
symmetrizer sums over the permutations of the labels that stay inside their row of `t`, and the
column antisymmetrizer sums with signs over those that stay inside their column.

This file defines `YoungTableau`, the row and column of a label, and the two subgroups
`YoungTableau.rowSubgroup t` and `YoungTableau.colSubgroup t` of `Equiv.Perm (Fin μ.card)`.  It
proves the two facts the symmetrizer theory rests on: the row and column groups meet trivially,
because a cell is determined by its row together with its column; and each of them is the product
of the symmetric groups of the rows, respectively columns, of `μ`.

Note that `YoungTableau μ` is an abbreviation, so that the whole `Equiv` API applies to a tableau
directly.  As a consequence dot notation on a tableau resolves in the `Equiv` namespace, and the
declarations below are to be spelled out, as in `YoungTableau.rowSubgroup t`.

A `μ`-tableau is required to be neither row- nor column-increasing; the increasing ones are
`TauCeti.StandardYoungTableau`, whose `toEquiv` field is a `μ`-tableau in the present sense, and
the weakly row-increasing fillings with arbitrary entries are Mathlib's
`SemistandardYoungTableau`.  The three notions are kept distinct.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 7.1.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layers 0 and 2.
-/

@[expose] public section

namespace TauCeti

/-- A `μ`-tableau: a bijective filling of the cells of the Young diagram `μ` by the labels
`Fin μ.card`. -/
abbrev YoungTableau (μ : YoungDiagram) : Type := ↥μ.cells ≃ Fin μ.card

namespace YoungTableau

variable {μ : YoungDiagram}

/-- The row of the cell of `μ` carrying the label `k` in the tableau `t`. -/
def rowIndex (t : YoungTableau μ) (k : Fin μ.card) : ℕ := (t.symm k : ℕ × ℕ).1

/-- The column of the cell of `μ` carrying the label `k` in the tableau `t`. -/
def colIndex (t : YoungTableau μ) (k : Fin μ.card) : ℕ := (t.symm k : ℕ × ℕ).2

@[simp]
theorem rowIndex_apply (t : YoungTableau μ) (c : ↥μ.cells) :
    rowIndex t (t c) = (c : ℕ × ℕ).1 := by
  simp [rowIndex]

@[simp]
theorem colIndex_apply (t : YoungTableau μ) (c : ↥μ.cells) :
    colIndex t (t c) = (c : ℕ × ℕ).2 := by
  simp [colIndex]

/-- A cell of a Young diagram is determined by its row together with its column, so a label of a
tableau is determined by its row and its column. -/
theorem rowIndex_colIndex_injective (t : YoungTableau μ) :
    Function.Injective fun k => (rowIndex t k, colIndex t k) := by
  intro k l h
  simp only [rowIndex, colIndex, Prod.mk.injEq] at h
  exact t.symm.injective (Subtype.ext (Prod.ext h.1 h.2))

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
  Iff.rfl

@[simp]
theorem mem_colSubgroup {t : YoungTableau μ} {σ : Equiv.Perm (Fin μ.card)} :
    σ ∈ colSubgroup t ↔ ∀ k, colIndex t (σ k) = colIndex t k :=
  Iff.rfl

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

/-- The labels lying in row `i` of a `μ`-tableau are the cells of the `i`-th row of `μ`. -/
def rowFiberEquiv (t : YoungTableau μ) (i : ℕ) :
    {k : Fin μ.card // rowIndex t k = i} ≃ ↥(μ.row i) :=
  (Equiv.subtypeEquiv t.symm fun _ => Iff.rfl).trans <|
    (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ μ.cells) fun c => c.1 = i).trans <|
      Equiv.subtypeEquivRight fun _ => by
        rw [YoungDiagram.mem_row_iff, YoungDiagram.mem_cells]

/-- The labels lying in column `j` of a `μ`-tableau are the cells of the `j`-th column of `μ`. -/
def colFiberEquiv (t : YoungTableau μ) (j : ℕ) :
    {k : Fin μ.card // colIndex t k = j} ≃ ↥(μ.col j) :=
  (Equiv.subtypeEquiv t.symm fun _ => Iff.rfl).trans <|
    (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ μ.cells) fun c => c.2 = j).trans <|
      Equiv.subtypeEquivRight fun _ => by
        rw [YoungDiagram.mem_col_iff, YoungDiagram.mem_cells]

@[simp]
theorem rowFiberEquiv_apply_coe (t : YoungTableau μ) (i : ℕ)
    (k : {k : Fin μ.card // rowIndex t k = i}) :
    (rowFiberEquiv t i k : ℕ × ℕ) = (t.symm k.1 : ℕ × ℕ) :=
  rfl

@[simp]
theorem colFiberEquiv_apply_coe (t : YoungTableau μ) (j : ℕ)
    (k : {k : Fin μ.card // colIndex t k = j}) :
    (colFiberEquiv t j k : ℕ × ℕ) = (t.symm k.1 : ℕ × ℕ) :=
  rfl

/-- The row group of a `μ`-tableau is the product, over the rows of `μ`, of the symmetric groups
of the rows.  Rows beyond the last one of `μ` are empty and contribute trivial factors. -/
def rowSubgroupMulEquiv (t : YoungTableau μ) :
    rowSubgroup t ≃* ∀ i, Equiv.Perm ↥(μ.row i) :=
  (fiberSubgroupMulEquivPiPerm (rowIndex t)).trans
    (MulEquiv.piCongrRight fun i => (rowFiberEquiv t i).permCongrHom)

/-- The column group of a `μ`-tableau is the product, over the columns of `μ`, of the symmetric
groups of the columns. -/
def colSubgroupMulEquiv (t : YoungTableau μ) :
    colSubgroup t ≃* ∀ j, Equiv.Perm ↥(μ.col j) :=
  (fiberSubgroupMulEquivPiPerm (colIndex t)).trans
    (MulEquiv.piCongrRight fun j => (colFiberEquiv t j).permCongrHom)

end YoungTableau

end TauCeti
