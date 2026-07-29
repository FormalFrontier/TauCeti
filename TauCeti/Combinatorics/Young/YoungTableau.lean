/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.Young.YoungDiagram

/-!
# Young tableaux

A `μ`-tableau is a bijective filling `t : ↥μ.cells ≃ Fin μ.card` of the cells of a Young diagram
`μ` by the labels `Fin μ.card`.  This file defines `YoungTableau`, the row and the column of a
label, and identifies the labels lying in a given row, respectively column, with the cells of that
row, respectively column, of `μ`.

Note that `YoungTableau μ` is an abbreviation, so that the whole `Equiv` API applies to a tableau
directly.  As a consequence dot notation on a tableau resolves in the `Equiv` namespace, and the
declarations below are to be spelled out, as in `YoungTableau.rowIndex t`.

A `μ`-tableau is required to be neither row- nor column-increasing.  The strictly row- and
column-increasing ones are `TauCeti.StandardYoungTableau`, whose `toEquiv` field is a `μ`-tableau
in the present sense; Mathlib's `SemistandardYoungTableau` is a different notion again, a filling
of `μ` by natural numbers that is weakly increasing along each row and strictly increasing down
each column (represented as a function `ℕ → ℕ → ℕ` vanishing outside `μ`), with no bijectivity
requirement.  The three notions are kept distinct.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 7.1.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 0.
-/

public section

namespace TauCeti

/-- A `μ`-tableau: a bijective filling of the cells of the Young diagram `μ` by the labels
`Fin μ.card`. -/
abbrev YoungTableau (μ : YoungDiagram) : Type := ↥μ.cells ≃ Fin μ.card

namespace YoungTableau

variable {μ : YoungDiagram}

/-- The row of the cell of `μ` carrying the label `k` in the tableau `t`. -/
@[expose] def rowIndex (t : YoungTableau μ) (k : Fin μ.card) : ℕ := (t.symm k : ℕ × ℕ).1

/-- The column of the cell of `μ` carrying the label `k` in the tableau `t`. -/
@[expose] def colIndex (t : YoungTableau μ) (k : Fin μ.card) : ℕ := (t.symm k : ℕ × ℕ).2

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

/-- The labels lying in row `i` of a `μ`-tableau are the cells of the `i`-th row of `μ`. -/
@[expose] def rowFiberEquiv (t : YoungTableau μ) (i : ℕ) :
    {k : Fin μ.card // rowIndex t k = i} ≃ ↥(μ.row i) :=
  (Equiv.subtypeEquiv t.symm fun _ => Iff.rfl).trans <|
    (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ μ.cells) fun c => c.1 = i).trans <|
      Equiv.subtypeEquivRight fun _ => by
        rw [YoungDiagram.mem_row_iff, YoungDiagram.mem_cells]

/-- The labels lying in column `j` of a `μ`-tableau are the cells of the `j`-th column of `μ`. -/
@[expose] def colFiberEquiv (t : YoungTableau μ) (j : ℕ) :
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

end YoungTableau

end TauCeti
