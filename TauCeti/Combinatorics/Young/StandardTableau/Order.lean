/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.StandardTableau.Basic
public import TauCeti.Combinatorics.Young.Tableau
import Mathlib.Order.Preorder.Finite

/-!
# The labels of a standard Young tableau, ordered by their cells

A standard Young tableau increases along its rows and down its columns, so the order of two of its
labels is decided by their cells as soon as those cells share a row or a column: two labels in one
column are ordered as their rows are (`TauCeti.StandardYoungTableau.lt_iff_rowIndex_lt`), and two
labels in one row are ordered as their columns are
(`TauCeti.StandardYoungTableau.lt_iff_colIndex_lt`).

The consequence this file is written for is that **a standard Young tableau is determined by the
row of each of its labels** (`TauCeti.StandardYoungTableau.rowIndex_injective`): the labels of a row
are placed there in increasing order, so nothing is left to choose once the rows are known.  Two
standard tableaux with the same rows differ by a permutation preserving every row of the first,
which restricts to a strictly monotone self-map of that row and is therefore the identity there by
Mathlib's `StrictMono.apply_eq`.

In the language of the Specht modules, the injectivity says that distinct standard tableaux have
distinct tabloids, and that is how
`TauCeti/RepresentationTheory/Symmetric/Specht/StandardBasis.lean` uses it.

## Main results

* `TauCeti.StandardYoungTableau.lt_iff_rowIndex_lt`: labels in one column are ordered by row.
* `TauCeti.StandardYoungTableau.lt_iff_colIndex_lt`: labels in one row are ordered by column.
* `TauCeti.StandardYoungTableau.rowIndex_injective`: a standard Young tableau is determined by the
  rows of its labels.

## References

* [B. E. Sagan, *The Symmetric Group*][sagan2001], Section 2.5, where the standard tableaux are
  ordered by their tabloids.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 5, whose standard basis of the Specht module this serves.
-/

public section

namespace TauCeti

open YoungTableau

namespace StandardYoungTableau

variable {μ : YoungDiagram}

/-! ### Comparing two labels in a common row or column -/

/-- Naming a cell by the row and the column of a label recovers that label. -/
private theorem apply_eq_of_coe_eq (T : StandardYoungTableau μ) (x : Fin μ.card) {c : ↥μ.cells}
    (h : (c : ℕ × ℕ) = (rowIndex T.toTableau x, colIndex T.toTableau x)) : T c = x := by
  have hc : c = T.toTableau.symm x := Subtype.ext (by rw [h, rowIndex_def, colIndex_def])
  rw [hc]
  exact T.toTableau.apply_symm_apply x

/-- Of two labels of a standard Young tableau lying in a common column, the one in the earlier row
is the smaller. -/
theorem lt_of_rowIndex_lt (T : StandardYoungTableau μ) {x y : Fin μ.card}
    (hcol : colIndex T.toTableau x = colIndex T.toTableau y)
    (hrow : rowIndex T.toTableau x < rowIndex T.toTableau y) : x < y := by
  have hlt := T.col_strict hrow (rowIndex_colIndex_mem T.toTableau y)
  rwa [apply_eq_of_coe_eq T x (by simp [hcol]), apply_eq_of_coe_eq T y rfl] at hlt

/-- Of two labels of a standard Young tableau lying in a common row, the one in the earlier column
is the smaller. -/
theorem lt_of_colIndex_lt (T : StandardYoungTableau μ) {x y : Fin μ.card}
    (hrow : rowIndex T.toTableau x = rowIndex T.toTableau y)
    (hcol : colIndex T.toTableau x < colIndex T.toTableau y) : x < y := by
  have hlt := T.row_strict hcol (rowIndex_colIndex_mem T.toTableau y)
  rwa [apply_eq_of_coe_eq T x (by simp [hrow]), apply_eq_of_coe_eq T y rfl] at hlt

/-- **Two labels of a standard Young tableau in a common column are ordered as their rows are.** -/
theorem lt_iff_rowIndex_lt (T : StandardYoungTableau μ) {x y : Fin μ.card}
    (hcol : colIndex T.toTableau x = colIndex T.toTableau y) :
    x < y ↔ rowIndex T.toTableau x < rowIndex T.toTableau y := by
  refine ⟨fun hxy => ?_, lt_of_rowIndex_lt T hcol⟩
  rcases lt_trichotomy (rowIndex T.toTableau x) (rowIndex T.toTableau y) with hr | hr | hr
  · exact hr
  · exact absurd (rowIndex_colIndex_injective T.toTableau (Prod.ext hr hcol)) hxy.ne
  · exact absurd (lt_of_rowIndex_lt T hcol.symm hr) (asymm hxy)

/-- **Two labels of a standard Young tableau in a common row are ordered as their columns are.** -/
theorem lt_iff_colIndex_lt (T : StandardYoungTableau μ) {x y : Fin μ.card}
    (hrow : rowIndex T.toTableau x = rowIndex T.toTableau y) :
    x < y ↔ colIndex T.toTableau x < colIndex T.toTableau y := by
  refine ⟨fun hxy => ?_, lt_of_colIndex_lt T hrow⟩
  rcases lt_trichotomy (colIndex T.toTableau x) (colIndex T.toTableau y) with hc | hc | hc
  · exact hc
  · exact absurd (rowIndex_colIndex_injective T.toTableau (Prod.ext hrow hc)) hxy.ne
  · exact absurd (lt_of_colIndex_lt T hrow.symm hc) (asymm hxy)

end StandardYoungTableau

/-! ### A standard Young tableau is determined by the rows of its labels -/

/-- **A standard Young tableau is determined by the rows of its labels.** -/
theorem StandardYoungTableau.rowIndex_injective (μ : YoungDiagram) :
    Function.Injective fun T : StandardYoungTableau μ => rowIndex T.toTableau := by
  classical
  intro T U h
  have hrow' : rowIndex T.toTableau = rowIndex U.toTableau := h
  obtain ⟨σ, hrel⟩ := exists_relabel_eq T.toTableau U.toTableau
  -- `σ` carries `T` to `U`, so the row and the column that `U` gives to `σ k` are those that `T`
  -- gives to `k`
  have hrowU : ∀ k, rowIndex U.toTableau (σ k) = rowIndex T.toTableau k := by
    intro k
    rw [← hrel, rowIndex_relabel]
    simp
  have hcolU : ∀ k, colIndex U.toTableau (σ k) = colIndex T.toTableau k := by
    intro k
    rw [← hrel, colIndex_relabel]
    simp
  have hrow : ∀ k, rowIndex T.toTableau (σ k) = rowIndex T.toTableau k := fun k => by
    rw [congrFun hrow' (σ k), hrowU k]
  -- on each row of `T` the permutation `σ` is increasing, so it is the identity there
  have hσ : σ = 1 := by
    refine Equiv.ext fun x => ?_
    -- `σ` preserves the row of `x`, so it restricts to a permutation of that row
    have hs : ∀ y, rowIndex T.toTableau (σ y) = rowIndex T.toTableau x ↔
        rowIndex T.toTableau y = rowIndex T.toTableau x := fun y => by rw [hrow y]
    have hmono : StrictMono (σ.subtypePerm hs :
        Equiv.Perm {y // rowIndex T.toTableau y = rowIndex T.toTableau x}) := by
      rintro ⟨y, hy⟩ ⟨y', hy'⟩ hlt
      rw [Equiv.Perm.subtypePerm_apply, Equiv.Perm.subtypePerm_apply, Subtype.mk_lt_mk,
        StandardYoungTableau.lt_iff_colIndex_lt U (by rw [hrowU y, hrowU y', hy, hy']),
        hcolU y, hcolU y', ← StandardYoungTableau.lt_iff_colIndex_lt T (hy.trans hy'.symm)]
      exact hlt
    have hfix : σ x = x := by
      simpa using congrArg Subtype.val (StrictMono.apply_eq (x := ⟨x, rfl⟩) hmono)
    simpa using hfix
  have htu : T.toTableau = U.toTableau := by rw [← hrel, hσ, relabel_one]
  exact StandardYoungTableau.ext fun c => by
    rw [← StandardYoungTableau.toTableau_apply, ← StandardYoungTableau.toTableau_apply, htu]

end TauCeti
