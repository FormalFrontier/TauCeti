/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.Young.HookLength
public import TauCeti.Combinatorics.Young.StandardTableau.Basic

/-!
# Reading tableaux and the shapes with a unique standard Young tableau

Numbering the cells of a Young diagram `μ` in *reading order* -- left to right along the first
row, then left to right along the second, and so on -- labels the cell `(i, j)` by
`TauCeti.YoungDiagram.readingIndex μ (i, j) = μ.rowLen 0 + ⋯ + μ.rowLen (i - 1) + j`.  Reading
order increases along rows and down columns, so this labelling is a standard Young tableau
`TauCeti.StandardYoungTableau.rowReading μ`; in particular `TauCeti.standardCount μ`, the number
`f^μ` of standard Young tableaux, is never zero.

Numbering the cells column by column instead gives a second standard Young tableau
`TauCeti.StandardYoungTableau.colReading μ`, the transpose of the row-reading tableau of the
transposed diagram.  The two disagree as soon as `μ` has a cell outside its first row *and* a cell
outside its first column, while a diagram that is a single row or a single column has only one
standard Young tableau at all.  So `f^μ = 1` holds exactly for the single rows and the single
columns.

Those are also exactly the shapes whose hook lengths are already known to multiply to `μ.card !`,
by `TauCeti.YoungDiagram.prod_hookLength_eq_factorial_of_colLen_le_one` and its transpose, so the
multiplicative hook-length formula `f^μ · ∏_{c ∈ μ} hookLength μ c = μ.card !` follows for them.

## Main definitions

* `TauCeti.YoungDiagram.readingIndex`: the position of a cell in reading order.
* `TauCeti.StandardYoungTableau.rowReading`: the tableau numbering the cells row by row.
* `TauCeti.StandardYoungTableau.colReading`: the tableau numbering the cells column by column.

## Main results

* `TauCeti.standardCount_pos`: every Young diagram has a standard Young tableau.
* `TauCeti.standardCount_eq_one_iff`: a Young diagram has exactly one standard Young tableau
  precisely when it is a single row or a single column.
* `TauCeti.standardCount_mul_prod_hookLength_of_colLen_le_one` and
  `TauCeti.standardCount_mul_prod_hookLength_of_rowLen_le_one`: the multiplicative hook-length
  formula for a single row and for a single column.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 1.1.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layers 0 and 5.
-/

@[expose] public section

open scoped Nat

namespace TauCeti

namespace YoungDiagram

variable {μ : YoungDiagram}

/-- The position of the cell `c` in reading order: the number of cells of `μ` lying in earlier
rows, plus the column index of `c`. -/
def readingIndex (μ : YoungDiagram) (c : ℕ × ℕ) : ℕ :=
  (∑ i ∈ Finset.range c.1, μ.rowLen i) + c.2

/-- The reading index of a cell is the sum of the lengths of the rows above it, plus its column
index. -/
theorem readingIndex_def (μ : YoungDiagram) (c : ℕ × ℕ) :
    readingIndex μ c = (∑ i ∈ Finset.range c.1, μ.rowLen i) + c.2 :=
  rfl

/-- A cell of the first row has its column index as its reading index. -/
@[simp]
theorem readingIndex_zero (μ : YoungDiagram) (j : ℕ) : readingIndex μ (0, j) = j := by
  simp [readingIndex]

/-- The first cell of the second row is numbered by the length of the first row. -/
theorem readingIndex_one_zero (μ : YoungDiagram) : readingIndex μ (1, 0) = μ.rowLen 0 := by
  simp [readingIndex]

/-- The first `k` row lengths count the cells in the first `k` rows, so the reading index of a
cell of `μ` is smaller than the number of cells of `μ`. -/
theorem readingIndex_lt_card {c : ℕ × ℕ} (hc : c ∈ μ) : readingIndex μ c < μ.card := by
  have hsucc : ∑ i ∈ Finset.range (c.1 + 1), μ.rowLen i ≤ μ.card := by
    rw [sum_range_rowLen_eq_card_filter_fst]
    exact Finset.card_filter_le _ _
  rw [Finset.sum_range_succ] at hsucc
  have hrow := _root_.YoungDiagram.mem_iff_lt_rowLen.mp hc
  rw [readingIndex]
  omega

/-- Reading order runs down the rows: a cell in an earlier row has the smaller reading index. -/
theorem readingIndex_lt_readingIndex_of_fst_lt {c d : ℕ × ℕ} (hc : c ∈ μ) (h : c.1 < d.1) :
    readingIndex μ c < readingIndex μ d := by
  have hsub : Finset.range (c.1 + 1) ⊆ Finset.range d.1 := by
    rw [Finset.range_subset_range]
    omega
  have hmono : ∑ i ∈ Finset.range (c.1 + 1), μ.rowLen i ≤ ∑ i ∈ Finset.range d.1, μ.rowLen i :=
    Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_range_succ] at hmono
  have hrow := _root_.YoungDiagram.mem_iff_lt_rowLen.mp hc
  rw [readingIndex, readingIndex]
  omega

/-- Reading order runs along each row: within a row, a cell in an earlier column has the smaller
reading index. -/
theorem readingIndex_lt_readingIndex_of_snd_lt {c d : ℕ × ℕ} (hrow : c.1 = d.1) (h : c.2 < d.2) :
    readingIndex μ c < readingIndex μ d := by
  rw [readingIndex, readingIndex, hrow]
  omega

/-- Distinct cells of `μ` have distinct reading indices. -/
theorem eq_of_readingIndex_eq {c d : ℕ × ℕ} (hc : c ∈ μ) (hd : d ∈ μ)
    (h : readingIndex μ c = readingIndex μ d) : c = d := by
  rcases lt_trichotomy c.1 d.1 with hfst | hfst | hfst
  · exact absurd h (readingIndex_lt_readingIndex_of_fst_lt hc hfst).ne
  · rcases lt_trichotomy c.2 d.2 with hsnd | hsnd | hsnd
    · exact absurd h (readingIndex_lt_readingIndex_of_snd_lt hfst hsnd).ne
    · exact Prod.ext hfst hsnd
    · exact absurd h (readingIndex_lt_readingIndex_of_snd_lt hfst.symm hsnd).ne'
  · exact absurd h (readingIndex_lt_readingIndex_of_fst_lt hd hfst).ne'

end YoungDiagram

namespace StandardYoungTableau

variable {μ : YoungDiagram}

/-- The **row-reading tableau** of `μ`: the standard Young tableau numbering the cells of `μ` in
reading order, left to right along the first row, then left to right along the second, and so
on. -/
noncomputable def rowReading (μ : YoungDiagram) : StandardYoungTableau μ where
  toEquiv :=
    Equiv.ofBijective
      (fun c => ⟨YoungDiagram.readingIndex μ c.1, YoungDiagram.readingIndex_lt_card c.2⟩)
      ((Fintype.bijective_iff_injective_and_card _).mpr
        ⟨fun c d hcd =>
          Subtype.ext (YoungDiagram.eq_of_readingIndex_eq c.2 d.2 (congrArg Fin.val hcd)),
          by simp⟩)
  row_strict' := fun {i j₁ j₂} h _ =>
    Fin.lt_def.mpr (YoungDiagram.readingIndex_lt_readingIndex_of_snd_lt
      (μ := μ) (c := (i, j₁)) (d := (i, j₂)) rfl h)
  col_strict' := fun {i₁ i₂ j} h hcell =>
    Fin.lt_def.mpr (YoungDiagram.readingIndex_lt_readingIndex_of_fst_lt
      (c := (i₁, j)) (d := (i₂, j)) (μ.up_left_mem h.le (le_refl j) hcell) h)

/-- The row-reading tableau labels a cell by its reading index. -/
@[simp]
theorem rowReading_apply_val (μ : YoungDiagram) (c : ↥μ.cells) :
    (rowReading μ c).val = YoungDiagram.readingIndex μ c.1 :=
  rfl

/-- The **column-reading tableau** of `μ`: the standard Young tableau numbering the cells of `μ`
top to bottom down the first column, then top to bottom down the second, and so on.  It is the
transpose of the row-reading tableau of the transposed diagram. -/
noncomputable def colReading (μ : YoungDiagram) : StandardYoungTableau μ :=
  (transposeEquiv μ).symm (rowReading μ.transpose)

/-- The column-reading tableau labels a cell by the reading index of the transposed cell in the
transposed diagram. -/
@[simp]
theorem colReading_apply_val (μ : YoungDiagram) (c : ↥μ.cells) :
    (colReading μ c).val = YoungDiagram.readingIndex μ.transpose c.1.swap := by
  rw [colReading, transposeEquiv_symm_apply_val, rowReading_apply_val]

/-- Every Young diagram carries a standard Young tableau. -/
instance instNonempty (μ : YoungDiagram) : Nonempty (StandardYoungTableau μ) :=
  ⟨rowReading μ⟩

/-! ### Diagrams with a unique standard Young tableau -/

/-- A diagram with at most one row has all of its cells in that row. -/
private theorem fst_eq_zero_of_colLen_le_one (h : μ.colLen 0 ≤ 1) {c : ℕ × ℕ} (hc : c ∈ μ) :
    c.1 = 0 := by
  have h₀ : (c.1, 0) ∈ μ := μ.up_left_mem (le_refl _) (Nat.zero_le _) hc
  have := _root_.YoungDiagram.mem_iff_lt_colLen.mp h₀
  omega

/-- A diagram with at most one row admits only the row-reading tableau: a standard Young tableau
on a single row labels the cells in increasing order of column index. -/
theorem eq_rowReading_of_colLen_le_one (h : μ.colLen 0 ≤ 1) (T : StandardYoungTableau μ) :
    T = rowReading μ := by
  have hcard : μ.card = μ.rowLen 0 := YoungDiagram.card_eq_rowLen_of_colLen_le_one h
  have hmem : ∀ k : Fin μ.card, ((0, (k : ℕ)) : ℕ × ℕ) ∈ μ := fun k =>
    _root_.YoungDiagram.mem_iff_lt_rowLen.mpr (hcard ▸ k.isLt)
  have hid : (fun k : Fin μ.card => T ⟨(0, (k : ℕ)), hmem k⟩) = id :=
    StrictMono.eq_id fun k l hkl => T.row_strict (Fin.lt_def.mp hkl) (hmem l)
  refine ext fun c => ?_
  obtain ⟨⟨i, j⟩, hij⟩ := c
  have hmemij : ((i, j) : ℕ × ℕ) ∈ μ := hij
  have hi : i = 0 := fst_eq_zero_of_colLen_le_one h hmemij
  subst hi
  have hlt : j < μ.card := hcard ▸ _root_.YoungDiagram.mem_iff_lt_rowLen.mp hmemij
  refine Fin.ext ?_
  rw [rowReading_apply_val, YoungDiagram.readingIndex_zero]
  exact congrArg Fin.val (congrFun hid ⟨j, hlt⟩)

/-- A diagram with at most one row has at most one standard Young tableau. -/
theorem subsingleton_of_colLen_le_one (h : μ.colLen 0 ≤ 1) :
    Subsingleton (StandardYoungTableau μ) :=
  ⟨fun T U =>
    (eq_rowReading_of_colLen_le_one h T).trans (eq_rowReading_of_colLen_le_one h U).symm⟩

/-- A diagram with at most one column has at most one standard Young tableau. -/
theorem subsingleton_of_rowLen_le_one (h : μ.rowLen 0 ≤ 1) :
    Subsingleton (StandardYoungTableau μ) :=
  (transposeEquiv μ).subsingleton_congr.mpr (subsingleton_of_colLen_le_one (by simpa using h))

/-- If `μ` has a cell outside its first row and a cell outside its first column, then the
row-reading and the column-reading tableaux differ: reading by rows labels the cell `(0, 1)` by
`1`, while reading by columns labels it by the length of the first column. -/
theorem rowReading_ne_colReading (hrow : 1 < μ.rowLen 0) (hcol : 1 < μ.colLen 0) :
    rowReading μ ≠ colReading μ := by
  have hmem : ((0, 1) : ℕ × ℕ) ∈ μ := _root_.YoungDiagram.mem_iff_lt_rowLen.mpr hrow
  intro heq
  have hval := congrArg Fin.val (DFunLike.congr_fun heq ⟨(0, 1), hmem⟩)
  rw [rowReading_apply_val, colReading_apply_val, YoungDiagram.readingIndex_zero,
    Prod.swap_prod_mk, YoungDiagram.readingIndex_one_zero,
    _root_.YoungDiagram.rowLen_transpose] at hval
  omega

end StandardYoungTableau

/-! ### Counting standard Young tableaux of extreme shapes -/

/-- **Every Young diagram has a standard Young tableau**, namely the row-reading one. -/
theorem standardCount_pos (μ : YoungDiagram) : 0 < standardCount μ := by
  rw [standardCount_def]
  exact Fintype.card_pos

/-- The number of standard Young tableaux of a given shape is never zero. -/
theorem standardCount_ne_zero (μ : YoungDiagram) : standardCount μ ≠ 0 :=
  (standardCount_pos μ).ne'

/-- A Young diagram with at most one row has exactly one standard Young tableau. -/
theorem standardCount_eq_one_of_colLen_le_one {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1) :
    standardCount μ = 1 := by
  haveI := StandardYoungTableau.subsingleton_of_colLen_le_one h
  rw [standardCount_def]
  exact Fintype.card_eq_one_iff.mpr
    ⟨StandardYoungTableau.rowReading μ, fun T => Subsingleton.elim _ _⟩

/-- A Young diagram with at most one column has exactly one standard Young tableau. -/
theorem standardCount_eq_one_of_rowLen_le_one {μ : YoungDiagram} (h : μ.rowLen 0 ≤ 1) :
    standardCount μ = 1 := by
  rw [← standardCount_transpose]
  exact standardCount_eq_one_of_colLen_le_one (by simpa using h)

/-- A Young diagram with a cell outside its first row and a cell outside its first column has at
least two standard Young tableaux. -/
theorem one_lt_standardCount {μ : YoungDiagram} (hrow : 1 < μ.rowLen 0) (hcol : 1 < μ.colLen 0) :
    1 < standardCount μ := by
  rw [standardCount_def]
  exact Fintype.one_lt_card_iff_nontrivial.mpr
    ⟨StandardYoungTableau.rowReading μ, StandardYoungTableau.colReading μ,
      StandardYoungTableau.rowReading_ne_colReading hrow hcol⟩

/-- **The shapes with a unique standard Young tableau** are exactly the single rows and the single
columns. -/
theorem standardCount_eq_one_iff {μ : YoungDiagram} :
    standardCount μ = 1 ↔ μ.rowLen 0 ≤ 1 ∨ μ.colLen 0 ≤ 1 := by
  refine ⟨fun h => ?_, fun h =>
    h.elim standardCount_eq_one_of_rowLen_le_one standardCount_eq_one_of_colLen_le_one⟩
  by_contra hcon
  have hrow : 1 < μ.rowLen 0 := by
    by_contra hrow
    exact hcon (Or.inl (by omega))
  have hcol : 1 < μ.colLen 0 := by
    by_contra hcol
    exact hcon (Or.inr (by omega))
  exact absurd h (one_lt_standardCount hrow hcol).ne'

/-- **The hook-length formula for a single row.** -/
theorem standardCount_mul_prod_hookLength_of_colLen_le_one {μ : YoungDiagram}
    (h : μ.colLen 0 ≤ 1) :
    standardCount μ * ∏ c ∈ μ.cells, YoungDiagram.hookLength μ c = μ.card ! := by
  rw [standardCount_eq_one_of_colLen_le_one h, one_mul,
    YoungDiagram.prod_hookLength_eq_factorial_of_colLen_le_one h]

/-- **The hook-length formula for a single column.** -/
theorem standardCount_mul_prod_hookLength_of_rowLen_le_one {μ : YoungDiagram}
    (h : μ.rowLen 0 ≤ 1) :
    standardCount μ * ∏ c ∈ μ.cells, YoungDiagram.hookLength μ c = μ.card ! := by
  rw [standardCount_eq_one_of_rowLen_le_one h, one_mul,
    YoungDiagram.prod_hookLength_eq_factorial_of_rowLen_le_one h]

end TauCeti
