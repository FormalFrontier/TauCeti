/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Young.YoungDiagram
public import TauCeti.Combinatorics.Young.Diagram

/-!
# Young tableaux

A `μ`-tableau is a bijective filling `t : ↥μ.cells ≃ Fin μ.card` of the cells of a Young diagram
`μ` by the labels `Fin μ.card`.  This file defines `YoungTableau`, the row and the column of a
label, and identifies the labels lying in a given row, respectively column, with the cells of that
row, respectively column, of `μ`; counting those labels recovers the row lengths of `μ`
(`YoungTableau.card_filter_rowIndex_eq`) and their partial sums
(`YoungTableau.card_filter_rowIndex_lt`).  On top of that it proves the counting lemma
`YoungTableau.colIndex_lt_rowLen_of_injective`: if the row of a label together with the column of
its image under a permutation `u` of the labels determine the label, then that pair of indices is
again a cell of `μ`.  It also defines `YoungTableau.relabel`, the transitive action of
the permutations of the labels on the tableaux of a fixed shape, which is how two tableaux of the
same shape are compared.

Note that `YoungTableau μ` is an abbreviation, so that the whole `Equiv` API applies to a tableau
directly.  As a consequence dot notation on a tableau resolves in the `Equiv` namespace, and the
declarations below are to be spelled out, as in `YoungTableau.rowIndex t`.

A `μ`-tableau is not required to be row- or column-increasing.  The strictly row- and
column-increasing ones are `TauCeti.StandardYoungTableau`, whose `toTableau` field is a `μ`-tableau
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
def rowIndex (t : YoungTableau μ) (k : Fin μ.card) : ℕ := (t.symm k : ℕ × ℕ).1

/-- The column of the cell of `μ` carrying the label `k` in the tableau `t`. -/
def colIndex (t : YoungTableau μ) (k : Fin μ.card) : ℕ := (t.symm k : ℕ × ℕ).2

/-- The row of a label is the first coordinate of the cell carrying it.  This is not a `simp`
lemma: `rowIndex` is the normal form, and `rowIndex_apply` computes it on a label presented as
the value of `t`. -/
theorem rowIndex_def (t : YoungTableau μ) (k : Fin μ.card) :
    rowIndex t k = (t.symm k : ℕ × ℕ).1 := by
  rw [rowIndex]

/-- The column of a label is the second coordinate of the cell carrying it.  As for
`rowIndex_def`, this is not a `simp` lemma. -/
theorem colIndex_def (t : YoungTableau μ) (k : Fin μ.card) :
    colIndex t k = (t.symm k : ℕ × ℕ).2 := by
  rw [colIndex]

@[simp]
theorem rowIndex_apply (t : YoungTableau μ) (c : ↥μ.cells) :
    rowIndex t (t c) = (c : ℕ × ℕ).1 := by
  rw [rowIndex_def, Equiv.symm_apply_apply]

@[simp]
theorem colIndex_apply (t : YoungTableau μ) (c : ↥μ.cells) :
    colIndex t (t c) = (c : ℕ × ℕ).2 := by
  rw [colIndex_def, Equiv.symm_apply_apply]

/-- A cell of a Young diagram is determined by its row together with its column, so a label of a
tableau is determined by its row and its column. -/
theorem rowIndex_colIndex_injective (t : YoungTableau μ) :
    Function.Injective fun k => (rowIndex t k, colIndex t k) := by
  intro k l h
  simp only [rowIndex_def, colIndex_def, Prod.mk.injEq] at h
  exact t.symm.injective (Subtype.ext (Prod.ext h.1 h.2))

/-- The labels lying in row `i` of a `μ`-tableau are the cells of the `i`-th row of `μ`. -/
def rowFiberEquiv (t : YoungTableau μ) (i : ℕ) :
    {k : Fin μ.card // rowIndex t k = i} ≃ ↥(μ.row i) :=
  -- the two predicates are given explicitly: inferring them from `Iff.rfl` would state the source
  -- subtype through the unfolding of `rowIndex` rather than through `rowIndex` itself
  (Equiv.subtypeEquiv (p := fun k => rowIndex t k = i) (q := fun c : ↥μ.cells => (↑c : ℕ × ℕ).1 = i)
      t.symm fun _ => Iff.rfl).trans <|
    (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ μ.cells) fun c => c.1 = i).trans <|
      Equiv.subtypeEquivRight fun _ => by
        rw [YoungDiagram.mem_row_iff, YoungDiagram.mem_cells]

/-- The labels lying in column `j` of a `μ`-tableau are the cells of the `j`-th column of `μ`. -/
def colFiberEquiv (t : YoungTableau μ) (j : ℕ) :
    {k : Fin μ.card // colIndex t k = j} ≃ ↥(μ.col j) :=
  -- as for `rowFiberEquiv`, the two predicates are given explicitly
  (Equiv.subtypeEquiv (p := fun k => colIndex t k = j) (q := fun c : ↥μ.cells => (↑c : ℕ × ℕ).2 = j)
      t.symm fun _ => Iff.rfl).trans <|
    (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ μ.cells) fun c => c.2 = j).trans <|
      Equiv.subtypeEquivRight fun _ => by
        rw [YoungDiagram.mem_col_iff, YoungDiagram.mem_cells]

-- This and `colFiberEquiv_apply_coe` are the defining equations of the two fiber equivalences: in
-- each chain only the leading `Equiv.subtypeEquiv` moves the underlying cell, by applying `t.symm`,
-- while `Equiv.subtypeSubtypeEquivSubtypeInter` and `Equiv.subtypeEquivRight` change only the
-- predicate, so the two sides differ by subtype coercions alone and hold by `rfl`.  The definitions
-- are deliberately not `@[expose]`d, so the pre-bump `simp [rowFiberEquiv]` has nothing to unfold;
-- the parentheses in `(rfl)` keep the definitional step inside this module, leaving these lemmas
-- and the `_symm_apply_coe` pair below as the whole interface for importers.
@[simp]
theorem rowFiberEquiv_apply_coe (t : YoungTableau μ) (i : ℕ)
    (k : {k : Fin μ.card // rowIndex t k = i}) :
    (rowFiberEquiv t i k : ℕ × ℕ) = (t.symm k.1 : ℕ × ℕ) := (rfl)

@[simp]
theorem colFiberEquiv_apply_coe (t : YoungTableau μ) (j : ℕ)
    (k : {k : Fin μ.card // colIndex t k = j}) :
    (colFiberEquiv t j k : ℕ × ℕ) = (t.symm k.1 : ℕ × ℕ) := (rfl)

/-- The label attached to a cell of row `i` is the label of that cell in the tableau. -/
@[simp]
theorem rowFiberEquiv_symm_apply_coe (t : YoungTableau μ) (i : ℕ) (c : ↥(μ.row i)) :
    ((rowFiberEquiv t i).symm c : Fin μ.card) =
      t ⟨(c : ℕ × ℕ), (YoungDiagram.mem_cells _).mpr (YoungDiagram.mem_row_iff.mp c.2).1⟩ := by
  apply t.symm.injective
  rw [Equiv.symm_apply_apply]
  refine Subtype.ext ?_
  rw [← rowFiberEquiv_apply_coe, Equiv.apply_symm_apply]

/-- The label attached to a cell of column `j` is the label of that cell in the tableau. -/
@[simp]
theorem colFiberEquiv_symm_apply_coe (t : YoungTableau μ) (j : ℕ) (c : ↥(μ.col j)) :
    ((colFiberEquiv t j).symm c : Fin μ.card) =
      t ⟨(c : ℕ × ℕ), (YoungDiagram.mem_cells _).mpr (YoungDiagram.mem_col_iff.mp c.2).1⟩ := by
  apply t.symm.injective
  rw [Equiv.symm_apply_apply]
  refine Subtype.ext ?_
  rw [← colFiberEquiv_apply_coe, Equiv.apply_symm_apply]

/-! ## Cells and labels -/

/-- The row and the column of a label are the coordinates of a cell of `μ`. -/
theorem rowIndex_colIndex_mem (t : YoungTableau μ) (x : Fin μ.card) :
    (rowIndex t x, colIndex t x) ∈ μ := by
  rw [rowIndex_def, colIndex_def]
  simp

/-- A label lies in a column strictly to the left of the end of its row. -/
theorem colIndex_lt_rowLen (t : YoungTableau μ) (x : Fin μ.card) :
    colIndex t x < μ.rowLen (rowIndex t x) :=
  YoungDiagram.mem_iff_lt_rowLen.mp (rowIndex_colIndex_mem t x)

/-- **The row of a label is below the number of rows.** The label lies in its own column, which is
no longer than the zeroth one. -/
theorem rowIndex_lt_colLen_zero (t : YoungTableau μ) (x : Fin μ.card) :
    rowIndex t x < μ.colLen 0 :=
  (YoungDiagram.mem_iff_lt_colLen.mp (rowIndex_colIndex_mem t x)).trans_le
    (μ.colLen_anti 0 _ (Nat.zero_le _))

/-- Every cell of `μ` carries a label. -/
theorem exists_rowIndex_colIndex (t : YoungTableau μ) {i j : ℕ} (h : (i, j) ∈ μ) :
    ∃ x, rowIndex t x = i ∧ colIndex t x = j :=
  ⟨t ⟨(i, j), (YoungDiagram.mem_cells _).mpr h⟩, by simp, by simp⟩

/-- Row `i` of a `μ`-tableau carries `μ.rowLen i` labels. -/
theorem card_filter_rowIndex_eq (t : YoungTableau μ) (i : ℕ) :
    (Finset.univ.filter fun y => rowIndex t y = i).card = μ.rowLen i := by
  rw [← Fintype.card_subtype, Fintype.card_congr (rowFiberEquiv t i), Fintype.card_coe]
  exact (YoungDiagram.rowLen_eq_card μ).symm

/-- The labels of a tableau lying in one of its first `k` rows are as many as the cells of the
shape in its first `k` rows. -/
theorem card_filter_rowIndex_lt (t : YoungTableau μ) (k : ℕ) :
    (Finset.univ.filter fun x => rowIndex t x < k).card = (μ.rowLens.take k).sum := by
  classical
  rw [YoungDiagram.sum_take_rowLens_eq_card_filter_fst]
  refine Finset.card_bij (fun x _ => ((t.symm x : ↥μ.cells) : ℕ × ℕ)) (fun x hx => ?_)
    (fun x _ y _ h => t.symm.injective (Subtype.ext h)) fun c hc => ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, rowIndex_def] at hx
    exact Finset.mem_filter.mpr ⟨(t.symm x).2, hx⟩
  · rw [Finset.mem_filter] at hc
    refine ⟨t ⟨c, hc.1⟩, ?_, ?_⟩
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, rowIndex_apply] using hc.2
    · rw [Equiv.symm_apply_apply]

/-! ## The counting lemma -/

/-- **Row `i` meets the first `k` columns in exactly `min (μ.rowLen i) k` labels.** -/
private theorem card_filter_colIndex_lt_and_rowIndex_eq (t : YoungTableau μ) (i k : ℕ) :
    (Finset.univ.filter fun y => colIndex t y < k ∧ rowIndex t y = i).card
      = min (μ.rowLen i) k := by
  have hinj : Set.InjOn (colIndex t)
      ↑(Finset.univ.filter fun y => colIndex t y < k ∧ rowIndex t y = i) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact rowIndex_colIndex_injective t (Prod.ext (ha.2.trans hb.2.symm) hab)
  have himg : (Finset.univ.filter fun y => colIndex t y < k ∧ rowIndex t y = i).image
      (colIndex t) = (Finset.range (μ.rowLen i)).filter fun j => j < k := by
    ext j
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      exact ⟨hy2 ▸ colIndex_lt_rowLen t y, hy1⟩
    · rintro ⟨hj1, hj2⟩
      obtain ⟨y, hy1, hy2⟩ :=
        exists_rowIndex_colIndex t (YoungDiagram.mem_iff_lt_rowLen.mpr hj1)
      exact ⟨y, ⟨hy2 ▸ hj2, hy1⟩, hy2⟩
  have hrange : ((Finset.range (μ.rowLen i)).filter fun j => j < k)
      = Finset.range (min (μ.rowLen i) k) := by
    ext j
    simp
  rw [← Finset.card_image_of_injOn hinj, himg, hrange, Finset.card_range]

/-- **Row `i` meets the first `k` columns of the `u`-image in at most `min (μ.rowLen i) k`
labels**, when the row of a label together with the column of its `u`-image determines the label.
Only injectivity of that pairing is used, so `u` need not be a permutation. -/
private theorem card_filter_colIndex_comp_lt_and_rowIndex_eq_le (t : YoungTableau μ)
    {u : Fin μ.card → Fin μ.card}
    (hu : Function.Injective fun x => (rowIndex t x, colIndex t (u x))) (i k : ℕ) :
    (Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i).card
      ≤ min (μ.rowLen i) k := by
  refine le_min ?_ ?_
  · rw [← card_filter_rowIndex_eq t i]
    refine Finset.card_le_card fun y hy => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hy.2
  · have hinj : Set.InjOn (fun y => colIndex t (u y))
        ↑(Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i) := by
      intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact hu (Prod.ext (ha.2.trans hb.2.symm) hab)
    calc (Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i).card
        = ((Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i).image
            fun y => colIndex t (u y)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range k).card := by
            refine Finset.card_le_card fun j hj => ?_
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hj
            obtain ⟨y, ⟨hy1, _⟩, rfl⟩ := hj
            exact Finset.mem_range.mpr hy1
      _ = k := Finset.card_range k

/-- **Summed over the rows, the labels whose `u`-image lies in the first `k` columns number
`∑ᵢ min (μ.rowLen i) k`.** No injectivity hypothesis is needed. -/
private theorem sum_card_filter_colIndex_comp_lt_and_rowIndex_eq (t : YoungTableau μ)
    (u : Equiv.Perm (Fin μ.card)) (k : ℕ) :
    ∑ i ∈ Finset.image (rowIndex t) Finset.univ,
        (Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i).card
      = ∑ i ∈ Finset.image (rowIndex t) Finset.univ, min (μ.rowLen i) k := by
  have hmemS : ∀ y : Fin μ.card, rowIndex t y ∈ Finset.image (rowIndex t) Finset.univ :=
    fun y => Finset.mem_image_of_mem _ (Finset.mem_univ y)
  have h1 : (Finset.univ.filter fun y => colIndex t (u y) < k).card
      = ∑ i ∈ Finset.image (rowIndex t) Finset.univ,
          (Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := rowIndex t)
      (t := Finset.image (rowIndex t) Finset.univ) fun y _ => hmemS y]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.filter_filter]
  have h2 : (Finset.univ.filter fun y => colIndex t y < k).card
      = ∑ i ∈ Finset.image (rowIndex t) Finset.univ,
          (Finset.univ.filter fun y => colIndex t y < k ∧ rowIndex t y = i).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := rowIndex t)
      (t := Finset.image (rowIndex t) Finset.univ) fun y _ => hmemS y]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.filter_filter]
  have h3 : (Finset.univ.filter fun y => colIndex t (u y) < k).card
      = (Finset.univ.filter fun y => colIndex t y < k).card :=
    Finset.card_equiv u fun i => by simp
  rw [← h1, h3, h2]
  exact Finset.sum_congr rfl fun i _ => card_filter_colIndex_lt_and_rowIndex_eq t i k

/-- **The counting lemma for rows and columns along a permutation.**  If the row of a label
together with the column of its `u`-image determine the label, then that pair is again a cell of
`μ`.

Both halves of the count are over the rows of `μ`: the labels whose `u`-image lies in one of the
first `k` columns number `∑ᵢ min (μ.rowLen i) k`, while row `i` can contribute at most
`min (μ.rowLen i) k` of them.  Upper bounds that add up to the total are equalities, and the case
`k = μ.rowLen i` of the resulting equality is the statement. -/
theorem colIndex_lt_rowLen_of_injective (t : YoungTableau μ) (u : Equiv.Perm (Fin μ.card))
    (hu : Function.Injective fun x => (rowIndex t x, colIndex t (u x))) (x : Fin μ.card) :
    colIndex t (u x) < μ.rowLen (rowIndex t x) := by
  have hmemS : ∀ y : Fin μ.card, rowIndex t y ∈ Finset.image (rowIndex t) Finset.univ :=
    fun y => Finset.mem_image_of_mem _ (Finset.mem_univ y)
  -- The row-wise upper bounds add up to the total, so each is an equality.
  have hi := (Finset.sum_eq_sum_iff_of_le fun i _ =>
      card_filter_colIndex_comp_lt_and_rowIndex_eq_le t hu i (μ.rowLen (rowIndex t x))).mp
    (sum_card_filter_colIndex_comp_lt_and_rowIndex_eq t u (μ.rowLen (rowIndex t x)))
    (rowIndex t x) (hmemS x)
  rw [min_self] at hi
  -- a subset of the row with the same cardinality is the whole row
  have hsub : (Finset.univ.filter fun y =>
        colIndex t (u y) < μ.rowLen (rowIndex t x) ∧ rowIndex t y = rowIndex t x)
      ⊆ Finset.univ.filter fun y => rowIndex t y = rowIndex t x := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hy.2
  have hEq := Finset.eq_of_subset_of_card_le hsub
    (le_of_eq (by rw [card_filter_rowIndex_eq t (rowIndex t x), hi]))
  have hx : x ∈ Finset.univ.filter fun y =>
      colIndex t (u y) < μ.rowLen (rowIndex t x) ∧ rowIndex t y = rowIndex t x := by
    rw [hEq]
    simp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact hx.1

/-! ## Relabeling -/

/-- The tableau `t` with its labels permuted by `σ`: the cell that `t` labels `k` is labelled
`σ k` by `relabel σ t`.

Relabeling is the left action of `Equiv.Perm (Fin μ.card)` on `YoungTableau μ` recorded by
`relabel_one` and `relabel_relabel`, and it is transitive by `exists_relabel_eq`.  It is not
registered as a `MulAction` instance because `YoungTableau μ` is an abbreviation for a type of
equivalences, so such an instance would fire on equivalences at large, far outside the tableaux
it is meant for. -/
def relabel (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) : YoungTableau μ :=
  t.trans σ

@[simp]
theorem relabel_apply (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) (c : ↥μ.cells) :
    relabel σ t c = σ (t c) :=
  (rfl)

@[simp]
theorem relabel_symm_apply (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) (k : Fin μ.card) :
    (relabel σ t).symm k = t.symm (σ⁻¹ k) := by
  rw [relabel, Equiv.symm_trans_apply, Equiv.Perm.inv_def]

/-- Relabeling by `σ` moves the label `k` to the row that `t` gives to `σ⁻¹ k`. -/
@[simp]
theorem rowIndex_relabel (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) (k : Fin μ.card) :
    rowIndex (relabel σ t) k = rowIndex t (σ⁻¹ k) := by
  rw [rowIndex_def, rowIndex_def, relabel_symm_apply]

/-- Relabeling by `σ` moves the label `k` to the column that `t` gives to `σ⁻¹ k`. -/
@[simp]
theorem colIndex_relabel (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) (k : Fin μ.card) :
    colIndex (relabel σ t) k = colIndex t (σ⁻¹ k) := by
  rw [colIndex_def, colIndex_def, relabel_symm_apply]

@[simp]
theorem relabel_one (t : YoungTableau μ) : relabel 1 t = t := by
  rw [relabel, Equiv.Perm.one_def, Equiv.trans_refl]

@[simp]
theorem relabel_relabel (σ τ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) :
    relabel σ (relabel τ t) = relabel (σ * τ) t := by
  rw [relabel, relabel, relabel, Equiv.trans_assoc, Equiv.Perm.mul_def]

/-- The permutation of the labels carrying the tableau `t` to the tableau `t'` of the same
shape. -/
def relabelPerm (t t' : YoungTableau μ) : Equiv.Perm (Fin μ.card) :=
  t.symm.trans t'

/-- The permutation carrying `t` to `t'` sends the label `k` to the label that `t'` gives to the
cell that `t` labels `k`. -/
@[simp]
theorem relabelPerm_apply (t t' : YoungTableau μ) (k : Fin μ.card) :
    relabelPerm t t' k = t' (t.symm k) := by
  rw [relabelPerm, Equiv.trans_apply]

@[simp]
theorem relabel_relabelPerm (t t' : YoungTableau μ) : relabel (relabelPerm t t') t = t' := by
  rw [relabel, relabelPerm, ← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans]

/-- Any two tableaux of the same shape differ by a relabeling. -/
theorem exists_relabel_eq (t t' : YoungTableau μ) : ∃ σ, relabel σ t = t' :=
  ⟨relabelPerm t t', relabel_relabelPerm t t'⟩

/-- Every Young diagram carries a tableau: enumerating its cells is one.

This is a theorem rather than a `Nonempty` instance because `YoungTableau μ` is an abbreviation
for a type of equivalences, so an instance would fire on equivalences at large. -/
theorem nonempty (μ : YoungDiagram) : Nonempty (YoungTableau μ) :=
  ⟨μ.cells.equivFin⟩

end YoungTableau

end TauCeti
