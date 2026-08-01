/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Combinatorics.Young.YoungDiagram

/-!
# Young tableaux

A `μ`-tableau is a bijective filling `t : ↥μ.cells ≃ Fin μ.card` of the cells of a Young diagram
`μ` by the labels `Fin μ.card`.  This file defines `YoungTableau`, the row and the column of a
label, and identifies the labels lying in a given row, respectively column, with the cells of that
row, respectively column, of `μ`.  It also defines `YoungTableau.relabel`, the transitive action of
the permutations of the labels on the tableaux of a fixed shape, which is how two tableaux of the
same shape are compared.

Note that `YoungTableau μ` is an abbreviation, so that the whole `Equiv` API applies to a tableau
directly.  As a consequence dot notation on a tableau resolves in the `Equiv` namespace, and the
declarations below are to be spelled out, as in `YoungTableau.rowIndex t`.

A `μ`-tableau is not required to be row- or column-increasing.  The strictly row- and
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

end YoungTableau

end TauCeti
