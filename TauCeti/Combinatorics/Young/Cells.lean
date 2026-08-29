/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Monotone.Defs

public section

/-!
# Finite sets of cells, closed in the row direction

A finite set `D : Finset (ι × κ)` of **cells** has its rows indexed by `ι` and its columns indexed
by `κ`. This file counts the cells of `D` one row at a time (`TauCeti.CellDiagram.rowLen`), imposes
the shape condition that makes such a set look like a Young diagram
(`TauCeti.CellDiagram.IsRowLowerClosed`: with every cell, `D` contains the cells directly above it),
and builds the set of cells lying under a prescribed tuple of row lengths
(`TauCeti.CellDiagram.ofRowLens`).

## Main definitions

* `TauCeti.CellDiagram.rowLen`: the number of cells of a set lying in a given row.
* `TauCeti.CellDiagram.IsRowLowerClosed`: closure of a set of cells in the row direction.
* `TauCeti.CellDiagram.ofRowLens`: the cells lying under a tuple of row lengths.

## Main results

* `TauCeti.CellDiagram.isRowLowerClosed_ofRowLens`: the cells under a weakly decreasing tuple of
  row lengths are closed in the row direction.
* `TauCeti.CellDiagram.rowLen_ofRowLens` and `TauCeti.CellDiagram.card_ofRowLens`: the rows of
  those cells have the prescribed lengths, and there are `∑ i, a i` cells in all.

## Implementation notes

Mathlib's `YoungDiagram` is a set of cells in `ℕ × ℕ` closed downwards in *both* directions, and
its rows are indexed by `ℕ`. The rows here are indexed by an abstract type `ι`, and only closure in
the row direction is imposed, because that is the condition the consumers need: it is exactly what
makes the raising operators of `gl ι` annihilate the wedge of the basis vectors indexed by the
cells, in `TauCeti.isGlHighestWeightVector_basisWedge`.
-/

namespace TauCeti.CellDiagram

variable {ι κ : Type*}

/-! ### Counting the cells of a row -/

section RowLen

variable [DecidableEq ι]

/-- The number of cells of `D` lying in row `i`. -/
def rowLen (D : Finset (ι × κ)) (i : ι) : ℕ :=
  (D.filter fun p => p.1 = i).card

/-- `TauCeti.CellDiagram.rowLen` unfolded. The definition is not exposed, so this is how the row
lengths are computed outside this file. -/
theorem rowLen_eq_card_filter (D : Finset (ι × κ)) (i : ι) :
    rowLen D i = (D.filter fun p => p.1 = i).card := by
  rw [rowLen]

/-- The cells of `D` in row `i`, counted by their column index. -/
theorem rowLen_eq_card_filter_mem [Fintype κ] [DecidableEq κ] (D : Finset (ι × κ)) (i : ι) :
    rowLen D i = (Finset.univ.filter fun c : κ => (i, c) ∈ D).card := by
  have hinj : Function.Injective fun c : κ => ((i, c) : ι × κ) := fun c d h => congrArg Prod.snd h
  rw [rowLen_eq_card_filter, ← Finset.card_image_of_injective
    (Finset.univ.filter fun c : κ => (i, c) ∈ D) hinj]
  refine congrArg Finset.card (Finset.ext ?_)
  rintro ⟨x, c⟩
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨hmem, hx⟩
    subst hx
    exact ⟨c, hmem, rfl, rfl⟩
  · rintro ⟨d, hd, hx, hc⟩
    subst hx
    subst hc
    exact ⟨hd, rfl⟩

end RowLen

/-! ### Closure in the row direction -/

/-- A set of cells is **row lower closed** when with every cell it contains all the cells directly
above it: if `(j, c)` is a cell and `i < j`, then `(i, c)` is a cell. In other words `D` is a lower
set in its row index. This is the shape condition on a Young diagram. -/
def IsRowLowerClosed [LT ι] (D : Finset (ι × κ)) : Prop :=
  ∀ p ∈ D, ∀ i : ι, i < p.1 → (i, p.2) ∈ D

/-- `TauCeti.CellDiagram.IsRowLowerClosed` unfolded. The definition is not exposed, so this is how
the condition is introduced and eliminated outside this file. -/
theorem isRowLowerClosed_iff [LT ι] {D : Finset (ι × κ)} :
    IsRowLowerClosed D ↔ ∀ p ∈ D, ∀ i : ι, i < p.1 → (i, p.2) ∈ D :=
  Iff.rfl

/-! ### The cells under a tuple of row lengths -/

section OfRowLens

variable [Fintype ι]

/-- The cells lying under the row lengths `a`: those cells `(i, c)` whose column index `c` is
smaller than the `i`-th row length. The columns are drawn from `Fin m`, so a row longer than `m` is
truncated. -/
def ofRowLens (a : ι → ℕ) (m : ℕ) : Finset (ι × Fin m) :=
  Finset.univ.filter fun p => (p.2 : ℕ) < a p.1

@[simp]
theorem mem_ofRowLens_iff {a : ι → ℕ} {m : ℕ} {p : ι × Fin m} :
    p ∈ ofRowLens a m ↔ (p.2 : ℕ) < a p.1 := by
  simp [ofRowLens]

/-- The cells under a weakly decreasing tuple of row lengths are closed in the row direction. -/
theorem isRowLowerClosed_ofRowLens [Preorder ι] {a : ι → ℕ} (ha : Antitone a) (m : ℕ) :
    IsRowLowerClosed (ofRowLens a m) := by
  intro p hp i hi
  exact mem_ofRowLens_iff.2 ((mem_ofRowLens_iff.1 hp).trans_le (ha hi.le))

variable [DecidableEq ι]

/-- The rows of the cells under `a` have the lengths `a` prescribes, as soon as there are enough
columns to hold them. -/
theorem rowLen_ofRowLens {a : ι → ℕ} {m : ℕ} (hm : ∀ i, a i ≤ m) (i : ι) :
    rowLen (ofRowLens a m) i = a i := by
  have himage : (ofRowLens a m).filter (fun p => p.1 = i)
      = Finset.univ.image fun c : Fin (a i) => ((i, Fin.castLE (hm i) c) : ι × Fin m) := by
    refine Finset.ext fun p => ?_
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, mem_ofRowLens_iff]
    refine ⟨?_, ?_⟩
    · rintro ⟨hlt, rfl⟩
      exact ⟨⟨p.2, hlt⟩, by simp⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c.isLt, rfl⟩
  rw [rowLen_eq_card_filter, himage, Finset.card_image_of_injective _ (fun c d h =>
      Fin.val_injective (congrArg (fun p : ι × Fin m => (p.2 : ℕ)) h)),
    Finset.card_univ, Fintype.card_fin]

omit [DecidableEq ι] in
/-- The cells under `a` are one for each unit of each row length, as soon as there are enough
columns to hold them. -/
theorem card_ofRowLens {a : ι → ℕ} {m : ℕ} (hm : ∀ i, a i ≤ m) :
    (ofRowLens a m).card = ∑ i, a i := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : ι × Fin m => p.1) (t := Finset.univ)
    fun _ _ => Finset.mem_univ _]
  exact Finset.sum_congr rfl fun i _ =>
    (rowLen_eq_card_filter (ofRowLens a m) i).symm.trans (rowLen_ofRowLens hm i)

end OfRowLens

end TauCeti.CellDiagram
