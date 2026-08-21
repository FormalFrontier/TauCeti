/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Max
public import TauCeti.Combinatorics.Young.Diagram

/-!
# Corners of a Young diagram

A *corner* of a Young diagram `μ` is a cell of `μ` with neither the cell to its right nor the cell
below it in `μ`.  Equivalently, the corners are the maximal cells of `μ`
(`YoungDiagram.IsCorner.eq_of_le`): they are exactly the cells `c` for which removing `c`
alone leaves a set of cells that is still a Young diagram.  So they index the ways of building `μ`
one cell at a time, and hence the recursions that count standard Young tableaux.  The corners are
also exactly the cells of hook length `1`, which is
`YoungDiagram.isCorner_iff_hookLength_eq_one` in
`TauCeti.Combinatorics.Young.HookLength`, downstream of this file.

Deletion is `YoungDiagram.erase`.  It is defined without any hypothesis on the cell — it
removes the whole principal upper set of `c`, that is `c` together with every cell weakly below and
to the right of it — so that it can be summed over the corners of `μ` with no dependent index.  At a
corner, and only at a cell of `μ` that is a corner, nothing but `c` itself is removed
(`YoungDiagram.IsCorner.cells_erase`), and at a cell outside `μ` nothing is removed at all.

## Main definitions

* `YoungDiagram.IsCorner`: the predicate cutting out the corners of a diagram.
* `YoungDiagram.corners`: the corners of a diagram, as a `Finset`.
* `YoungDiagram.erase`: the diagram with the principal upper set of a cell removed.

## Main results

* `YoungDiagram.IsCorner.cells_erase`: erasing a corner deletes exactly that cell, and
  `YoungDiagram.IsCorner.card_erase`: it drops the number of cells by one.
* `YoungDiagram.exists_isCorner`: a nonempty Young diagram has a corner, so the corner
  recursions are not vacuous.
* `YoungDiagram.corners_transpose` and `YoungDiagram.erase_transpose`: corners and
  deletion commute with transposition.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 1.1.
* [B. E. Sagan, *The Symmetric Group*][sagan2001], Section 3.10, where the corner recursion for
  standard Young tableaux is the starting point of the hook-length formula.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 5, whose `hookLengthFormula` milestone is proved by induction along the corners of `μ`.
-/

public section

namespace YoungDiagram

variable {μ : YoungDiagram} {c d : ℕ × ℕ}

/-! ### Corners -/

/-- A **corner** of a Young diagram: a cell of `μ` with neither the cell to its right nor the cell
below it in `μ`.  These are exactly the maximal cells of `μ`
(`YoungDiagram.IsCorner.eq_of_le`), equivalently the cells whose removal on its own leaves a
set of cells that is still a Young diagram. -/
def IsCorner (μ : YoungDiagram) (c : ℕ × ℕ) : Prop :=
  c ∈ μ ∧ (c.1, c.2 + 1) ∉ μ ∧ (c.1 + 1, c.2) ∉ μ

/-- The defining conjunction of `YoungDiagram.IsCorner`, for introducing and eliminating the
predicate. -/
theorem isCorner_def (μ : YoungDiagram) (c : ℕ × ℕ) :
    IsCorner μ c ↔ c ∈ μ ∧ (c.1, c.2 + 1) ∉ μ ∧ (c.1 + 1, c.2) ∉ μ :=
  Iff.rfl

instance instDecidableIsCorner (μ : YoungDiagram) (c : ℕ × ℕ) : Decidable (IsCorner μ c) :=
  decidable_of_iff _ (isCorner_def μ c).symm

namespace IsCorner

theorem mem (h : IsCorner μ c) : c ∈ μ := h.1

theorem right_notMem (h : IsCorner μ c) : (c.1, c.2 + 1) ∉ μ := h.2.1

theorem below_notMem (h : IsCorner μ c) : (c.1 + 1, c.2) ∉ μ := h.2.2

/-- A corner is a maximal cell: the only cell of `μ` weakly below and to the right of a corner is
the corner itself. -/
theorem eq_of_le (h : IsCorner μ c) (hd : d ∈ μ) (hcd : c ≤ d) : d = c := by
  obtain ⟨hc1, hc2⟩ := hcd
  have h1 : c.1 = d.1 := by
    refine le_antisymm hc1 (le_of_not_gt fun hlt => h.below_notMem ?_)
    exact μ.up_left_mem hlt hc2 hd
  have h2 : c.2 = d.2 := by
    refine le_antisymm hc2 (le_of_not_gt fun hlt => h.right_notMem ?_)
    exact μ.up_left_mem hc1 hlt hd
  exact Prod.ext h1.symm h2.symm

theorem le_iff (h : IsCorner μ c) (hd : d ∈ μ) : c ≤ d ↔ d = c :=
  ⟨h.eq_of_le hd, fun hdc => hdc ▸ le_rfl⟩

end IsCorner

/-- The corners of a Young diagram, as a finite set of cells. -/
def corners (μ : YoungDiagram) : Finset (ℕ × ℕ) :=
  μ.cells.filter (IsCorner μ)

@[simp]
theorem mem_corners : c ∈ corners μ ↔ IsCorner μ c := by
  simp only [corners, Finset.mem_filter, _root_.YoungDiagram.mem_cells, and_iff_right_iff_imp]
  exact fun h => h.mem

theorem corners_subset_cells (μ : YoungDiagram) : corners μ ⊆ μ.cells :=
  Finset.filter_subset _ _

/-- **A nonempty Young diagram has a corner**: a cell maximizing `i + j` has neither the cell to its
right nor the cell below it in the diagram. -/
theorem exists_isCorner (hμ : 0 < μ.card) : ∃ c, IsCorner μ c := by
  obtain ⟨c, hc, hmax⟩ :=
    μ.cells.exists_max_image (fun d => d.1 + d.2) (Finset.card_pos.mp hμ)
  refine ⟨c, hc, fun hmem => ?_, fun hmem => ?_⟩
  · have h := hmax _ hmem
    omega
  · have h := hmax _ hmem
    omega

theorem corners_nonempty (hμ : 0 < μ.card) : (corners μ).Nonempty := by
  obtain ⟨c, hc⟩ := exists_isCorner hμ
  exact ⟨c, mem_corners.mpr hc⟩

/-! ### Deleting a corner -/

/-- The Young diagram obtained from `μ` by deleting the cell `c` together with every cell weakly
below and to the right of it.

The definition is total, so that it can be summed over the corners of `μ` without a dependent index.
It is `Finset.erase` on cells exactly at a corner (`YoungDiagram.IsCorner.cells_erase`), and
it leaves `μ` unchanged at a cell outside `μ`
(`YoungDiagram.erase_eq_self_of_notMem`); at a cell of `μ` that is not a corner it deletes
the entire principal upper set of `c` in `μ`, which is the price of totality. -/
def erase (μ : YoungDiagram) (c : ℕ × ℕ) : YoungDiagram where
  cells := μ.cells.filter fun d => ¬ c ≤ d
  isLowerSet := by
    intro a b hba ha
    simp only [Finset.mem_coe, Finset.mem_filter] at ha ⊢
    exact ⟨μ.isLowerSet hba (Finset.mem_coe.mpr ha.1), fun hc => ha.2 (hc.trans hba)⟩

@[simp]
theorem mem_erase : d ∈ erase μ c ↔ d ∈ μ ∧ ¬ c ≤ d :=
  Finset.mem_filter

theorem mem_of_mem_erase (h : d ∈ erase μ c) : d ∈ μ :=
  (mem_erase.mp h).1

theorem erase_le (μ : YoungDiagram) (c : ℕ × ℕ) : erase μ c ≤ μ :=
  Finset.filter_subset _ _

@[simp]
theorem erase_eq_self_of_notMem (h : c ∉ μ) : erase μ c = μ := by
  ext d
  refine ⟨fun hd => mem_of_mem_erase hd, fun hd => mem_erase.mpr ⟨hd, fun hcd => h ?_⟩⟩
  exact μ.isLowerSet hcd hd

namespace IsCorner

theorem mem_erase_iff (h : IsCorner μ c) : d ∈ erase μ c ↔ d ∈ μ ∧ d ≠ c := by
  rw [YoungDiagram.mem_erase]
  exact and_congr_right fun hd => not_congr (h.le_iff hd)

@[simp]
theorem cells_erase (h : IsCorner μ c) : (erase μ c).cells = μ.cells.erase c := by
  ext d
  simp only [Finset.mem_erase, _root_.YoungDiagram.mem_cells, h.mem_erase_iff]
  tauto

theorem notMem_erase (h : IsCorner μ c) : c ∉ erase μ c := fun hc =>
  (h.mem_erase_iff.mp hc).2 rfl

/-- Erasing a corner drops the number of cells by exactly one. -/
@[simp]
theorem card_erase (h : IsCorner μ c) : (erase μ c).card + 1 = μ.card := by
  rw [YoungDiagram.card, h.cells_erase, Finset.card_erase_of_mem h.mem]
  exact Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr ⟨c, h.mem⟩)

theorem card_pos (h : IsCorner μ c) : 0 < μ.card :=
  Finset.card_pos.mpr ⟨c, h.mem⟩

end IsCorner

/-! ### Transposition -/

@[simp]
theorem isCorner_transpose : IsCorner μ.transpose c ↔ IsCorner μ c.swap := by
  simp only [isCorner_def, _root_.YoungDiagram.mem_transpose, Prod.swap_prod_mk, Prod.fst_swap,
    Prod.snd_swap]
  tauto

@[simp]
theorem corners_transpose (μ : YoungDiagram) :
    corners μ.transpose = (corners μ).image Prod.swap := by
  ext c
  constructor
  · intro hc
    exact Finset.mem_image.mpr
      ⟨c.swap, mem_corners.mpr (isCorner_transpose.mp (mem_corners.mp hc)), c.swap_swap⟩
  · intro hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    refine mem_corners.mpr (isCorner_transpose.mpr ?_)
    rw [Prod.swap_swap]
    exact mem_corners.mp hd

@[simp]
theorem erase_transpose (μ : YoungDiagram) (c : ℕ × ℕ) :
    erase μ.transpose c = (erase μ c.swap).transpose := by
  refine SetLike.ext fun d => ?_
  rw [mem_erase, _root_.YoungDiagram.mem_transpose, _root_.YoungDiagram.mem_transpose, mem_erase]
  exact and_congr_right fun _ =>
    not_congr ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

end YoungDiagram

