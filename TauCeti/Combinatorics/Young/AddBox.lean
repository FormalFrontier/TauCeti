/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Corner

/-!
# Adding a cell to a Young diagram

Deleting a corner of a Young diagram is `YoungDiagram.erase`.  This file builds the inverse
operation: a cell `c` is **addable** to `μ` (`YoungDiagram.IsAddable`) when it does not lie in
`μ` but everything strictly above and to the left of it does, and then `YoungDiagram.addBox μ c`
is the diagram `μ` together with `c`.  Addable cells and corners correspond: `c` is a corner of
`YoungDiagram.addBox μ c`, deleting it returns `μ`, and conversely a corner `c` of `μ` is addable
to `YoungDiagram.erase μ c`, which rebuilt at `c` is `μ` again.  So the pairs consisting of a
diagram together with one of its corners are the same thing as the pairs consisting of a diagram
together with one of its addable cells, with the number of cells shifted by one; that is the
reindexing every recursion along corners needs.

Addability is a condition on row lengths (`YoungDiagram.isAddable_iff`): the cell is `(i, μᵢ)` at
the end of row `i`, and every earlier row is strictly longer.  In that form it is decidable, and
the addable cells assemble into a `Finset`, `YoungDiagram.addableCells`.

The definition of `YoungDiagram.addBox` is total, like that of `YoungDiagram.erase`: it takes the
supremum of `μ` with the rectangle of cells weakly above and to the left of `c`, which is the
smallest Young diagram containing `c`.  At an addable cell — and only there — that adjoins exactly
`c`.

## Main definitions

* `YoungDiagram.rectangle`: the cells weakly above and to the left of a given cell.
* `YoungDiagram.addBox`: the diagram `μ` with a cell adjoined.
* `YoungDiagram.IsAddable`: the predicate cutting out the cells that may be adjoined.
* `YoungDiagram.addableCells`: the addable cells of a diagram, as a `Finset`.

## Main results

* `YoungDiagram.isAddable_iff`: addability in terms of row lengths, whence the decidability
  instance and `YoungDiagram.mem_addableCells`.
* `YoungDiagram.IsAddable.cells_addBox`, `YoungDiagram.IsAddable.card_addBox`: adding a cell
  adjoins exactly that cell, and raises the number of cells by one.
* `YoungDiagram.IsAddable.isCorner_addBox` and `YoungDiagram.IsAddable.erase_addBox`, together
  with `YoungDiagram.IsCorner.isAddable_erase` and `YoungDiagram.IsCorner.addBox_erase`: adding
  and deleting are mutually inverse.
* `YoungDiagram.IsAddable.rowLen_addBox` and `YoungDiagram.IsCorner.rowLen_erase`: the effect of
  either operation on the row lengths.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 1.1.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 8: Schur-Weyl duality
-/

public section

namespace YoungDiagram

variable {μ : YoungDiagram} {c d : ℕ × ℕ}

/-! ### The smallest diagram containing a cell -/

/-- The **rectangle** of a cell: the cells weakly above and to the left of `c`.  It is the
smallest Young diagram containing `c`. -/
def rectangle (c : ℕ × ℕ) : YoungDiagram where
  cells := Finset.range (c.1 + 1) ×ˢ Finset.range (c.2 + 1)
  isLowerSet := by
    intro a b hba ha
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at ha ⊢
    exact ⟨lt_of_le_of_lt hba.1 ha.1, lt_of_le_of_lt hba.2 ha.2⟩

@[simp]
theorem mem_rectangle : d ∈ rectangle c ↔ d.1 ≤ c.1 ∧ d.2 ≤ c.2 := by
  simp only [rectangle, ← mem_cells, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff]

theorem mem_rectangle_iff_le : d ∈ rectangle c ↔ d ≤ c := by
  rw [mem_rectangle, Prod.le_def]

/-! ### Addable cells -/

/-- A cell is **addable** to `μ` when it does not lie in `μ` but every cell strictly above or to
the left of it does; equivalently, adjoining it to `μ` leaves a Young diagram. -/
def IsAddable (μ : YoungDiagram) (c : ℕ × ℕ) : Prop :=
  c ∉ μ ∧ ∀ d, d ≤ c → d ≠ c → d ∈ μ

/-- **Addability in terms of row lengths**: the cell sits at the end of its row, and every
earlier row of `μ` is strictly longer. -/
theorem isAddable_iff :
    IsAddable μ c ↔ c.2 = μ.rowLen c.1 ∧ ∀ j < c.1, μ.rowLen c.1 < μ.rowLen j := by
  constructor
  · rintro ⟨hc, hlt⟩
    have hle : μ.rowLen c.1 ≤ c.2 := by
      by_contra hcon
      exact hc (mem_iff_lt_rowLen.mpr (not_le.mp hcon))
    have hge : c.2 ≤ μ.rowLen c.1 := by
      rcases Nat.eq_zero_or_pos c.2 with h0 | h0
      · omega
      · have : ((c.1, c.2 - 1) : ℕ × ℕ) ∈ μ :=
          hlt _ (Prod.mk_le_mk.mpr ⟨le_rfl, by omega⟩) (by simp only [ne_eq, Prod.ext_iff]; omega)
        have := mem_iff_lt_rowLen.mp this
        omega
    refine ⟨by omega, fun j hj => ?_⟩
    have : ((j, c.2) : ℕ × ℕ) ∈ μ :=
      hlt _ (Prod.mk_le_mk.mpr ⟨hj.le, le_rfl⟩) (by simp only [ne_eq, Prod.ext_iff]; omega)
    have := mem_iff_lt_rowLen.mp this
    omega
  · rintro ⟨hsnd, hrow⟩
    refine ⟨fun hc => ?_, fun d hd hne => ?_⟩
    · have := mem_iff_lt_rowLen.mp hc
      omega
    · have h1 : d.1 ≤ c.1 := (Prod.le_def.mp hd).1
      have h2 : d.2 ≤ c.2 := (Prod.le_def.mp hd).2
      rcases eq_or_lt_of_le h1 with h | h
      · have : d.2 ≠ c.2 := fun hcon => hne (Prod.ext h hcon)
        have : d.2 < μ.rowLen d.1 := by rw [h]; omega
        exact mem_iff_lt_rowLen.mpr this
      · have := hrow d.1 h
        exact mem_iff_lt_rowLen.mpr (by omega)

instance instDecidableIsAddable (μ : YoungDiagram) (c : ℕ × ℕ) : Decidable (IsAddable μ c) :=
  decidable_of_iff _ isAddable_iff.symm

/-- An addable cell sits at the end of its row. -/
theorem IsAddable.snd_eq (h : IsAddable μ c) : c.2 = μ.rowLen c.1 :=
  (isAddable_iff.mp h).1

/-- Every row before that of an addable cell is strictly longer. -/
theorem IsAddable.rowLen_lt (h : IsAddable μ c) {j : ℕ} (hj : j < c.1) :
    μ.rowLen c.1 < μ.rowLen j :=
  (isAddable_iff.mp h).2 j hj

/-- **The cell at the end of row `i` is addable exactly when every earlier row is longer.** -/
theorem isAddable_row (μ : YoungDiagram) (i : ℕ) :
    IsAddable μ (i, μ.rowLen i) ↔ ∀ j < i, μ.rowLen i < μ.rowLen j := by
  rw [isAddable_iff]
  simp

/-- An addable cell lies in a row of index at most the height of the diagram. -/
theorem IsAddable.fst_le_colLen (h : IsAddable μ c) : c.1 ≤ μ.colLen 0 := by
  by_contra hcon
  push Not at hcon
  have hpos : 0 < c.1 := lt_of_le_of_lt (Nat.zero_le _) hcon
  have hmem : ((c.1 - 1, 0) : ℕ × ℕ) ∈ μ :=
    h.2 _ (Prod.mk_le_mk.mpr ⟨by omega, Nat.zero_le _⟩) (by simp only [ne_eq, Prod.ext_iff]; omega)
  have := mem_iff_lt_colLen.mp hmem
  omega

/-- An addable cell lies in a column of index at most the width of the diagram. -/
theorem IsAddable.snd_le_rowLen_zero (h : IsAddable μ c) : c.2 ≤ μ.rowLen 0 := by
  rw [h.snd_eq]
  exact μ.rowLen_anti 0 c.1 (Nat.zero_le _)

/-- The addable cells of a diagram, as a `Finset`. -/
def addableCells (μ : YoungDiagram) : Finset (ℕ × ℕ) :=
  (Finset.range (μ.colLen 0 + 1) ×ˢ Finset.range (μ.rowLen 0 + 1)).filter (IsAddable μ)

@[simp]
theorem mem_addableCells : c ∈ addableCells μ ↔ IsAddable μ c := by
  refine ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨?_, h⟩⟩
  have h1 := h.fst_le_colLen
  have h2 := h.snd_le_rowLen_zero
  simp only [Finset.mem_product, Finset.mem_range]
  omega

/-! ### Adding a cell -/

/-- The Young diagram `μ` with the cell `c` adjoined.

The definition is total, so that it can be summed over the addable cells of `μ` without a
dependent index: it is the supremum of `μ` with the rectangle of `c`.  At an addable cell it
adjoins exactly `c` (`YoungDiagram.IsAddable.cells_addBox`). -/
def addBox (μ : YoungDiagram) (c : ℕ × ℕ) : YoungDiagram :=
  μ ⊔ rectangle c

theorem IsAddable.mem_addBox_iff (h : IsAddable μ c) : d ∈ addBox μ c ↔ d ∈ μ ∨ d = c := by
  rw [addBox, mem_sup, mem_rectangle_iff_le]
  constructor
  · rintro (hd | hle)
    · exact Or.inl hd
    · by_cases hne : d = c
      · exact Or.inr hne
      · exact Or.inl (h.2 d hle hne)
  · rintro (hd | rfl)
    · exact Or.inl hd
    · exact Or.inr le_rfl

/-- Adding an addable cell adjoins exactly that cell. -/
@[simp]
theorem IsAddable.cells_addBox (h : IsAddable μ c) : (addBox μ c).cells = insert c μ.cells := by
  ext d
  rw [mem_cells, h.mem_addBox_iff, Finset.mem_insert, mem_cells]
  tauto

/-- Adding a cell raises the number of cells by one. -/
theorem IsAddable.card_addBox (h : IsAddable μ c) : (addBox μ c).card = μ.card + 1 := by
  rw [YoungDiagram.card, h.cells_addBox, Finset.card_insert_of_notMem h.1]

/-- The cell added is a corner of the result. -/
theorem IsAddable.isCorner_addBox (h : IsAddable μ c) : IsCorner (addBox μ c) c := by
  refine (isCorner_def _ _).mpr ⟨h.mem_addBox_iff.mpr (Or.inr rfl), ?_, ?_⟩
  · rw [h.mem_addBox_iff]
    rintro (hmem | hmem)
    · exact h.1 (μ.isLowerSet (Prod.mk_le_mk.mpr ⟨le_rfl, Nat.le_succ _⟩) hmem)
    · simp only [Prod.ext_iff] at hmem; omega
  · rw [h.mem_addBox_iff]
    rintro (hmem | hmem)
    · exact h.1 (μ.isLowerSet (Prod.mk_le_mk.mpr ⟨Nat.le_succ _, le_rfl⟩) hmem)
    · simp only [Prod.ext_iff] at hmem; omega

/-- Deleting the cell just added returns the original diagram. -/
theorem IsAddable.erase_addBox (h : IsAddable μ c) : erase (addBox μ c) c = μ := by
  ext d
  rw [mem_cells, mem_cells, h.isCorner_addBox.mem_erase_iff, h.mem_addBox_iff]
  refine ⟨fun hd => hd.1.resolve_right hd.2, fun hd => ⟨Or.inl hd, fun hcon => h.1 (hcon ▸ hd)⟩⟩

/-- A corner is addable to what is left after deleting it. -/
theorem IsCorner.isAddable_erase (h : IsCorner μ c) : IsAddable (erase μ c) c := by
  refine ⟨h.notMem_erase, fun d hd hne => ?_⟩
  refine h.mem_erase_iff.mpr ⟨μ.isLowerSet hd h.mem, hne⟩

/-- Putting a corner back returns the original diagram. -/
theorem IsCorner.addBox_erase (h : IsCorner μ c) : addBox (erase μ c) c = μ := by
  ext d
  rw [mem_cells, mem_cells, h.isAddable_erase.mem_addBox_iff, h.mem_erase_iff]
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · rcases hd with ⟨hd, -⟩ | rfl
    · exact hd
    · exact h.mem
  · by_cases hdc : d = c
    · exact Or.inr hdc
    · exact Or.inl ⟨hd, hdc⟩

/-! ### Row lengths -/

/-- A row length is pinned down by which cells of the row are present. -/
theorem rowLen_eq_of_mem {μ : YoungDiagram} {i n : ℕ} (h1 : ∀ b < n, ((i, b) : ℕ × ℕ) ∈ μ)
    (h2 : ((i, n) : ℕ × ℕ) ∉ μ) : μ.rowLen i = n := by
  rw [mem_iff_lt_rowLen] at h2
  push Not at h2
  by_contra hcon
  have hlt : μ.rowLen i < n := by omega
  have := mem_iff_lt_rowLen.mp (h1 _ hlt)
  omega

/-- Adding a cell lengthens its row by one and leaves the other rows alone. -/
theorem IsAddable.rowLen_addBox (h : IsAddable μ c) (i : ℕ) :
    (addBox μ c).rowLen i = if i = c.1 then μ.rowLen i + 1 else μ.rowLen i := by
  have hsnd := h.snd_eq
  split_ifs with hi
  · subst hi
    refine rowLen_eq_of_mem (fun b hb => h.mem_addBox_iff.mpr ?_) (h.mem_addBox_iff.not.mpr ?_)
    · rcases Nat.lt_or_ge b (μ.rowLen c.1) with hb' | hb'
      · exact Or.inl (mem_iff_lt_rowLen.mpr hb')
      · exact Or.inr (Prod.ext rfl (by omega))
    · push Not
      refine ⟨fun hmem => h.1 ?_, ?_⟩
      · exact μ.isLowerSet (Prod.mk_le_mk.mpr ⟨le_rfl, by omega⟩) hmem
      · simp only [ne_eq, Prod.ext_iff]; omega
  · refine rowLen_eq_of_mem (fun b hb => h.mem_addBox_iff.mpr (Or.inl (mem_iff_lt_rowLen.mpr hb)))
      (h.mem_addBox_iff.not.mpr ?_)
    push Not
    exact ⟨fun hmem => absurd (mem_iff_lt_rowLen.mp hmem) (lt_irrefl _),
      by simp only [ne_eq, Prod.ext_iff]; tauto⟩

/-- A corner sits at the end of its row, which is one longer than the row below it. -/
theorem isCorner_iff_rowLen {ν : YoungDiagram} {i b : ℕ} :
    IsCorner ν (i, b) ↔ b + 1 = ν.rowLen i ∧ ν.rowLen (i + 1) ≤ b := by
  simp only [isCorner_def, mem_iff_lt_rowLen, not_lt]
  omega

/-- A corner lies in a row of index below the height of the diagram. -/
theorem IsCorner.fst_lt_colLen {ν : YoungDiagram} {c : ℕ × ℕ} (h : IsCorner ν c) :
    c.1 < ν.colLen 0 := by
  have hmem : ((c.1, 0) : ℕ × ℕ) ∈ ν :=
    ν.isLowerSet (Prod.mk_le_mk.mpr ⟨le_rfl, Nat.zero_le _⟩) h.mem
  exact mem_iff_lt_colLen.mp hmem

/-- Deleting a corner shortens its row by one and leaves the other rows alone. -/
theorem IsCorner.rowLen_erase {ν : YoungDiagram} {c : ℕ × ℕ} (h : IsCorner ν c) (i : ℕ) :
    (erase ν c).rowLen i = if i = c.1 then ν.rowLen i - 1 else ν.rowLen i := by
  have hc : c.2 + 1 = ν.rowLen c.1 := (isCorner_iff_rowLen.mp (by simpa using h)).1
  split_ifs with hi
  · subst hi
    refine rowLen_eq_of_mem (fun b hb => h.mem_erase_iff.mpr ⟨?_, ?_⟩) ?_
    · exact mem_iff_lt_rowLen.mpr (by omega)
    · simp only [ne_eq, Prod.ext_iff]; omega
    · rw [h.mem_erase_iff]
      push Not
      intro _
      exact Prod.ext rfl (by omega)
  · refine rowLen_eq_of_mem (fun b hb => h.mem_erase_iff.mpr ⟨mem_iff_lt_rowLen.mpr hb, ?_⟩) ?_
    · simp only [ne_eq, Prod.ext_iff]; tauto
    · rw [h.mem_erase_iff]
      push Not
      exact fun hmem => absurd (mem_iff_lt_rowLen.mp hmem) (lt_irrefl _)

end YoungDiagram
