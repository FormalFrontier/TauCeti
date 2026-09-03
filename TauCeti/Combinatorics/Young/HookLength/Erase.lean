/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.HookLength.Basic

/-!
# Hook lengths after erasing a corner

Erasing a corner `c` from a Young diagram shortens precisely the hooks based strictly to the left
of `c` in its row and strictly above `c` in its column. The row- and column-length comparisons
live with the erasure API in `TauCeti.Combinatorics.Young.Corner`; this file applies them to hook
lengths, proves the three pointwise cases, and packages them as a single conditional formula.

The final product identity rewrites the hook product of the smaller diagram entirely in terms of
the hooks of the original diagram. It is the local input needed to combine the corner recursion
for `standardCount` with the hook-product recurrence in the multiplicative hook-length formula.

## Main results

* `YoungDiagram.IsCorner.rowLen_erase` and `YoungDiagram.IsCorner.colLen_erase` describe the row and
  column lengths after a corner is erased.
* `YoungDiagram.IsCorner.hookLength_erase_of_same_row` and
  `YoungDiagram.IsCorner.hookLength_erase_of_same_col` say that the affected hooks drop by one.
* `YoungDiagram.IsCorner.hookLength_erase` is the combined pointwise comparison.
* `YoungDiagram.IsCorner.prod_hookLength_erase` compares the complete hook products.

## References

* [B. E. Sagan, *The Symmetric Group*][sagan2001], Section 3.10.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 5: the multiplicative hook-length formula.
-/

public section

namespace YoungDiagram

variable {μ : YoungDiagram} {c d : ℕ × ℕ} {i j : ℕ}

namespace IsCorner

/-! ### Pointwise hook-length comparison -/

/-- A surviving cell in the corner's row lies strictly to its left. -/
private theorem snd_lt_of_mem_erase_of_fst_eq (h : IsCorner μ c) (hd : d ∈ erase μ c)
    (hrow : d.1 = c.1) : d.2 < c.2 := by
  have hdmem := _root_.YoungDiagram.mem_iff_lt_rowLen.mp (mem_of_mem_erase hd)
  have hdne := (h.mem_erase_iff.mp hd).2
  have hsnd : d.2 ≠ c.2 := fun hsnd => hdne (Prod.ext hrow hsnd)
  rw [hrow, h.rowLen_eq_snd_add_one] at hdmem
  omega

/-- A surviving cell in the corner's column lies strictly above it. -/
private theorem fst_lt_of_mem_erase_of_snd_eq (h : IsCorner μ c) (hd : d ∈ erase μ c)
    (hcol : d.2 = c.2) : d.1 < c.1 := by
  have hdmem := _root_.YoungDiagram.mem_iff_lt_colLen.mp (mem_of_mem_erase hd)
  have hdne := (h.mem_erase_iff.mp hd).2
  have hfst : d.1 ≠ c.1 := fun hfst => hdne (Prod.ext hfst hcol)
  rw [hcol, h.colLen_eq_fst_add_one] at hdmem
  omega

/-- Erasing a corner decreases by one the hook length of every surviving cell in its row. -/
theorem hookLength_erase_of_same_row (h : IsCorner μ c) (hd : d ∈ erase μ c)
    (hrow : d.1 = c.1) : hookLength (erase μ c) d + 1 = hookLength μ d := by
  have hdcol : d.2 ≠ c.2 := by
    intro heq
    exact (h.mem_erase_iff.mp hd).2 (Prod.ext hrow heq)
  have hdlt := h.snd_lt_of_mem_erase_of_fst_eq hd hrow
  simp only [hookLength_def, armLength_def, legLength_def, h.rowLen_erase, h.colLen_erase,
    ite_eq_left hrow.symm, ite_eq_right hdcol.symm]
  have hrowlen := h.rowLen_eq_snd_add_one
  rw [← hrow] at hrowlen
  omega

/-- Erasing a corner decreases by one the hook length of every surviving cell in its column. -/
theorem hookLength_erase_of_same_col (h : IsCorner μ c) (hd : d ∈ erase μ c)
    (hcol : d.2 = c.2) : hookLength (erase μ c) d + 1 = hookLength μ d := by
  have hdrow : d.1 ≠ c.1 := by
    intro heq
    exact (h.mem_erase_iff.mp hd).2 (Prod.ext heq hcol)
  have hdlt := h.fst_lt_of_mem_erase_of_snd_eq hd hcol
  simp only [hookLength_def, armLength_def, legLength_def, h.rowLen_erase, h.colLen_erase,
    ite_eq_right hdrow.symm, ite_eq_left hcol.symm]
  have hcollen := h.colLen_eq_fst_add_one
  rw [← hcol] at hcollen
  omega

/-- Erasing a corner leaves unchanged the hook length of a cell outside its row and column. -/
theorem hookLength_erase_of_ne_row_of_ne_col (h : IsCorner μ c)
    (hrow : d.1 ≠ c.1) (hcol : d.2 ≠ c.2) :
    hookLength (erase μ c) d = hookLength μ d := by
  simp only [hookLength_def, armLength_def, legLength_def, h.rowLen_erase, h.colLen_erase,
    ite_eq_right hrow.symm, ite_eq_right hcol.symm]

/-- **Hook lengths under corner erasure.** A surviving hook drops by one exactly when its base cell
lies in the erased corner's row or column; every other hook is unchanged. -/
@[simp]
theorem hookLength_erase (h : IsCorner μ c) (hd : d ∈ erase μ c) :
    hookLength (erase μ c) d =
      if d.1 = c.1 ∨ d.2 = c.2 then hookLength μ d - 1 else hookLength μ d := by
  by_cases hrow : d.1 = c.1
  · rw [ite_eq_left (Or.inl hrow)]
    have hdrop := h.hookLength_erase_of_same_row hd hrow
    omega
  by_cases hcol : d.2 = c.2
  · rw [ite_eq_left (Or.inr hcol)]
    have hdrop := h.hookLength_erase_of_same_col hd hcol
    omega
  · rw [ite_eq_right (not_or_intro hrow hcol)]
    exact h.hookLength_erase_of_ne_row_of_ne_col hrow hcol

/-! ### The hook product after erasure -/

/-- **The hook product after erasing a corner**, expressed using only the original diagram: remove
the corner's own factor, subtract one from the hooks based in its row or column, and leave all
other factors unchanged. -/
theorem prod_hookLength_erase (h : IsCorner μ c) :
    ∏ d ∈ (erase μ c).cells, hookLength (erase μ c) d =
      ∏ d ∈ μ.cells.erase c,
        if d.1 = c.1 ∨ d.2 = c.2 then hookLength μ d - 1 else hookLength μ d := by
  rw [h.cells_erase]
  apply Finset.prod_congr rfl
  intro d hd
  rw [h.hookLength_erase]
  exact h.mem_erase_iff.mpr ⟨Finset.mem_of_mem_erase hd, Finset.ne_of_mem_erase hd⟩

end IsCorner

end YoungDiagram
