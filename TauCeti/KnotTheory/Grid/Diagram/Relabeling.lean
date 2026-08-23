/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Diagram.Basic

/-!
# Relabeling and column-of-row lookups

This file records how relabeling and swapping rows or columns transports the column-of-row
lookups of a grid state and the `O`/`X` column-of-row lookups of a grid diagram. These formulas
depend only on the relabeling API of `Diagram.lean`; they are the lookup analogue of the existing
`OColumnOfRow_apply`/`relabelColumns_O_apply` simp lemmas there, split into their own file only to
respect the file-length limit.

A row relabeling reads the lookup at the inverse row label, a column relabeling applies the column
permutation to the resulting column, and the swap corollaries specialize these to the elementary
grid commutations.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane
G.5, "Invariance over 𝔽₂. Grid moves = commutation + (de)stabilization". The conventions follow
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace GridState

variable {n : ℕ} (x : GridState n)

/-- Row relabeling moves the column containing a given row by reading the old state at the
inverse row label. -/
theorem columnOfRow_relabelRows (ρ : Equiv.Perm (Fin n)) (r : Fin n) :
    (x.relabelRows ρ).columnOfRow r = x.columnOfRow (ρ.symm r) := by
  apply (x.relabelRows ρ).toPerm.injective
  simp

/-- Column relabeling moves the column containing a given row by applying the column permutation
to the old column. -/
theorem columnOfRow_relabelColumns (κ : Equiv.Perm (Fin n)) (r : Fin n) :
    (x.relabelColumns κ).columnOfRow r = κ (x.columnOfRow r) := by
  apply (x.relabelColumns κ).toPerm.injective
  simp

/-- After swapping rows, the column containing row `r` is the old column containing the swapped
row label. -/
theorem columnOfRow_swapRows (a b r : Fin n) :
    (x.swapRows a b).columnOfRow r = x.columnOfRow (Equiv.swap a b r) := by
  simp [swapRows]

/-- After swapping columns, the column containing row `r` is the swap of the old column
containing that row. -/
theorem columnOfRow_swapColumns (a b r : Fin n) :
    (x.swapColumns a b).columnOfRow r = Equiv.swap a b (x.columnOfRow r) := by
  simp [swapColumns]

end GridState

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- Row relabeling moves the `O` column lookup by reading the old diagram at the inverse row
label. -/
@[simp]
theorem OColumnOfRow_relabelRows (ρ : Equiv.Perm (Fin n)) (r : Fin n) :
    OColumnOfRow (G.relabelRows ρ) r = OColumnOfRow G (ρ.symm r) := by
  simp [OColumnOfRow]

/-- Row relabeling moves the `X` column lookup by reading the old diagram at the inverse row
label. -/
@[simp]
theorem XColumnOfRow_relabelRows (ρ : Equiv.Perm (Fin n)) (r : Fin n) :
    XColumnOfRow (G.relabelRows ρ) r = XColumnOfRow G (ρ.symm r) := by
  simp [XColumnOfRow]

/-- Column relabeling moves the `O` column lookup by applying the column permutation to the old
lookup. -/
@[simp]
theorem OColumnOfRow_relabelColumns (κ : Equiv.Perm (Fin n)) (r : Fin n) :
    OColumnOfRow (G.relabelColumns κ) r = κ (OColumnOfRow G r) := by
  simp [OColumnOfRow]

/-- Column relabeling moves the `X` column lookup by applying the column permutation to the old
lookup. -/
@[simp]
theorem XColumnOfRow_relabelColumns (κ : Equiv.Perm (Fin n)) (r : Fin n) :
    XColumnOfRow (G.relabelColumns κ) r = κ (XColumnOfRow G r) := by
  simp [XColumnOfRow]

/-- After swapping rows, the `O` marking in row `r` lies in the old `O` column for the swapped
row label. -/
@[simp]
theorem OColumnOfRow_swapRows (a b r : Fin n) :
    OColumnOfRow (G.swapRows a b) r = OColumnOfRow G (Equiv.swap a b r) := by
  simp [swapRows]

/-- After swapping rows, the `X` marking in row `r` lies in the old `X` column for the swapped
row label. -/
@[simp]
theorem XColumnOfRow_swapRows (a b r : Fin n) :
    XColumnOfRow (G.swapRows a b) r = XColumnOfRow G (Equiv.swap a b r) := by
  simp [swapRows]

/-- After swapping columns, the `O` marking in row `r` lies in the swapped old `O` column. -/
@[simp]
theorem OColumnOfRow_swapColumns (a b r : Fin n) :
    OColumnOfRow (G.swapColumns a b) r = Equiv.swap a b (OColumnOfRow G r) := by
  simp [swapColumns]

/-- After swapping columns, the `X` marking in row `r` lies in the swapped old `X` column. -/
@[simp]
theorem XColumnOfRow_swapColumns (a b r : Fin n) :
    XColumnOfRow (G.swapColumns a b) r = Equiv.swap a b (XColumnOfRow G r) := by
  simp [swapColumns]

end GridDiagram

end TauCeti
