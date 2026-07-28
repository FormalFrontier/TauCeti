/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Move
public import TauCeti.KnotTheory.Grid.Diagram.Components

/-!
# Link components under grid commutation

An elementary grid commutation exchanges two adjacent, non-interleaving rows or columns. It
does not change the represented link, and the first combinatorial shadow of this fact is that it
preserves the component traversal. A row commutation leaves the component permutation unchanged.
A column commutation conjugates it by the transposition of the exchanged columns. Consequently
both moves preserve the multiset of component sizes, the number of components, and whether the
diagram represents a knot.

These results deliberately concern only component combinatorics. The later invariance proof for
grid homology attaches pentagon-counting chain maps to the same elementary commutations.

## Main results

* `TauCeti.GridDiagram.IsRowCommutation.componentPerm_eq`: row commutation leaves the component
  permutation unchanged.
* `TauCeti.GridDiagram.IsColumnCommutation.componentPerm_eq_conj`: column commutation conjugates
  the component permutation.
* `TauCeti.GridDiagram.IsCommutation.componentCycleType_eq`: every commutation preserves the
  multiset of component sizes.
* `TauCeti.GridDiagram.IsCommutation.componentCount_eq` and
  `TauCeti.GridDiagram.IsCommutation.isKnot_iff`: every commutation preserves component count and
  the knot predicate.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.5, "Invariance over
𝔽₂. Grid moves = commutation + (de)stabilization", by establishing that the already-defined
elementary commutations preserve the link-component data from Lane G.1. The grid-move convention
follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} {G G' : GridDiagram n}

/-- A row commutation leaves the component traversal permutation unchanged. -/
theorem IsRowCommutation.componentPerm_eq (h : IsRowCommutation G G') :
    G'.componentPerm = G.componentPerm := by
  rw [isRowCommutation_iff] at h
  rcases h with ⟨a, _, _, rfl⟩
  simp [GridDiagram.swapRows]

/-- A column commutation conjugates the component traversal permutation by the transposition
of the exchanged columns. -/
theorem IsColumnCommutation.componentPerm_eq_conj (h : IsColumnCommutation G G') :
    ∃ a : Fin n, G'.componentPerm =
      Equiv.swap a (finRotate n a) * G.componentPerm *
        (Equiv.swap a (finRotate n a))⁻¹ := by
  rw [isColumnCommutation_iff] at h
  rcases h with ⟨a, _, _, rfl⟩
  exact ⟨a, by
    simpa [GridDiagram.swapColumns] using
      componentPerm_relabelColumns G (Equiv.swap a (finRotate n a))⟩

/-- A row commutation preserves the multiset of component sizes. -/
theorem IsRowCommutation.componentCycleType_eq (h : IsRowCommutation G G') :
    G'.componentCycleType = G.componentCycleType := by
  rw [componentCycleType_def, h.componentPerm_eq, componentCycleType_def]

/-- A column commutation preserves the multiset of component sizes. -/
theorem IsColumnCommutation.componentCycleType_eq (h : IsColumnCommutation G G') :
    G'.componentCycleType = G.componentCycleType := by
  obtain ⟨a, ha⟩ := h.componentPerm_eq_conj
  rw [componentCycleType_def, ha, Equiv.Perm.cycleType_conj, componentCycleType_def]

/-- Every elementary commutation preserves the multiset of component sizes. -/
theorem IsCommutation.componentCycleType_eq (h : IsCommutation G G') :
    G'.componentCycleType = G.componentCycleType := by
  rw [isCommutation_iff] at h
  exact h.elim IsRowCommutation.componentCycleType_eq
    IsColumnCommutation.componentCycleType_eq

/-- Every elementary commutation preserves the number of represented link components. -/
theorem IsCommutation.componentCount_eq (h : IsCommutation G G') :
    G'.componentCount = G.componentCount := by
  rw [componentCount_def, h.componentCycleType_eq, componentCount_def]

/-- A row commutation preserves the number of represented link components. -/
theorem IsRowCommutation.componentCount_eq (h : IsRowCommutation G G') :
    G'.componentCount = G.componentCount :=
  (isCommutation_iff G G').mpr (Or.inl h) |>.componentCount_eq

/-- A column commutation preserves the number of represented link components. -/
theorem IsColumnCommutation.componentCount_eq (h : IsColumnCommutation G G') :
    G'.componentCount = G.componentCount :=
  (isCommutation_iff G G').mpr (Or.inr h) |>.componentCount_eq

/-- Every elementary commutation preserves whether a grid diagram represents a knot. -/
theorem IsCommutation.isKnot_iff (h : IsCommutation G G') :
    G'.IsKnot ↔ G.IsKnot := by
  rw [isKnot_def, h.componentCount_eq, isKnot_def]

/-- A row commutation preserves whether a grid diagram represents a knot. -/
theorem IsRowCommutation.isKnot_iff (h : IsRowCommutation G G') :
    G'.IsKnot ↔ G.IsKnot :=
  (isCommutation_iff G G').mpr (Or.inl h) |>.isKnot_iff

/-- A column commutation preserves whether a grid diagram represents a knot. -/
theorem IsColumnCommutation.isKnot_iff (h : IsColumnCommutation G G') :
    G'.IsKnot ↔ G.IsKnot :=
  (isCommutation_iff G G').mpr (Or.inr h) |>.isKnot_iff

end GridDiagram

end TauCeti
