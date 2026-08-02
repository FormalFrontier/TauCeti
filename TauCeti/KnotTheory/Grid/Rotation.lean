/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Fin.Rev
public import TauCeti.KnotTheory.Grid.Diagram.Basic

/-!
# The half-turn rotation of grid states and diagrams

This file adds the `180°` rotation of the toroidal grid to the grid-combinatorial lane of the
Heegaard Floer roadmap, alongside the already-developed diagonal reflection (`transpose`) and
marking swap (`swapMarkings`). Rotation reverses both the column and the row coordinate, so on
grid squares it is the map `(c, r) ↦ (cᵒ, rᵒ)` with `·ᵒ = Fin.rev`. It is the composition of the
column and row relabelings by the coordinate reversal `Fin.revPerm`, so it reuses the existing
relabeling API rather than introducing a new primitive. It carries a grid state to a grid state
and a grid diagram to a grid diagram.

Only the basic state/diagram operation and its point-set lemmas live here, parallel to where
`transpose` is developed; the invariance of the `J`-function under coordinate reversal is in
`TauCeti.KnotTheory.Grid.JFunction.Basic`, and the resulting grading invariance is in
`TauCeti.KnotTheory.Grid.Gradings` and `TauCeti.KnotTheory.Grid.Grading.Integer`.

## Main definitions

* `TauCeti.GridState.rotate`: the half-turn rotation of a grid state.
* `TauCeti.GridDiagram.rotate`: the half-turn rotation of a grid diagram.

## Main results

* `TauCeti.GridState.rotate_rotate`, `TauCeti.GridDiagram.rotate_rotate`: rotation is an
  involution on grid states and grid diagrams.
* `TauCeti.GridState.rotate_pointSet`, `TauCeti.GridDiagram.rotate_OSet`,
  `TauCeti.GridDiagram.rotate_XSet`: the point sets of a rotated state or diagram are the
  half-turn rotation of the original point sets.
* `TauCeti.GridState.relabelRows_rotate`, `TauCeti.GridState.relabelColumns_rotate`,
  `TauCeti.GridDiagram.swapMarkings_rotate`: rotation interacts predictably with the existing
  relabeling, swap, and marking-swap operations.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G item 8,
"Symmetries and the genus bound": the half-turn rotation of a grid diagram is one of the
standard grid symmetries of Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*,
Chapter 3.
-/

@[expose] public section

namespace TauCeti

variable {n : ℕ}

/-- Reversing both coordinates of a grid square twice returns the original square. -/
private theorem rev2_rev2 (p : Fin n × Fin n) :
    Prod.map Fin.rev Fin.rev (Prod.map Fin.rev Fin.rev p) = p := by
  obtain ⟨a, b⟩ := p
  simp [Fin.rev_rev]

/-- Conjugating a row or column swap by coordinate reversal swaps the reversed indices. -/
private theorem revPerm_trans_swap_trans_revPerm (a b : Fin n) :
    Fin.revPerm.trans ((Equiv.swap a b).trans Fin.revPerm) = Equiv.swap a.rev b.rev := by
  ext c
  by_cases hca : c = a.rev
  · subst hca
    simp
  · by_cases hcb : c = b.rev
    · subst hcb
      simp
    · have hca' : c.rev ≠ a := by
        intro h
        exact hca (Fin.rev_eq_iff.mp h)
      have hcb' : c.rev ≠ b := by
        intro h
        exact hcb (Fin.rev_eq_iff.mp h)
      simp [Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.swap_apply_of_ne_of_ne hca' hcb',
        Fin.rev_rev]

namespace GridState

/-- The half-turn rotation of a grid state.

Rotating the occupied squares by `180°` reverses both the column and the row coordinate. It is
the composition of the column and row relabelings by the coordinate reversal `Fin.revPerm`. -/
def rotate (x : GridState n) : GridState n :=
  (x.relabelColumns Fin.revPerm).relabelRows Fin.revPerm

/-- The rotated state reads off a column by reversing it, applying the original state, and
reversing the resulting row. -/
@[simp]
theorem rotate_apply (x : GridState n) (c : Fin n) :
    x.rotate c = (x (Fin.rev c)).rev := by
  simp [rotate]

/-- In the rotated state, the occupied square in row `r` lies in the reversed column of the
occupied square in row `r.rev` of the original state. -/
theorem columnOfRow_rotate (x : GridState n) (r : Fin n) :
    x.rotate.columnOfRow r = (x.columnOfRow r.rev).rev := by
  apply x.rotate.toPerm.injective
  simp [GridState.rotate_apply, Fin.rev_rev]

/-- A square lies in the rotated state exactly when its half-turn rotation lies in the original
state. -/
theorem mem_pointSet_rotate (x : GridState n) (p : Fin n × Fin n) :
    p ∈ x.rotate.pointSet ↔ Prod.map Fin.rev Fin.rev p ∈ x.pointSet := by
  simp only [mem_pointSet, rotate_apply, Prod.map_fst, Prod.map_snd, Fin.rev_eq_iff]

/-- The point set of the rotated state is the half-turn rotation of the original point set. -/
theorem rotate_pointSet (x : GridState n) :
    x.rotate.pointSet = x.pointSet.image (Prod.map Fin.rev Fin.rev) := by
  ext p
  rw [mem_pointSet_rotate, Finset.mem_image]
  constructor
  · intro hp
    exact ⟨Prod.map Fin.rev Fin.rev p, hp, rev2_rev2 p⟩
  · rintro ⟨q, hq, rfl⟩
    rwa [rev2_rev2 q]

/-- The half-turn rotation is an involution on grid states. -/
@[simp]
theorem rotate_rotate (x : GridState n) : x.rotate.rotate = x := by
  ext c
  simp [Fin.rev_rev]

/-- Diagonal reflection commutes with the half-turn rotation of a grid state. -/
@[simp]
theorem transpose_rotate (x : GridState n) : x.transpose.rotate = x.rotate.transpose := by
  simp [rotate, GridState.relabelRows_relabelColumns]

/-- Row relabeling before rotation becomes row relabeling by the conjugate permutation after
rotation. -/
@[simp]
theorem relabelRows_rotate (ρ : Equiv.Perm (Fin n)) (x : GridState n) :
    (x.relabelRows ρ).rotate = x.rotate.relabelRows (Fin.revPerm.trans (ρ.trans Fin.revPerm)) := by
  ext c
  simp [rotate, Fin.rev_rev]

/-- Column relabeling before rotation becomes column relabeling by the conjugate permutation
after rotation. -/
@[simp]
theorem relabelColumns_rotate (κ : Equiv.Perm (Fin n)) (x : GridState n) :
    (x.relabelColumns κ).rotate =
      x.rotate.relabelColumns (Fin.revPerm.trans (κ.trans Fin.revPerm)) := by
  ext c
  simp [rotate, Fin.rev_rev]

/-- Swapping rows before rotation is the same as swapping the reversed rows after rotation. -/
@[simp]
theorem swapRows_rotate (a b : Fin n) (x : GridState n) :
    (x.swapRows a b).rotate = x.rotate.swapRows a.rev b.rev := by
  rw [swapRows, relabelRows_rotate, revPerm_trans_swap_trans_revPerm]
  rfl

/-- Swapping columns before rotation is the same as swapping the reversed columns after
rotation. -/
@[simp]
theorem swapColumns_rotate (a b : Fin n) (x : GridState n) :
    (x.swapColumns a b).rotate = x.rotate.swapColumns a.rev b.rev := by
  rw [swapColumns, relabelColumns_rotate, revPerm_trans_swap_trans_revPerm]
  rfl

end GridState

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The half-turn rotation of a grid diagram, rotating both marking states.

It is the composition of the column and row relabelings by the coordinate reversal `Fin.revPerm`,
applied to both marking states at once. Each relabeling is again a grid diagram, so rotation
preserves the condition that no square carries both an `O` and an `X` marking. -/
def rotate (G : GridDiagram n) : GridDiagram n :=
  (G.relabelColumns Fin.revPerm).relabelRows Fin.revPerm

/-- The `O`-marking state of the rotated diagram is the rotation of the original `O`-state. -/
@[simp]
theorem rotate_O : G.rotate.O = G.O.rotate :=
  rfl

/-- The `X`-marking state of the rotated diagram is the rotation of the original `X`-state. -/
@[simp]
theorem rotate_X : G.rotate.X = G.X.rotate :=
  rfl

/-- In the rotated diagram, the `O` marking in row `r` lies in the reversed column of the
original `O` marking in row `r.rev`. -/
@[simp]
theorem OColumnOfRow_rotate (r : Fin n) :
    OColumnOfRow G.rotate r = (OColumnOfRow G r.rev).rev :=
  GridState.columnOfRow_rotate G.O r

/-- In the rotated diagram, the `X` marking in row `r` lies in the reversed column of the
original `X` marking in row `r.rev`. -/
@[simp]
theorem XColumnOfRow_rotate (r : Fin n) :
    XColumnOfRow G.rotate r = (XColumnOfRow G r.rev).rev :=
  GridState.columnOfRow_rotate G.X r

/-- The `O`-markings of the rotated diagram are the half-turn rotation of the original
`O`-markings. -/
theorem rotate_OSet : G.rotate.OSet = G.OSet.image (Prod.map Fin.rev Fin.rev) :=
  GridState.rotate_pointSet G.O

/-- The `X`-markings of the rotated diagram are the half-turn rotation of the original
`X`-markings. -/
theorem rotate_XSet : G.rotate.XSet = G.XSet.image (Prod.map Fin.rev Fin.rev) :=
  GridState.rotate_pointSet G.X

/-- A square lies in the rotated diagram's `O`-marking set exactly when its half-turn rotation
lies in the original `O`-marking set. -/
theorem mem_OSet_rotate (p : Fin n × Fin n) :
    p ∈ G.rotate.OSet ↔ Prod.map Fin.rev Fin.rev p ∈ G.OSet := by
  rw [OSet, OSet, rotate_O]
  exact GridState.mem_pointSet_rotate G.O p

/-- A square lies in the rotated diagram's `X`-marking set exactly when its half-turn rotation
lies in the original `X`-marking set. -/
theorem mem_XSet_rotate (p : Fin n × Fin n) :
    p ∈ G.rotate.XSet ↔ Prod.map Fin.rev Fin.rev p ∈ G.XSet := by
  rw [XSet, XSet, rotate_X]
  exact GridState.mem_pointSet_rotate G.X p

/-- The half-turn rotation is an involution on grid diagrams. -/
@[simp]
theorem rotate_rotate : G.rotate.rotate = G := by
  ext c <;> simp

/-- Diagonal reflection commutes with the half-turn rotation of a grid diagram. -/
@[simp]
theorem transpose_rotate : G.transpose.rotate = G.rotate.transpose := by
  ext c <;> simp [GridState.transpose_rotate]

/-- Row relabeling before rotation becomes row relabeling by the conjugate permutation after
rotation. -/
@[simp]
theorem relabelRows_rotate (ρ : Equiv.Perm (Fin n)) :
    (G.relabelRows ρ).rotate = G.rotate.relabelRows (Fin.revPerm.trans (ρ.trans Fin.revPerm)) := by
  ext c <;> simp

/-- Column relabeling before rotation becomes column relabeling by the conjugate permutation
after rotation. -/
@[simp]
theorem relabelColumns_rotate (κ : Equiv.Perm (Fin n)) : (G.relabelColumns κ).rotate =
      G.rotate.relabelColumns (Fin.revPerm.trans (κ.trans Fin.revPerm)) := by
  ext c <;> simp

/-- Swapping rows before rotation is the same as swapping the reversed rows after rotation. -/
@[simp]
theorem swapRows_rotate (a b : Fin n) :
    (G.swapRows a b).rotate = G.rotate.swapRows a.rev b.rev := by
  rw [swapRows, relabelRows_rotate, revPerm_trans_swap_trans_revPerm]
  rfl

/-- Swapping columns before rotation is the same as swapping the reversed columns after
rotation. -/
@[simp]
theorem swapColumns_rotate (a b : Fin n) :
    (G.swapColumns a b).rotate = G.rotate.swapColumns a.rev b.rev := by
  rw [swapColumns, relabelColumns_rotate, revPerm_trans_swap_trans_revPerm]
  rfl

/-- Exchanging the two marking states commutes with the half-turn rotation. -/
@[simp]
theorem swapMarkings_rotate : G.swapMarkings.rotate = G.rotate.swapMarkings := by
  ext c <;> simp [GridDiagram.rotate]

end GridDiagram

end TauCeti
