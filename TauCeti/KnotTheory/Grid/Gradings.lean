/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.Ring
public import TauCeti.KnotTheory.Grid.JFunction.Center

/-!
# Maslov and Alexander gradings for grid states

This file records the rational-valued grading formulas for the grid-combinatorial lane of the
Heegaard Floer roadmap. The point-set `J`-function of a pair of grid states and the pairing of a
grid state against a set of marked squares were developed separately; here we use them to define
the `O`- and `X`-Maslov gradings and the Alexander grading of a grid state.

The `O`-Maslov grading is
`M_O(x) = J(x, x) - 2 J_O(x) + J(𝕆, 𝕆) + 1`, and the `X`-Maslov grading is defined analogously.
The middle term compares grid points against markings, so it uses the asymmetric marking pairing
`GridDiagram.JO` or `GridDiagram.JX` from `JFunction/Center.lean`, which accounts for the markings
sitting at the centres of their squares. The two outer terms compare like with like and use the
ordinary `J`-pairing.

The definitions are intentionally formula-level. The later integer-valuedness and
rectangle-change theorems can refer to these names without unfolding the point-pair count.

## Main definitions

* `TauCeti.GridDiagram.maslovO`, `TauCeti.GridDiagram.maslovX`: the two Maslov grading
  formulas attached to the `O` and `X` markings.
* `TauCeti.GridDiagram.alexander`: the Alexander grading formula.

## Main results

* `TauCeti.GridDiagram.maslovO_transpose`, `TauCeti.GridDiagram.maslovX_transpose`,
  `TauCeti.GridDiagram.alexander_transpose`: the Maslov and Alexander gradings are invariant
  under the diagonal reflection of a grid state and diagram.
* `TauCeti.GridDiagram.maslovO_swapMarkings`, `TauCeti.GridDiagram.maslovX_swapMarkings`: the
  two Maslov gradings are exchanged by the marking swap.
* `TauCeti.GridDiagram.alexander_swapMarkings`: the Alexander grading is negated up to the
  normalization shift under the marking swap.

## References

This supplies the grading-definition part of
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`,
Lane G.2, "Gradings. The `J`-function, `M_O`, `M_X`, `A`; integer-valuedness of `A`;
grading-change formulas across a rectangle." The grading conventions follow
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.2, with markings realized
at the centres of their squares. In particular,
`A(x) = (M_O(x) - M_X(x)) / 2 - (n - 1) / 2`.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The `O`-Maslov grading of a grid state: the state and marking self-pairings, minus twice the
asymmetric pairing of the state against the `O`-markings, plus the normalization constant. -/
@[expose] def maslovO (x : GridState n) : ℚ :=
  GridState.J x x - 2 * G.JO x + GridState.J G.O G.O + 1

/-- The `O`-Maslov grading as its defining formula. -/
@[simp]
theorem maslovO_def (x : GridState n) :
    G.maslovO x = GridState.J x x - 2 * G.JO x + GridState.J G.O G.O + 1 :=
  rfl

/-- The `X`-Maslov grading of a grid state: the state and marking self-pairings, minus twice the
asymmetric pairing of the state against the `X`-markings, plus the normalization constant. -/
@[expose] def maslovX (x : GridState n) : ℚ :=
  GridState.J x x - 2 * G.JX x + GridState.J G.X G.X + 1

/-- The `X`-Maslov grading as its defining formula. -/
@[simp]
theorem maslovX_def (x : GridState n) :
    G.maslovX x = GridState.J x x - 2 * G.JX x + GridState.J G.X G.X + 1 :=
  rfl

/-- The Alexander grading of a grid state.

This is the formula `A(x) = (M_O(x) - M_X(x)) / 2 - (n - 1) / 2`. The shift is cast
through `ℤ`, so the formula remains literal at `n = 0`; integer-valuedness is a later grading
theorem. -/
@[expose] def alexander (x : GridState n) : ℚ :=
  (G.maslovO x - G.maslovX x) / 2 - (((n : ℤ) - 1 : ℤ) : ℚ) / 2

/-- The Alexander grading as the difference of the two Maslov gradings with the standard
normalization shift. -/
@[simp]
theorem alexander_def (x : GridState n) :
    G.alexander x =
      (G.maslovO x - G.maslovX x) / 2 - (((n : ℤ) - 1 : ℤ) : ℚ) / 2 :=
  rfl

/-- The Alexander grading with the two Maslov formulas expanded. -/
theorem alexander_eq (x : GridState n) :
    G.alexander x =
      (2 * (G.JX x - G.JO x) + (GridState.J G.O G.O - GridState.J G.X G.X) -
        (((n : ℤ) - 1 : ℤ) : ℚ)) / 2 := by
  rw [alexander, maslovO_def, maslovX_def]
  ring

/-- The difference of the two Maslov gradings is twice the Alexander grading plus the
normalization shift. -/
theorem maslovO_sub_maslovX_eq (x : GridState n) :
    G.maslovO x - G.maslovX x =
      2 * G.alexander x + (((n : ℤ) - 1 : ℤ) : ℚ) := by
  rw [alexander]
  ring

/-- Replacing the two Maslov gradings by the same value leaves only the normalization shift in
the Alexander formula. -/
theorem alexander_eq_neg_shift_of_maslov_eq {x : GridState n} (h : G.maslovO x = G.maslovX x) :
    G.alexander x = -(((n : ℤ) - 1 : ℤ) : ℚ) / 2 := by
  rw [alexander, h]
  ring

/-- The `O`-Maslov grading is invariant under the diagonal reflection. -/
theorem maslovO_transpose (x : GridState n) :
    G.transpose.maslovO x.transpose = G.maslovO x := by
  rw [maslovO_def, maslovO_def, JO_transpose, transpose_O, GridState.J_transpose,
    GridState.J_transpose]

/-- The `X`-Maslov grading is invariant under the diagonal reflection. -/
theorem maslovX_transpose (x : GridState n) :
    G.transpose.maslovX x.transpose = G.maslovX x := by
  rw [maslovX_def, maslovX_def, JX_transpose, transpose_X, GridState.J_transpose,
    GridState.J_transpose]

/-- The Alexander grading is invariant under the diagonal reflection. The normalization shift
depends only on the common grid size, so it cancels between the two diagrams. -/
theorem alexander_transpose (x : GridState n) :
    G.transpose.alexander x.transpose = G.alexander x := by
  rw [alexander_def, alexander_def, maslovO_transpose, maslovX_transpose]

/-- The marking swap exchanges the two Maslov gradings: `M_O` of the swap is `M_X`. -/
@[simp]
theorem maslovO_swapMarkings (x : GridState n) :
    G.swapMarkings.maslovO x = G.maslovX x := by
  rw [maslovO_def, maslovX_def, JO_swapMarkings, swapMarkings_O]

/-- The marking swap exchanges the two Maslov gradings: `M_X` of the swap is `M_O`. -/
@[simp]
theorem maslovX_swapMarkings (x : GridState n) :
    G.swapMarkings.maslovX x = G.maslovO x := by
  rw [maslovX_def, maslovO_def, JX_swapMarkings, swapMarkings_X]

/-- The marking swap negates the Alexander grading, up to the constant normalization shift:
  `A_swap(x) = -A(x) - (n - 1)`. The grading is built antisymmetrically from the two Maslov
  gradings, which the swap exchanges, while the shift depends only on the grid size. -/
theorem alexander_swapMarkings (x : GridState n) :
    G.swapMarkings.alexander x = -G.alexander x - (((n : ℤ) - 1 : ℤ) : ℚ) := by
  rw [alexander_def, alexander_def, maslovO_swapMarkings, maslovX_swapMarkings]
  ring

end GridDiagram

end TauCeti
