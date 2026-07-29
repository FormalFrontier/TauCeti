/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.KnotTheory.Grid.Unknot
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# The standard two-by-two grid grading computation

This file records the first explicit grading calculation for the grid-combinatorial lane.
There are exactly two grid states in grid size two: the identity graph and the transposition
graph. The standard `2 × 2` grid diagram used for the unknot has `O` markings on the identity
graph and `X` markings on the transposition graph.

The named states are available from `StateCardinality` and the standard diagram itself from
`Unknot`, where it is the smallest member of the unknot grid family. Here we combine that
small-grid API with the integer grading API to compute the two generators' Maslov and Alexander
gradings in this concrete diagram.

## Main results

* `TauCeti.GridDiagram.maslovOℤ_twoByTwo_twoByTwoId`,
  `TauCeti.GridDiagram.maslovXℤ_twoByTwo_twoByTwoId`,
  `TauCeti.GridDiagram.alexander_twoByTwo_twoByTwoId`, and the corresponding `twoByTwoSwap`
  lemmas: the exact small-grid bigrading data.
* `TauCeti.GridDiagram.alexander_eq_neg_one_or_eq_zero_of_two`: in any `2 × 2` diagram every
  generator has Alexander grading `-1` or `0`.

## References

This supplies a small prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`,
Lane G.3, "The complexes and `∂² = 0`", and the acceptance criterion that grid homology
compute on the `2 × 2` unknot grid with its bigradings. The grid and grading conventions
follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 3 and 4.
-/

public section

namespace TauCeti

namespace GridDiagram

/-- The standard two-by-two diagram has `O` markings at `(0,0)` and `(1,1)`. -/
@[simp]
theorem twoByTwo_OSet :
    twoByTwo.OSet = {(0, 0), (1, 1)} := by
  ext p
  rcases p with ⟨c, r⟩
  fin_cases c <;> fin_cases r <;> simp [OSet]

/-- The standard two-by-two diagram has `X` markings at `(0,1)` and `(1,0)`. -/
@[simp]
theorem twoByTwo_XSet :
    twoByTwo.XSet = {(0, 1), (1, 0)} := by
  ext p
  rcases p with ⟨c, r⟩
  fin_cases c <;> fin_cases r <;> simp [XSet]

private theorem twoByTwoId_pairCard_self :
    (Finset.univ.filter fun p : Fin 2 × Fin 2 =>
      p.1 < p.2 ∧ GridState.twoByTwoId p.1 < GridState.twoByTwoId p.2).card = 1 := by
  have hfilter : (Finset.univ.filter fun p : Fin 2 × Fin 2 =>
      p.1 < p.2 ∧ GridState.twoByTwoId p.1 < GridState.twoByTwoId p.2) = {(0, 1)} := by
    ext p
    rcases p with ⟨c, r⟩
    fin_cases c <;> fin_cases r <;> simp
  rw [hfilter]
  simp

private theorem twoByTwoSwap_pairCard_self :
    (Finset.univ.filter fun p : Fin 2 × Fin 2 =>
      p.1 < p.2 ∧ GridState.twoByTwoSwap p.1 < GridState.twoByTwoSwap p.2).card = 0 := by
  have hfilter : (Finset.univ.filter fun p : Fin 2 × Fin 2 =>
      p.1 < p.2 ∧ GridState.twoByTwoSwap p.1 < GridState.twoByTwoSwap p.2) = ∅ := by
    ext p
    rcases p with ⟨c, r⟩
    fin_cases c <;> fin_cases r <;> simp
  rw [hfilter]
  simp

private theorem twoByTwoId_pairCard_swap :
    (Finset.univ.filter fun p : Fin 2 × Fin 2 =>
      p.1 < p.2 ∧ GridState.twoByTwoId p.1 < GridState.twoByTwoSwap p.2).card = 0 := by
  have hfilter : (Finset.univ.filter fun p : Fin 2 × Fin 2 =>
      p.1 < p.2 ∧ GridState.twoByTwoId p.1 < GridState.twoByTwoSwap p.2) = ∅ := by
    ext p
    rcases p with ⟨c, r⟩
    fin_cases c <;> fin_cases r <;> simp
  rw [hfilter]
  simp

private theorem twoByTwoSwap_pairCard_id :
    (Finset.univ.filter fun p : Fin 2 × Fin 2 =>
      p.1 < p.2 ∧ GridState.twoByTwoSwap p.1 < GridState.twoByTwoId p.2).card = 0 := by
  have hfilter : (Finset.univ.filter fun p : Fin 2 × Fin 2 =>
      p.1 < p.2 ∧ GridState.twoByTwoSwap p.1 < GridState.twoByTwoId p.2) = ∅ := by
    ext p
    rcases p with ⟨c, r⟩
    fin_cases c <;> fin_cases r <;> simp
  rw [hfilter]
  simp

/-- In a `2 × 2` diagram, the integer `X`-Maslov grading of the `O`-marking state is `2`. -/
theorem maslovXℤ_O_of_two (G : GridDiagram 2) : G.maslovXℤ G.O = 2 := by
  rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap G.O with hO | hO
  · rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap G.X with hX | hX
    · exfalso
      exact G.disjoint 0 (by simp [hO, hX])
    · rw [maslovXℤ_eq_card, hO, hX]
      rw [twoByTwoId_pairCard_self, twoByTwoId_pairCard_swap, twoByTwoSwap_pairCard_id,
        twoByTwoSwap_pairCard_self]
      norm_num
  · rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap G.X with hX | hX
    · rw [maslovXℤ_eq_card, hO, hX]
      rw [twoByTwoSwap_pairCard_self, twoByTwoSwap_pairCard_id, twoByTwoId_pairCard_swap,
        twoByTwoId_pairCard_self]
      norm_num
    · exfalso
      exact G.disjoint 0 (by simp [hO, hX])

/-- In a `2 × 2` diagram, the integer `O`-Maslov grading of the `X`-marking state is `2`. -/
theorem maslovOℤ_X_of_two (G : GridDiagram 2) : G.maslovOℤ G.X = 2 := by
  simpa using maslovXℤ_O_of_two G.swapMarkings

/-- Twice the Alexander grading of the `O`-marking state in a `2 × 2` diagram is `-2`. -/
theorem alexanderTwoℤ_O_of_two (G : GridDiagram 2) : G.alexanderTwoℤ G.O = -2 := by
  rw [alexanderTwoℤ_def, maslovOℤ_O, maslovXℤ_O_of_two]
  norm_num

/-- Twice the Alexander grading of the `X`-marking state in a `2 × 2` diagram is `0`. -/
theorem alexanderTwoℤ_X_of_two (G : GridDiagram 2) : G.alexanderTwoℤ G.X = 0 := by
  rw [alexanderTwoℤ_def, maslovOℤ_X_of_two, maslovXℤ_X]
  norm_num

/-- The Alexander grading of the `O`-marking state in a `2 × 2` diagram is `-1`. -/
theorem alexander_O_of_two (G : GridDiagram 2) : G.alexander G.O = -1 := by
  rw [alexander_def, G.maslovO_eq_intCast, G.maslovX_eq_intCast]
  rw [maslovOℤ_O, maslovXℤ_O_of_two]
  norm_num

/-- The Alexander grading of the `X`-marking state in a `2 × 2` diagram is `0`. -/
theorem alexander_X_of_two (G : GridDiagram 2) : G.alexander G.X = 0 := by
  rw [alexander_def, G.maslovO_eq_intCast, G.maslovX_eq_intCast]
  rw [maslovOℤ_X_of_two, maslovXℤ_X]
  norm_num

/-- The integer `O`-Maslov grading of the identity generator in the standard two-by-two
diagram is `1`. -/
theorem maslovOℤ_twoByTwo_twoByTwoId :
    twoByTwo.maslovOℤ GridState.twoByTwoId = 1 := by
  simpa using maslovOℤ_O twoByTwo

/-- The integer `X`-Maslov grading of the identity generator in the standard two-by-two
diagram is `2`. -/
theorem maslovXℤ_twoByTwo_twoByTwoId :
    twoByTwo.maslovXℤ GridState.twoByTwoId = 2 := by
  simpa using maslovXℤ_O_of_two twoByTwo

/-- Twice the Alexander grading of the identity generator in the standard two-by-two diagram
is `-2`. -/
theorem alexanderTwoℤ_twoByTwo_twoByTwoId :
    twoByTwo.alexanderTwoℤ GridState.twoByTwoId = -2 := by
  simpa using alexanderTwoℤ_O_of_two twoByTwo

/-- The Alexander grading of the identity generator in the standard two-by-two diagram is `-1`. -/
theorem alexander_twoByTwo_twoByTwoId :
    twoByTwo.alexander GridState.twoByTwoId = -1 := by
  simpa using alexander_O_of_two twoByTwo

/-- The integer `O`-Maslov grading of the transposition generator in the standard two-by-two
diagram is `2`. -/
theorem maslovOℤ_twoByTwo_twoByTwoSwap :
    twoByTwo.maslovOℤ GridState.twoByTwoSwap = 2 := by
  simpa using maslovOℤ_X_of_two twoByTwo

/-- The integer `X`-Maslov grading of the transposition generator in the standard two-by-two
diagram is `1`. -/
theorem maslovXℤ_twoByTwo_twoByTwoSwap :
    twoByTwo.maslovXℤ GridState.twoByTwoSwap = 1 := by
  simpa only [twoByTwo_X] using maslovXℤ_X twoByTwo

/-- Twice the Alexander grading of the transposition generator in the standard two-by-two
diagram is `0`. -/
theorem alexanderTwoℤ_twoByTwo_twoByTwoSwap :
    twoByTwo.alexanderTwoℤ GridState.twoByTwoSwap = 0 := by
  simpa using alexanderTwoℤ_X_of_two twoByTwo

/-- The Alexander grading of the transposition generator in the standard two-by-two diagram
is `0`. -/
theorem alexander_twoByTwo_twoByTwoSwap :
    twoByTwo.alexander GridState.twoByTwoSwap = 0 := by
  simpa using alexander_X_of_two twoByTwo

/-- Every generator of an arbitrary `2 × 2` diagram has Alexander grading `-1` or `0`. -/
theorem alexander_eq_neg_one_or_eq_zero_of_two (G : GridDiagram 2) (x : GridState 2) :
    G.alexander x = -1 ∨ G.alexander x = 0 := by
  have hx : x = G.O ∨ x = G.X := by
    rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap x with hx | hx <;>
      rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap G.O with hO | hO <;>
      rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap G.X with hX | hX <;>
      first
        | exact Or.inl (hx.trans hO.symm)
        | exact Or.inr (hx.trans hX.symm)
        | exact False.elim ((G.disjoint 0) (by simp [hO, hX]))
  rcases hx with hx | hx
  · exact Or.inl (by rw [hx]; exact alexander_O_of_two G)
  · exact Or.inr (by rw [hx]; exact alexander_X_of_two G)

/-- Every generator of the standard two-by-two diagram has one of the two computed Alexander
gradings. -/
theorem alexander_twoByTwo_eq_neg_one_or_eq_zero (x : GridState 2) :
    twoByTwo.alexander x = -1 ∨ twoByTwo.alexander x = 0 :=
  alexander_eq_neg_one_or_eq_zero_of_two twoByTwo x

end GridDiagram

end TauCeti
