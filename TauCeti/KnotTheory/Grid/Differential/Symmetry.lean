/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LSum
public import TauCeti.KnotTheory.Grid.Complex

/-!
# Symmetries of the fully blocked grid differential

The grid-combinatorial lane already records how the diagonal reflection and the `O`/`X` marking
swap of a grid diagram act on the Maslov and Alexander gradings (`Gradings.lean`,
`GradingInteger.lean`): the diagonal reflection leaves both gradings unchanged, while the marking
swap exchanges the two Maslov gradings `M_O` and `M_X` and sends the Alexander grading to its
negative up to a shift. This file proves the matching statements one level up, on the chain
complex itself.

The rectangle-level groundwork lives earlier: `Rectangle.lean` shows that the diagonal
reflection `GridRectangleBetween.transpose` preserves emptiness and marking avoidance, and
`BlockedRectangle.lean` turns this into the rectangle-count symmetries
`fullyBlockedRectangleCount_transpose` and `fullyBlockedRectangleCount_swapMarkings`. Here we lift
those matrix coefficients to the differential itself: the marking swap fixes the whole
differential, while the diagonal reflection intertwines the differentials of `G` and
`G.transpose` through the chain relabeling `GridChain.transposeEquiv` (defined in `Complex.lean`)
induced by `GridState.transpose`.

## Main results

* `TauCeti.GridDiagram.fullyBlockedDifferential_swapMarkings`: the whole differential is unchanged
  by swapping the `O` and `X` markings.
* `TauCeti.GridDiagram.fullyBlockedDifferential_transpose`: the differential commutes with the
  transpose chain relabeling, intertwining the differentials of `G` and `G.transpose`; this is the
  chain symmetry of the diagonal reflection.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G item 8
("Symmetries and the genus bound"), together with that roadmap's standing convention to "state
invariance naturality-ready": these are the chain-level symmetries of the fully blocked grid
complex on which an invariance statement is later built. The diagonal and marking symmetries
follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The generator row of the fully blocked differential is invariant under swapping the `O` and
`X` markings. -/
@[simp]
theorem fullyBlockedDifferentialOnGenerator_swapMarkings (x : GridState n) :
    G.swapMarkings.fullyBlockedDifferentialOnGenerator x =
      G.fullyBlockedDifferentialOnGenerator x := by
  unfold fullyBlockedDifferentialOnGenerator
  simp_rw [fullyBlockedRectangleCount_swapMarkings]

/-- The whole fully blocked grid differential is invariant under swapping the `O` and `X`
markings. -/
@[simp]
theorem fullyBlockedDifferential_swapMarkings :
    G.swapMarkings.fullyBlockedDifferential = G.fullyBlockedDifferential := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, fullyBlockedDifferential_single,
    fullyBlockedDifferentialOnGenerator_swapMarkings]

/-- The generator row of the fully blocked differential intertwines the diagonal reflection: the
reflected diagram's row on `x.transpose` is the transpose relabeling of the original row on `x`. -/
theorem fullyBlockedDifferentialOnGenerator_transpose (x : GridState n) :
    G.transpose.fullyBlockedDifferentialOnGenerator x.transpose =
      GridChain.transposeEquiv (ZMod 2) n (G.fullyBlockedDifferentialOnGenerator x) := by
  refine Finsupp.ext fun y => ?_
  rw [GridChain.transposeEquiv_apply, fullyBlockedDifferentialOnGenerator_apply,
    fullyBlockedDifferentialOnGenerator_apply,
    ← G.fullyBlockedRectangleCount_transpose x y.transpose, GridState.transpose_transpose]

/-- The fully blocked grid differential commutes with the transpose chain relabeling, intertwining
the differentials of `G` and `G.transpose`. This is the chain-level form of the statement that the
diagonal reflection is a symmetry of the fully blocked grid complex. -/
theorem fullyBlockedDifferential_transpose :
    G.transpose.fullyBlockedDifferential ∘ₗ (GridChain.transposeEquiv (ZMod 2) n).toLinearMap =
      (GridChain.transposeEquiv (ZMod 2) n).toLinearMap ∘ₗ G.fullyBlockedDifferential := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lsingle_apply,
    GridChain.transposeEquiv_single, fullyBlockedDifferential_single]
  exact G.fullyBlockedDifferentialOnGenerator_transpose x

end GridDiagram

end TauCeti
