/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.KnotTheory.Grid.CycleSymmetry
public import TauCeti.KnotTheory.Grid.Homology.Basic

/-!
# Symmetries of the fully blocked grid complex act on the cycle subquotient

`CycleSymmetry.lean` lifts the chain symmetries of the fully blocked grid complex — the diagonal
reflection, the half-turn rotation, and the `O`/`X` marking swap — from the differential to the
cycle and boundary submodules. This file records the immediate consequence one level up: each
chain symmetry induces a linear equivalence between the cycle subquotient `Z / (B ⊓ Z)` of `G`
and that of the symmetric diagram.

These equivalences need no square-zero input. They are not yet homology symmetry isomorphisms:
that interpretation requires the later theorem that every boundary is a cycle. The subquotient
form of `fullyBlockedHomology` cooperates with the cycle-level equivalences from
`CycleSymmetry.lean`, and each induced quotient equivalence sends a class to the class of its
transported representative.

## Main definitions

* `TauCeti.GridDiagram.fullyBlockedCycleSubquotientTransposeEquiv`,
  `TauCeti.GridDiagram.fullyBlockedCycleSubquotientRotateEquiv`,
  `TauCeti.GridDiagram.fullyBlockedCycleSubquotientSwapMarkingsEquiv`: the induced cycle
  subquotient equivalences.

## Main results

* `TauCeti.GridDiagram.fullyBlockedBoundariesInCycles_transpose`,
  `TauCeti.GridDiagram.fullyBlockedBoundariesInCycles_rotate`,
  `TauCeti.GridDiagram.fullyBlockedBoundariesInCycles_swapMarkings`:
  each cycle-level equivalence carries the boundaries-in-cycles submodule onto the target
  diagram's boundaries-in-cycles.
* `TauCeti.GridDiagram.fullyBlockedCycleSubquotientTransposeEquiv_mk`,
  `TauCeti.GridDiagram.fullyBlockedCycleSubquotientRotateEquiv_mk`,
  `TauCeti.GridDiagram.fullyBlockedCycleSubquotientSwapMarkingsEquiv_mk`:
  each subquotient equivalence sends a class to the class of its cycle-equivalence image.

## References

This supplies symmetry infrastructure for
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`. The underlying chain symmetries follow
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3. The homology-level
interpretation remains downstream of Lane G.3's square-zero theorem.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

section Transpose

/-- The diagonal reflection carries the fully blocked boundaries-in-cycles submodule of `G` onto
the boundaries-in-cycles of `G.transpose`. This is `fullyBlockedBoundaries_transpose` transported
to the cycle submodule and is the input to the cycle-subquotient equivalence below. -/
theorem fullyBlockedBoundariesInCycles_transpose :
    G.fullyBlockedBoundariesInCycles.map
        (G.fullyBlockedCyclesTransposeEquiv :
          G.fullyBlockedCycles →ₗ[ZMod 2] G.transpose.fullyBlockedCycles) =
      G.transpose.fullyBlockedBoundariesInCycles := by
  ext x
  simp only [Submodule.mem_map, mem_fullyBlockedBoundariesInCycles]
  refine ⟨?_, ?_⟩
  · rintro ⟨y, hyB, rfl⟩
    simp only [LinearEquiv.coe_coe, fullyBlockedCyclesTransposeEquiv_apply]
    exact G.fullyBlockedBoundaries_transpose ▸ Submodule.mem_map_of_mem hyB
  · intro hxB
    refine ⟨G.fullyBlockedCyclesTransposeEquiv.symm x, ?_,
      G.fullyBlockedCyclesTransposeEquiv.apply_symm_apply x⟩
    simp only [fullyBlockedCyclesTransposeEquiv_symm_apply]
    have hsymm :=
      (Submodule.map_symm_eq_iff (GridChain.transposeEquiv (ZMod 2) n)).mpr
        G.fullyBlockedBoundaries_transpose
    rw [← hsymm]
    exact Submodule.mem_map_of_mem hxB

/-- The diagonal reflection as a linear equivalence between the cycle subquotients of `G` and
`G.transpose`, transporting a class along the transpose cycle equivalence. -/
noncomputable def fullyBlockedCycleSubquotientTransposeEquiv :
    G.fullyBlockedHomology ≃ₗ[ZMod 2] G.transpose.fullyBlockedHomology :=
  Submodule.Quotient.equiv _ _ G.fullyBlockedCyclesTransposeEquiv
    G.fullyBlockedBoundariesInCycles_transpose

/-- The diagonal-reflection subquotient equivalence sends a class to the class of its transposed
representative. -/
@[simp]
theorem fullyBlockedCycleSubquotientTransposeEquiv_mk (c : G.fullyBlockedCycles) :
    G.fullyBlockedCycleSubquotientTransposeEquiv (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (G.fullyBlockedCyclesTransposeEquiv c) := by
  simp [fullyBlockedCycleSubquotientTransposeEquiv, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply]

/-- The inverse diagonal-reflection subquotient equivalence sends a class to the class of its
inverse-transposed representative. -/
@[simp]
theorem fullyBlockedCycleSubquotientTransposeEquiv_symm_mk
    (c : G.transpose.fullyBlockedCycles) :
    G.fullyBlockedCycleSubquotientTransposeEquiv.symm (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (G.fullyBlockedCyclesTransposeEquiv.symm c) := by
  simp [fullyBlockedCycleSubquotientTransposeEquiv, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply]

end Transpose

section Rotate

/-- The half-turn rotation carries the fully blocked boundaries-in-cycles submodule of `G` onto
the boundaries-in-cycles of `G.rotate`. This is `fullyBlockedBoundaries_rotate` transported to
the cycle submodule. -/
theorem fullyBlockedBoundariesInCycles_rotate :
    G.fullyBlockedBoundariesInCycles.map
        (G.fullyBlockedCyclesRotateEquiv :
          G.fullyBlockedCycles →ₗ[ZMod 2] G.rotate.fullyBlockedCycles) =
      G.rotate.fullyBlockedBoundariesInCycles := by
  ext x
  simp only [Submodule.mem_map, mem_fullyBlockedBoundariesInCycles]
  refine ⟨?_, ?_⟩
  · rintro ⟨y, hyB, rfl⟩
    simp only [LinearEquiv.coe_coe, fullyBlockedCyclesRotateEquiv_apply]
    exact G.fullyBlockedBoundaries_rotate ▸ Submodule.mem_map_of_mem hyB
  · intro hxB
    refine ⟨G.fullyBlockedCyclesRotateEquiv.symm x, ?_,
      G.fullyBlockedCyclesRotateEquiv.apply_symm_apply x⟩
    simp only [fullyBlockedCyclesRotateEquiv_symm_apply]
    have hsymm :=
      (Submodule.map_symm_eq_iff (GridChain.rotateEquiv (ZMod 2) n)).mpr
        G.fullyBlockedBoundaries_rotate
    rw [← hsymm]
    exact Submodule.mem_map_of_mem hxB

/-- The half-turn rotation as a linear equivalence between the cycle subquotients of `G` and
`G.rotate`, transporting a class along the rotation cycle equivalence. -/
noncomputable def fullyBlockedCycleSubquotientRotateEquiv :
    G.fullyBlockedHomology ≃ₗ[ZMod 2] G.rotate.fullyBlockedHomology :=
  Submodule.Quotient.equiv _ _ G.fullyBlockedCyclesRotateEquiv
    G.fullyBlockedBoundariesInCycles_rotate

/-- The half-turn rotation subquotient equivalence sends a class to the class of its rotated
representative. -/
@[simp]
theorem fullyBlockedCycleSubquotientRotateEquiv_mk (c : G.fullyBlockedCycles) :
    G.fullyBlockedCycleSubquotientRotateEquiv (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (G.fullyBlockedCyclesRotateEquiv c) := by
  simp [fullyBlockedCycleSubquotientRotateEquiv, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply]

/-- The inverse half-turn subquotient equivalence sends a class to the class of its
inverse-rotated representative. -/
@[simp]
theorem fullyBlockedCycleSubquotientRotateEquiv_symm_mk
    (c : G.rotate.fullyBlockedCycles) :
    G.fullyBlockedCycleSubquotientRotateEquiv.symm (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (G.fullyBlockedCyclesRotateEquiv.symm c) := by
  simp [fullyBlockedCycleSubquotientRotateEquiv, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply]

end Rotate

section SwapMarkings

/-- The marking swap carries the fully blocked boundaries-in-cycles submodule of `G` onto the
boundaries-in-cycles of `G.swapMarkings`. Both the cycle and the boundary submodules are equal,
so the transport is by the underlying identity chain relabeling. -/
theorem fullyBlockedBoundariesInCycles_swapMarkings :
    G.fullyBlockedBoundariesInCycles.map
        (G.fullyBlockedCyclesSwapMarkingsEquiv :
          G.fullyBlockedCycles →ₗ[ZMod 2] G.swapMarkings.fullyBlockedCycles) =
      G.swapMarkings.fullyBlockedBoundariesInCycles := by
  ext x
  simp only [Submodule.mem_map, mem_fullyBlockedBoundariesInCycles,
    G.fullyBlockedBoundaries_swapMarkings]
  refine ⟨?_, ?_⟩
  · rintro ⟨y, hyB, rfl⟩
    simpa using hyB
  · intro hxB
    refine ⟨G.fullyBlockedCyclesSwapMarkingsEquiv.symm x, ?_,
      G.fullyBlockedCyclesSwapMarkingsEquiv.apply_symm_apply x⟩
    simpa using hxB

/-- The marking swap as a linear equivalence between the cycle subquotients of `G` and
`G.swapMarkings`, transporting a class along the marking-swap cycle equivalence. -/
noncomputable def fullyBlockedCycleSubquotientSwapMarkingsEquiv :
    G.fullyBlockedHomology ≃ₗ[ZMod 2] G.swapMarkings.fullyBlockedHomology :=
  Submodule.Quotient.equiv _ _ G.fullyBlockedCyclesSwapMarkingsEquiv
    G.fullyBlockedBoundariesInCycles_swapMarkings

/-- The marking-swap subquotient equivalence sends a class to the class of its marking-swap
transported representative. -/
@[simp]
theorem fullyBlockedCycleSubquotientSwapMarkingsEquiv_mk (c : G.fullyBlockedCycles) :
    G.fullyBlockedCycleSubquotientSwapMarkingsEquiv (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (G.fullyBlockedCyclesSwapMarkingsEquiv c) := by
  simp [fullyBlockedCycleSubquotientSwapMarkingsEquiv, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply]

/-- The inverse marking-swap subquotient equivalence sends a class to the class of its
inverse-transported representative. -/
@[simp]
theorem fullyBlockedCycleSubquotientSwapMarkingsEquiv_symm_mk
    (c : G.swapMarkings.fullyBlockedCycles) :
    G.fullyBlockedCycleSubquotientSwapMarkingsEquiv.symm (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (G.fullyBlockedCyclesSwapMarkingsEquiv.symm c) := by
  simp [fullyBlockedCycleSubquotientSwapMarkingsEquiv, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply]

end SwapMarkings

end GridDiagram

end TauCeti
