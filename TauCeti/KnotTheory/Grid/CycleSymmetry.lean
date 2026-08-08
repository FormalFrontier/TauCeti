/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.Submodule.Equiv
public import TauCeti.KnotTheory.Grid.BasicCycles
public import TauCeti.KnotTheory.Grid.Differential.Symmetry

/-!
# Symmetries of the fully blocked grid complex act on cycles and boundaries

`DifferentialSymmetry.lean` shows that the diagonal reflection, the half-turn rotation, and the
`O`/`X` marking swap of a grid diagram are chain symmetries of the fully blocked grid complex:
the marking swap fixes the differential outright, while the reflection and rotation intertwine
the differentials of `G` and `G.transpose` (resp. `G.rotate`) through the chain relabelings
`GridChain.transposeEquiv` and `GridChain.rotateEquiv`. This file records the immediate
consequence one level up, on the kernel and range submodules from `BasicCycles.lean`: a chain
symmetry carries cycles to cycles and boundaries to boundaries.

Because these are equalities of submodules under a linear automorphism, they package as linear
equivalences between the cycle (resp. boundary) submodules of a diagram and its reflected,
rotated, or marking-swapped counterpart. These chain-level symmetry equivalences need no
square-zero input.

## Main results

* `TauCeti.GridDiagram.fullyBlockedCycles_transpose`,
  `TauCeti.GridDiagram.fullyBlockedBoundaries_transpose`,
  `TauCeti.GridDiagram.fullyBlockedCycles_rotate`,
  `TauCeti.GridDiagram.fullyBlockedBoundaries_rotate`: the transpose and rotation chain
  relabelings map the cycles (resp. boundaries) of `G` onto those of `G.transpose` (resp.
  `G.rotate`).
* `TauCeti.GridDiagram.fullyBlockedCycles_swapMarkings`,
  `TauCeti.GridDiagram.fullyBlockedBoundaries_swapMarkings`: swapping the `O` and `X` markings
  leaves the cycle and boundary submodules unchanged.
* `TauCeti.GridDiagram.fullyBlockedCyclesTransposeEquiv`,
  `TauCeti.GridDiagram.fullyBlockedBoundariesTransposeEquiv`,
  `TauCeti.GridDiagram.fullyBlockedCyclesRotateEquiv`,
  `TauCeti.GridDiagram.fullyBlockedBoundariesRotateEquiv`: the same statements packaged as linear
  equivalences of submodules, each characterized on elements by an `_apply` lemma recording that
  it acts by the underlying chain relabeling.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G item 8
("Symmetries and the genus bound"), together with that roadmap's standing convention to "state
invariance naturality-ready". The underlying chain symmetries follow
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace GridChain

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

/-- If a linear automorphism `e` intertwines two endomorphisms `f` and `g` pointwise
(`g (e d) = e (f d)`), it carries the kernel of `f` onto the kernel of `g`. This is the general
shape behind the cycle-symmetry statements for the fully blocked grid differential. -/
private theorem map_ker_of_intertwine (e : M ≃ₗ[ZMod 2] M) (f g : M →ₗ[ZMod 2] M)
    (h : ∀ d, g (e d) = e (f d)) :
    Submodule.map (e : M →ₗ[ZMod 2] M) (LinearMap.ker f) = LinearMap.ker g := by
  ext c
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨d, hd, rfl⟩
    rw [h d, hd, map_zero]
  · intro hc
    refine ⟨e.symm c, ?_, e.apply_symm_apply c⟩
    have : e (f (e.symm c)) = 0 := by rw [← h, e.apply_symm_apply, hc]
    exact e.map_eq_zero_iff.mp this

/-- If a linear automorphism `e` intertwines two endomorphisms `f` and `g` pointwise
(`g (e d) = e (f d)`), it carries the range of `f` onto the range of `g`. This is the general
shape behind the boundary-symmetry statements for the fully blocked grid differential. -/
private theorem map_range_of_intertwine (e : M ≃ₗ[ZMod 2] M) (f g : M →ₗ[ZMod 2] M)
    (h : ∀ d, g (e d) = e (f d)) :
    Submodule.map (e : M →ₗ[ZMod 2] M) (LinearMap.range f) = LinearMap.range g := by
  ext c
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨d, ⟨b, rfl⟩, rfl⟩
    exact ⟨e b, h b⟩
  · rintro ⟨b, rfl⟩
    exact ⟨f (e.symm b), ⟨e.symm b, rfl⟩, by rw [← h, e.apply_symm_apply]⟩

end GridChain

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The pointwise transpose intertwining of the fully blocked differentials of `G` and
`G.transpose`, extracted from `fullyBlockedDifferential_transpose`. -/
private theorem fullyBlockedDifferential_transpose_apply (d : GridChain (ZMod 2) n) :
    G.transpose.fullyBlockedDifferential (GridChain.transposeEquiv (ZMod 2) n d) =
      GridChain.transposeEquiv (ZMod 2) n (G.fullyBlockedDifferential d) := by
  have := DFunLike.congr_fun G.fullyBlockedDifferential_transpose d
  simpa using this

/-- The pointwise rotation intertwining of the fully blocked differentials of `G` and
`G.rotate`, extracted from `fullyBlockedDifferential_rotate`. -/
private theorem fullyBlockedDifferential_rotate_apply (d : GridChain (ZMod 2) n) :
    G.rotate.fullyBlockedDifferential (GridChain.rotateEquiv (ZMod 2) n d) =
      GridChain.rotateEquiv (ZMod 2) n (G.fullyBlockedDifferential d) := by
  have := DFunLike.congr_fun G.fullyBlockedDifferential_rotate d
  simpa using this

/-- The transpose chain relabeling carries the fully blocked cycles of `G` onto those of
`G.transpose`. -/
theorem fullyBlockedCycles_transpose :
    Submodule.map (GridChain.transposeEquiv (ZMod 2) n : _ →ₗ[ZMod 2] _) G.fullyBlockedCycles =
      G.transpose.fullyBlockedCycles := by
  rw [G.fullyBlockedCycles_eq_ker, G.transpose.fullyBlockedCycles_eq_ker]
  exact GridChain.map_ker_of_intertwine _ _ _ G.fullyBlockedDifferential_transpose_apply

/-- The transpose chain relabeling carries the fully blocked boundaries of `G` onto those of
`G.transpose`. -/
theorem fullyBlockedBoundaries_transpose :
    Submodule.map (GridChain.transposeEquiv (ZMod 2) n : _ →ₗ[ZMod 2] _) G.fullyBlockedBoundaries =
      G.transpose.fullyBlockedBoundaries := by
  rw [G.fullyBlockedBoundaries_eq_range, G.transpose.fullyBlockedBoundaries_eq_range]
  exact GridChain.map_range_of_intertwine _ _ _ G.fullyBlockedDifferential_transpose_apply

/-- The rotation chain relabeling carries the fully blocked cycles of `G` onto those of
`G.rotate`. -/
theorem fullyBlockedCycles_rotate :
    Submodule.map (GridChain.rotateEquiv (ZMod 2) n : _ →ₗ[ZMod 2] _) G.fullyBlockedCycles =
      G.rotate.fullyBlockedCycles := by
  rw [G.fullyBlockedCycles_eq_ker, G.rotate.fullyBlockedCycles_eq_ker]
  exact GridChain.map_ker_of_intertwine _ _ _ G.fullyBlockedDifferential_rotate_apply

/-- The rotation chain relabeling carries the fully blocked boundaries of `G` onto those of
`G.rotate`. -/
theorem fullyBlockedBoundaries_rotate :
    Submodule.map (GridChain.rotateEquiv (ZMod 2) n : _ →ₗ[ZMod 2] _) G.fullyBlockedBoundaries =
      G.rotate.fullyBlockedBoundaries := by
  rw [G.fullyBlockedBoundaries_eq_range, G.rotate.fullyBlockedBoundaries_eq_range]
  exact GridChain.map_range_of_intertwine _ _ _ G.fullyBlockedDifferential_rotate_apply

/-- Swapping the `O` and `X` markings leaves the fully blocked cycle submodule unchanged, since
it fixes the differential. -/
@[simp]
theorem fullyBlockedCycles_swapMarkings :
    G.swapMarkings.fullyBlockedCycles = G.fullyBlockedCycles := by
  rw [G.swapMarkings.fullyBlockedCycles_eq_ker, G.fullyBlockedCycles_eq_ker,
    fullyBlockedDifferential_swapMarkings]

/-- Swapping the `O` and `X` markings leaves the fully blocked boundary submodule unchanged, since
it fixes the differential. -/
@[simp]
theorem fullyBlockedBoundaries_swapMarkings :
    G.swapMarkings.fullyBlockedBoundaries = G.fullyBlockedBoundaries := by
  rw [G.swapMarkings.fullyBlockedBoundaries_eq_range, G.fullyBlockedBoundaries_eq_range,
    fullyBlockedDifferential_swapMarkings]

/-- The diagonal reflection as a linear equivalence between the fully blocked cycles of `G` and
those of `G.transpose`. -/
noncomputable def fullyBlockedCyclesTransposeEquiv :
    G.fullyBlockedCycles ≃ₗ[ZMod 2] G.transpose.fullyBlockedCycles :=
  (GridChain.transposeEquiv (ZMod 2) n).ofSubmodules _ _ G.fullyBlockedCycles_transpose

/-- The diagonal reflection as a linear equivalence between the fully blocked boundaries of `G`
and those of `G.transpose`. -/
noncomputable def fullyBlockedBoundariesTransposeEquiv :
    G.fullyBlockedBoundaries ≃ₗ[ZMod 2] G.transpose.fullyBlockedBoundaries :=
  (GridChain.transposeEquiv (ZMod 2) n).ofSubmodules _ _ G.fullyBlockedBoundaries_transpose

/-- The half-turn rotation as a linear equivalence between the fully blocked cycles of `G` and
those of `G.rotate`. -/
noncomputable def fullyBlockedCyclesRotateEquiv :
    G.fullyBlockedCycles ≃ₗ[ZMod 2] G.rotate.fullyBlockedCycles :=
  (GridChain.rotateEquiv (ZMod 2) n).ofSubmodules _ _ G.fullyBlockedCycles_rotate

/-- The half-turn rotation as a linear equivalence between the fully blocked boundaries of `G`
and those of `G.rotate`. -/
noncomputable def fullyBlockedBoundariesRotateEquiv :
    G.fullyBlockedBoundaries ≃ₗ[ZMod 2] G.rotate.fullyBlockedBoundaries :=
  (GridChain.rotateEquiv (ZMod 2) n).ofSubmodules _ _ G.fullyBlockedBoundaries_rotate

/-- The transpose cycle equivalence acts by the underlying transpose chain relabeling. -/
@[simp]
theorem fullyBlockedCyclesTransposeEquiv_apply (c : G.fullyBlockedCycles) :
    (G.fullyBlockedCyclesTransposeEquiv c : GridChain (ZMod 2) n) =
      GridChain.transposeEquiv (ZMod 2) n c := by
  exact (GridChain.transposeEquiv (ZMod 2) n).ofSubmodules_apply
    G.fullyBlockedCycles_transpose c

/-- The transpose boundary equivalence acts by the underlying transpose chain relabeling. -/
@[simp]
theorem fullyBlockedBoundariesTransposeEquiv_apply (c : G.fullyBlockedBoundaries) :
    (G.fullyBlockedBoundariesTransposeEquiv c : GridChain (ZMod 2) n) =
      GridChain.transposeEquiv (ZMod 2) n c := by
  exact (GridChain.transposeEquiv (ZMod 2) n).ofSubmodules_apply
    G.fullyBlockedBoundaries_transpose c

/-- The rotation cycle equivalence acts by the underlying rotation chain relabeling. -/
@[simp]
theorem fullyBlockedCyclesRotateEquiv_apply (c : G.fullyBlockedCycles) :
    (G.fullyBlockedCyclesRotateEquiv c : GridChain (ZMod 2) n) =
      GridChain.rotateEquiv (ZMod 2) n c := by
  exact (GridChain.rotateEquiv (ZMod 2) n).ofSubmodules_apply
    G.fullyBlockedCycles_rotate c

/-- The rotation boundary equivalence acts by the underlying rotation chain relabeling. -/
@[simp]
theorem fullyBlockedBoundariesRotateEquiv_apply (c : G.fullyBlockedBoundaries) :
    (G.fullyBlockedBoundariesRotateEquiv c : GridChain (ZMod 2) n) =
      GridChain.rotateEquiv (ZMod 2) n c := by
  exact (GridChain.rotateEquiv (ZMod 2) n).ofSubmodules_apply
    G.fullyBlockedBoundaries_rotate c

/-- The inverse of the diagonal-reflection cycle equivalence acts on underlying chains by the
inverse transpose chain relabeling: the transpose equivalence swaps rows and columns of the
underlying chain and inverting the cycle-level equivalence undoes exactly that. -/
@[simp]
theorem fullyBlockedCyclesTransposeEquiv_symm_apply (c : G.transpose.fullyBlockedCycles) :
    ((G.fullyBlockedCyclesTransposeEquiv.symm c : G.fullyBlockedCycles) :
        GridChain (ZMod 2) n) =
      (GridChain.transposeEquiv (ZMod 2) n).symm (c : GridChain (ZMod 2) n) := by
  exact (GridChain.transposeEquiv (ZMod 2) n).ofSubmodules_symm_apply
    G.fullyBlockedCycles_transpose c

/-- The inverse of the half-turn rotation cycle equivalence acts on underlying chains by the
inverse rotation chain relabeling: the rotation equivalence half-turns the underlying chain and
inverting the cycle-level equivalence undoes exactly that. -/
@[simp]
theorem fullyBlockedCyclesRotateEquiv_symm_apply (c : G.rotate.fullyBlockedCycles) :
    ((G.fullyBlockedCyclesRotateEquiv.symm c : G.fullyBlockedCycles) :
        GridChain (ZMod 2) n) =
      (GridChain.rotateEquiv (ZMod 2) n).symm (c : GridChain (ZMod 2) n) := by
  exact (GridChain.rotateEquiv (ZMod 2) n).ofSubmodules_symm_apply
    G.fullyBlockedCycles_rotate c

/-- The marking swap as a linear equivalence between the fully blocked cycles of `G` and those of
`G.swapMarkings`. The two cycle submodules of `GridChain` coincide, since the marking swap fixes
the differential, so this is transport along that equality. -/
noncomputable def fullyBlockedCyclesSwapMarkingsEquiv :
    G.fullyBlockedCycles ≃ₗ[ZMod 2] G.swapMarkings.fullyBlockedCycles :=
  LinearEquiv.ofEq _ _ G.fullyBlockedCycles_swapMarkings.symm

/-- The marking-swap cycle equivalence preserves underlying chains. -/
@[simp]
theorem fullyBlockedCyclesSwapMarkingsEquiv_apply (c : G.fullyBlockedCycles) :
    ((G.fullyBlockedCyclesSwapMarkingsEquiv c : G.swapMarkings.fullyBlockedCycles) :
        GridChain (ZMod 2) n) = (c : GridChain (ZMod 2) n) := by
  simp [fullyBlockedCyclesSwapMarkingsEquiv]

/-- The inverse of the marking-swap cycle equivalence preserves underlying chains. -/
@[simp]
theorem fullyBlockedCyclesSwapMarkingsEquiv_symm_apply (c : G.swapMarkings.fullyBlockedCycles) :
    ((G.fullyBlockedCyclesSwapMarkingsEquiv.symm c : G.fullyBlockedCycles) :
        GridChain (ZMod 2) n) = (c : GridChain (ZMod 2) n) := by
  simp [fullyBlockedCyclesSwapMarkingsEquiv]

end GridDiagram

end TauCeti
