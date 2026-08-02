/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.KnotTheory.Grid.Complex
public import Mathlib.Algebra.Module.Submodule.Range

/-!
# Cycles and boundaries for the fully blocked grid differential

This file packages the kernel and range of the fully blocked grid differential as the cycle
and boundary submodules of the finite free grid chain module. It does not assert the global
square-zero theorem; instead it records the exact condition under which boundaries are cycles.

## Main results

* `TauCeti.GridDiagram.fullyBlockedCycles`: the kernel of the fully blocked differential.
* `TauCeti.GridDiagram.fullyBlockedBoundaries`: the range of the fully blocked differential.
* `TauCeti.GridDiagram.fullyBlockedCycles_eq_ker`,
  `TauCeti.GridDiagram.fullyBlockedBoundaries_eq_range`: the cycle and boundary submodules
  restated as the kernel and range of the differential.
* `TauCeti.GridDiagram.fullyBlockedBoundaries_le_cycles`: boundaries lie in cycles whenever the
  fully blocked differential squares to zero.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`,
Lane G.3, "The complexes and `∂² = 0`". The terminology follows Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The cycles of the fully blocked grid differential: chains killed by `∂`. -/
noncomputable def fullyBlockedCycles : Submodule (ZMod 2) (GridChain (ZMod 2) n) :=
  LinearMap.ker G.fullyBlockedDifferential

/-- The boundaries of the fully blocked grid differential: chains hit by `∂`. -/
noncomputable def fullyBlockedBoundaries : Submodule (ZMod 2) (GridChain (ZMod 2) n) :=
  LinearMap.range G.fullyBlockedDifferential

/-- A chain is a fully blocked cycle exactly when its differential vanishes. -/
@[simp]
theorem mem_fullyBlockedCycles (c : GridChain (ZMod 2) n) :
    c ∈ G.fullyBlockedCycles ↔ G.fullyBlockedDifferential c = 0 :=
  by
    rw [fullyBlockedCycles]
    exact LinearMap.mem_ker

/-- A chain is a fully blocked boundary exactly when it is the differential of some chain. -/
@[simp]
theorem mem_fullyBlockedBoundaries (c : GridChain (ZMod 2) n) :
    c ∈ G.fullyBlockedBoundaries ↔
      ∃ b : GridChain (ZMod 2) n, G.fullyBlockedDifferential b = c :=
  by
    rw [fullyBlockedBoundaries]
    exact LinearMap.mem_range

/-- The fully blocked cycle submodule is the kernel of the fully blocked differential, restated
so that downstream files can rewrite with it without unfolding the definition. -/
theorem fullyBlockedCycles_eq_ker :
    G.fullyBlockedCycles = LinearMap.ker G.fullyBlockedDifferential := by
  rw [fullyBlockedCycles]

/-- The fully blocked boundary submodule is the range of the fully blocked differential, restated
so that downstream files can rewrite with it without unfolding the definition. -/
theorem fullyBlockedBoundaries_eq_range :
    G.fullyBlockedBoundaries = LinearMap.range G.fullyBlockedDifferential := by
  rw [fullyBlockedBoundaries]

/-- Boundaries lie in cycles once the fully blocked differential is square-zero. -/
theorem fullyBlockedBoundaries_le_cycles
    (hsq : G.fullyBlockedDifferential.comp G.fullyBlockedDifferential = 0) :
    G.fullyBlockedBoundaries ≤ G.fullyBlockedCycles := by
  rw [fullyBlockedBoundaries, fullyBlockedCycles]
  exact LinearMap.range_le_ker_iff.mpr hsq

/-- The fully blocked cycle submodule is top when the differential is the zero map. -/
theorem fullyBlockedCycles_eq_top_of_fullyBlockedDifferential_eq_zero
    (h : G.fullyBlockedDifferential = (0 : GridChain (ZMod 2) n →ₗ[ZMod 2] GridChain (ZMod 2) n)) :
    G.fullyBlockedCycles = ⊤ := by
  rw [fullyBlockedCycles]
  exact LinearMap.ker_eq_top.mpr h

/-- The fully blocked boundary submodule is bottom when the differential is the zero map. -/
theorem fullyBlockedBoundaries_eq_bot_of_fullyBlockedDifferential_eq_zero
    (h : G.fullyBlockedDifferential = (0 : GridChain (ZMod 2) n →ₗ[ZMod 2] GridChain (ZMod 2) n)) :
    G.fullyBlockedBoundaries = ⊥ := by
  rw [fullyBlockedBoundaries]
  exact LinearMap.range_eq_bot.mpr h

end GridDiagram

end TauCeti
