/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.KnotTheory.Grid.BasicCycles
public import TauCeti.KnotTheory.Grid.SmallGrid.Differential
public import TauCeti.KnotTheory.Grid.ChainCardinality

/-!
# Small-grid cycles and boundaries for the fully blocked grid differential

This file computes the cycle and boundary submodules of the fully blocked grid differential in
the already-proved zero-differential small-grid case.

## Main results

* `TauCeti.GridDiagram.fullyBlockedCycles_eq_top_of_le_two` and
  `TauCeti.GridDiagram.fullyBlockedBoundaries_eq_bot_of_le_two`: the small-grid computation.
* `TauCeti.GridDiagram.natCard_fullyBlockedCycles_of_le_two` and
  `TauCeti.GridDiagram.natCard_fullyBlockedBoundaries_of_le_two`: the small-grid cardinalities.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`,
Lane G.3, "The complexes and `∂² = 0`", and for the standing convention that grid complexes
compute on explicit small grids.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- In grid size at most two, every chain is a cycle for the fully blocked differential. -/
theorem fullyBlockedCycles_eq_top_of_le_two (hn : n ≤ 2) :
    G.fullyBlockedCycles = ⊤ :=
  G.fullyBlockedCycles_eq_top_of_fullyBlockedDifferential_eq_zero
    (G.fullyBlockedDifferential_eq_zero_of_le_two hn)

/-- In grid size at most two, the only boundary for the fully blocked differential is zero. -/
theorem fullyBlockedBoundaries_eq_bot_of_le_two (hn : n ≤ 2) :
    G.fullyBlockedBoundaries = ⊥ :=
  G.fullyBlockedBoundaries_eq_bot_of_fullyBlockedDifferential_eq_zero
    (G.fullyBlockedDifferential_eq_zero_of_le_two hn)

/-- On every `2 × 2` grid, every chain is a cycle for the fully blocked differential. -/
@[simp]
theorem fullyBlockedCycles_eq_top_of_two (G : GridDiagram 2) :
    G.fullyBlockedCycles = ⊤ :=
  G.fullyBlockedCycles_eq_top_of_le_two le_rfl

/-- On every `2 × 2` grid, the only boundary for the fully blocked differential is zero. -/
@[simp]
theorem fullyBlockedBoundaries_eq_bot_of_two (G : GridDiagram 2) :
    G.fullyBlockedBoundaries = ⊥ :=
  G.fullyBlockedBoundaries_eq_bot_of_le_two le_rfl

/-- In grid size at most two, every chain is a fully blocked cycle. -/
theorem mem_fullyBlockedCycles_of_le_two (hn : n ≤ 2) (c : GridChain (ZMod 2) n) :
    c ∈ G.fullyBlockedCycles := by
  rw [G.fullyBlockedCycles_eq_top_of_le_two hn]
  exact Submodule.mem_top

/-- In grid size at most two, a fully blocked boundary is exactly the zero chain. -/
theorem mem_fullyBlockedBoundaries_iff_eq_zero_of_le_two (hn : n ≤ 2) (c : GridChain (ZMod 2) n) :
    c ∈ G.fullyBlockedBoundaries ↔ c = 0 := by
  rw [G.fullyBlockedBoundaries_eq_bot_of_le_two hn]
  exact Submodule.mem_bot (R := ZMod 2)

/-- On every `2 × 2` grid, every chain is a fully blocked cycle. -/
theorem mem_fullyBlockedCycles_of_two (G : GridDiagram 2) (c : GridChain (ZMod 2) 2) :
    c ∈ G.fullyBlockedCycles :=
  G.mem_fullyBlockedCycles_of_le_two le_rfl c

/-- On every `2 × 2` grid, a fully blocked boundary is exactly the zero chain. -/
theorem mem_fullyBlockedBoundaries_iff_eq_zero_of_two
    (G : GridDiagram 2) (c : GridChain (ZMod 2) 2) :
    c ∈ G.fullyBlockedBoundaries ↔ c = 0 :=
  G.mem_fullyBlockedBoundaries_iff_eq_zero_of_le_two le_rfl c

/-- In grid size at most two, there are `2 ^ n!` fully blocked cycles. -/
theorem natCard_fullyBlockedCycles_of_le_two (hn : n ≤ 2) :
    Nat.card G.fullyBlockedCycles = 2 ^ n.factorial := by
  classical
  rw [G.fullyBlockedCycles_eq_top_of_le_two hn]
  rw [← GridChain.natCard_zmod_two n]
  exact Nat.card_congr
    (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) (GridChain (ZMod 2) n)) ≃ₗ[ZMod 2]
      GridChain (ZMod 2) n).toEquiv

/-- In grid size at most two, there is one fully blocked boundary. -/
theorem natCard_fullyBlockedBoundaries_of_le_two (hn : n ≤ 2) :
    Nat.card G.fullyBlockedBoundaries = 1 := by
  classical
  rw [G.fullyBlockedBoundaries_eq_bot_of_le_two hn]
  simp

/-- Every `2 × 2` grid has four fully blocked cycles. -/
theorem natCard_fullyBlockedCycles_of_two (G : GridDiagram 2) :
    Nat.card G.fullyBlockedCycles = 4 := by
  rw [G.natCard_fullyBlockedCycles_of_le_two le_rfl]
  simp

/-- Every `2 × 2` grid has one fully blocked boundary. -/
theorem natCard_fullyBlockedBoundaries_of_two (G : GridDiagram 2) :
    Nat.card G.fullyBlockedBoundaries = 1 :=
  G.natCard_fullyBlockedBoundaries_of_le_two le_rfl

end GridDiagram

end TauCeti
