/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.Equiv
public import TauCeti.KnotTheory.Grid.Cycles

/-!
# The fully blocked grid homology

This file introduces the homology of the fully blocked grid complex as the subquotient of the
finite free grid chain module by cycles over boundaries, and evaluates it on the smallest grids.

The cycle submodule (`fullyBlockedCycles`, the kernel of the differential) and the boundary
submodule (`fullyBlockedBoundaries`, its range) were built in `BasicCycles.lean`. Viewing the
boundaries inside the cycles gives `fullyBlockedBoundariesInCycles`, and the homology is their
subquotient

`fullyBlockedHomology G = fullyBlockedCycles G ⧸ fullyBlockedBoundariesInCycles G`,

the cycles modulo the boundaries that are themselves cycles. Whenever the differential squares to
zero every boundary is a cycle (`fullyBlockedBoundaries_le_cycles`), so the subquotient is the
genuine homology `Z / B`; the general subquotient form is what lets us name the object before the
square-zero theorem is available in every grid size. Two cycles represent the same homology class
exactly when their difference is a boundary (`fullyBlockedHomology_mk_eq_iff`), independently of
square-zeroness.

For grids of size at most two the differential vanishes (`SmallGridDifferential.lean`), so every
chain is a cycle and the only boundary is zero. The homology is therefore the whole chain module:
it is `ZMod 2`-linearly isomorphic to `GridChain (ZMod 2) n`, has `2 ^ n!` elements, and has
`ZMod 2`-dimension `n!`. On the standard `2 × 2` unknot grid this is dimension two, the rank of
the stabilization factor `W = 𝔽 ⊕ 𝔽` predicted by `GH̃(G) ≅ GĤ(L) ⊗ W^{⊗(n-1)}` for the unknot.

## Main definitions

* `TauCeti.GridDiagram.fullyBlockedBoundariesInCycles`: the boundaries viewed inside the cycles.
* `TauCeti.GridDiagram.fullyBlockedHomology`: the fully blocked grid homology, cycles modulo the
  boundaries lying in them.
* `TauCeti.GridDiagram.fullyBlockedHomologyEquivChainOfLeTwo`: for `n ≤ 2` the homology is
  isomorphic to the whole chain module.

## Main results

* `TauCeti.GridDiagram.fullyBlockedHomology_mk_eq_iff`: two cycles are homologous exactly when
  their difference is a boundary, and `TauCeti.GridDiagram.fullyBlockedHomology_mk_eq_zero_iff`:
  a class vanishes exactly when a representing cycle is a boundary.
* `TauCeti.GridDiagram.natCard_fullyBlockedHomology_of_le_two` and
  `TauCeti.GridDiagram.finrank_fullyBlockedHomology_of_le_two`: the small-grid cardinality
  `2 ^ n!` and dimension `n!`.
* `TauCeti.GridDiagram.natCard_fullyBlockedHomology_of_two` and
  `TauCeti.GridDiagram.finrank_fullyBlockedHomology_of_two`: the four-element, dimension-two
  homology of the `2 × 2` unknot grid, exhibiting the rank-two `W` factor.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3,
"The complexes and `∂² = 0`", and the acceptance criterion that grid homology compute on the
`2 × 2` unknot grid with its bigradings, exhibiting the `W^{⊗(n-1)}` stabilization factor. The
homology and stabilization conventions follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots
and Links*, Chapter 4.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The fully blocked boundaries, viewed as a submodule of the fully blocked cycles: the cycles
that are hit by the differential. This is `B ⊓ Z` sitting inside `Z`, and equals `B` itself once
the differential squares to zero (`fullyBlockedBoundaries_le_cycles`). -/
noncomputable def fullyBlockedBoundariesInCycles : Submodule (ZMod 2) G.fullyBlockedCycles :=
  G.fullyBlockedBoundaries.submoduleOf G.fullyBlockedCycles

/-- A cycle lies in `fullyBlockedBoundariesInCycles` exactly when it is a fully blocked boundary,
letting membership be established without unfolding `submoduleOf`. -/
@[simp]
theorem mem_fullyBlockedBoundariesInCycles (x : G.fullyBlockedCycles) :
    x ∈ G.fullyBlockedBoundariesInCycles ↔
      (x : GridChain (ZMod 2) n) ∈ G.fullyBlockedBoundaries := by
  rw [fullyBlockedBoundariesInCycles, Submodule.submoduleOf, Submodule.mem_comap]
  rfl

/-- The fully blocked grid homology: the cycles of the fully blocked differential modulo the
boundaries that lie inside them.

This is the subquotient `Z ⧸ (B ⊓ Z)`, which is the genuine homology `Z / B` once every boundary
is a cycle, i.e. once the differential squares to zero (`fullyBlockedBoundaries_le_cycles`). Using
the subquotient lets the object be named uniformly, before the square-zero theorem is available in
every grid size. -/
abbrev fullyBlockedHomology : Type _ :=
  G.fullyBlockedCycles ⧸ G.fullyBlockedBoundariesInCycles

/-- Two cycles represent the same fully blocked homology class exactly when their difference is a
boundary. This is the defining relation of the homology and does not need the differential to
square to zero. -/
theorem fullyBlockedHomology_mk_eq_iff (a b : G.fullyBlockedCycles) :
    (Submodule.Quotient.mk a : G.fullyBlockedHomology) = Submodule.Quotient.mk b ↔
      (a : GridChain (ZMod 2) n) - b ∈ G.fullyBlockedBoundaries := by
  rw [Submodule.Quotient.eq, fullyBlockedBoundariesInCycles, Submodule.submoduleOf,
    Submodule.mem_comap]
  simp

/-- A fully blocked homology class is zero exactly when a representing cycle is a boundary,
letting classes be shown trivial without unfolding `submoduleOf`. -/
theorem fullyBlockedHomology_mk_eq_zero_iff (a : G.fullyBlockedCycles) :
    (Submodule.Quotient.mk a : G.fullyBlockedHomology) = 0 ↔
      (a : GridChain (ZMod 2) n) ∈ G.fullyBlockedBoundaries := by
  rw [Submodule.Quotient.mk_eq_zero, mem_fullyBlockedBoundariesInCycles]

/-- On grids of size at most two the fully blocked differential vanishes, so the homology is the
whole chain module: cycles are everything and the only boundary is zero. -/
noncomputable def fullyBlockedHomologyEquivChainOfLeTwo (hn : n ≤ 2) :
    G.fullyBlockedHomology ≃ₗ[ZMod 2] GridChain (ZMod 2) n :=
  have hp : G.fullyBlockedBoundariesInCycles = ⊥ := by
    rw [fullyBlockedBoundariesInCycles, G.fullyBlockedBoundaries_eq_bot_of_le_two hn,
      Submodule.submoduleOf, Submodule.comap_bot, Submodule.ker_subtype]
  (Submodule.quotEquivOfEqBot _ hp).trans
    ((LinearEquiv.ofEq _ _ (G.fullyBlockedCycles_eq_top_of_le_two hn)).trans Submodule.topEquiv)

/-- In grid size at most two the fully blocked homology has `2 ^ n!` elements: the size of the
whole chain module, since the differential vanishes. -/
theorem natCard_fullyBlockedHomology_of_le_two (hn : n ≤ 2) :
    Nat.card G.fullyBlockedHomology = 2 ^ n.factorial := by
  rw [Nat.card_congr (G.fullyBlockedHomologyEquivChainOfLeTwo hn).toEquiv,
    GridChain.natCard_zmod_two]

/-- In grid size at most two the fully blocked homology has `ZMod 2`-dimension `n!`. -/
theorem finrank_fullyBlockedHomology_of_le_two (hn : n ≤ 2) :
    Module.finrank (ZMod 2) G.fullyBlockedHomology = n.factorial := by
  rw [(G.fullyBlockedHomologyEquivChainOfLeTwo hn).finrank_eq, Module.finrank_finsupp_self,
    GridState.card]

/-- Every `2 × 2` grid has a four-element fully blocked homology. -/
theorem natCard_fullyBlockedHomology_of_two (G : GridDiagram 2) :
    Nat.card G.fullyBlockedHomology = 4 := by
  rw [G.natCard_fullyBlockedHomology_of_le_two le_rfl]
  decide

/-- Every `2 × 2` grid has a two-dimensional fully blocked homology, the rank of the
stabilization factor `W = 𝔽 ⊕ 𝔽` predicted for the unknot. -/
theorem finrank_fullyBlockedHomology_of_two (G : GridDiagram 2) :
    Module.finrank (ZMod 2) G.fullyBlockedHomology = 2 := by
  rw [G.finrank_fullyBlockedHomology_of_le_two le_rfl]
  decide

end GridDiagram

end TauCeti
