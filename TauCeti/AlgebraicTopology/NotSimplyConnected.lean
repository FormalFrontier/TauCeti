/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.Contractible

/-!
# Consequences of a space not being simply connected

A space whose fundamental group at some basepoint is nontrivial is not simply connected, and a
non-simply-connected space inherits the standard topological obstructions: it is not
contractible, and it is not homeomorphic to any simply connected space — in particular not to
any real topological vector space nor to `ℝ`.

These facts use the space only through the (non-)triviality of its fundamental group, so they
are stated once here for an arbitrary space and then specialised to concrete circles
(`AddCircle.*`, `TauCeti.UnitAddCircle.*`, `TauCeti.Circle.*`). Non-simple-connectivity
follows because a simply connected space has a subsingleton fundamental group; the
homeomorphism statements consume Mathlib's transfer of `SimplyConnectedSpace` along a homotopy
equivalence (`ContinuousMap.HomotopyEquiv.simplyConnectedSpace`, via
`Homeomorph.toHomotopyEquiv`) and the contractibility of a real topological vector space
(`RealTopologicalVectorSpace.contractibleSpace`). No Mathlib code is vendored.

## Main declarations

* `TauCeti.not_simplyConnectedSpace_of_nontrivial_fundamentalGroup`: a space with a nontrivial
  fundamental group at some basepoint is not simply connected.
* `TauCeti.not_contractibleSpace_of_not_simplyConnectedSpace`: a non-simply-connected space is
  not contractible.
* `TauCeti.isEmpty_homeomorph_of_not_simplyConnectedSpace`,
  `TauCeti.isEmpty_homeomorph_realTopologicalVectorSpace_of_not_simplyConnectedSpace`,
  `TauCeti.isEmpty_homeomorph_real_of_not_simplyConnectedSpace`: a non-simply-connected space is
  not homeomorphic to a simply connected space, to a real topological vector space, or to `ℝ`.
-/

public section

namespace TauCeti

/-- A space with a nontrivial fundamental group at some basepoint is **not simply connected**: a
simply connected space has a subsingleton fundamental group. -/
theorem not_simplyConnectedSpace_of_nontrivial_fundamentalGroup {X : Type*} [TopologicalSpace X]
    (x : X) [Nontrivial (FundamentalGroup X x)] : ¬ SimplyConnectedSpace X := by
  intro h
  have := h
  exact false_of_nontrivial_of_subsingleton (FundamentalGroup X x)

/-- A **not simply connected** space is **not contractible**: a contractible space is simply
connected. -/
theorem not_contractibleSpace_of_not_simplyConnectedSpace {X : Type*} [TopologicalSpace X]
    (h : ¬ SimplyConnectedSpace X) : ¬ ContractibleSpace X := by
  intro hc
  have := hc
  exact h inferInstance

/-- A **not simply connected** space is not homeomorphic to any simply connected space: a
homeomorphism is in particular a homotopy equivalence, and simple connectivity transfers along
homotopy equivalences. -/
theorem isEmpty_homeomorph_of_not_simplyConnectedSpace {X : Type*} [TopologicalSpace X]
    (h : ¬ SimplyConnectedSpace X) (Y : Type*) [TopologicalSpace Y] [SimplyConnectedSpace Y] :
    IsEmpty (X ≃ₜ Y) := by
  refine ⟨fun e => ?_⟩
  exact h e.toHomotopyEquiv.simplyConnectedSpace

/-- A **not simply connected** space is not homeomorphic to any real topological vector space
(in particular, to any real normed space), since such a space is contractible, hence simply
connected. -/
theorem isEmpty_homeomorph_realTopologicalVectorSpace_of_not_simplyConnectedSpace
    {X : Type*} [TopologicalSpace X] (h : ¬ SimplyConnectedSpace X) (E : Type*)
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E] :
    IsEmpty (X ≃ₜ E) :=
  isEmpty_homeomorph_of_not_simplyConnectedSpace h E

/-- A **not simply connected** space is not homeomorphic to the real line: `ℝ` is contractible,
hence simply connected. -/
theorem isEmpty_homeomorph_real_of_not_simplyConnectedSpace {X : Type*} [TopologicalSpace X]
    (h : ¬ SimplyConnectedSpace X) : IsEmpty (X ≃ₜ ℝ) :=
  isEmpty_homeomorph_realTopologicalVectorSpace_of_not_simplyConnectedSpace h ℝ

end TauCeti
