/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Instances.ZMultiples
public import TauCeti.Topology.Homotopy.HomotopyGroup.Covering

/-!
# Higher homotopy groups of the circle

The real line covers every real additive circle `AddCircle p`. This file combines that
covering with the invariance of higher homotopy groups under covering maps to show that all
homotopy groups of a circle in dimensions at least two are trivial.

The only calculation needed in the total space is elementary: any two generalized loops in a
real normed vector space are homotopic relative to the cube boundary by pointwise linear
interpolation. Consequently all homotopy groups of such a space are subsingletons. Applying
the covering-map isomorphism for `ℝ → AddCircle p` gives the circle calculation.

This proves Stage 4, item 11 of the Tau Ceti universal-covers roadmap
(`TauCetiRoadmap/UniversalCovers/README.md`): `π_n(S¹) = 0` for `n ≥ 2`.

## Main declarations

* `TauCeti.GenLoop.homotopic_of_topologicalVectorSpace`: generalized loops in a real
  topological vector space
  with the same basepoint are homotopic.
* `TauCeti.HomotopyGroup.subsingleton_of_topologicalVectorSpace`: all homotopy groups of a real
  topological vector space are subsingletons.
* `TauCeti.AddCircle.homotopyGroup_subsingleton`: `π_N(AddCircle p)` is trivial when `N` has
  at least two elements.
* `TauCeti.AddCircle.homotopyGroupPi_subsingleton`: the `π_(n + 2)` form.

The covering map is Junyan Xu's `AddCircle.isCoveringMap_coe` in
`Mathlib.Topology.Covering.AddCircle`.
-/

public section

namespace TauCeti

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

namespace GenLoop

variable {N E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {x : E}

/-- Any two generalized loops based at the same point in a real topological vector space are
homotopic relative to the cube boundary. The homotopy is pointwise linear interpolation. -/
theorem homotopic_of_topologicalVectorSpace (f g : Ω^ N E x) :
    _root_.GenLoop.Homotopic f g := by
  refine ⟨⟨⟨⟨fun tu ↦ (1 - (tu.1 : ℝ)) • f tu.2 + (tu.1 : ℝ) • g tu.2, ?_⟩, ?_, ?_⟩, ?_⟩⟩
  · fun_prop
  · intro u
    simp
  · intro u
    simp
  · intro t u hu
    -- Expose the value hidden by the nested `HomotopyRel` and `ContinuousMap` coercions.
    change (1 - (t : ℝ)) • f u + (t : ℝ) • g u = f u
    rw [_root_.GenLoop.boundary f u hu, _root_.GenLoop.boundary g u hu]
    module

end GenLoop

namespace HomotopyGroup

variable {N E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {x : E}

/-- Every homotopy group of a real topological vector space is a subsingleton. This includes
dimension zero: a real topological vector space is path connected. -/
theorem subsingleton_of_topologicalVectorSpace : Subsingleton (HomotopyGroup N E x) := by
  constructor
  intro a b
  refine Quotient.inductionOn₂ a b fun f g ↦ ?_
  exact Quotient.sound (GenLoop.homotopic_of_topologicalVectorSpace f g)

end HomotopyGroup

namespace AddCircle

/-- Every higher homotopy group of a real circle is trivial. The index type `N` being
nontrivial expresses that the dimension is at least two. -/
theorem homotopyGroup_subsingleton {N : Type*} [Nontrivial N]
    (p x : ℝ) : Subsingleton (HomotopyGroup N (AddCircle p) (x : AddCircle p)) := by
  classical
  letI : Subsingleton (HomotopyGroup N ℝ x) :=
    HomotopyGroup.subsingleton_of_topologicalVectorSpace
  let e :=
    TauCeti.IsCoveringMap.homotopyGroupMulEquiv (N := N)
      (_root_.AddCircle.isCoveringMap_coe p) x
  exact e.toEquiv.subsingleton_congr.mp inferInstance

/-- The homotopy group `π_(n + 2)` of a real circle is trivial, for every `n`. -/
theorem homotopyGroupPi_subsingleton (p x : ℝ) (n : ℕ) :
    Subsingleton (π_ (n + 2) (AddCircle p) (x : AddCircle p)) :=
  homotopyGroup_subsingleton p x

/-- Every element of `π_(n + 2)` of a real circle is the identity. -/
theorem homotopyGroupPi_eq_one (p x : ℝ) (n : ℕ)
    (a : π_ (n + 2) (AddCircle p) (x : AddCircle p)) : a = 1 :=
  @Subsingleton.elim _ (homotopyGroupPi_subsingleton p x n) _ _

end AddCircle

end TauCeti
