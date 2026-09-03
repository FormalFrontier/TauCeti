/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Subrings of a topological ring

Two facts about a subring `R` of a topological ring `B` that involve no further structure: the
underlying set of `Subring.topologicalClosure` is the closure of the underlying set of `R`, and
the integral closure of `R` in `B` is open as soon as `R` is, for which only continuity of
addition is needed.

The first is the `Subring` case of the family `Subsemigroup.coe_topologicalClosure`,
`Submonoid.coe_topologicalClosure`, `Subsemiring.topologicalClosure_coe`; Mathlib stops short of
`Subring`, so the equation is only available as a definitional unfolding, which is what this file
supplies as a rewrite. The second is the observation that the integral closure contains `R` and
that an additive subgroup containing an open one is open.

## Main results

* `Subring.topologicalClosure_coe`: `↑S.topologicalClosure = closure ↑S`.
* `isOpen_integralClosure_toSubring`: the integral closure of an open subring is open.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Definition 7.14, where the integral closure of an open
  subring is taken and its openness is used without comment.
-/

public section

namespace Subring

variable {R : Type*} [Ring R] [TopologicalSpace R] [IsSemitopologicalRing R]

/-- The closure of a subring, as a set, is the closure of its underlying set: that set is how
`Subring.topologicalClosure` is defined. Mathlib has the `Subsemigroup`, `Submonoid` and
`Subsemiring` forms of this equation but not the `Subring` one. -/
@[simp]
theorem topologicalClosure_coe (S : Subring R) :
    (S.topologicalClosure : Set R) = _root_.closure (S : Set R) := (rfl)

end Subring

variable {B : Type*} [CommRing B] [TopologicalSpace B] [ContinuousAdd B]

/-- The integral closure of an open subring `R` of `B` is open: it contains `R` itself, as the
image of `algebraMap`, and an additive subgroup containing an open one is open. Only continuity
of addition on `B` is used, not the full additive topological group structure. -/
theorem isOpen_integralClosure_toSubring {R : Subring B} (hR : IsOpen (R : Set B)) :
    IsOpen ((integralClosure R B).toSubring : Set B) :=
  AddSubgroup.isOpen_mono (H₁ := R.toAddSubgroup)
    (H₂ := (integralClosure R B).toSubring.toAddSubgroup)
    (fun x hx ↦ (integralClosure R B).algebraMap_mem ⟨x, hx⟩) hR
