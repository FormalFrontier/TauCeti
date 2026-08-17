/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Transfer instances for restricted and properly discontinuous actions

This file records generic instances for actions on a topological space that typeclass search
cannot otherwise reach. A submonoid, and hence a subgroup, inherits `ContinuousConstSMul` from
an ambient scalar action; and a properly discontinuous action has `Finite` point stabilisers.

## Main results

* `TauCeti.Submonoid.continuousConstSMul` and `TauCeti.Subgroup.continuousConstSMul`: continuity
  in the point is inherited by a submonoid, hence by a subgroup.
* `TauCeti.finite_stabilizer_of_properlyDiscontinuousSMul`: a properly discontinuous action has
  finite point stabilisers, as an instance rather than as `Set.Finite` of the carrier.
-/

public section

namespace TauCeti

namespace Submonoid

/-- A submonoid inherits continuity in the point from an ambient continuous action. -/
@[to_additive AddSubmonoid.continuousConstVAdd
/-- An additive submonoid inherits continuity in the point from an ambient continuous additive
action. -/]
instance continuousConstSMul {M X : Type*} [MulOneClass M] [TopologicalSpace X] [SMul M X]
    [ContinuousConstSMul M X] (S : Submonoid M) : ContinuousConstSMul S X :=
  ⟨fun g => by
    simpa only [Submonoid.smul_def] using continuous_const_smul (g : M)⟩

end Submonoid

namespace Subgroup

/-- A subgroup inherits continuity in the point from an ambient continuous action. -/
instance continuousConstSMul {G X : Type*} [Group G] [TopologicalSpace X] [SMul G X]
    [ContinuousConstSMul G X] (S : Subgroup G) : ContinuousConstSMul S X :=
  TauCeti.Submonoid.continuousConstSMul S.toSubmonoid

end Subgroup

/-- **A properly discontinuous action has finite point stabilisers**, as a `Finite` instance.

Mathlib's `ProperlyDiscontinuousSMul.finite_stabilizer` (Alex Kontorovich and Heather Macbeth,
`Mathlib/Topology/Algebra/ConstMulAction.lean`) states this as `Set.Finite` of the stabiliser's
carrier. That form does not drive typeclass search, so a count through `Nat.card` — which is the
junk value `0` on an infinite type — has to bridge to `Finite` by hand at each use. This does it
once, for every properly discontinuous action.

For an action of a subgroup of `GL(2, ℝ)` no further instance is needed: Mathlib's
`Subgroup.IsArithmetic.properlyDiscontinuous` supplies proper discontinuity for an arithmetic
`𝒢 ≤ GL(2, ℝ)`, and the image of a finite-index `Γ ≤ SL(2, ℤ)` is arithmetic, so both shapes
reach `Finite` through this instance alone. The stabiliser of a point under `SL(2, ℤ)` itself is
*not* one of those shapes — `SL(2, ℤ)` is a type, not a `Subgroup (GL (Fin 2) ℝ)`, so there is no
`ProperlyDiscontinuousSMul SL(2, ℤ) ℍ` to apply — and stays with the hand-proved
`TauCeti.ModularGroup.finite_stabilizer`. -/
@[to_additive
/-- **A properly discontinuous additive action has finite point stabilisers**, as a `Finite`
instance. Mathlib's `ProperlyDiscontinuousVAdd.finite_stabilizer` states it as `Set.Finite` of
the stabiliser's carrier, which does not drive typeclass search; this bridges it once. -/]
instance finite_stabilizer_of_properlyDiscontinuousSMul {G T : Type*} [Group G]
    [TopologicalSpace T] [MulAction G T] [ProperlyDiscontinuousSMul G T] (x : T) :
    Finite (MulAction.stabilizer G x) :=
  (ProperlyDiscontinuousSMul.finite_stabilizer x).to_subtype

end TauCeti
