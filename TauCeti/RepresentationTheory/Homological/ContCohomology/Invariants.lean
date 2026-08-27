/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.GroupTheory.GroupAction.FixedPoints

/-!
# Invariants of a discrete module as a module over a quotient

For a normal subgroup `H` of `G` acting distributively on an additive group `M`, the invariants
`M ^ H` carry a distributive action of `G ⧸ H`. Over a profinite `G` with `H` open normal this is
the coefficient system of the finite-level tower computing continuous cohomology: the finite group
`G ⧸ H` acts on the discrete module `M ^ H`, and shrinking `H` enlarges `M ^ H` along transition
inclusions. For a general normal `H` the same quotient action is the coefficient half of
inflation, and it is again continuous as soon as the `G`-action on the discrete module `M` is.

The invariant subgroup `M ^ H` is Mathlib's `FixedPoints.addSubgroup H M`; no second name for it is
introduced here, and its distributive `G`- and `G ⧸ H`-actions are the generic ones supplied by
`TauCeti/GroupTheory/GroupAction/FixedPoints.lean`, together with the generic transition
inclusions and coefficient-map functoriality. What this file adds is the topology: the two
finite-level facts the tower needs — directedness over the open normal subgroups and continuity of
the discrete quotient action — together with the two facts inflation needs, namely continuity of
the `G ⧸ H`-action for an *arbitrary* normal `H` over a continuously acting `G`, and continuity of
the inclusion `M ^ H ↪ M`.

The fixed-point functoriality and finite-level facts are first stated for an additive monoid with a
distributive `G`-action, then specialized to `FixedPoints.addSubgroup` for additive groups; an
abelian group gives the usual discrete-module theory. The topology classes are added only where
continuity is used, and no new bundling structure is introduced, so instance search composes the
unbundled classes freely.

## Main results

* `TauCeti.directed_fixedPoints_addSubmonoid` and
  `TauCeti.continuousSMulQuotientFixedPointsAddSubmonoid`, with their additive-subgroup forms
  `TauCeti.directed_fixedPoints_addSubgroup` and `TauCeti.continuousSMulQuotientFixedPoints`:
  the fixed points over the open normal subgroups form a directed family, and each carries a
  continuous action of the discrete quotient group.
* `TauCeti.continuous_fixedPoints_addSubgroup_subtype`: the inclusion `M ^ H ↪ M` is continuous,
  in the `AddSubgroup.subtype` spelling that the compatible pairs of inflation need.
* `TauCeti.continuousSMulQuotientFixedPointsOfContinuousSMul`: for an *arbitrary* normal subgroup
  `H` of a group with a topology acting continuously on a discrete module, the quotient `G ⧸ H`
  acts continuously on `M ^ H`; no compatibility of the topology of `G` with its group structure
  is used.

## Roadmap

This file addresses the "Constructions" bullet of Layer 0 of
`TauCetiRoadmap/ProfiniteCohomology/README.md`, which asks for the invariants `M ^ U` as a
`G ⧸ U`-module with their induced discrete action, together with that layer's API line for `M ^ U`:
the inclusions `M ^ U ↪ M ^ V` and `M ^ U ↪ M`, functoriality in `M` along equivariant maps and in
`U` along inclusions, and the edge cases at `⊥` and `⊤`. Milestones 2 and 3 of Layer 4's transition
system — the coefficient inclusion and its equivariance after restriction along the quotient
homomorphism — are exactly those Layer 0 items, supplied by the imported generic fixed-point API;
milestones 5 and 6 are the identity and composition laws of the *induced map on cohomology* and
need Layers 1 to 3, so the generic identity and composition laws are the coefficient-inclusion half
they will rest on.
The "Openness" bullet of Layer 0 lives in
`TauCeti/RepresentationTheory/Homological/ContCohomology/Discrete.lean` and is not restated here.
Directedness is what makes Layer 4's colimit over the finite quotients filtered.
-/

public section

open MulAction

namespace TauCeti

section FiniteLevel

variable (G : Type*) [Group G] [TopologicalSpace G]
variable (M : Type*) [AddMonoid M] [DistribMulAction G M]

/-- The finite-level fixed-point additive submonoids form a directed family: the open normal
subgroups are closed under intersection, and the fixed points grow as the subgroup shrinks. -/
theorem directed_fixedPoints_addSubmonoid :
    Directed (· ≤ ·) fun U : OpenNormalSubgroup G ↦ FixedPoints.addSubmonoid U.toSubgroup M :=
  Antitone.directed_le fun _ _ h ↦ fixedPoints_subgroup_antitone G M h

variable [TopologicalSpace M] [DiscreteTopology M] [SeparatelyContinuousMul G]

/-- For an open normal subgroup `U`, the action of the discrete quotient on the fixed-point
additive submonoid is continuous. -/
instance continuousSMulQuotientFixedPointsAddSubmonoid (U : OpenNormalSubgroup G) :
    ContinuousSMul (G ⧸ U.toSubgroup) (FixedPoints.addSubmonoid U.toSubgroup M) :=
  ⟨continuous_of_discreteTopology⟩

end FiniteLevel

section FiniteLevelAddGroup

variable (G : Type*) [Group G] [TopologicalSpace G]
variable (M : Type*) [AddGroup M] [DistribMulAction G M]

/-- The finite-level invariants form a directed family: the open normal subgroups are closed under
intersection, and the invariants grow as the subgroup shrinks. Layer 4's colimit is filtered for
this reason. -/
theorem directed_fixedPoints_addSubgroup :
    Directed (· ≤ ·) fun U : OpenNormalSubgroup G ↦ FixedPoints.addSubgroup U.toSubgroup M :=
  Antitone.directed_le fun _ _ h ↦ fixedPoints_subgroup_antitone G M h

variable [SeparatelyContinuousMul G] [TopologicalSpace M] [DiscreteTopology M]

/-- For an open normal subgroup `U` the action of the discrete quotient group `G ⧸ U` on the
invariant coefficients `M ^ U` is continuous. -/
instance continuousSMulQuotientFixedPoints (U : OpenNormalSubgroup G) :
    ContinuousSMul (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) :=
  inferInstanceAs <| ContinuousSMul (G ⧸ U.toSubgroup)
    (FixedPoints.addSubmonoid U.toSubgroup M)

end FiniteLevelAddGroup

section Subtype

variable (G : Type*) [Group G] (M : Type*) [AddGroup M] [DistribMulAction G M]
variable [TopologicalSpace M]

/-- The inclusion `M ^ H ↪ M` of the invariants is continuous for the subspace topology.

Mathlib's `continuous_subtype_val` says the same thing for the bare coercion `Subtype.val`, whose
type matches `⇑(FixedPoints.addSubgroup H M).subtype` only after unfolding; the compatible pairs of
`TauCeti/RepresentationTheory/Homological/ContCohomology/Inflation.lean` need the statement in the
`AddSubgroup.subtype` spelling, since a proof of the unfolded form blocks rewriting inside every
map built from it. -/
theorem continuous_fixedPoints_addSubgroup_subtype (H : Subgroup G) :
    Continuous ⇑(FixedPoints.addSubgroup H M).subtype :=
  continuous_subtype_val

end Subtype

section ArbitraryNormalSubgroup

variable (G : Type*) [Group G] [TopologicalSpace G]
variable (M : Type*) [AddGroup M] [DistribMulAction G M]
variable [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- For an arbitrary normal subgroup `H`, the action of `G ⧸ H` on the invariants `M ^ H` of a
discrete module is continuous. Unlike
`TauCeti.continuousSMulQuotientFixedPoints`, which reads the continuity off the discreteness of
`G ⧸ H` for open `H` and needs no continuity of the `G`-action, this deduces it from continuity of
the `G`-action: the invariants are discrete, so continuity is continuity in the group variable
alone, and there it is the continuity of the `G`-action read through the quotient map. No
compatibility of the topology of `G` with its group structure is needed, since `G ⧸ H` carries the
quotient topology. -/
instance continuousSMulQuotientFixedPointsOfContinuousSMul (H : Subgroup G) [H.Normal] :
    ContinuousSMul (G ⧸ H) (FixedPoints.addSubgroup H M) where
  continuous_smul := by
    rw [continuous_prod_of_discrete_right]
    intro m
    refine (QuotientGroup.isQuotientMap_mk H).continuous_iff.2 ?_
    refine Topology.IsInducing.subtypeVal.continuous_iff.2 ?_
    exact (continuous_id.smul continuous_const : Continuous fun g : G => g • (m : M))

end ArbitraryNormalSubgroup

end TauCeti
