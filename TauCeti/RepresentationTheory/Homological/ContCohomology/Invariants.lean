/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.GroupTheory.GroupAction.FixedPoints

/-!
# Invariants of a discrete module as a module over a finite quotient

For a normal subgroup `H` of `G` acting distributively on an additive group `M`, the invariants
`M ^ H` carry a distributive action of `G ⧸ H`. Over a profinite `G` with `H` open normal this is
the coefficient system of the finite-level tower computing continuous cohomology: the finite group
`G ⧸ H` acts on the discrete module `M ^ H`, and shrinking `H` enlarges `M ^ H` along transition
inclusions.

The invariant subgroup `M ^ H` is Mathlib's `FixedPoints.addSubgroup H M`; no second name for it is
introduced here, and its distributive `G`- and `G ⧸ H`-actions are the generic ones supplied by
`TauCeti/GroupTheory/GroupAction/FixedPoints.lean`. What this file adds is the transition
inclusions of the finite-quotient tower with their equivariance and functoriality, the
functoriality of `M ^ H` in the coefficient module, and the two finite-level facts the tower needs.

The declarations below work for an additive group with a distributive `G`-action; specializing to
an abelian group gives the usual discrete-module theory. The unbundled classes `[AddGroup M]
[DistribMulAction G M]`, with `[TopologicalSpace M] [DiscreteTopology M]` added only where the
topology is used, are the hypotheses throughout, rather than a new bundling structure, so that
instance search composes them freely.

## Main results

* `TauCeti.fixedPointsInclusion`: the coefficient half of a transition map of the finite-quotient
  tower, with its equivariance along `G ⧸ K →* G ⧸ H` and its identity and composition laws.
* `TauCeti.fixedPointsMap` and `TauCeti.fixedPointsQuotientMap`: the functoriality of `M ^ H` in
  the coefficient module, additively and as a `G ⧸ H`-equivariant map.
* `TauCeti.directed_fixedPoints_addSubgroup` and `TauCeti.continuousSMulQuotientFixedPoints`:
  the invariants over the open normal subgroups form a directed family, and each carries a
  continuous action of the discrete quotient group.

## Roadmap

This file addresses the "Constructions" bullet of Layer 0 of
`TauCetiRoadmap/ProfiniteCohomology/README.md`, which asks for the invariants `M ^ U` as a
`G ⧸ U`-module with their induced discrete action, together with that layer's API line for `M ^ U`:
the inclusions `M ^ U ↪ M ^ V` and `M ^ U ↪ M`, functoriality in `M` along equivariant maps and in
`U` along inclusions, and the edge cases at `⊥` and `⊤`. Milestones 2 and 3 of Layer 4's transition
system — the coefficient inclusion and its equivariance after restriction along the quotient
homomorphism — are exactly those Layer 0 items, so they are supplied here; milestones 5 and 6 are
the identity and composition laws of the *induced map on cohomology* and need Layers 1 to 3, so the
identity and composition laws proved here are the coefficient-inclusion half they will rest on.
The "Openness" bullet of Layer 0 lives in
`TauCeti/RepresentationTheory/Homological/ContCohomology/Discrete.lean` and is not restated here.
Directedness is what makes Layer 4's colimit over the finite quotients filtered.
-/

public section

open MulAction

namespace TauCeti

section Invariants

variable {G : Type*} [Group G] {M : Type*} [AddGroup M] [DistribMulAction G M]
variable {H K : Subgroup G}

/-- The coefficient half of a transition map of the finite-quotient tower: for `K ≤ H` the
invariants of `H` include into the invariants of `K`. -/
def fixedPointsInclusion (h : K ≤ H) :
    FixedPoints.addSubgroup H M →+ FixedPoints.addSubgroup K M :=
  AddSubgroup.inclusion (fixedPoints_subgroup_antitone G M h)

/-- The transition inclusion does not move an element of `M`. Together with
`TauCeti.coe_smul_fixedPoints_addSubgroup` this is the equivariance of `M ^ H ↪ M`. -/
@[simp]
theorem coe_fixedPointsInclusion (h : K ≤ H) (m : FixedPoints.addSubgroup H M) :
    (fixedPointsInclusion h m : M) = (m : M) :=
  AddSubgroup.coe_inclusion _ m

/-- The transition inclusions of the tower are monomorphisms. -/
theorem fixedPointsInclusion_injective (h : K ≤ H) :
    Function.Injective (fixedPointsInclusion (M := M) h) :=
  AddSubgroup.inclusion_injective _

/-- The transition inclusion is `G`-equivariant. -/
@[simp]
theorem fixedPointsInclusion_smul [H.Normal] [K.Normal] (h : K ≤ H) (g : G)
    (m : FixedPoints.addSubgroup H M) :
    fixedPointsInclusion h (g • m) = g • fixedPointsInclusion h m :=
  Subtype.ext <| by simp

/-- The transition inclusion is equivariant along Mathlib's canonical quotient homomorphism
`G ⧸ K →* G ⧸ H`. Without this the quotient map and the coefficient inclusion are not a
compatible pair. -/
@[simp]
theorem fixedPointsInclusion_quotientGroupMap_smul [H.Normal] [K.Normal] (h : K ≤ H) (q : G ⧸ K)
    (m : FixedPoints.addSubgroup H M) :
    fixedPointsInclusion h
        ((QuotientGroup.map K H (MonoidHom.id G) (h.trans_eq (Subgroup.comap_id H).symm) q) • m) =
      q • fixedPointsInclusion h m := by
  induction q using QuotientGroup.induction_on with
  | H g => simp

variable (M) in
/-- The transition inclusions are functorial in the subgroup: the identity inclusion is the
identity. -/
@[simp]
theorem fixedPointsInclusion_self (H : Subgroup G) :
    fixedPointsInclusion (M := M) (le_refl H) = AddMonoidHom.id _ :=
  AddMonoidHom.ext fun m ↦ Subtype.ext (coe_fixedPointsInclusion _ m)

/-- The transition inclusions are functorial in the subgroup: they compose. -/
@[simp]
theorem fixedPointsInclusion_comp_fixedPointsInclusion {L : Subgroup G} (h : K ≤ H) (h' : L ≤ K) :
    (fixedPointsInclusion (M := M) h').comp (fixedPointsInclusion h) =
      fixedPointsInclusion (h'.trans h) :=
  AddMonoidHom.ext fun _ ↦ Subtype.ext <| by simp

section Map

variable {N : Type*} [AddGroup N] [DistribMulAction G N]

/-- A `G`-equivariant additive map restricts to the invariants of any subgroup. This is the
functoriality of `M ^ H` in the coefficients. -/
def fixedPointsMap (f : M →+[G] N) (H : Subgroup G) :
    FixedPoints.addSubgroup H M →+ FixedPoints.addSubgroup H N where
  toFun m := ⟨f (m : M), f.toMulActionHom.map_mem_fixedPoints (H := H.toSubmonoid) m.2⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' a b := Subtype.ext (map_add f (a : M) (b : M))

/-- The restricted map is the original map on underlying elements. -/
@[simp]
theorem coe_fixedPointsMap (f : M →+[G] N) (H : Subgroup G)
    (m : FixedPoints.addSubgroup H M) :
    (fixedPointsMap f H m : N) = f (m : M) := by
  rfl

/-- Restriction to invariants preserves the identity map. -/
@[simp]
theorem fixedPointsMap_id (H : Subgroup G) :
    fixedPointsMap (DistribMulActionHom.id G : M →+[G] M) H = AddMonoidHom.id _ :=
  AddMonoidHom.ext fun _ ↦ Subtype.ext <| by simp

/-- Restriction to invariants preserves composition. -/
@[simp]
theorem fixedPointsMap_comp_fixedPointsMap {P : Type*} [AddGroup P] [DistribMulAction G P]
    (f : M →+[G] N) (f' : N →+[G] P) (H : Subgroup G) :
    (fixedPointsMap f' H).comp (fixedPointsMap f H) = fixedPointsMap (f'.comp f) H :=
  AddMonoidHom.ext fun _ ↦ Subtype.ext <| by simp

/-- Restriction to the invariants is equivariant for the `G`-actions of a normal subgroup. -/
@[simp]
theorem fixedPointsMap_smul (f : M →+[G] N) (H : Subgroup G) [H.Normal] (g : G)
    (m : FixedPoints.addSubgroup H M) :
    fixedPointsMap f H (g • m) = g • fixedPointsMap f H m :=
  Subtype.ext <| by simp

/-- Restriction to the invariants is equivariant for the finite-level `G ⧸ H`-actions. -/
@[simp]
theorem fixedPointsMap_quotient_smul (f : M →+[G] N) (H : Subgroup G) [H.Normal] (q : G ⧸ H)
    (m : FixedPoints.addSubgroup H M) :
    fixedPointsMap f H (q • m) = q • fixedPointsMap f H m := by
  induction q using QuotientGroup.induction_on with
  | H g => simp

/-- For normal `H`, restriction to the invariants is a `G ⧸ H`-equivariant additive map. -/
def fixedPointsQuotientMap (f : M →+[G] N) (H : Subgroup G) [H.Normal] :
    FixedPoints.addSubgroup H M →+[G ⧸ H] FixedPoints.addSubgroup H N where
  toAddMonoidHom := fixedPointsMap f H
  map_smul' := fixedPointsMap_quotient_smul f H

/-- The quotient-equivariant map is the original map on underlying elements. -/
@[simp]
theorem coe_fixedPointsQuotientMap (f : M →+[G] N) (H : Subgroup G) [H.Normal]
    (m : FixedPoints.addSubgroup H M) :
    (fixedPointsQuotientMap f H m : N) = f (m : M) := by
  rfl

/-- Quotient-equivariant restriction to invariants preserves the identity map. -/
@[simp]
theorem fixedPointsQuotientMap_id (H : Subgroup G) [H.Normal] :
    fixedPointsQuotientMap (DistribMulActionHom.id G : M →+[G] M) H =
      DistribMulActionHom.id (G ⧸ H) :=
  DistribMulActionHom.ext fun _ ↦ Subtype.ext <| by simp

/-- Quotient-equivariant restriction to invariants preserves composition. -/
@[simp]
theorem fixedPointsQuotientMap_comp_fixedPointsQuotientMap {P : Type*} [AddGroup P]
    [DistribMulAction G P] (f : M →+[G] N) (f' : N →+[G] P) (H : Subgroup G) [H.Normal] :
    (fixedPointsQuotientMap f' H).comp (fixedPointsQuotientMap f H) =
      fixedPointsQuotientMap (f'.comp f) H :=
  DistribMulActionHom.ext fun _ ↦ Subtype.ext <| by simp

/-- Restriction to the invariants commutes with the transition inclusions. -/
theorem fixedPointsMap_comp_fixedPointsInclusion (f : M →+[G] N) (h : K ≤ H) :
    (fixedPointsMap f K).comp (fixedPointsInclusion h) =
      (fixedPointsInclusion h).comp (fixedPointsMap f H) :=
  AddMonoidHom.ext fun _ ↦ Subtype.ext <| by simp

end Map

end Invariants

section FiniteLevel

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
  ⟨continuous_of_discreteTopology⟩

end FiniteLevel

end TauCeti
