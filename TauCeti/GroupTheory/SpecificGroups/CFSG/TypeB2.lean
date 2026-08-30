/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Frobenius
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.RootDatum
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Closure

/-!
# The Suzuki family on the rank-two type-B carrier

The Suzuki family `²B₂(2^(2m+1))` is built on the rank-two diagram `B₂`, so the ambient group the
CFSG recipe asks for is the group of algebraic-closure-valued points of the simply connected
Chevalley--Demazure group scheme of type `B₂` in characteristic two. This file supplies that
ambient group, its Bourbaki-numbered simple root subgroups, and its `q`-power Frobenius, for every
validated Suzuki index.

The carrier used is Tau Ceti's explicit full-weight type-`C` Chevalley carrier at its rank-two
member, `TauCeti.SpStd.groupScheme 1`. That is not a substitution: the two constructor names
`B 2` and `C 2` denote the same rank-two root system, which is why `TauCeti.DynkinType.Valid`
keeps only `B 2` of the two, and the identification is recorded rather than assumed. The Bourbaki
numbering does move: `TauCeti.SpStd.rootGeneratorWeight_inl_eq_root_simpleIndex_B_two` shows that
the character by which the pinned torus rescales the parameter of the carrier's `k`-th numbered
raising subgroup is the simple root of the pinned `B₂` datum at the *other* node. So the node
correspondence `TauCeti.SuzukiLieIndex.carrierNode` composes the rank equality with the swap of the
two nodes, and every numbered object below is indexed by `Fin d.1.rank`, the upstream Bourbaki
index type of the index's own Dynkin type, rather than by a node of the carrier.

What is *not* here is the Steinberg map, and hence not the finite-group candidate either. The
Steinberg endomorphism of a Suzuki index is `τ ^ (2m+1)` for the special isogeny `τ` of the pinned
`B₂` group scheme in characteristic two, which milestone L2 consumes from Layer 9 of the
reductive-groups roadmap and does not build. What this file provides on that path is the second
factor of the relation `τ ^ 2 = Frob_p` that identifies `τ`: `TauCeti.SuzukiLieIndex.frobenius` is
the `q`-power Frobenius on the same ambient group, at the field order `q = 2^(2m+1)` the index
records.

Nor is the untwisted family `B₂(q)` built here, although it is the other classification-list family
on this diagram and would use the same carrier and the same Frobenius: the branch its Steinberg map
needs is separate work, and this file adds no index subtype for it.

Nothing here asserts that the carrier is reductive, that its weight torus is maximal, that it is
the symplectic group scheme, or that any group below is finite, perfect, or simple.

## Main declarations

* `TauCeti.SuzukiLieIndex.carrierNode`: the node correspondence `Fin d.1.rank ≃ Fin 2` between the
  Bourbaki numbering of `B₂` and the numbering of the rank-two type-`C` carrier.
* `TauCeti.SuzukiLieIndex.AmbientGroup`: the algebraic-closure-valued points of that carrier.
* `TauCeti.SuzukiLieIndex.simpleRootSubgroup`: the positive simple-root subgroup at a Bourbaki node.
* `TauCeti.SuzukiLieIndex.rootGeneratorWeight_carrierNode`: the character of that subgroup is the
  corresponding simple root of the pinned `B₂` datum.
* `TauCeti.SuzukiLieIndex.frobenius` and
  `TauCeti.SuzukiLieIndex.frobenius_simpleRootSubgroup`: the `q`-power Frobenius and its pinned
  equation `Frob_q (x_i(u)) = x_i(u ^ q)`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 14.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* The target signatures realized here follow the human-authored formal skeleton
  `TauCetiRoadmap/CFSGStatement/Suggested.lean`: the ambient group, the numbered simple root
  subgroup, and the Frobenius with its pinned equation, all taken on a validated-index subtype.

This is the `suzuki` branch of milestone L0, "pinned ambient groups", of
`TauCetiRoadmap/CFSGStatement/README.md`, together with the Frobenius half of milestone L1. The
type-A counterpart is `TauCeti/GroupTheory/SpecificGroups/CFSG/TypeA.lean`.
-/

public section

namespace TauCeti

namespace SuzukiLieIndex

open DynkinType

noncomputable section

variable (d : SuzukiLieIndex)

/-! ## The node correspondence -/

/-- **The Bourbaki node of `B₂` named by a node of the rank-two type-`C` carrier**, and back. It is
the rank equality `TauCeti.SuzukiLieIndex.rank_eq_two` followed by the swap of the two nodes, the
swap being what
`TauCeti.SpStd.rootGeneratorWeight_inl_eq_root_simpleIndex_B_two` shows the two numberings differ
by. -/
def carrierNode : Fin d.1.rank ≃ Fin 2 :=
  (finCongr d.rank_eq_two).trans (Equiv.swap 0 1)

@[simp] theorem carrierNode_apply (i : Fin d.1.rank) :
    d.carrierNode i = Equiv.swap 0 1 (finCongr d.rank_eq_two i) :=
  (rfl)

/-! ## The ambient group and its simple root subgroups -/

/-- **The pinned ambient group of a validated Suzuki index**: the points of the explicit
full-weight rank-two type-`C` Chevalley carrier over the algebraic closure of the field with two
elements. It is infinite; no finiteness, reductivity or maximality statement is attached to it. -/
abbrev AmbientGroup : Type := SpStd.points 1 d.1.Closure

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of the `B₂` diagram. It is
the carrier's numbered raising subgroup at the node that `carrierNode` names. -/
def simpleRootSubgroup (i : Fin d.1.rank) : Multiplicative d.1.Closure →* d.AmbientGroup :=
  SpStd.rootSubgroupPoints 1 (.inl (d.carrierNode i)) d.1.Closure

/-- The simple-root subgroup is the carrier's numbered raising subgroup at the corresponding
carrier node. This is the equation through which the upstream root-subgroup API reaches
`simpleRootSubgroup`. It is not a `simp` lemma: `frobenius_simpleRootSubgroup` is the normal form
the pinned equations of this file are stated against, and unfolding to
`TauCeti.SpStd.rootSubgroupPoints` would keep it from firing. -/
theorem simpleRootSubgroup_def (i : Fin d.1.rank) :
    d.simpleRootSubgroup i = SpStd.rootSubgroupPoints 1 (.inl (d.carrierNode i)) d.1.Closure :=
  (rfl)

/-- **The simple-root subgroups sit at the simple roots of the pinned `B₂` datum.** The character
by which the carrier's split torus rescales the parameter of `simpleRootSubgroup i`, read in the
same node correspondence, is the `i`-th simple root of
`TauCeti.DynkinType.simplyConnectedRootDatum` at `B 2`. This is what makes the rank-two type-`C`
carrier the pinned group of the diagram that the Suzuki index names. -/
theorem rootGeneratorWeight_carrierNode (ht : (B 2).Valid) (i j : Fin d.1.rank) :
    SpStd.rootGeneratorWeight 1 (.inl (d.carrierNode i)) (d.carrierNode j) =
      ((B 2).simplyConnectedRootDatum ht).root
        ((B 2).simpleIndex ht (finCongr d.rank_eq_two i)) (finCongr d.rank_eq_two j) := by
  rw [carrierNode_apply, carrierNode_apply,
    SpStd.rootGeneratorWeight_inl_eq_root_simpleIndex_B_two ht,
    Equiv.swap_apply_self, Equiv.swap_apply_self]

/-! ## The Frobenius endomorphism -/

/-- **The `q`-power Frobenius endomorphism of the ambient group of a Suzuki index**, for
`q = 2^(2m+1)` the field order the index records. It is not the Steinberg map of the family, which
is the odd power `τ ^ (2m+1)` of the special isogeny; it is the map that odd power squares to. -/
def frobenius : d.AmbientGroup →* d.AmbientGroup :=
  SpStd.frobenius 1 d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The Frobenius of a Suzuki index is the carrier's Frobenius at the exponent the index records.
This is its unfolding lemma; the definition itself stays sealed. -/
theorem frobenius_def :
    d.frobenius = SpStd.frobenius 1 d.1.characteristic d.1.fieldExponent d.1.Closure :=
  (rfl)

/-- **The Frobenius fixes the Bourbaki numbering of a simple-root subgroup and raises its parameter
to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`. This is the equation milestone L1
asks of an ordinary Frobenius factor. -/
@[simp]
theorem frobenius_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.frobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [frobenius_def, simpleRootSubgroup_def, SpStd.frobenius_rootSubgroupPoints,
    ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

end

end SuzukiLieIndex

end TauCeti
