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
# The Suzuki family on the rank-two type-`C` carrier

The Suzuki family `²B₂(2^(2m+1))` is built on the rank-two diagram `B₂`. This file supplies, for
every validated Suzuki index, the group of algebraic-closure-valued points of Tau Ceti's explicit
full-weight type-`C` Chevalley carrier at its rank-two member, `TauCeti.SpStd.groupScheme 1`,
together with that group's Bourbaki-numbered simple root subgroups and its `q`-power Frobenius.

The rank-two type-`C` carrier is not a substitution for the diagram the family names: the two
constructor names `B 2` and `C 2` denote the same rank-two root system, which is why
`TauCeti.DynkinType.Valid` keeps only `B 2` of the two, and the identification is recorded rather
than assumed. What is recorded is an identification of numbered root characters, not of group
schemes. `TauCeti.SpStd.rootGeneratorWeight_inl_eq_root_simpleIndex_B_two` shows that
the character by which the carrier's split torus rescales the parameter of its `k`-th numbered
raising subgroup is the simple root of the `B₂` root datum at the *other* node. So the node
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
on this diagram and would share the carrier. The two families differ in their Steinberg maps: the
untwisted one takes the `q`-power Frobenius itself, where the Suzuki family takes the odd power
`τ ^ (2m+1)` of the special isogeny. `TauCeti.TypeB2LieIndex` supplies the untwisted validated index
subtype, but attaching the L0 carrier and its Steinberg map is separate work.

Nothing here asserts that the carrier is reductive, that its weight torus is maximal, that it is
the symplectic group scheme, or that any group below is finite, perfect, or simple. In particular
the carrier is not claimed to be *the* simply connected Chevalley--Demazure group scheme of type
`B₂`: no pinning datum is constructed for it here or in the files it imports, which say so
themselves. The identification with the `B₂` diagram proved below is the one on numbered root
characters stated in `rootGeneratorWeight_carrierNode_eq_root_simpleIndex`.

## Main declarations

* `TauCeti.SuzukiLieIndex.carrierNode`: the node correspondence `Fin d.1.rank ≃ Fin 2` between the
  Bourbaki numbering of `B₂` and the numbering of the rank-two type-`C` carrier.
* `TauCeti.SuzukiLieIndex.AmbientGroup`: the algebraic-closure-valued points of that carrier.
* `TauCeti.SuzukiLieIndex.simpleRootSubgroup`: the positive simple-root subgroup at a Bourbaki node.
* `TauCeti.SuzukiLieIndex.rootGeneratorWeight_carrierNode_eq_root_simpleIndex`: the character of
  that subgroup is the corresponding simple root of the `B₂` root datum.
* `TauCeti.SuzukiLieIndex.frobenius` and
  `TauCeti.SuzukiLieIndex.frobenius_simpleRootSubgroup`: the `q`-power Frobenius and its pinned
  equation `Frob_q (x_i(u)) = x_i(u ^ q)`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 14.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates II and III, for the numbering
  of the two rank-two diagrams that the node correspondence below moves between.
* The target signatures realized here follow the human-authored formal skeleton
  `TauCetiRoadmap/CFSGStatement/Suggested.lean`: the ambient group, the numbered simple root
  subgroup, and the Frobenius with its pinned equation, all taken on a validated-index subtype.

## Roadmap

Milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md` asks for the points of the *pinned* simply
connected Chevalley--Demazure group scheme of `TauCeti.DynkinType.simplyConnectedRootDatum` at the
diagram the index names, with its root subgroups. **This file does not close L0 on the `suzuki`
branch, and the rank-two type-`C` carrier is not offered as a substitute for that pinned group.**
The pinned group scheme, its pinning, and any identification of a carrier with it are Layer 9
targets of `TauCetiRoadmap/ReductiveGroups/README.md` that the CFSG roadmap consumes rather than
builds; none of them is proved of `TauCeti.SpStd.groupScheme 1` here or in the files this one
imports. What this file supplies is the branch's explicit carrier, its numbered root characters read
in the `B₂` root datum, and the equation `Frob_q (x_i(u)) = x_i(u ^ q)` that milestone L1 asks of an
ordinary Frobenius factor, each in the shape those milestones state it; they transfer to the L0
carrier along that Layer 9 identification, and not before. The type-A counterpart is
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeA.lean`.
-/

public section

namespace TauCeti

namespace SuzukiLieIndex

open DynkinType

noncomputable section

variable (d : SuzukiLieIndex)

/-! ## The node correspondence -/

/-- **The rank-two type-`C` carrier node corresponding to a Bourbaki-numbered node of `B₂`**, with
the inverse equivalence giving the correspondence back. It is the rank equality
`TauCeti.SuzukiLieIndex.rank_eq_two` followed by the swap of the two nodes, the swap being what
`TauCeti.SpStd.rootGeneratorWeight_inl_eq_root_simpleIndex_B_two` shows the two numberings differ
by. -/
def carrierNode : Fin d.1.rank ≃ Fin 2 :=
  (finCongr d.rank_eq_two).trans (Equiv.swap 0 1)

@[simp] theorem carrierNode_apply (i : Fin d.1.rank) :
    d.carrierNode i = Equiv.swap 0 1 (finCongr d.rank_eq_two i) :=
  (rfl)

/-! ## The ambient group and its simple root subgroups -/

/-- **The ambient group this file attaches to a validated Suzuki index**: the points of the explicit
full-weight rank-two type-`C` Chevalley carrier over the algebraic closure of the field with two
elements. It is infinite; no finiteness, reductivity, pinning or maximality statement is attached to
it, and it is not claimed to be the pinned `B₂` group scheme's points that milestone L0 asks for,
that identification being the Layer 9 target described in the module docstring. -/
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

/-- **The simple-root subgroups sit at the simple roots of the `B₂` root datum.** The character
by which the carrier's split torus rescales the parameter of `simpleRootSubgroup i`, read in the
same node correspondence, is the `i`-th simple root of
`TauCeti.DynkinType.simplyConnectedRootDatum` at `B 2`. This is the sense in which the rank-two
type-`C` carrier serves the diagram that the Suzuki index names; it is not a claim that the
carrier is the pinned group of that diagram, no pinning being constructed for it. -/
theorem rootGeneratorWeight_carrierNode_eq_root_simpleIndex (ht : (B 2).Valid)
    (i j : Fin d.1.rank) :
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
