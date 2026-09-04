/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Frobenius
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.RootDatum
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius

/-!
# The two families on the rank-two diagram `B₂`

Two classification-list families are built on the rank-two diagram `B₂`: the untwisted `B₂(q)` and
the Suzuki family `²B₂(2^(2m+1))`. They share a diagram, so they share a carrier, and
`TauCeti.RankTwoBLieIndex` is the subtype that collects exactly them. This file supplies, for every
such index, the group of algebraic-closure-valued points of Tau Ceti's explicit full-weight type-`C`
Chevalley carrier at its rank-two member, `TauCeti.SpStd.groupScheme 1`, together with that group's
Bourbaki-numbered simple root subgroups, its `q`-power Frobenius, and the description of the points
that Frobenius fixes.

The rank-two type-`C` carrier is not a substitution for the diagram the families name: the two
constructor names `B 2` and `C 2` denote the same rank-two root system, which is why
`TauCeti.DynkinType.Valid` keeps only `B 2` of the two, and the identification is recorded rather
than assumed. What is recorded is an identification of numbered root characters, not of group
schemes. `TauCeti.SpStd.rootGeneratorWeight_inl_eq_root_simpleIndex_B_two` shows that
the character by which the carrier's split torus rescales the parameter of its `k`-th numbered
raising subgroup is the simple root of the `B₂` root datum at the *other* node. So the node
correspondence `TauCeti.RankTwoBLieIndex.carrierNode` composes the rank equality with the swap of
the two nodes, and every numbered object below is indexed by `Fin d.1.rank`, the upstream Bourbaki
index type of the index's own Dynkin type, rather than by a node of the carrier.

## What the shared Frobenius is for on each branch

The two families differ exactly in the endomorphism whose fixed points are taken. On the untwisted
branch that endomorphism is the `q`-power Frobenius outright, in keeping with the trivial diagram
permutation that `TauCeti.TypeB2LieIndex.diagramPerm_toGraphTwistedIndex` computes: the `B₂`
diagram has no symmetry to twist by, its two nodes carrying different root lengths. On the Suzuki
branch it is instead `τ ^ (2m+1)` for the special isogeny `τ` of the pinned `B₂` group scheme in
characteristic two, which is not constructed here. That `τ` is identified by the relation
`τ ^ 2 = Frob_p` in the prime characteristic, and `Frob_p` is not the map supplied here: validity
forces `1 ≤ m`, so the field order `q = 2 ^ (2m+1)` the index records is larger than the prime.
What this file supplies is `Frob_q`, the map the odd power `τ ^ (2m+1)` squares to. Either way the
map below is the `q`-power Frobenius at the field order the index records, taken on this carrier.
A Suzuki index reaches all of it through `TauCeti.SuzukiLieIndex.toRankTwoBLieIndex`.

Neither branch gets a Steinberg endomorphism here, and neither gets a candidate simple group. The
Steinberg endomorphism of either family is an endomorphism of the points of the *pinned* simply
connected group scheme of the diagram, and no identification of the carrier below with that pinned
group is available; so neither that endomorphism, nor the group of its fixed points, nor the
quotient of the derived subgroup of those fixed points by its centre, is stated of the rank-two
type-`C` carrier. What is named below is named after what it is:
`TauCeti.RankTwoBLieIndex.frobenius` is the Frobenius of this carrier, and
`TauCeti.RankTwoBLieIndex.mem_fixedSubgroup_frobenius_iff` describes the group it fixes as the
points whose matrix entries lie in the field of definition `𝔽_q`.

Nothing here asserts that the carrier is reductive, that its weight torus is maximal, that it is
the symplectic group scheme, or that any group below is finite, perfect, or simple. In particular
the carrier is not claimed to be *the* simply connected Chevalley--Demazure group scheme of type
`B₂`: no pinning datum is constructed for it here or in the files it imports, which say so
themselves. The identification with the `B₂` diagram proved below is the one on numbered root
characters stated in `rootGeneratorWeight_carrierNode_eq_root_simpleIndex`.

The same carrier-and-Frobenius material on the branches already assembled is in
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeA.lean`,
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeE6.lean` and
`TauCeti/GroupTheory/SpecificGroups/CFSG/Unimodular.lean`.

## Main declarations

* `TauCeti.RankTwoBLieIndex.carrierNode`: the node correspondence `Fin d.1.rank ≃ Fin 2` between the
  Bourbaki numbering of `B₂` and the numbering of the rank-two type-`C` carrier.
* `TauCeti.RankTwoBLieIndex.AmbientGroup`: the algebraic-closure-valued points of that carrier.
* `TauCeti.RankTwoBLieIndex.simpleRootSubgroup`: the positive simple-root subgroup at a Bourbaki
  node.
* `TauCeti.RankTwoBLieIndex.rootGeneratorWeight_carrierNode_eq_root_simpleIndex`: the character of
  that subgroup is the corresponding simple root of the `B₂` root datum.
* `TauCeti.RankTwoBLieIndex.frobenius`, `TauCeti.RankTwoBLieIndex.coe_frobenius_apply` and
  `TauCeti.RankTwoBLieIndex.frobenius_simpleRootSubgroup`: the `q`-power Frobenius, its entrywise
  description, and its pinned equation `Frob_q (x_i(u)) = x_i(u ^ q)`.
* `TauCeti.RankTwoBLieIndex.mem_fixedSubgroup_frobenius_iff`: its fixed points are the points whose
  matrix entries lie in the field of definition `𝔽_q`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 14.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates II and III, for the numbering
  of the two rank-two diagrams that the node correspondence below moves between.
* The target signatures realized here follow the human-authored formal skeleton
  `TauCetiRoadmap/CFSGStatement/Suggested.lean`: the ambient group, the numbered simple root
  subgroup, and the Frobenius with its pinned equation, all taken on a validated-index subtype.
-/

public section

namespace TauCeti

namespace RankTwoBLieIndex

open DynkinType

noncomputable section

variable (d : RankTwoBLieIndex)

/-! ## The node correspondence -/

/-- **The rank-two type-`C` carrier node corresponding to a Bourbaki-numbered node of `B₂`**, with
the inverse equivalence giving the correspondence back. It is the rank equality
`TauCeti.RankTwoBLieIndex.rank_eq_two` followed by the swap of the two nodes, the swap being what
`TauCeti.SpStd.rootGeneratorWeight_inl_eq_root_simpleIndex_B_two` shows the two numberings differ
by. -/
def carrierNode : Fin d.1.rank ≃ Fin 2 :=
  (finCongr d.rank_eq_two).trans (Equiv.swap 0 1)

@[simp] theorem carrierNode_apply (i : Fin d.1.rank) :
    d.carrierNode i = Equiv.swap 0 1 (finCongr d.rank_eq_two i) :=
  (rfl)

/-! ## The ambient group and its simple root subgroups -/

/-- **The ambient group this file attaches to a validated index on the `B₂` diagram**: the points of
the explicit full-weight rank-two type-`C` Chevalley carrier over the algebraic closure of its prime
field. It is infinite; no finiteness, reductivity, pinning or maximality statement is attached to
it, and it is not claimed to be the points of the pinned simply connected group scheme of type
`B₂`; no such identification is available, as the module docstring explains.

It is the same group for the untwisted and the Suzuki family of a given field order, those two
differing only in the endomorphism taken of it. -/
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
type-`C` carrier serves the diagram that the two rank-two type-`B` families name; it is not a claim
that the carrier is the pinned group of that diagram, no pinning being constructed for it. -/
theorem rootGeneratorWeight_carrierNode_eq_root_simpleIndex (i j : Fin d.1.rank) :
    SpStd.rootGeneratorWeight 1 (.inl (d.carrierNode i)) (d.carrierNode j) =
      ((B 2).simplyConnectedRootDatum (valid_B.mpr le_rfl)).root
        ((B 2).simpleIndex (valid_B.mpr le_rfl) (finCongr d.rank_eq_two i))
        (finCongr d.rank_eq_two j) := by
  rw [carrierNode_apply, carrierNode_apply,
    SpStd.rootGeneratorWeight_inl_eq_root_simpleIndex_B_two (valid_B.mpr le_rfl),
    Equiv.swap_apply_self, Equiv.swap_apply_self]

/-! ## The Frobenius endomorphism -/

/-- **The `q`-power Frobenius endomorphism of the ambient group of an index on the `B₂` diagram**,
for `q` the field order the index records. The map the Steinberg endomorphism of either family on
this diagram is built from is its counterpart on the pinned simply connected carrier: on the
untwisted family `B₂(q)` that endomorphism is the `q`-power Frobenius outright, and on the Suzuki
family it is the odd power `τ ^ (2m+1)` of the special isogeny, the map that odd power squares to
being the `q`-power Frobenius. Neither is formed here. -/
def frobenius : d.AmbientGroup →* d.AmbientGroup :=
  SpStd.frobenius 1 d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The Frobenius of an index on the `B₂` diagram is the carrier's Frobenius at the exponent the
index records. This is its unfolding lemma; the definition itself stays sealed.

It is deliberately not a `simp` lemma: `frobenius_simpleRootSubgroup` and `coe_frobenius_apply` are
the normal forms the pinned equations of this file are stated against, and unfolding to
`TauCeti.SpStd.frobenius` would keep them from firing. -/
theorem frobenius_def :
    d.frobenius = SpStd.frobenius 1 d.1.characteristic d.1.fieldExponent d.1.Closure :=
  (rfl)

/-- The Frobenius acts on the ambient group by raising every matrix entry to the `q`-th power.

The index type is written `Fin 4`, which is the carrier's own `Fin ((1 + 1) + (1 + 1))` at `n = 1`
definitionally but not syntactically. Only the binders of `r` and `c` are affected: the entry
coercions elaborate at the carrier's index type either way. -/
@[simp]
theorem coe_frobenius_apply (g : d.AmbientGroup) (r c : Fin 4) :
    ((d.frobenius g : Matrix.GeneralLinearGroup (Fin 4) d.1.Closure) :
        Matrix (Fin 4) (Fin 4) d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup (Fin 4) d.1.Closure) :
        Matrix (Fin 4) (Fin 4) d.1.Closure) r c ^ d.1.fieldOrder := by
  rw [frobenius_def, d.1.fieldOrder_eq_characteristic_pow]
  -- The upstream lemma is instantiated by hand rather than rewritten with: its entry arguments
  -- live in `Fin ((1 + 1) + (1 + 1))`, which is only definitionally the `Fin 4` stated above.
  exact SpStd.coe_frobenius_apply 1 _ _ _ g r c

/-- **The Frobenius fixes the Bourbaki numbering of a simple-root subgroup and raises its parameter
to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`. This is the equation that pins an
ordinary Frobenius factor of a Steinberg map on the numbered simple-root subgroups. -/
@[simp]
theorem frobenius_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.frobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [frobenius_def, simpleRootSubgroup_def, SpStd.frobenius_rootSubgroupPoints,
    ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

/-- **A point of the ambient group is fixed by the Frobenius exactly when all of its matrix entries
lie in the field of definition.** Writing `𝔽_q` for `TauCeti.ValidLieTypeIndex.fixedField`, the copy
of the field of `q` elements inside the algebraic closure, the Frobenius fixed points are the points
of the rank-two type-`C` carrier whose entries lie in `𝔽_q`. As in `coe_frobenius_apply`, the index
type is written `Fin 4` for the carrier's own `Fin ((1 + 1) + (1 + 1))` at `n = 1`; here the two
entry binders are elaborated at the carrier's index type as well.

As for `TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_geckFrobenius_iff`, this is not a `simp` lemma:
`TauCeti.fixedSubgroup` is `MonoidHom.eqLocus` against the identity, so `simp` rewrites its
left-hand side to `d.frobenius g = g` through `MonoidHom.mem_eqLocus`, and the `simpNF` linter
rejects the annotation. -/
theorem mem_fixedSubgroup_frobenius_iff (g : d.AmbientGroup) :
    g ∈ fixedSubgroup d.frobenius ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup (Fin 4) d.1.Closure) :
        Matrix (Fin 4) (Fin 4) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [mem_fixedSubgroup, frobenius_def, SpStd.frobenius_eq_self_iff]
  simp only [mem_frobeniusFixedSubring, ValidLieTypeIndex.mem_fixedField,
    d.1.fieldOrder_eq_characteristic_pow]

end

end RankTwoBLieIndex

end TauCeti
