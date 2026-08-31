/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Frobenius
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.RootDatum
public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.GraphTwisted

/-!
# The rank-two type-`B` families in the CFSG list

Two families of the classification list are built on the rank-two diagram `B₂`:

```text
B₂(q),        ²B₂(2^(2m+1)).
```

`TauCeti.RankTwoBLieIndex`, the subtype of `TauCeti.ValidLieTypeIndex` consisting of exactly these
two constructors, is supplied by `CFSG/Index.lean`. This file supplies, for every such index, the
group of algebraic-closure-valued points of Tau Ceti's explicit full-weight type-`C` Chevalley
carrier at its rank-two member, `TauCeti.SpStd.groupScheme 1`, together with that group's
Bourbaki-numbered simple root subgroups and its `q`-power Frobenius. Excluded ranks and duplicate
representatives cannot reach any of them: `B₂(2)`, `B₂(3)` and `²B₂(2)` are not indices of the
subtype.

The rank-two type-`C` carrier is not a substitution for the diagram the two families name: the two
constructor names `B 2` and `C 2` denote the same rank-two root system, which is why
`TauCeti.DynkinType.Valid` keeps only `B 2` of the two, and the identification is recorded rather
than assumed. What is recorded is an identification of numbered root characters, not of group
schemes. `TauCeti.SpStd.rootGeneratorWeight_inl_eq_root_simpleIndex_B_two` shows that the character
by which the carrier's split torus rescales the parameter of its `k`-th numbered raising subgroup is
the simple root of the `B₂` root datum at the *other* node. So the node correspondence
`TauCeti.RankTwoBLieIndex.carrierNode` composes the rank equality with the swap of the two nodes,
and every numbered object below is indexed by `Fin d.1.rank`, the upstream Bourbaki index type of
the index's own Dynkin type, rather than by a node of the carrier.

## The two branches part company at the Steinberg map

The carrier and the Frobenius are shared, and the Steinberg endomorphism is not. On the untwisted
branch it is the Frobenius itself, since `TauCeti.GraphTwistedIndex.diagramPerm` is trivial on
`B₂(q)`; that is `TauCeti.TypeBTwoLieIndex.steinberg`, and the recipe of milestone L3 runs on it to
give the candidate `TauCeti.TypeBTwoLieIndex.Group`. On the Suzuki branch the Steinberg map is
instead `τ ^ (2m+1)` for the special isogeny `τ` of the pinned `B₂` group scheme in characteristic
two, which milestone L2 consumes from Layer 9 of the reductive-groups roadmap and does not build,
so no Steinberg map and no candidate group is attached to a `TauCeti.SuzukiLieIndex` here. What
this file provides on that path is the second factor of the relation `τ ^ 2 = Frob_p` that
identifies `τ`: the Frobenius on the same ambient group, at the field order `q = 2^(2m+1)` the
Suzuki index records.

Nothing here asserts that the carrier is reductive, that its weight torus is maximal, that it is
the symplectic group scheme, or that any group below is finite, perfect, or simple. In particular
the carrier is not claimed to be *the* simply connected Chevalley--Demazure group scheme of type
`B₂`: no pinning datum is constructed for it here or in the files it imports, which say so
themselves. The identification with the `B₂` diagram proved below is the one on numbered root
characters stated in `rootGeneratorWeight_carrierNode_eq_root_simpleIndex`.

## Main declarations

* `TauCeti.RankTwoBLieIndex.carrierNode`: the node correspondence `Fin d.1.rank ≃ Fin 2` between the
  Bourbaki numbering of `B₂` and the numbering of the rank-two type-`C` carrier.
* `TauCeti.RankTwoBLieIndex.AmbientGroup`: the algebraic-closure-valued points of that carrier.
* `TauCeti.RankTwoBLieIndex.simpleRootSubgroup`: the positive simple-root subgroup at a Bourbaki
  node.
* `TauCeti.RankTwoBLieIndex.rootGeneratorWeight_carrierNode_eq_root_simpleIndex`: the character of
  that subgroup is the corresponding simple root of the `B₂` root datum.
* `TauCeti.RankTwoBLieIndex.frobenius` and
  `TauCeti.RankTwoBLieIndex.frobenius_simpleRootSubgroup`: the `q`-power Frobenius and its pinned
  equation `Frob_q (x_i(u)) = x_i(u ^ q)`.
* `TauCeti.TypeBTwoLieIndex`: the untwisted branch `B₂(q)`, with
  `TauCeti.TypeBTwoLieIndex.steinberg` its Steinberg map,
  `TauCeti.TypeBTwoLieIndex.mem_fixedSubgroup_steinberg_iff` the description of its fixed points,
  and `TauCeti.TypeBTwoLieIndex.Group` the candidate simple group.

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
diagram the index names, with its root subgroups. **This file does not close L0 on either branch,
and the rank-two type-`C` carrier is not offered as a substitute for that pinned group.** The
pinned group scheme, its pinning, and any identification of a carrier with it are Layer 9 targets of
`TauCetiRoadmap/ReductiveGroups/README.md` that the CFSG roadmap consumes rather than builds; none
of them is proved of `TauCeti.SpStd.groupScheme 1` here or in the files this one imports. What this
file supplies is the branches' explicit carrier, its numbered root characters read in the `B₂` root
datum, the equation `Frob_q (x_i(u)) = x_i(u ^ q)` that milestone L1 asks of an ordinary Frobenius
factor, and, on the untwisted branch, the fixed-point, derived-subgroup and central-quotient recipe
of milestone L3, each in the shape those milestones state it; they transfer to the L0 carrier along
that Layer 9 identification, and not before. The type-A counterpart is
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeA.lean`, and the counterpart on the Geck carrier for
the three unimodular untwisted families is
`TauCeti/GroupTheory/SpecificGroups/CFSG/Unimodular.lean`.
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

/-- **The ambient group this file attaches to a validated rank-two type-`B` index**: the points of
the explicit full-weight rank-two type-`C` Chevalley carrier over the algebraic closure of the prime
field in the characteristic the index records. It is infinite; no finiteness, reductivity, pinning
or maximality statement is attached to it, and it is not claimed to be the pinned `B₂` group
scheme's points that milestone L0 asks for, that identification being the Layer 9 target described
in the module docstring. -/
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
type-`C` carrier serves the diagram that the index names; it is not a claim that the carrier is the
pinned group of that diagram, no pinning being constructed for it. -/
theorem rootGeneratorWeight_carrierNode_eq_root_simpleIndex (ht : (B 2).Valid)
    (i j : Fin d.1.rank) :
    SpStd.rootGeneratorWeight 1 (.inl (d.carrierNode i)) (d.carrierNode j) =
      ((B 2).simplyConnectedRootDatum ht).root
        ((B 2).simpleIndex ht (finCongr d.rank_eq_two i)) (finCongr d.rank_eq_two j) := by
  rw [carrierNode_apply, carrierNode_apply,
    SpStd.rootGeneratorWeight_inl_eq_root_simpleIndex_B_two ht,
    Equiv.swap_apply_self, Equiv.swap_apply_self]

/-! ## The Frobenius endomorphism -/

/-- **The `q`-power Frobenius endomorphism of the ambient group of a rank-two type-`B` index**, for
`q` the field order the index records. On the untwisted branch it is the Steinberg map of the
family; on the Suzuki branch it is not, the Steinberg map there being the odd power `τ ^ (2m+1)` of
the special isogeny, which this map is the square of. -/
def frobenius : d.AmbientGroup →* d.AmbientGroup :=
  SpStd.frobenius 1 d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The Frobenius of a rank-two type-`B` index is the carrier's Frobenius at the exponent the index
records. This is its unfolding lemma; the definition itself stays sealed. -/
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

/-- **A point of the ambient group is fixed by the Frobenius exactly when all of its matrix entries
lie in the field of definition.** Writing `𝔽_q` for `TauCeti.ValidLieTypeIndex.fixedField`, the copy
of the field of `q` elements inside the algebraic closure, the Frobenius-fixed points are the
points of the carrier whose entries lie in `𝔽_q`.

As for `TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_geckFrobenius_iff`, this is not a `simp` lemma:
`simp` rewrites its left-hand side through `MonoidHom.mem_eqLocus`, and the `simpNF` linter rejects
the annotation. -/
theorem mem_fixedSubgroup_frobenius_iff (g : d.AmbientGroup) :
    g ∈ fixedSubgroup d.frobenius ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup (Fin 4) d.1.Closure) :
        Matrix (Fin 4) (Fin 4) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [mem_fixedSubgroup, frobenius_def, SpStd.frobenius_eq_self_iff]
  simp only [mem_frobeniusFixedSubring, ValidLieTypeIndex.mem_fixedField,
    d.1.fieldOrder_eq_characteristic_pow]

end

end RankTwoBLieIndex

/-! ## The untwisted family `B₂(q)` -/

/-- A rank-two type-`B` index whose Steinberg map is not an odd power of a half-Frobenius. By
`TauCeti.LieTypeIndex.exists_eq_of_hasRankTwoBDiagram_of_not_usesHalfFrobenius` these are exactly
the untwisted family `B₂(q)`; the condition removes the Suzuki family `²B₂(2^(2m+1))`, which shares
the diagram. -/
abbrev TypeBTwoLieIndex : Type := {d : RankTwoBLieIndex // ¬d.1.1.UsesHalfFrobenius}

namespace TypeBTwoLieIndex

noncomputable section

variable (d : TypeBTwoLieIndex)

/-- Introduce a valid untwisted index `B₂(q)`. Validity forces `4 ≤ q.card`, by `four_le_fieldOrder`
below. -/
abbrev of (q : PrimePower) (hvalid : (LieTypeIndex.B 2 q).Valid) : TypeBTwoLieIndex :=
  ⟨⟨⟨.B 2 q, hvalid⟩, by simp⟩, by simp [LieTypeIndex.usesHalfFrobenius_iff]⟩

/-- Every untwisted rank-two type-`B` index is of the introduction form. This is the eliminator
matching `of`, so a consumer never repeats the case split over the other constructors. -/
theorem exists_eq_of :
    ∃ (q : PrimePower) (hvalid : (LieTypeIndex.B 2 q).Valid), d = of q hvalid := by
  obtain ⟨⟨⟨e, hvalid⟩, hdiag⟩, hhalf⟩ := d
  obtain ⟨q, rfl⟩ :=
    LieTypeIndex.exists_eq_of_hasRankTwoBDiagram_of_not_usesHalfFrobenius hdiag hhalf
  exact ⟨q, hvalid, rfl⟩

/-- **The field order of an untwisted rank-two type-`B` index is at least four.** The two smaller
prime powers are excluded from the classification list as duplicate names: the recipe run on
`B₂(2)` produces the group the list already carries as `A₆`, and on `B₂(3)` the one it carries as
`²A₃(2)`. Following the roadmap, the first exclusion is placed in
`TauCeti.LieTypeIndex.InStandardRange` and the second in
`TauCeti.LieTypeIndex.IsDuplicateRepresentative`; this theorem reads off what the two together
leave. -/
theorem four_le_fieldOrder : 4 ≤ d.1.1.fieldOrder := by
  obtain ⟨q, hvalid, rfl⟩ := d.exists_eq_of
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff] at hvalid
  have h2 := q.two_le_card
  simp only [ValidLieTypeIndex.fieldOrder, LieTypeIndex.fieldOrder_B]
  omega

/-- An untwisted rank-two type-`B` index is an ordinary index: its Steinberg map is the field
Frobenius composed with a diagram automorphism. -/
abbrev toGraphTwistedIndex : GraphTwistedIndex := ⟨d.1.1, d.2⟩

/-- **The diagram automorphism of an untwisted rank-two type-`B` index is trivial**, which is what
makes `steinberg` below the Frobenius rather than a proper composite: `B₂(q)` carries no
superscript in its printed name. -/
@[simp] theorem diagramPerm_toGraphTwistedIndex :
    GraphTwistedIndex.diagramPerm d.toGraphTwistedIndex = 1 := by
  obtain ⟨q, hvalid, rfl⟩ := d.exists_eq_of
  exact GraphTwistedIndex.diagramPerm_B hvalid

/-! ### The Steinberg map and the finite-group candidate -/

/-- **The Steinberg endomorphism of an untwisted rank-two type-`B` index**: the `q`-power Frobenius
of its ambient group, where `q` is the field order recorded by the index. The family is untwisted,
by `diagramPerm_toGraphTwistedIndex`, so no diagram automorphism and no half-Frobenius enters. -/
def steinberg : d.1.AmbientGroup →* d.1.AmbientGroup :=
  d.1.frobenius

/-- The Steinberg map of an untwisted rank-two type-`B` index is the Frobenius of its ambient group.
This is its unfolding lemma; the definition itself stays sealed.

It is deliberately not a `simp` lemma: `steinberg_simpleRootSubgroup` and
`mem_fixedSubgroup_steinberg_iff` are the normal forms the pinned equations of this section are
stated against, and unfolding to `TauCeti.RankTwoBLieIndex.frobenius` would keep them from
firing. -/
theorem steinberg_eq_frobenius : d.steinberg = d.1.frobenius := by
  rw [steinberg]

/-- **The Steinberg map fixes the Bourbaki numbering of a simple-root subgroup and raises its
parameter to the `q`-th power**, that is, `F (x_i(u)) = x_i(u ^ q)`. This is the equation milestone
L1 asks of an untwisted family. -/
@[simp]
theorem steinberg_simpleRootSubgroup (i : Fin d.1.1.rank) (u : Multiplicative d.1.1.Closure) :
    d.steinberg (d.1.simpleRootSubgroup i u) =
      d.1.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.1.fieldOrder)) := by
  rw [steinberg_eq_frobenius]
  exact d.1.frobenius_simpleRootSubgroup i u

/-- **A point of the ambient group is fixed by the Steinberg map exactly when all of its matrix
entries lie in the field of definition.** The group `H_d` that the milestone L3 recipe is run on
below is therefore the group of points of the rank-two type-`C` carrier whose entries lie in the
copy `𝔽_q` of the field of `q` elements inside the algebraic closure.

As for `TauCeti.RankTwoBLieIndex.mem_fixedSubgroup_frobenius_iff`, this is not a `simp` lemma:
`simp` rewrites its left-hand side through `MonoidHom.mem_eqLocus`, and the `simpNF` linter rejects
the annotation. -/
theorem mem_fixedSubgroup_steinberg_iff (g : d.1.AmbientGroup) :
    g ∈ fixedSubgroup d.steinberg ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup (Fin 4) d.1.1.Closure) :
        Matrix (Fin 4) (Fin 4) d.1.1.Closure) r c ∈ d.1.1.fixedField := by
  rw [steinberg_eq_frobenius]
  exact d.1.mem_fixedSubgroup_frobenius_iff g

/-- **The candidate simple group of an untwisted rank-two type-`B` index**: the derived subgroup of
the fixed points of its Steinberg map, modulo the centre of that derived subgroup.

This is the CFSG recipe on the `B₂(q)` branch, run on the rank-two type-`C` carrier. Nothing here
asserts that it is finite, perfect, or simple, nor that the carrier is the one milestone L0 asks
for. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

/-- Milestone L3 asks every valid branch to carry a group instance; the quotient construction
supplies it. -/
example : _root_.Group d.Group := inferInstance

end

end TypeBTwoLieIndex

end TauCeti
