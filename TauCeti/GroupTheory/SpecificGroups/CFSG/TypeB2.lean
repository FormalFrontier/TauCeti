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

/-!
# The two families on the rank-two diagram `B₂`

Two classification-list families are built on the rank-two diagram `B₂`: the untwisted `B₂(q)` and
the Suzuki family `²B₂(2^(2m+1))`. They share a diagram, so they share a carrier, and
`TauCeti.RankTwoBLieIndex` is the subtype that collects exactly them. This file supplies, for every
such index, the group of algebraic-closure-valued points of Tau Ceti's explicit full-weight type-`C`
Chevalley carrier at its rank-two member, `TauCeti.SpStd.groupScheme 1`, together with that group's
Bourbaki-numbered simple root subgroups and its `q`-power Frobenius; and it then runs the
classification recipe on the untwisted branch, where the Frobenius *is* the Steinberg map.

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

## Why only one of the two branches gets a candidate group

The two families differ exactly in the endomorphism whose fixed points milestone L3 takes. On the
untwisted branch that endomorphism is the `q`-power Frobenius outright, which is what milestone L1's
table asks of an untwisted family and what `TauCeti.TypeB2LieIndex.diagramPerm_toGraphTwistedIndex`
checks: the diagram permutation the index carries is trivial, the `B₂` diagram having no symmetry to
twist by. So `TauCeti.TypeB2LieIndex.steinberg` is the shared Frobenius, and the recipe

```text
H_d = fixedSubgroup d.steinberg,        d.Group = [H_d, H_d] / Z([H_d, H_d])
```

closes on this branch. A validated untwisted index has `4 ≤ q`, by
`TauCeti.TypeB2LieIndex.four_le_fieldOrder`: the classification list carries the two smaller
parameters under other names, `B₂(2)` under `A₆` and `B₂(3)` under `²A₃(2)`, so they are dropped
from the index rather than from the construction.

On the Suzuki branch the Steinberg endomorphism is instead `τ ^ (2m+1)` for the special isogeny `τ`
of the pinned `B₂` group scheme in characteristic two, which milestone L2 consumes from Layer 9 of
the reductive-groups roadmap and does not build; no such map is formed here, and hence no candidate
group either. What this file provides on that path is the second factor of the relation
`τ ^ 2 = Frob_p` that identifies `τ`: `TauCeti.RankTwoBLieIndex.frobenius` is the `q`-power
Frobenius, at the field order `q = 2^(2m+1)` a Suzuki index records, on the very carrier the
Suzuki fixed points will be taken in. A Suzuki index reaches all of it through
`TauCeti.SuzukiLieIndex.toRankTwoBLieIndex`.

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
* `TauCeti.RankTwoBLieIndex.frobenius`, `TauCeti.RankTwoBLieIndex.coe_frobenius_apply` and
  `TauCeti.RankTwoBLieIndex.frobenius_simpleRootSubgroup`: the `q`-power Frobenius, its entrywise
  description, and its pinned equation `Frob_q (x_i(u)) = x_i(u ^ q)`.
* `TauCeti.RankTwoBLieIndex.mem_fixedSubgroup_frobenius_iff`: its fixed points are the points whose
  matrix entries lie in the field of definition `𝔽_q`.
* `TauCeti.TypeB2LieIndex.steinberg` and `TauCeti.TypeB2LieIndex.Group`: the Steinberg
  endomorphism of the untwisted family `B₂(q)` and the candidate group milestone L3 builds from it.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 14.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates II and III, for the numbering
  of the two rank-two diagrams that the node correspondence below moves between.
* The target signatures realized here follow the human-authored formal skeleton
  `TauCetiRoadmap/CFSGStatement/Suggested.lean`: the ambient group, the numbered simple root
  subgroup, the Frobenius with its pinned equation, and the fixed-point recipe, all taken on a
  validated-index subtype.

## Roadmap

Milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md` asks for the points of the *pinned* simply
connected Chevalley--Demazure group scheme of `TauCeti.DynkinType.simplyConnectedRootDatum` at the
diagram the index names, with its root subgroups. **This file does not close L0 on either `B₂`
branch, and the rank-two type-`C` carrier is not offered as a substitute for that pinned group.**
The pinned group scheme, its pinning, and any identification of a carrier with it are Layer 9
targets of `TauCetiRoadmap/ReductiveGroups/README.md` that the CFSG roadmap consumes rather than
builds; none of them is proved of `TauCeti.SpStd.groupScheme 1` here or in the files this one
imports. What this file supplies is the branches' explicit carrier, its numbered root characters
read in the `B₂` root datum, the equation `Frob_q (x_i(u)) = x_i(u ^ q)` that milestone L1 asks of
an ordinary Frobenius factor, and, on the untwisted branch, the milestone L3 recipe run on that
Frobenius, each in the shape those milestones state it; they transfer to the L0 carrier along that
Layer 9 identification, and not before. The counterparts on the branches already assembled are
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeA.lean`,
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeE6.lean` and
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

/-- **The ambient group this file attaches to a validated index on the `B₂` diagram**: the points of
the explicit full-weight rank-two type-`C` Chevalley carrier over the algebraic closure of its prime
field. It is infinite; no finiteness, reductivity, pinning or maximality statement is attached to
it, and it is not claimed to be the pinned `B₂` group scheme's points that milestone L0 asks for,
that identification being the Layer 9 target described in the module docstring.

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
theorem rootGeneratorWeight_carrierNode_eq_root_simpleIndex (ht : (B 2).Valid)
    (i j : Fin d.1.rank) :
    SpStd.rootGeneratorWeight 1 (.inl (d.carrierNode i)) (d.carrierNode j) =
      ((B 2).simplyConnectedRootDatum ht).root
        ((B 2).simpleIndex ht (finCongr d.rank_eq_two i)) (finCongr d.rank_eq_two j) := by
  rw [carrierNode_apply, carrierNode_apply,
    SpStd.rootGeneratorWeight_inl_eq_root_simpleIndex_B_two ht,
    Equiv.swap_apply_self, Equiv.swap_apply_self]

/-! ## The Frobenius endomorphism -/

/-- **The `q`-power Frobenius endomorphism of the ambient group of an index on the `B₂` diagram**,
for `q` the field order the index records. On the untwisted family `B₂(q)` it is the Steinberg map
itself, by `TauCeti.TypeB2LieIndex.steinberg_def`. On the Suzuki family it is not: there the
Steinberg map is the odd power `τ ^ (2m+1)` of the special isogeny, and this is the map that odd
power squares to. -/
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

/-- The Frobenius acts on the ambient group by raising every matrix entry to the `q`-th power. -/
@[simp]
theorem coe_frobenius_apply (g : d.AmbientGroup) (r c : Fin 4) :
    ((d.frobenius g : Matrix.GeneralLinearGroup (Fin 4) d.1.Closure) :
        Matrix (Fin 4) (Fin 4) d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup (Fin 4) d.1.Closure) :
        Matrix (Fin 4) (Fin 4) d.1.Closure) r c ^ d.1.fieldOrder := by
  rw [frobenius_def, d.1.fieldOrder_eq_characteristic_pow]
  exact SpStd.coe_frobenius_apply 1 _ _ _ g r c

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
of the field of `q` elements inside the algebraic closure, the Frobenius fixed points are the points
of the rank-two type-`C` carrier whose entries lie in `𝔽_q`.

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

namespace TypeB2LieIndex

noncomputable section

variable (d : TypeB2LieIndex)

/-! ## The Steinberg endomorphism of the untwisted family -/

/-- **The Steinberg endomorphism of a validated untwisted index `B₂(q)`**: the `q`-power Frobenius
of the ambient group, `q` being the field order the index records. The family is untwisted, so no
diagram automorphism and no half-Frobenius enters; `diagramPerm_toGraphTwistedIndex` is the check
that its diagram permutation is trivial. -/
def steinberg : d.1.AmbientGroup →* d.1.AmbientGroup := d.1.frobenius

/-- The Steinberg map of an untwisted `B₂` index is the Frobenius that both families on the `B₂`
diagram share. This is its unfolding lemma; the definition itself stays sealed, and it is through
this equation that the ambient-group API of `TauCeti.RankTwoBLieIndex` reaches the Steinberg
map. -/
theorem steinberg_def : d.steinberg = d.1.frobenius := (rfl)

/-- **The Steinberg map fixes the Bourbaki numbering of a simple-root subgroup and raises its
parameter to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`. This is the equation
milestone L1 asks of the untwisted families, on this branch. -/
@[simp]
theorem steinberg_simpleRootSubgroup (i : Fin d.1.1.rank) (u : Multiplicative d.1.1.Closure) :
    d.steinberg (d.1.simpleRootSubgroup i u) =
      d.1.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.1.fieldOrder)) := by
  rw [steinberg_def]
  exact d.1.frobenius_simpleRootSubgroup i u

/-- **A point of the ambient group is fixed by the Steinberg map exactly when all of its matrix
entries lie in the field of definition**, so the group `H_d` that the milestone L3 recipe is run on
below is the group of points of the rank-two type-`C` carrier whose entries lie in `𝔽_q`. -/
theorem mem_fixedSubgroup_steinberg_iff (g : d.1.AmbientGroup) :
    g ∈ fixedSubgroup d.steinberg ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup (Fin 4) d.1.1.Closure) :
        Matrix (Fin 4) (Fin 4) d.1.1.Closure) r c ∈ d.1.1.fixedField := by
  rw [steinberg_def]
  exact d.1.mem_fixedSubgroup_frobenius_iff g

/-! ## The classification candidate -/

/-- **The candidate simple group of the untwisted family `B₂(q)`**: the derived subgroup of the
fixed points of its Steinberg map, modulo the centre of that derived subgroup.

This is the milestone L3 recipe on the `B₂` branch, run on the rank-two type-`C` carrier. Nothing
below asserts that it is finite, perfect, or simple, nor that the carrier is the one milestone L0
asks for. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

/-- Milestone L3 asks every valid branch to carry a group instance; the quotient construction
supplies it. -/
example : _root_.Group d.Group := inferInstance

end

end TypeB2LieIndex

end TauCeti
