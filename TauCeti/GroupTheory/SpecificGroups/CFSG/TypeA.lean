/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.TwistedFrobenius
public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Closure
public import TauCeti.GroupTheory.SpecificGroups.CFSG.GraphTwisted

/-!
# The type-A families in the CFSG list

The full-weight type-`A_r` Chevalley carrier, its Frobenius endomorphism, and its pinned graph
automorphism are already available in Tau Ceti. This file connects that construction to the
validated indices for the two type-A families in the classification list:

```text
A_r(q),       ²A_r(q).
```

`TauCeti.TypeALieIndex`, the subtype of `TauCeti.ValidLieTypeIndex` consisting of exactly these two
constructors, is supplied by `CFSG/Index.lean`. Thus every group-valued definition below still
takes a validated Lie-type index: excluded ranks and duplicate representatives cannot reach a
carrier or Steinberg map.

For an index `d`, `TauCeti.TypeALieIndex.AmbientGroup d` is the group of
`d.Closure`-valued points of the explicit type-A carrier. Its positive simple-root subgroup at
the Bourbaki node `i` is `TauCeti.TypeALieIndex.simpleRootSubgroup d i`. The Steinberg map is the
entrywise `q`-power Frobenius on `A_r(q)` and the graph automorphism composed with that Frobenius
on `²A_r(q)`. The uniform pinned equation is

```text
F (x_i(u)) = x_{γ i}(u ^ q),
```

where `γ` is the diagram permutation already attached to the index: the identity on `A_r(q)`, and
on `²A_r(q)` the reversal `i ↦ i.rev` of the zero-based Bourbaki numbering. Finally,
`TauCeti.TypeALieIndex.Group d` applies the roadmap's fixed-points, derived-subgroup, and
central-quotient recipe to this endomorphism.

The branch equations `steinberg_ofA` and `steinberg_ofTwistedA` name the Steinberg map of each
family as `TauCeti.SlStd.frobenius` and `TauCeti.SlStd.twistedFrobenius` outright, so the upstream
results about those maps apply to `d.steinberg` directly and are not restated here. The upstream
lemmas include the commutation `TauCeti.SlStd.graphAutomorphismPoints_comp_frobenius` and the
involution equation `TauCeti.SlStd.graphAutomorphismPoints_graphAutomorphismPoints` required by
milestone L1. Separately, `TauCeti.SlStd.twistedFrobenius_comp_self` supplies the square relation
for the composite Steinberg map. The fixed-point identification
`TauCeti.SlStd.map_subtype_fixedSubgroup_frobenius_eq` and the containment
`TauCeti.SlStd.map_subtype_fixedSubgroup_twistedFrobenius_le` are available in the same way. The
lemma `simpleRootSubgroup_def` plays this role for the root subgroups.

This closes the type-A branch of milestones L0 and L3 and advances milestone L1 of
`TauCetiRoadmap/CFSGStatement/README.md`. L1 still needs an index-level `graphAut` on the type-A
branch of `GraphTwistedIndex`, together with its pinned simple-root equation
`γ (x_i(u)) = x_{γ i}(u)`. This file does not define the uniform
`ValidLieTypeIndex.AmbientGroup`: the other Dynkin types still need their full-weight carriers.
Nothing here asserts that a constructed group is finite or simple.

## Main declarations

* `TauCeti.TypeALieIndex.AmbientGroup`: the algebraic-closure-valued points of the full-weight
  type-A carrier.
* `TauCeti.TypeALieIndex.simpleRootSubgroup` and `TauCeti.TypeALieIndex.simpleRootSubgroup_def`:
  the positive simple-root subgroup at a Bourbaki node, and its identification with the carrier's
  numbered root subgroup.
* `TauCeti.TypeALieIndex.steinberg`, with `TauCeti.TypeALieIndex.steinberg_ofA` and
  `TauCeti.TypeALieIndex.steinberg_ofTwistedA`: Frobenius on `A_r(q)` and graph-twisted Frobenius
  on `²A_r(q)`.
* `TauCeti.TypeALieIndex.steinberg_simpleRootSubgroup`: the pinned simple-root-subgroup equation.
* `TauCeti.TypeALieIndex.FixedPoints` and `TauCeti.TypeALieIndex.Group`: the fixed group and its
  derived central quotient.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Chapters 2 and 14.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* The target signatures realized here follow the human-authored formal skeleton
  `TauCetiRoadmap/CFSGStatement/Suggested.lean`: the ambient group, the numbered simple root
  subgroup, the Steinberg map and its pinned equation `x_i(u) ↦ x_{γ i}(u ^ q)`, the fixed points,
  and the derived central quotient, all taken on a validated-index subtype.
-/

public section

namespace TauCeti

namespace TypeALieIndex

/-- The algebraic-closure-valued points of the explicit full-weight type-A Chevalley carrier. -/
noncomputable abbrev AmbientGroup (d : TypeALieIndex) : Type :=
  SlStd.points d.1.rank d.1.Closure

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of a type-A carrier. -/
noncomputable def simpleRootSubgroup (d : TypeALieIndex) (i : Fin d.1.rank) :
    Multiplicative d.1.Closure →* d.AmbientGroup :=
  SlStd.rootSubgroupPoints d.1.rank (.inl i) d.1.Closure

/-- The simple-root subgroup is the carrier's numbered root subgroup at the positive simple root
`i`. This is the equation through which the upstream root-subgroup API reaches
`simpleRootSubgroup`. It is not a `simp` lemma: `steinberg_simpleRootSubgroup` is the normal form
the pinned equations of this file are stated against, and unfolding to
`TauCeti.SlStd.rootSubgroupPoints` would keep it from firing. -/
theorem simpleRootSubgroup_def (d : TypeALieIndex) (i : Fin d.1.rank) :
    d.simpleRootSubgroup i = SlStd.rootSubgroupPoints d.1.rank (.inl i) d.1.Closure :=
  (rfl)

/-- **The Steinberg endomorphism of a validated type-A index.** It is the `q`-power Frobenius on
`A_r(q)` and the reversal graph automorphism composed with that Frobenius on `²A_r(q)`.

The two branch equations `steinberg_ofA` and `steinberg_ofTwistedA` name the selected upstream map
on each family, so no consumer needs this body. -/
noncomputable def steinberg (d : TypeALieIndex) : d.AmbientGroup →* d.AmbientGroup :=
  -- Matching on `d.1.1` rather than destructuring `d` keeps the validated index `d.1` a variable,
  -- which is what lets `Fin d.1.rank`, `d.1.Closure` and its `ExpChar` instance be found uniformly
  -- in every branch.
  match h : d.1.1 with
  | .A _ _ => SlStd.frobenius d.1.rank d.1.characteristic d.1.fieldExponent d.1.Closure
  | .twistedA _ _ =>
      SlStd.twistedFrobenius d.1.rank d.1.characteristic d.1.fieldExponent d.1.Closure
  | .B _ _ | .C _ _ | .D _ _ | .twistedD _ _ | .E6 _ | .E7 _ | .E8 _ | .F4 _ | .G2 _
  | .twistedE6 _ | .trialityD4 _ | .suzuki _ | .reeG2 _ | .reeF4 _ | .tits =>
      absurd d.2 (by rw [LieTypeIndex.isTypeA_iff, h]; exact not_false)

/-- On `A_r(q)` the Steinberg map is the `q`-power Frobenius of the standard carrier. -/
theorem steinberg_ofA (rank : ℕ) (q : PrimePower)
    (hvalid : (LieTypeIndex.A rank q).Valid) :
    (ofA rank q hvalid).steinberg =
      SlStd.frobenius (ofA rank q hvalid).1.rank (ofA rank q hvalid).1.characteristic
        (ofA rank q hvalid).1.fieldExponent (ofA rank q hvalid).1.Closure := by
  simp only [steinberg]

/-- On `²A_r(q)` the Steinberg map is the graph-twisted `q`-power Frobenius of the standard
carrier, that is, the pinned reversal graph automorphism composed with the Frobenius. -/
theorem steinberg_ofTwistedA (rank : ℕ) (q : PrimePower)
    (hvalid : (LieTypeIndex.twistedA rank q).Valid) :
    (ofTwistedA rank q hvalid).steinberg =
      SlStd.twistedFrobenius (ofTwistedA rank q hvalid).1.rank
        (ofTwistedA rank q hvalid).1.characteristic (ofTwistedA rank q hvalid).1.fieldExponent
        (ofTwistedA rank q hvalid).1.Closure := by
  simp only [steinberg]

/-- **The Steinberg map has the pinned action on every positive simple-root subgroup.** It sends
`x_i(u)` to `x_{γ i}(u ^ q)`, where `γ` is the diagram permutation of the index and `q` is its
recorded field order. -/
@[simp]
theorem steinberg_simpleRootSubgroup (d : TypeALieIndex) (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (d.toGraphTwistedIndex.diagramPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rcases d.exists_eq_ofA_or_exists_eq_ofTwistedA with
    ⟨rank, q, hvalid, rfl⟩ | ⟨rank, q, hvalid, rfl⟩
  · rw [steinberg_ofA, simpleRootSubgroup_def, simpleRootSubgroup_def,
      SlStd.frobenius_rootSubgroupPoints, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      GraphTwistedIndex.diagramPerm_A, Equiv.Perm.one_apply]
  · rw [steinberg_ofTwistedA, simpleRootSubgroup_def, simpleRootSubgroup_def,
      SlStd.twistedFrobenius_rootSubgroupPoints,
      ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      GraphTwistedIndex.diagramPerm_twistedA]
    -- The remaining two equations, `SlStd.graphRootPerm_inl` and `graphPermA_apply`, are stated
    -- for a node of `Fin rank`, whereas the goal types its node by the unreduced
    -- `Fin (LieTypeIndex.twistedA rank q).dynkinType.rank`. The two agree by the exposed
    -- `LieTypeIndex.dynkinType` and `DynkinType.rank`, which is the same reduction that
    -- `GraphTwistedIndex.diagramPerm_twistedA` is stated up to. Present the goal in the reduced
    -- form once, rather than at each rewrite.
    change Fin rank at i
    change SlStd.rootSubgroupPoints rank (SlStd.graphRootPerm rank (.inl i)) _ _ =
      SlStd.rootSubgroupPoints rank (.inl (graphPermA rank i)) _ _
    rw [SlStd.graphRootPerm_inl, graphPermA_apply]

/-- The fixed subgroup of the Steinberg endomorphism attached to a type-A index. -/
abbrev FixedPoints (d : TypeALieIndex) : Type :=
  ↥(fixedSubgroup d.steinberg)

/-- **The finite-simple-group candidate attached to a type-A index**: the derived subgroup of
the Steinberg fixed points, modulo the centre of that derived subgroup. No finiteness or
simplicity assertion is part of this definition. -/
abbrev Group (d : TypeALieIndex) : Type :=
  FixedPointCandidate d.steinberg

end TypeALieIndex

end TauCeti
