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

The Steinberg map is also split back into its two factors. `TauCeti.TypeALieIndex.frobenius` is the
`q`-power Frobenius, which is the same map on both families, and
`TauCeti.TypeALieIndex.graphAut` is the pinned graph automorphism realizing the index's diagram
permutation: the identity on `A_r(q)` and signed reverse inverse transpose on `²A_r(q)`. Their
pinned equations are `Frob_q (x_i(u)) = x_i(u ^ q)` and the sign-free `γ (x_i(u)) = x_{γ i}(u)`,
and the two factorizations
```text
F = γ ∘ Frob_q = Frob_q ∘ γ
```
carry the relations that milestone L1 asks of a graph-twisted Steinberg map: the twist order of the
diagram permutation `γ` realizes annihilates `γ`, that is `γ = 1` on `A_r(q)` and `γ ^ 2 = 1` on
`²A_r(q)`, and `γ` commutes with the Frobenius. Its exact order is not proved here.

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

This closes the type-A branch of milestones L0, L1 and L3 of
`TauCetiRoadmap/CFSGStatement/README.md`. This file does not define the uniform
`ValidLieTypeIndex.AmbientGroup`, `ValidLieTypeIndex.frobenius` or `GraphTwistedIndex.graphAut`:
the other Dynkin types still need their full-weight carriers. Nothing here asserts that a
constructed group is finite or simple.

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
* `TauCeti.TypeALieIndex.frobenius` and `TauCeti.TypeALieIndex.frobenius_simpleRootSubgroup`: the
  `q`-power Frobenius factor and its pinned equation.
* `TauCeti.TypeALieIndex.graphAut`, with `TauCeti.TypeALieIndex.graphAut_ofA` and
  `TauCeti.TypeALieIndex.graphAut_ofTwistedA`: the pinned graph automorphism factor.
* `TauCeti.TypeALieIndex.graphAut_simpleRootSubgroup`: its pinned simple-root-subgroup equation
  `γ (x_i(u)) = x_{γ i}(u)`, with no field power and no sign.
* `TauCeti.TypeALieIndex.graphAut_pow_twistOrder` and
  `TauCeti.TypeALieIndex.graphAut_comp_frobenius`: the order relation on the graph factor, and its
  commutation with the Frobenius.
* `TauCeti.TypeALieIndex.steinberg_eq_graphAut_comp_frobenius` and
  `TauCeti.TypeALieIndex.steinberg_eq_frobenius_comp_graphAut`: the Steinberg map is the composite
  of the two factors, in either order.
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

/-! ## The two factors of the Steinberg map -/

/-- **The `q`-power Frobenius endomorphism of a type-A ambient group**, for `q` the Frobenius
parameter recorded by the index. It is the same map on both type-A families: what distinguishes
`²A_r(q)` from `A_r(q)` is the graph automorphism `TauCeti.TypeALieIndex.graphAut` its Steinberg
map composes with this one. -/
noncomputable def frobenius (d : TypeALieIndex) : d.AmbientGroup →* d.AmbientGroup :=
  SlStd.frobenius d.1.rank d.1.characteristic d.1.fieldExponent d.1.Closure

/-- **The Frobenius fixes the Bourbaki numbering of a positive simple-root subgroup and raises its
parameter to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`. -/
@[simp]
theorem frobenius_simpleRootSubgroup (d : TypeALieIndex) (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.frobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [TypeALieIndex.frobenius, simpleRootSubgroup_def, SlStd.frobenius_rootSubgroupPoints,
    ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

/-- **The pinned graph automorphism of a validated type-A index.** It realizes on the ambient group
the diagram permutation `TauCeti.GraphTwistedIndex.diagramPerm` already attached to the index: it is
the identity on `A_r(q)`, whose diagram permutation is trivial, and signed reverse inverse transpose
on `²A_r(q)`, which reverses the Bourbaki numbering.

The two branch equations `graphAut_ofA` and `graphAut_ofTwistedA` name the selected map on each
family, so no consumer needs this body. -/
noncomputable def graphAut (d : TypeALieIndex) : MulAut d.AmbientGroup :=
  -- As in `steinberg`, matching on `d.1.1` rather than destructuring `d` keeps the validated index
  -- `d.1` a variable, which is what lets `d.1.rank` and `d.1.Closure` be found uniformly in every
  -- branch.
  match h : d.1.1 with
  | .A _ _ => 1
  | .twistedA _ _ => SlStd.graphAutomorphismPoints d.1.rank d.1.Closure
  | .B _ _ | .C _ _ | .D _ _ | .twistedD _ _ | .E6 _ | .E7 _ | .E8 _ | .F4 _ | .G2 _
  | .twistedE6 _ | .trialityD4 _ | .suzuki _ | .reeG2 _ | .reeF4 _ | .tits =>
      absurd d.2 (by rw [LieTypeIndex.isTypeA_iff, h]; exact not_false)

/-- On `A_r(q)` the graph automorphism is trivial: the `A_r` diagram symmetry is not used by the
untwisted family. -/
theorem graphAut_ofA (rank : ℕ) (q : PrimePower) (hvalid : (LieTypeIndex.A rank q).Valid) :
    (ofA rank q hvalid).graphAut = 1 := by
  simp only [graphAut]

/-- On `²A_r(q)` the graph automorphism is the standard carrier's pinned graph automorphism, signed
reverse inverse transpose. -/
theorem graphAut_ofTwistedA (rank : ℕ) (q : PrimePower)
    (hvalid : (LieTypeIndex.twistedA rank q).Valid) :
    (ofTwistedA rank q hvalid).graphAut =
      SlStd.graphAutomorphismPoints (ofTwistedA rank q hvalid).1.rank
        (ofTwistedA rank q hvalid).1.Closure := by
  simp only [graphAut]

/-- **The graph automorphism has the pinned action on every positive simple-root subgroup**: it
sends `x_i(u)` to `x_{γ i}(u)`, where `γ` is the diagram permutation of the index. The parameter is
carried across unchanged, with neither a field power nor a sign; on a general root the equation
would acquire a sign forced by the Chevalley structure constants. -/
@[simp]
theorem graphAut_simpleRootSubgroup (d : TypeALieIndex) (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.graphAut (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (d.toGraphTwistedIndex.diagramPerm i) u := by
  rcases d.exists_eq_ofA_or_exists_eq_ofTwistedA with
    ⟨rank, q, hvalid, rfl⟩ | ⟨rank, q, hvalid, rfl⟩
  · rw [graphAut_ofA, MulAut.one_apply, GraphTwistedIndex.diagramPerm_A, Equiv.Perm.one_apply]
  · rw [graphAut_ofTwistedA, simpleRootSubgroup_def, simpleRootSubgroup_def,
      SlStd.graphAutomorphismPoints_rootSubgroupPoints, GraphTwistedIndex.diagramPerm_twistedA]
    -- As in `steinberg_simpleRootSubgroup`, the remaining two equations `SlStd.graphRootPerm_inl`
    -- and `graphPermA_apply` are stated for a node of `Fin rank`, whereas the goal types its node
    -- by the unreduced `Fin (LieTypeIndex.twistedA rank q).dynkinType.rank`. The two agree by the
    -- exposed `LieTypeIndex.dynkinType` and `DynkinType.rank`. Present the goal in the reduced form
    -- once, rather than at each rewrite.
    change Fin rank at i
    change SlStd.rootSubgroupPoints rank (SlStd.graphRootPerm rank (.inl i)) _ _ =
      SlStd.rootSubgroupPoints rank (.inl (graphPermA rank i)) _ _
    rw [SlStd.graphRootPerm_inl, graphPermA_apply]

/-- **The graph automorphism of a type-A index is an involution.** -/
@[simp]
theorem graphAut_graphAut (d : TypeALieIndex) (g : d.AmbientGroup) :
    d.graphAut (d.graphAut g) = g := by
  rcases d.exists_eq_ofA_or_exists_eq_ofTwistedA with
    ⟨rank, q, hvalid, rfl⟩ | ⟨rank, q, hvalid, rfl⟩
  · rw [graphAut_ofA, MulAut.one_apply, MulAut.one_apply]
  · rw [graphAut_ofTwistedA, SlStd.graphAutomorphismPoints_graphAutomorphismPoints]

/-- The graph automorphism of a type-A index squares to the identity in the automorphism group. -/
theorem graphAut_mul_self (d : TypeALieIndex) : d.graphAut * d.graphAut = 1 :=
  MulEquiv.ext fun g => by rw [MulAut.mul_apply, graphAut_graphAut, MulAut.one_apply]

/-- **The twist order of a type-A index annihilates its graph automorphism**, so `γ = 1` on
`A_r(q)` and `γ ^ 2 = 1` on `²A_r(q)`. This is the order relation milestone L1 asks of the graph
factor of a Steinberg map, and it matches `TauCeti.GraphTwistedIndex.diagramPerm_pow_twistOrder` on
the diagram permutation that `γ` realizes. -/
@[simp]
theorem graphAut_pow_twistOrder (d : TypeALieIndex) :
    d.graphAut ^ d.toGraphTwistedIndex.twistOrder = 1 := by
  rcases d.exists_eq_ofA_or_exists_eq_ofTwistedA with
    ⟨rank, q, hvalid, rfl⟩ | ⟨rank, q, hvalid, rfl⟩
  · rw [graphAut_ofA, one_pow]
  · rw [GraphTwistedIndex.twistOrder_twistedA, pow_two, graphAut_mul_self]

/-- **The graph automorphism commutes with the Frobenius.** -/
theorem graphAut_frobenius (d : TypeALieIndex) (g : d.AmbientGroup) :
    d.graphAut (d.frobenius g) = d.frobenius (d.graphAut g) := by
  rcases d.exists_eq_ofA_or_exists_eq_ofTwistedA with
    ⟨rank, q, hvalid, rfl⟩ | ⟨rank, q, hvalid, rfl⟩
  · rw [graphAut_ofA, MulAut.one_apply, MulAut.one_apply]
  · rw [graphAut_ofTwistedA, TypeALieIndex.frobenius, SlStd.graphAutomorphismPoints_frobenius]

/-- The graph automorphism commutes with the Frobenius, as an identity of endomorphisms. This is
the relation `γ ∘ Frob_q = Frob_q ∘ γ` required of the graph-twisted families by milestone L1. -/
theorem graphAut_comp_frobenius (d : TypeALieIndex) :
    d.graphAut.toMonoidHom.comp d.frobenius = d.frobenius.comp d.graphAut.toMonoidHom :=
  MonoidHom.ext fun g => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact d.graphAut_frobenius g

/-- **The Steinberg map of a type-A index is its graph automorphism composed with its Frobenius**,
uniformly on both families. On `A_r(q)` the graph factor is trivial, so the composite is the
Frobenius itself. -/
theorem steinberg_eq_graphAut_comp_frobenius (d : TypeALieIndex) :
    d.steinberg = d.graphAut.toMonoidHom.comp d.frobenius := by
  refine MonoidHom.ext fun g => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rcases d.exists_eq_ofA_or_exists_eq_ofTwistedA with
    ⟨rank, q, hvalid, rfl⟩ | ⟨rank, q, hvalid, rfl⟩
  · rw [steinberg_ofA, graphAut_ofA, TypeALieIndex.frobenius, MulAut.one_apply]
  · rw [steinberg_ofTwistedA, graphAut_ofTwistedA, TypeALieIndex.frobenius,
      SlStd.twistedFrobenius_apply]

/-- The Steinberg map may equally be read with its Frobenius factor last, the two factors
commuting. -/
theorem steinberg_eq_frobenius_comp_graphAut (d : TypeALieIndex) :
    d.steinberg = d.frobenius.comp d.graphAut.toMonoidHom := by
  rw [steinberg_eq_graphAut_comp_frobenius, graphAut_comp_frobenius]

/-! ## The finite-group candidate -/

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
