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

`TauCeti.TypeALieIndex` is the subtype of `TauCeti.ValidLieTypeIndex` consisting of exactly these
two constructors. Thus every group-valued definition below still takes a validated Lie-type
index: excluded ranks and duplicate representatives cannot reach a carrier or Steinberg map.

For an index `d`, `TauCeti.TypeALieIndex.AmbientGroup d` is the group of
`d.Closure`-valued points of the explicit type-A carrier. Its positive simple-root subgroup at
the Bourbaki node `i` is `TauCeti.TypeALieIndex.simpleRootSubgroup d i`. The Steinberg map is the
entrywise `q`-power Frobenius on `A_r(q)` and the graph automorphism composed with that Frobenius
on `²A_r(q)`. The uniform pinned equation is

```text
F (x_i(u)) = x_{γ i}(u ^ q),
```

where `γ` is the diagram permutation already attached to the index. Finally,
`TauCeti.TypeALieIndex.Group d` applies the roadmap's fixed-points, derived-subgroup, and
central-quotient recipe to this endomorphism. The required commutation and square relation for the
twisted map are `TauCeti.SlStd.graphAutomorphismPoints_comp_frobenius` and
`TauCeti.SlStd.twistedFrobenius_comp_self`; `steinberg_ofTwistedA` identifies this file's branch
with that map without duplicating those results.

This closes the type-A branch of milestones L0, L1, and L3 of
`TauCetiRoadmap/CFSGStatement/README.md`. It does not define the uniform
`ValidLieTypeIndex.AmbientGroup`: the other Dynkin types still need their full-weight carriers.
Nothing here asserts that a constructed group is finite or simple.

## Main declarations

* `TauCeti.TypeALieIndex`: the valid untwisted and twisted type-A indices.
* `TauCeti.TypeALieIndex.AmbientGroup`: the algebraic-closure-valued points of the full-weight
  type-A carrier.
* `TauCeti.TypeALieIndex.simpleRootSubgroup`: the positive simple-root subgroup at a Bourbaki
  node.
* `TauCeti.TypeALieIndex.steinberg`: Frobenius on `A_r(q)` and graph-twisted Frobenius on
  `²A_r(q)`.
* `TauCeti.TypeALieIndex.steinberg_simpleRootSubgroup`: the pinned simple-root-subgroup equation.
* `TauCeti.TypeALieIndex.FixedPoints` and `TauCeti.TypeALieIndex.Group`: the fixed group and its
  derived central quotient.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Chapters 2 and 14.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
-/

public section

namespace TauCeti

namespace LieTypeIndex

/-- Whether a Lie-type index belongs to one of the two type-A families, `A_r(q)` or `²A_r(q)`.

This is a constructor selector, not a mathematical property of a group. In particular it carries
no finiteness, simplicity, or small-field assumption; those restrictions come from the enclosing
`ValidLieTypeIndex`. -/
abbrev IsTypeA : LieTypeIndex → Prop
  | .A _ _ | .twistedA _ _ => True
  | _ => False

/-- Characterization of the two type-A constructors. -/
@[simp]
theorem isTypeA_iff (d : LieTypeIndex) : d.IsTypeA ↔
    match d with
    | .A _ _ | .twistedA _ _ => True
    | _ => False :=
  Iff.rfl

instance : DecidablePred IsTypeA := fun d => by
  cases d <;> rw [isTypeA_iff] <;> infer_instance

end LieTypeIndex

/-- A validated index in one of the two type-A families `A_r(q)` and `²A_r(q)`.

The outer subtype is important: a raw type-A constructor with an excluded rank or field parameter
is not a `TypeALieIndex`. -/
abbrev TypeALieIndex : Type := {d : ValidLieTypeIndex // d.1.IsTypeA}

namespace TypeALieIndex

open LieTypeIndex (isTypeA_iff usesHalfFrobenius_iff)

/-- Introduce a valid untwisted type-A index. -/
abbrev ofA (rank : ℕ) (q : PrimePower) (hvalid : (LieTypeIndex.A rank q).Valid) :
    TypeALieIndex :=
  ⟨⟨.A rank q, hvalid⟩, trivial⟩

/-- Introduce a valid graph-twisted type-A index. -/
abbrev ofTwistedA (rank : ℕ) (q : PrimePower) (hvalid : (LieTypeIndex.twistedA rank q).Valid) :
    TypeALieIndex :=
  ⟨⟨.twistedA rank q, hvalid⟩, trivial⟩

/-- A type-A index, regarded as an ordinary-or-graph-twisted index. -/
abbrev toGraphTwistedIndex (d : TypeALieIndex) : GraphTwistedIndex :=
  ⟨d.1, by
    obtain ⟨⟨d, hvalid⟩, hA⟩ := d
    change d.IsTypeA at hA
    change ¬d.UsesHalfFrobenius
    cases d <;> simp_all [usesHalfFrobenius_iff]⟩

@[simp]
theorem toGraphTwistedIndex_ofA (rank : ℕ) (q : PrimePower)
    (hvalid : (LieTypeIndex.A rank q).Valid) :
    (ofA rank q hvalid).toGraphTwistedIndex =
      ⟨⟨.A rank q, hvalid⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  by rfl

@[simp]
theorem toGraphTwistedIndex_ofTwistedA (rank : ℕ) (q : PrimePower)
    (hvalid : (LieTypeIndex.twistedA rank q).Valid) :
    (ofTwistedA rank q hvalid).toGraphTwistedIndex =
      ⟨⟨.twistedA rank q, hvalid⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  by rfl

@[simp]
theorem diagramPerm_ofA (rank : ℕ) (q : PrimePower)
    (hvalid : (LieTypeIndex.A rank q).Valid) (i : Fin rank) :
    (ofA rank q hvalid).toGraphTwistedIndex.diagramPerm i = i := by
  simp only [toGraphTwistedIndex, GraphTwistedIndex.diagramPerm_A]
  rfl

@[simp]
theorem diagramPerm_ofTwistedA (rank : ℕ) (q : PrimePower)
    (hvalid : (LieTypeIndex.twistedA rank q).Valid) (i : Fin rank) :
    (ofTwistedA rank q hvalid).toGraphTwistedIndex.diagramPerm i = i.rev := by
  simp only [toGraphTwistedIndex, GraphTwistedIndex.diagramPerm_twistedA]
  exact graphPermA_apply rank i

/-- The algebraic-closure-valued points of the explicit full-weight type-A Chevalley carrier. -/
noncomputable abbrev AmbientGroup (d : TypeALieIndex) : Type :=
  SlStd.points d.1.rank d.1.Closure

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of a type-A carrier. -/
noncomputable def simpleRootSubgroup (d : TypeALieIndex) (i : Fin d.1.rank) :
    Multiplicative d.1.Closure →* d.AmbientGroup :=
  SlStd.rootSubgroupPoints d.1.rank (.inl i) d.1.Closure

private noncomputable def plainFrobenius (d : ValidLieTypeIndex) :
    SlStd.points d.rank d.Closure →* SlStd.points d.rank d.Closure :=
  SlStd.frobenius d.rank d.characteristic d.fieldExponent d.Closure

private noncomputable def typeAGraphFrobenius (d : ValidLieTypeIndex) :
    SlStd.points d.rank d.Closure →* SlStd.points d.rank d.Closure :=
  SlStd.twistedFrobenius d.rank d.characteristic d.fieldExponent d.Closure

/-- The entrywise field Frobenius on the validated untwisted type-A carrier. -/
noncomputable def frobenius (rank : ℕ) (q : PrimePower)
    (hvalid : (LieTypeIndex.A rank q).Valid) :
    (ofA rank q hvalid).AmbientGroup →* (ofA rank q hvalid).AmbientGroup :=
  plainFrobenius ⟨.A rank q, hvalid⟩

/-- The reversal graph automorphism composed with field Frobenius on the validated twisted type-A
carrier. -/
noncomputable def twistedFrobenius (rank : ℕ) (q : PrimePower)
    (hvalid : (LieTypeIndex.twistedA rank q).Valid) :
    (ofTwistedA rank q hvalid).AmbientGroup →* (ofTwistedA rank q hvalid).AmbientGroup :=
  typeAGraphFrobenius ⟨.twistedA rank q, hvalid⟩

/-- **The Steinberg endomorphism of a validated type-A index.** It is the `q`-power Frobenius on
`A_r(q)` and the reversal graph automorphism composed with that Frobenius on `²A_r(q)`. -/
noncomputable def steinberg : (d : TypeALieIndex) → d.AmbientGroup →* d.AmbientGroup
  | ⟨⟨.A rank q, hvalid⟩, _⟩ => frobenius rank q hvalid
  | ⟨⟨.twistedA rank q, hvalid⟩, _⟩ => twistedFrobenius rank q hvalid
  | ⟨⟨.B _ _, _⟩, hA⟩ | ⟨⟨.C _ _, _⟩, hA⟩ | ⟨⟨.D _ _, _⟩, hA⟩
  | ⟨⟨.twistedD _ _, _⟩, hA⟩ | ⟨⟨.E6 _, _⟩, hA⟩ | ⟨⟨.E7 _, _⟩, hA⟩
  | ⟨⟨.E8 _, _⟩, hA⟩ | ⟨⟨.F4 _, _⟩, hA⟩ | ⟨⟨.G2 _, _⟩, hA⟩
  | ⟨⟨.twistedE6 _, _⟩, hA⟩ | ⟨⟨.trialityD4 _, _⟩, hA⟩
  | ⟨⟨.suzuki _, _⟩, hA⟩ | ⟨⟨.reeG2 _, _⟩, hA⟩ | ⟨⟨.reeF4 _, _⟩, hA⟩
  | ⟨⟨.tits, _⟩, hA⟩ => False.elim hA

@[simp]
theorem steinberg_ofA (rank : ℕ) (q : PrimePower)
    (hvalid : (LieTypeIndex.A rank q).Valid) :
    (ofA rank q hvalid).steinberg = frobenius rank q hvalid := by
  rw [steinberg.eq_def]

@[simp]
theorem steinberg_ofTwistedA (rank : ℕ) (q : PrimePower)
    (hvalid : (LieTypeIndex.twistedA rank q).Valid) :
    (ofTwistedA rank q hvalid).steinberg = twistedFrobenius rank q hvalid := by
  rw [steinberg.eq_def]

/-- **The Steinberg map has the pinned action on every positive simple-root subgroup.** It sends
`x_i(u)` to `x_{γ i}(u ^ q)`, where `γ` is the diagram permutation of the index and `q` is its
recorded field order. -/
@[simp]
theorem steinberg_simpleRootSubgroup (d : TypeALieIndex) (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (d.toGraphTwistedIndex.diagramPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  obtain ⟨⟨d, hvalid⟩, hA⟩ := d
  change d.IsTypeA at hA
  revert hvalid hA i u
  cases d
  case A rank q =>
    intro hvalid hA i u
    cases hA
    simp only [steinberg.eq_def]
    rw [frobenius.eq_def, plainFrobenius.eq_def]
    simp only [simpleRootSubgroup]
    rw [SlStd.frobenius_rootSubgroupPoints,
      ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
    simp only [toGraphTwistedIndex, GraphTwistedIndex.diagramPerm_A]
    rfl
  case twistedA rank q =>
    intro hvalid hA i u
    cases hA
    change Fin rank at i
    simp only [steinberg.eq_def]
    rw [twistedFrobenius.eq_def, typeAGraphFrobenius.eq_def]
    simp only [simpleRootSubgroup]
    rw [SlStd.twistedFrobenius_rootSubgroupPoints,
      ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
    simp only [toGraphTwistedIndex, GraphTwistedIndex.diagramPerm_twistedA]
    change SlStd.rootSubgroupPoints rank (SlStd.graphRootPerm rank (.inl i)) _ _ =
      SlStd.rootSubgroupPoints rank (.inl (graphPermA rank i)) _ _
    rw [SlStd.graphRootPerm_inl, graphPermA_apply]
  all_goals intro hvalid hA; contradiction

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
