/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Frobenius
public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Closure
public import TauCeti.GroupTheory.SpecificGroups.CFSG.GraphTwisted

/-!
# The type-C finite-group candidates

This file carries the ordinary symplectic families `C_n(q)` through the explicit construction
prescribed by the CFSG-statement roadmap. `TauCeti.TypeCLieIndex` is the subtype of
`TauCeti.ValidLieTypeIndex` containing exactly the type-`C` constructor, so the conventional rank,
odd-characteristic, and duplicate-representative restrictions are present before any group-valued
definition is formed.

For such an index, `TauCeti.TypeCLieIndex.AmbientGroup` is the group of algebraic-closure-valued
points of `TauCeti.SpStd.groupScheme`, the explicit full-weight type-`C` Chevalley carrier. Its
Steinberg endomorphism is the carrier's `q`-power Frobenius, and its action on every positive
simple-root subgroup is

```text
F (x_i(u)) = x_i(u ^ q).
```

Finally `TauCeti.TypeCLieIndex.Group` applies the uniform fixed-point recipe

```text
H = fixedSubgroup F,        Group = [H, H] / Z([H, H]).
```

This advances the type-`C` slice of milestones L0, L1, and L3 of the CFSG-statement roadmap from
the explicit carrier already constructed in Tau Ceti. Upstream work still has to finish identifying
that carrier as the pinned simply connected reductive group of its named root datum before the L0
acceptance criterion is closed. Nothing here asserts that the resulting groups are finite or
simple. The type-`C` family is kept only in odd characteristic by
`TauCeti.LieTypeIndex.InStandardRange`; in characteristic two its groups are represented by the
coincident type-`B` family.

## Main declarations

* `TauCeti.TypeCLieIndex`: the valid type-`C` indices.
* `TauCeti.TypeCLieIndex.AmbientGroup`: points of the explicit full-weight type-`C` carrier.
* `TauCeti.TypeCLieIndex.steinberg`: the `q`-power Frobenius of that carrier.
* `TauCeti.TypeCLieIndex.simpleRootSubgroup` and `steinberg_simpleRootSubgroup`: the pinned
  positive simple-root subgroups and the Steinberg equation on them.
* `TauCeti.TypeCLieIndex.FixedPoints` and `Group`: the fixed subgroup and its derived central
  quotient.

## References

The construction follows R. W. Carter, *Simple Groups of Lie Type*, Sections 4.4 and 11.3, and
R. Steinberg, *Endomorphisms of Linear Algebraic Groups*, Memoirs AMS **80** (1968), Section 11.
It is the type-`C` slice of milestones L0--L3 in
`TauCetiRoadmap/CFSGStatement/README.md`; the explicit carrier and Frobenius are Layer 9 outputs of
`TauCetiRoadmap/ReductiveGroups/README.md`.
-/

public section

namespace TauCeti

namespace LieTypeIndex

/-- Whether a Lie-type index belongs to the ordinary symplectic family `C_n(q)`.

This is only a constructor selector. The enclosing `ValidLieTypeIndex` supplies the mathematical
rank and field restrictions. -/
abbrev IsTypeC : LieTypeIndex → Prop
  | .C _ _ => True
  | _ => False

instance : DecidablePred IsTypeC := fun d => by
  cases d <;> simp only [IsTypeC] <;> infer_instance

end LieTypeIndex

/-- A validated index in the ordinary symplectic family `C_n(q)`.

In particular, this type contains neither a rank below three nor an even-characteristic parameter,
as both are excluded by `LieTypeIndex.Valid`. -/
abbrev TypeCLieIndex : Type := {d : ValidLieTypeIndex // d.1.IsTypeC}

namespace TypeCLieIndex

open LieTypeIndex (usesHalfFrobenius_iff)

/-- Introduce a valid type-`C` index. -/
abbrev ofC (rank : ℕ) (q : PrimePower) (hvalid : (LieTypeIndex.C rank q).Valid) :
    TypeCLieIndex :=
  ⟨⟨.C rank q, hvalid⟩, trivial⟩

/-- A type-`C` index, regarded as an index whose Steinberg map uses ordinary or graph-twisted
Frobenius. Here the diagram component is always trivial. -/
abbrev toGraphTwistedIndex (d : TypeCLieIndex) : GraphTwistedIndex :=
  ⟨d.1, by
    obtain ⟨⟨d, hvalid⟩, hC⟩ := d
    -- Expose the two nested subtype coercions before splitting on the family constructor.
    change d.IsTypeC at hC
    change ¬d.UsesHalfFrobenius
    cases d <;> simp_all [usesHalfFrobenius_iff]⟩

/-- The type-`C` carrier is indexed by one less than its Dynkin rank, because
`TauCeti.SpStd.groupScheme n` has type `C_(n+1)`. -/
abbrev carrierRank (d : TypeCLieIndex) : ℕ := d.1.rank - 1

/-- Adding one back to the carrier parameter recovers the Dynkin rank. -/
theorem carrierRank_add_one (d : TypeCLieIndex) : d.carrierRank + 1 = d.1.rank := by
  obtain ⟨⟨d, hvalid⟩, hC⟩ := d
  -- Expose the nested subtype coercion so the impossible non-`C` constructors reduce.
  change d.IsTypeC at hC
  cases d <;> try contradiction
  case C rank q =>
    -- Unfold the carrier and Dynkin-rank abbreviations to the common constructor parameter.
    change rank - 1 + 1 = rank
    have hrange := ((LieTypeIndex.valid_iff _).mp hvalid).1
    have hrank := ((LieTypeIndex.inStandardRange_iff _).mp hrange).1
    omega

/-- A Bourbaki node of the Dynkin diagram, reindexed for the `SpStd` carrier parameter. -/
abbrev carrierNode (d : TypeCLieIndex) (i : Fin d.1.rank) : Fin (d.carrierRank + 1) :=
  Fin.cast d.carrierRank_add_one.symm i

/-- The diagram permutation of a type-`C` index is the identity. -/
@[simp]
theorem diagramPerm_apply (d : TypeCLieIndex) (i : Fin d.1.rank) :
    d.toGraphTwistedIndex.diagramPerm i = i := by
  obtain ⟨⟨d, hvalid⟩, hC⟩ := d
  -- Expose the nested subtype coercion so only the type-`C` constructor remains.
  change d.IsTypeC at hC
  cases d <;> try contradiction
  case C rank q =>
    simp only [toGraphTwistedIndex, GraphTwistedIndex.diagramPerm_C]
    rfl

/-- The algebraic-closure-valued points of the explicit full-weight type-`C` Chevalley carrier. -/
noncomputable abbrev AmbientGroup (d : TypeCLieIndex) : Type :=
  SpStd.points d.carrierRank d.1.Closure

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of a type-`C` carrier. -/
noncomputable def simpleRootSubgroup (d : TypeCLieIndex) (i : Fin d.1.rank) :
    Multiplicative d.1.Closure →* d.AmbientGroup :=
  SpStd.rootSubgroupPoints d.carrierRank (.inl (d.carrierNode i)) d.1.Closure

/-- **The Steinberg endomorphism of a validated type-`C` index:** the `q`-power Frobenius of the
explicit full-weight symplectic carrier. -/
noncomputable def steinberg (d : TypeCLieIndex) : d.AmbientGroup →* d.AmbientGroup :=
  SpStd.frobenius d.carrierRank d.1.characteristic d.1.fieldExponent d.1.Closure

/-- **The Steinberg map has the pinned action on every positive simple-root subgroup.** It fixes
the Bourbaki node and raises the parameter to the recorded field order `q`. The node is written
through the uniform diagram permutation to match the interface of the graph-twisted families. -/
@[simp]
theorem steinberg_simpleRootSubgroup (d : TypeCLieIndex) (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (d.toGraphTwistedIndex.diagramPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [diagramPerm_apply, steinberg, simpleRootSubgroup,
    SpStd.frobenius_rootSubgroupPoints, d.1.fieldOrder_eq_characteristic_pow]

/-! ## Fixed points and the candidate group -/

/-- The fixed subgroup of the type-`C` Steinberg endomorphism. -/
noncomputable abbrev FixedPoints (d : TypeCLieIndex) : Subgroup d.AmbientGroup :=
  fixedSubgroup d.steinberg

/-- **The finite-simple-group candidate attached to a type-`C` index:** the derived subgroup of
the Steinberg fixed points, modulo the centre of that derived subgroup. No finiteness or
simplicity instance is asserted. -/
noncomputable abbrev Group (d : TypeCLieIndex) : Type :=
  FixedPointCandidate d.steinberg

end TypeCLieIndex

end TauCeti
