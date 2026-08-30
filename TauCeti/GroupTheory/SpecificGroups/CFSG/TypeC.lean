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
Steinberg endomorphism is the carrier's `q`-power Frobenius, and its action on every signed
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
* `TauCeti.TypeCLieIndex.rootSubgroup`, `simpleRootSubgroup`, and their Steinberg equations: the
  pinned signed and positive simple-root subgroups.
* `TauCeti.TypeCLieIndex.fixedPoints` and `Group`: the fixed subgroup and its derived central
  quotient.

## References

The construction follows R. W. Carter, *Simple Groups of Lie Type*, Sections 4.4 and 11.3, and
R. Steinberg, *Endomorphisms of Linear Algebraic Groups*, Memoirs AMS **80** (1968), Section 11.
It is the type-`C` slice of milestones L0, L1, and L3 in
`TauCetiRoadmap/CFSGStatement/README.md`;
`TauCetiRoadmap/CFSGStatement/Suggested.lean` supplies the target signatures. The explicit carrier
and Frobenius come from the standard-carrier development governed by
`TauCetiRoadmap/ReductiveGroups/README.md`.
-/

public section

namespace TauCeti

namespace TypeCLieIndex

/-! ## The standard carrier and its Frobenius -/

/-- The type-`C` carrier parameter is one less than its Dynkin rank, because
`TauCeti.SpStd.groupScheme n` has type `C_(n+1)`. -/
abbrev carrierIndex (d : TypeCLieIndex) : ℕ := d.1.rank - 1

/-- Adding one back to the carrier parameter recovers the Dynkin rank. -/
theorem carrierIndex_add_one_eq_rank (d : TypeCLieIndex) :
    d.carrierIndex + 1 = d.1.rank := by
  have hrank := d.three_le_rank
  simp only [carrierIndex]
  omega

/-- A Bourbaki node of the Dynkin diagram, reindexed for the `SpStd` carrier parameter. -/
abbrev carrierNode (d : TypeCLieIndex) (i : Fin d.1.rank) : Fin (d.carrierIndex + 1) :=
  Fin.cast d.carrierIndex_add_one_eq_rank.symm i

/-- The algebraic-closure-valued points of the explicit full-weight type-`C` Chevalley carrier. -/
noncomputable abbrev AmbientGroup (d : TypeCLieIndex) : Type :=
  SpStd.points d.carrierIndex d.1.Closure

/-- A signed simple-root subgroup of the type-`C` carrier. The left and right summands index the
positive and negative simple roots, respectively. -/
noncomputable abbrev rootSubgroup (d : TypeCLieIndex)
    (k : Fin (d.carrierIndex + 1) ⊕ Fin (d.carrierIndex + 1)) :
    Multiplicative d.1.Closure →* d.AmbientGroup :=
  SpStd.rootSubgroupPoints d.carrierIndex k d.1.Closure

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of a type-`C` carrier. -/
noncomputable def simpleRootSubgroup (d : TypeCLieIndex) (i : Fin d.1.rank) :
    Multiplicative d.1.Closure →* d.AmbientGroup :=
  d.rootSubgroup (.inl (d.carrierNode i))

/-- The positive simple-root subgroup is the corresponding standard-carrier root subgroup. -/
theorem simpleRootSubgroup_def (d : TypeCLieIndex) (i : Fin d.1.rank) :
    d.simpleRootSubgroup i =
      SpStd.rootSubgroupPoints d.carrierIndex (.inl (d.carrierNode i)) d.1.Closure := by
  rw [simpleRootSubgroup, rootSubgroup]

/-- **The Steinberg endomorphism of a validated type-`C` index:** the `q`-power Frobenius of the
explicit full-weight symplectic carrier. -/
noncomputable def steinberg (d : TypeCLieIndex) : d.AmbientGroup →* d.AmbientGroup :=
  SpStd.frobenius d.carrierIndex d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The type-`C` Steinberg endomorphism is the standard carrier's recorded Frobenius. -/
theorem steinberg_def (d : TypeCLieIndex) :
    d.steinberg =
      SpStd.frobenius d.carrierIndex d.1.characteristic d.1.fieldExponent d.1.Closure := by
  rw [steinberg]

/-- **The Steinberg map has the pinned action on every signed simple-root subgroup.** -/
@[simp]
theorem steinberg_rootSubgroup (d : TypeCLieIndex)
    (k : Fin (d.carrierIndex + 1) ⊕ Fin (d.carrierIndex + 1))
    (u : Multiplicative d.1.Closure) :
    d.steinberg (d.rootSubgroup k u) =
      d.rootSubgroup k
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  simp only [steinberg_def, rootSubgroup, SpStd.frobenius_rootSubgroupPoints,
    d.1.fieldOrder_eq_characteristic_pow]

/-- **The Steinberg map has the pinned action on every positive simple-root subgroup.** It fixes
the Bourbaki node and raises the parameter to the recorded field order `q`. The node is written
through the uniform diagram permutation to match the interface of the graph-twisted families. -/
@[simp]
theorem steinberg_simpleRootSubgroup (d : TypeCLieIndex) (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (d.toGraphTwistedIndex.diagramPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  simpa only [simpleRootSubgroup_def, rootSubgroup, diagramPerm_eq_one,
    Equiv.Perm.one_apply] using
    d.steinberg_rootSubgroup (.inl (d.carrierNode i)) u

/-! ## Fixed points and the candidate group -/

/-- The fixed subgroup of the type-`C` Steinberg endomorphism. -/
noncomputable abbrev fixedPoints (d : TypeCLieIndex) : Subgroup d.AmbientGroup :=
  fixedSubgroup d.steinberg

/-- **The finite-simple-group candidate attached to a type-`C` index:** the derived subgroup of
the Steinberg fixed points, modulo the centre of that derived subgroup. No finiteness or
simplicity instance is asserted. -/
noncomputable abbrev Group (d : TypeCLieIndex) : Type :=
  FixedPointCandidate d.steinberg

end TypeCLieIndex

end TauCeti
