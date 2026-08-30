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
# The type-C family in the CFSG list

This file connects the explicit full-weight type-`C_r` Chevalley carrier to the validated indices
of the finite simple groups `C_r(q)`. The standard-range predicate on these indices requires
`3 ≤ r` and odd characteristic, so the systematic coincidences `C₂(q) = B₂(q)` and
`C_r(2^e) = B_r(2^e)` cannot reach the construction here.

The carrier already comes with algebraic-closure-valued points, Bourbaki-numbered simple-root
subgroups, and entrywise Frobenius. There is a harmless indexing offset: the carrier parameter
`n` denotes type `C_(n+1)`, whereas `LieTypeIndex.C r q` stores the Dynkin rank `r`. For a
`TauCeti.TypeCLieIndex d`, `TauCeti.TypeCLieIndex.carrierParameter d` is therefore
`d.1.rank - 1`, and `carrierParameter_add_one` proves that the carrier really has `d.1.rank`
numbered simple roots.

The ambient group is the group of points over `d.1.Closure`. Its Steinberg endomorphism is the
`q`-power Frobenius, with pinned equation

```text
F (x_i(u)) = x_i(u ^ q).
```

Finally, `TauCeti.TypeCLieIndex.Group d` is the derived subgroup of the fixed points modulo the
centre of that derived subgroup. This is exactly the recipe prescribed by milestones L0, L1, and
L3 of `TauCetiRoadmap/CFSGStatement/README.md`. Nothing here asserts that the resulting group is
finite or simple.

## Main declarations

* `TauCeti.TypeCLieIndex`: the valid indices in the untwisted type-`C` family.
* `TauCeti.TypeCLieIndex.AmbientGroup`: the algebraic-closure-valued points of the full-weight
  type-`C` carrier.
* `TauCeti.TypeCLieIndex.simpleRootSubgroup`: its positive simple-root subgroups, indexed by the
  Dynkin rank stored in the CFSG index.
* `TauCeti.TypeCLieIndex.steinberg` and `TauCeti.TypeCLieIndex.coe_steinberg_apply`: the indexed
  field Frobenius and its coefficient-level action.
* `TauCeti.TypeCLieIndex.steinberg_simpleRootSubgroup`: the pinned Frobenius equation.
* `TauCeti.TypeCLieIndex.FixedPoints` and `TauCeti.TypeCLieIndex.Group`: the fixed group and its
  derived central quotient.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Chapters 2 and 11.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.

The organization follows the parallel type-`A` CFSG assembly in
[TauCetiProject/TauCeti#5219](https://github.com/TauCetiProject/TauCeti/pull/5219). The type-`C`
rank conversion and all uses of the symplectic carrier are specific to this file.
-/

public section

namespace TauCeti

namespace TypeCLieIndex

/-- The parameter used by `SpStd`: its value `n` denotes Dynkin type `C_(n+1)`. -/
abbrev carrierParameter (d : TypeCLieIndex) : ℕ := d.1.rank - 1

/-- The symplectic carrier selected by an index has exactly the indexed Dynkin rank. -/
@[simp]
theorem carrierParameter_add_one (d : TypeCLieIndex) : d.carrierParameter + 1 = d.1.rank := by
  exact Nat.sub_add_cancel ((by decide : 1 ≤ 3).trans d.three_le_rank)

/-- Reindex a CFSG simple-root node as a node of the symplectic carrier. -/
private abbrev rootIndex (d : TypeCLieIndex) (i : Fin d.1.rank) :
    Fin (d.carrierParameter + 1) :=
  Fin.cast d.carrierParameter_add_one.symm i

/-- The algebraic-closure-valued points of the explicit full-weight type-`C` Chevalley carrier. -/
noncomputable abbrev AmbientGroup (d : TypeCLieIndex) : Type :=
  SpStd.points d.carrierParameter d.1.Closure

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of a type-`C` carrier. -/
noncomputable def simpleRootSubgroup (d : TypeCLieIndex) (i : Fin d.1.rank) :
    Multiplicative d.1.Closure →* d.AmbientGroup :=
  SpStd.rootSubgroupPoints d.carrierParameter (.inl (rootIndex d i)) d.1.Closure

/-- The type-`C` simple-root subgroup is the corresponding positive numbered root subgroup of the
symplectic carrier. This is intentionally not a simp lemma: `steinberg_simpleRootSubgroup` is the
pinned normal form for these expressions. -/
theorem simpleRootSubgroup_def (d : TypeCLieIndex) (i : Fin d.1.rank) :
    d.simpleRootSubgroup i =
      SpStd.rootSubgroupPoints d.carrierParameter
        (.inl (Fin.cast d.carrierParameter_add_one.symm i)) d.1.Closure :=
  (rfl)

/-- **The Steinberg endomorphism of a validated type-`C` index:** entrywise `q`-power
Frobenius on the full-weight symplectic carrier. -/
noncomputable def steinberg (d : TypeCLieIndex) : d.AmbientGroup →* d.AmbientGroup :=
  SpStd.frobenius d.carrierParameter d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The indexed Steinberg endomorphism is the symplectic carrier's entrywise Frobenius. -/
theorem steinberg_def (d : TypeCLieIndex) :
    d.steinberg =
      SpStd.frobenius d.carrierParameter d.1.characteristic d.1.fieldExponent d.1.Closure :=
  (rfl)

/-- Entrywise, the indexed Steinberg endomorphism raises every matrix coefficient to the recorded
field order. The opaque `steinberg` definition keeps this indexed equation as the canonical simp
normal form rather than exposing the carrier's characteristic-and-exponent spelling. -/
@[simp]
theorem coe_steinberg_apply (d : TypeCLieIndex) (g : d.AmbientGroup)
    (i j : Fin ((d.carrierParameter + 1) + (d.carrierParameter + 1))) :
    ((d.steinberg g : Matrix.GeneralLinearGroup
          (Fin ((d.carrierParameter + 1) + (d.carrierParameter + 1))) d.1.Closure) :
        Matrix (Fin ((d.carrierParameter + 1) + (d.carrierParameter + 1)))
          (Fin ((d.carrierParameter + 1) + (d.carrierParameter + 1))) d.1.Closure) i j =
      ((g : Matrix.GeneralLinearGroup
          (Fin ((d.carrierParameter + 1) + (d.carrierParameter + 1))) d.1.Closure) :
        Matrix (Fin ((d.carrierParameter + 1) + (d.carrierParameter + 1)))
          (Fin ((d.carrierParameter + 1) + (d.carrierParameter + 1))) d.1.Closure) i j ^
        d.1.fieldOrder := by
  rw [steinberg_def, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
  exact SpStd.coe_frobenius_apply d.carrierParameter d.1.characteristic d.1.fieldExponent
    d.1.Closure g i j

/-- **The type-`C` Steinberg map has the pinned action on every positive simple-root subgroup.**
It sends `x_i(u)` to `x_i(u ^ q)`, where `q` is the field order recorded by the index. -/
@[simp]
theorem steinberg_simpleRootSubgroup (d : TypeCLieIndex) (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (d.toGraphTwistedIndex.diagramPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  simp only [diagramPerm_eq_one, Equiv.Perm.coe_one, id_eq]
  rw [steinberg_def, simpleRootSubgroup_def,
    SpStd.frobenius_rootSubgroupPoints,
    ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

/-- The fixed subgroup of the Steinberg endomorphism attached to a type-`C` index. -/
abbrev FixedPoints (d : TypeCLieIndex) : Type :=
  ↥(fixedSubgroup d.steinberg)

/-- **The finite-simple-group candidate attached to a type-`C` index:** the derived subgroup of
the Steinberg fixed points, modulo the centre of that derived subgroup. No finiteness or
simplicity assertion is part of this definition. -/
abbrev Group (d : TypeCLieIndex) : Type :=
  FixedPointCandidate d.steinberg

end TypeCLieIndex

end TauCeti
