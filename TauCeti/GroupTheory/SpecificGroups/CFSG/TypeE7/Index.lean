/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Index

/-!
# The index of the exceptional family `E₇(q)`

The classification list carries a single family on the `E₇` diagram, the untwisted `E₇(q)`: the
diagram is a tree with no nontrivial symmetry, so there is no graph automorphism to twist a
Steinberg map by and no partner family beside it.

This file cuts that family out of `TauCeti.LieTypeIndex` with the constructor selector
`TauCeti.LieTypeIndex.IsTypeE7` and the subtype `TauCeti.TypeE7LieIndex` of validated indices
satisfying it, and reads off the numbered data such an index carries: its Dynkin type is `E₇` and
its rank is seven. Every `E₇` parameter is valid, so the family contributes one classification
entry for each prime power.

Nothing here mentions a group: these are selectors on the index datatype, matching the type-`E₆`
index API of `TauCeti/GroupTheory/SpecificGroups/CFSG/Index.lean`. The carrier the family is built
on is attached to such an index in
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeE7/Basic.lean`, and the diagram permutation its
Steinberg map composes with in `TauCeti/GroupTheory/SpecificGroups/CFSG/GraphTwisted.lean`.

## Main declarations

* `TauCeti.LieTypeIndex.IsTypeE7`: the constructor selector for the family.
* `TauCeti.TypeE7LieIndex`: the subtype of validated indices it cuts out, with the introduction
  form `TauCeti.TypeE7LieIndex.of` and the matching eliminator
  `TauCeti.TypeE7LieIndex.exists_eq_of`.

## Main results

* `TauCeti.LieTypeIndex.valid_E7`: every `E₇` parameter is a preferred classification
  representative.
* `TauCeti.LieTypeIndex.not_usesHalfFrobenius_of_isTypeE7`: an `E₇` index takes an ordinary
  Steinberg map, so it is one of `TauCeti.GraphTwistedIndex`.
* `TauCeti.TypeE7LieIndex.dynkinType_eq` and `TauCeti.TypeE7LieIndex.rank_eq_seven`: the family is
  built on the diagram `E₇`, of rank seven.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §14, for the classification list this index ranges
  over.
-/

public section

namespace TauCeti

namespace LieTypeIndex

/-- Whether a Lie-type index names the untwisted exceptional family `E₇(q)`.

This is a constructor selector, not a mathematical property of a group: it asserts no finiteness
and no simplicity. Unlike `TauCeti.LieTypeIndex.IsTypeE6`, it has no graph-twisted counterpart to
be distinguished from, the `E₇` diagram having no nontrivial symmetry. -/
def IsTypeE7 : LieTypeIndex → Prop
  | .E7 _ => True
  | _ => False

/-- Characterization of the type-`E₇` constructor. -/
@[simp] theorem isTypeE7_iff (d : LieTypeIndex) : d.IsTypeE7 ↔
    match d with
    | .E7 _ => True
    | _ => False :=
  Iff.rfl

instance : DecidablePred IsTypeE7 := fun d => by
  cases d <;> rw [isTypeE7_iff] <;> infer_instance

/-- The family `E₇(q)` does not use a half-Frobenius: its Steinberg map is a diagram automorphism
composed with the field Frobenius, so an `E₇` index is one of `TauCeti.GraphTwistedIndex`. -/
theorem not_usesHalfFrobenius_of_isTypeE7 {d : LieTypeIndex} (h : d.IsTypeE7) :
    ¬ d.UsesHalfFrobenius := by
  cases d <;> simp_all [usesHalfFrobenius_iff]

/-- **Every `E₇(q)` index is valid.** The `E₇` row of `TauCeti.LieTypeIndex.InStandardRange` is
unrestricted, and no `E₇` parameter is a duplicate representative, so the family contributes one
classification entry for each prime power. -/
theorem valid_E7 (q : PrimePower) : (E7 q).Valid := by simp

end LieTypeIndex

/-- A validated index in the exceptional family `E₇(q)`.

Every `E₇(q)` is valid, by `TauCeti.LieTypeIndex.valid_E7`, so the outer subtype excludes nothing
here; it is retained because the carrier-valued constructions of the family take
`TauCeti.ValidLieTypeIndex`. -/
abbrev TypeE7LieIndex : Type _ := {d : ValidLieTypeIndex // d.1.IsTypeE7}

/-! ## The index and its numbered data -/

namespace TypeE7LieIndex

/-- Introduce the index `E₇(q)`. No validity hypothesis is taken: every `E₇` parameter is valid by
`TauCeti.LieTypeIndex.valid_E7`. -/
abbrev of (q : PrimePower) : TypeE7LieIndex :=
  ⟨⟨.E7 q, LieTypeIndex.valid_E7 q⟩, (LieTypeIndex.isTypeE7_iff _).mpr trivial⟩

/-- Every type-`E₇` index is of the introduction form. This is the eliminator matching `of`, so a
consumer never repeats the case split over the other constructors. -/
theorem exists_eq_of (d : TypeE7LieIndex) : ∃ q : PrimePower, d = of q := by
  obtain ⟨⟨d, hvalid⟩, hd⟩ := d
  revert hvalid hd
  cases d
  case E7 q => exact fun _ _ => ⟨q, rfl⟩
  all_goals exact fun _ hd => ((LieTypeIndex.isTypeE7_iff _).mp hd).elim

/-- The family `E₇(q)` is built on the diagram `E₇`. -/
@[simp] theorem dynkinType_eq (d : TypeE7LieIndex) : d.1.dynkinType = .E7 := by
  obtain ⟨q, rfl⟩ := d.exists_eq_of
  exact LieTypeIndex.dynkinType_E7 q

/-- The family `E₇(q)` has rank seven, that being the rank of `E₇`. -/
@[simp] theorem rank_eq_seven (d : TypeE7LieIndex) : d.1.rank = 7 :=
  congrArg DynkinType.rank d.dynkinType_eq

end TypeE7LieIndex

end TauCeti
