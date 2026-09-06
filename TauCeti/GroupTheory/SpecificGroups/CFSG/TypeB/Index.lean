/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Index

/-!
# The validated indices of the untwisted family `Bₙ(q)`

The classification list carries the untwisted odd orthogonal family named `Bₙ(q)` for `n ≥ 2`,
whose matrix name in Gorenstein--Lyons--Solomon is `Ω_{2n+1}(q)`. This file cuts that family out of
`TauCeti.ValidLieTypeIndex`, in the shape the other families are cut out in
`TauCeti/GroupTheory/SpecificGroups/CFSG/Index.lean`: a constructor selector, the subtype of
validated indices it selects, an introduction form, and the diagram facts that hold of every index
of the subtype.

The selector is false on the Suzuki family `²B₂(2^(2m+1))`, which shares the rank-two diagram `B₂`
but takes an odd power of a half-Frobenius for its Steinberg map, and the two families on that
diagram are separated instead by `TauCeti.RankTwoBLieIndex` and `TauCeti.TypeB2LieIndex`.

This file is diagram-level indexing data only: it attaches no carrier, no endomorphism and no
group, and nothing here asserts that a named group is finite or simple. The carrier of the family,
its Steinberg endomorphism and the fixed-point construction run on them are in
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeB/Basic.lean`, and the rank-two members are also
served, beside the Suzuki family, in
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeB/Two.lean`.

## Main declarations

* `TauCeti.LieTypeIndex.IsTypeB` and `TauCeti.TypeBLieIndex`: the constructor selector of the
  family and the subtype of validated indices it cuts out.
* `TauCeti.TypeBLieIndex.ofB` and `TauCeti.TypeBLieIndex.exists_eq_ofB`: the introduction form and
  the induction principle it supplies.
* `TauCeti.TypeBLieIndex.dynkinType_cartanMatrix_apply` and `TauCeti.TypeBLieIndex.two_le_rank`:
  the Cartan matrix of the diagram such an index names, and the rank bound that the double edge
  naming the family imposes.

## References

* D. Gorenstein, R. Lyons and R. Solomon, *The Classification of the Finite Simple Groups*,
  Number 1, §2.2, for the small-parameter exclusions that the validated index carries.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II, for the numbering of the
  `Bₙ` diagram.
-/

public section

namespace TauCeti

namespace LieTypeIndex

/-- Whether a Lie-type index belongs to the untwisted family `B_r(q)`.

This is a constructor selector, not a mathematical property of a group. It is false on the Suzuki
family `²B₂(2^(2m+1))`, which shares the `B₂` diagram but takes an odd power of a half-Frobenius
for its Steinberg map. The rank, field, and preferred-representative restrictions come from the
enclosing `TauCeti.ValidLieTypeIndex`. -/
abbrev IsTypeB : LieTypeIndex → Prop
  | .B _ _ => True
  | _ => False

instance : DecidablePred IsTypeB := fun d => by
  cases d <;> infer_instance

end LieTypeIndex

/-- A validated index in the untwisted type-`B` family `B_r(q)`.

In particular, its rank is at least two, and neither `B₂(2)`, whose recipe does not produce a
simple group, nor `B₂(3)`, which the list carries as `²A₃(2)`, is an index of this subtype. The
Suzuki family `²B₂(2^(2m+1))`, which shares the `B₂` diagram, is not of this subtype either. -/
abbrev TypeBLieIndex : Type _ := {d : ValidLieTypeIndex // d.1.IsTypeB}

namespace TypeBLieIndex

open LieTypeIndex (inStandardRange_iff valid_iff)

/-- Introduce a valid type-`B` index. -/
abbrev ofB (rank : ℕ) (q : PrimePower) (hvalid : (LieTypeIndex.B rank q).Valid) :
    TypeBLieIndex :=
  ⟨⟨.B rank q, hvalid⟩, trivial⟩

/-- Every type-B index is an introduction form `ofB rank q hvalid`. -/
theorem exists_eq_ofB (d : TypeBLieIndex) :
    ∃ (rank : ℕ) (q : PrimePower) (hvalid : (LieTypeIndex.B rank q).Valid),
      d = ofB rank q hvalid := by
  obtain ⟨⟨d, hvalid⟩, hB⟩ := d
  revert hvalid hB
  cases d
  case B rank q => exact fun hvalid _ => ⟨rank, q, hvalid, rfl⟩
  all_goals exact fun _ hB => False.elim hB

/-- **The Cartan matrix of the diagram a validated type-`B` index names**, entry by entry: it is
the type-`B` Cartan matrix at the index's rank. This is the projection of the introduction form
`TauCeti.TypeBLieIndex.ofB` through `TauCeti.DynkinType.cartanMatrix_B`, stated on entries rather
than on matrices because the rank occurs in the index types of the two nodes. -/
theorem dynkinType_cartanMatrix_apply (d : TypeBLieIndex) (i j : Fin d.1.rank) :
    d.1.dynkinType.cartanMatrix i j = CartanMatrix.B d.1.rank i j := by
  obtain ⟨rank, q, hvalid, rfl⟩ := d.exists_eq_ofB
  exact congrFun₂ (DynkinType.cartanMatrix_B rank) i j

/-- The rank of a validated type-`B` index is at least two: the `B₁` diagram is `A₁`, and the
double edge that names the family appears from rank two on. -/
theorem two_le_rank (d : TypeBLieIndex) : 2 ≤ d.1.rank := by
  obtain ⟨rank, q, hvalid, rfl⟩ := d.exists_eq_ofB
  simpa only [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType,
    LieTypeIndex.dynkinType_B, DynkinType.rank_B] using
      ((inStandardRange_iff _).mp ((valid_iff _).mp hvalid).1).1

end TypeBLieIndex

end TauCeti
