/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Basic
public import TauCeti.Algebra.Bialgebra.MonoidAlgebra.GroupLike

/-!
# Character groups of groups of multiplicative type

The geometric character group of a finite-type commutative Hopf algebra of multiplicative type
is finitely generated. Indeed, the multiplicative-type hypothesis says that the group-like
elements span the coordinate algebra after extension to an algebraic closure, and finite type
then forces the group of group-like elements to be finitely generated.

## Main declarations

* `TauCeti.CommHopfAlgCat.geometricCharacterGroup_fg_of_multiplicativeType`: the geometric
  character group of a group of multiplicative type is finitely generated.
* `TauCeti.DiagonalizableGroup.geometricCharacterGroupEquiv`: the geometric character group of
  a diagonalizable coordinate ring is its defining finitely generated commutative group.

## References

See J. S. Milne, *Algebraic Groups* (2017), §§12.14--12.17, and W. C. Waterhouse,
*Introduction to Affine Group Schemes*, Chapter 2.
-/

public section

namespace TauCeti

universe u

namespace CommHopfAlgCat

variable {k : Type u} [Field k]

/-- The geometric character group of a finite-type commutative Hopf algebra of multiplicative
type is finitely generated. -/
theorem geometricCharacterGroup_fg_of_multiplicativeType
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : multiplicativeTypeCommHopfAlgProperty k H) :
    Group.FG (geometricCharacterGroup H.obj) := by
  have hspan : DiagonalizableGroup.groupLikeSpannedProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :=
    (multiplicativeTypeCommHopfAlgProperty_iff k H).mp hH
  -- `geometricCharacterGroup H.obj` unfolds through two bundled base-change layers; state the
  -- underlying group-like type so the finite-generation theorem sees its coordinate algebra.
  change Group.FG (_root_.GroupLike (AlgebraicClosure k)
    (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H))
  exact TauCeti.GroupLike.fg_of_finiteType_of_groupLikeSetSpan_eq_top
    (AlgebraicClosure k) (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)
      inferInstance ((DiagonalizableGroup.groupLikeSpannedProperty_iff
        (AlgebraicClosure k) _).mp hspan)

end CommHopfAlgCat

namespace DiagonalizableGroup

/-- The intrinsic geometric character group of a diagonalizable coordinate ring is the finitely
generated commutative group used to construct it. -/
noncomputable def geometricCharacterGroupEquiv
    (k : Type u) [Field k] (G : FGCommGrpCat.{u}) :
    CommHopfAlgCat.geometricCharacterGroup (coordinateRing k G).obj ≃* G :=
  (TauCeti.GroupLike.mapEquiv
    (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv k (AlgebraicClosure k) (G := G))).trans
    (TauCeti.MonoidAlgebra.groupLikeEquiv (R := AlgebraicClosure k) (H := G))

end DiagonalizableGroup

end TauCeti
