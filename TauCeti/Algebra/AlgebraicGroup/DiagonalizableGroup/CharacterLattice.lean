/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.FiniteType
public import TauCeti.Algebra.Bialgebra.MonoidAlgebra.BaseChange
public import TauCeti.Algebra.Bialgebra.MonoidAlgebra.GroupLike

/-!
# Character groups of diagonalizable groups

The intrinsic geometric character group of a diagonalizable coordinate ring recovers the
finitely generated commutative group used to construct it.

## Main declarations

* `TauCeti.DiagonalizableGroup.geometricCharacterGroupEquiv`: the geometric character group of
  a diagonalizable coordinate ring is its defining finitely generated commutative group.

## References

See J. S. Milne, *Algebraic Groups* (2017), §§12.14--12.17, and W. C. Waterhouse,
*Introduction to Affine Group Schemes*, Chapter 2.
-/

public section

namespace TauCeti

universe u

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
