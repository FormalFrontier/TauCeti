/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.FiniteType
public import TauCeti.Algebra.Bialgebra.GroupLike.Map
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

/-- A geometric character corresponds to `g` exactly when base change identifies its underlying
group-like element with the standard monomial indexed by `g`. -/
@[simp]
theorem geometricCharacterGroupEquiv_apply_eq_iff
    (k : Type u) [Field k] (G : FGCommGrpCat.{u})
    (x : CommHopfAlgCat.geometricCharacterGroup (coordinateRing k G).obj) (g : G) :
    geometricCharacterGroupEquiv k G x = g ↔
      TauCeti.MonoidAlgebra.scalarTensorBialgEquiv k (AlgebraicClosure k) x.val =
        _root_.MonoidAlgebra.single g 1 := by
  simp only [geometricCharacterGroupEquiv, MulEquiv.trans_apply,
    TauCeti.MonoidAlgebra.groupLikeEquiv_apply_eq_iff, TauCeti.GroupLike.val_mapEquiv]

/-- The inverse character corresponding to `g` is the standard monomial indexed by `g`, viewed
in the scalar-extended coordinate ring. -/
@[simp]
theorem geometricCharacterGroupEquiv_symm_apply_val
    (k : Type u) [Field k] (G : FGCommGrpCat.{u}) (g : G) :
    ((geometricCharacterGroupEquiv k G).symm g).val =
      1 ⊗ₜ[k] _root_.MonoidAlgebra.single g 1 := by
  let e := TauCeti.MonoidAlgebra.scalarTensorBialgEquiv k (AlgebraicClosure k) (G := G)
  have h := (geometricCharacterGroupEquiv_apply_eq_iff k G
      ((geometricCharacterGroupEquiv k G).symm g) g).mp
    ((geometricCharacterGroupEquiv k G).apply_symm_apply g)
  calc
    ((geometricCharacterGroupEquiv k G).symm g).val =
        e.symm (e ((geometricCharacterGroupEquiv k G).symm g).val) :=
      (e.symm_apply_apply _).symm
    _ = e.symm (_root_.MonoidAlgebra.single g 1) := congrArg e.symm h
    _ = 1 ⊗ₜ[k] _root_.MonoidAlgebra.single g 1 :=
      TauCeti.MonoidAlgebra.scalarTensorBialgEquiv_symm_single k (AlgebraicClosure k) g 1

end DiagonalizableGroup

end TauCeti
