/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice.Basic
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.BaseChange
public import TauCeti.Algebra.Bialgebra.MonoidAlgebra.GroupLike

/-!
# Character groups of diagonalizable groups

The intrinsic geometric character group of a diagonalizable coordinate ring recovers the
finitely generated commutative group used to construct it. Its absolute-Galois action is trivial.

## Main declarations

* `TauCeti.CommHopfAlgCat.geometricCharacterGroupEquivOfIso`: identify a geometric character
  group whenever its base change is a monoid algebra.
* `TauCeti.DiagonalizableGroup.geometricCharacterGroupEquiv`: the geometric character group of
  a diagonalizable coordinate ring is its defining finitely generated commutative group.
* `TauCeti.DiagonalizableGroup.smul_geometricCharacterGroup_eq_self`: the absolute-Galois action
  on this character group is trivial.

## References

See J. S. Milne, *Algebraic Groups* (2017), Definition 12.7 and Theorems 12.8--12.9.
-/

public section

open TensorProduct

namespace TauCeti

universe u

namespace CommHopfAlgCat

/-- The bialgebra equivalence underlying an isomorphism from a diagonalizable coordinate ring to
the base change of a finite-type commutative Hopf algebra. -/
private noncomputable def bialgEquivOfBaseChangeIso
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (G : FGCommGrpCat.{u})
    (i : DiagonalizableGroup.coordinateRing (AlgebraicClosure k) G ≅
      FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :
    _root_.MonoidAlgebra (AlgebraicClosure k) G ≃ₐc[AlgebraicClosure k]
      AlgebraicClosure k ⊗[k] H.obj :=
  _root_.CommHopfAlgCat.ofIso
    ((finiteTypeCommHopfAlgProperty (AlgebraicClosure k)).ι.mapIso i)

/-- The base-change bialgebra equivalence evaluates as the morphism underlying the isomorphism. -/
@[simp]
private theorem bialgEquivOfBaseChangeIso_apply
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (G : FGCommGrpCat.{u})
    (i : DiagonalizableGroup.coordinateRing (AlgebraicClosure k) G ≅
      FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)
    (x : _root_.MonoidAlgebra (AlgebraicClosure k) G) :
    bialgEquivOfBaseChangeIso k H G i x = i.hom.hom x :=
  by
    rw [bialgEquivOfBaseChangeIso]
    simpa only [CategoryTheory.Functor.mapIso_hom, CategoryTheory.ObjectProperty.ι_map] using
      _root_.CommHopfAlgCat.ofIso_apply
        ((finiteTypeCommHopfAlgProperty (AlgebraicClosure k)).ι.mapIso i) x

/-- The inverse base-change bialgebra equivalence evaluates as the inverse isomorphism. -/
@[simp]
private theorem bialgEquivOfBaseChangeIso_symm_apply
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (G : FGCommGrpCat.{u})
    (i : DiagonalizableGroup.coordinateRing (AlgebraicClosure k) G ≅
      FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)
    (x : AlgebraicClosure k ⊗[k] H.obj) :
    (bialgEquivOfBaseChangeIso k H G i).symm x = i.inv.hom x :=
  by
    apply (bialgEquivOfBaseChangeIso k H G i).symm_apply_eq.mpr
    calc
      x = i.hom.hom (i.inv.hom x) := (i.inv_hom_id_apply x).symm
      _ = bialgEquivOfBaseChangeIso k H G i (i.inv.hom x) :=
        (bialgEquivOfBaseChangeIso_apply k H G i (i.inv.hom x)).symm

/-- If the base change of a finite-type commutative Hopf algebra is a diagonalizable coordinate
ring, its geometric character group is the group indexing that coordinate ring. -/
noncomputable def geometricCharacterGroupEquivOfIso
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (G : FGCommGrpCat.{u})
    (i : DiagonalizableGroup.coordinateRing (AlgebraicClosure k) G ≅
      FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :
    geometricCharacterGroup H.obj ≃* G :=
  (TauCeti.GroupLike.mapEquiv (bialgEquivOfBaseChangeIso k H G i)).symm.trans
    (TauCeti.MonoidAlgebra.groupLikeEquiv (R := AlgebraicClosure k) (H := G))

/-- Characterization of the character corresponding to an index under
`geometricCharacterGroupEquivOfIso`. -/
@[simp]
theorem geometricCharacterGroupEquivOfIso_apply_eq_iff
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (G : FGCommGrpCat.{u})
    (i : DiagonalizableGroup.coordinateRing (AlgebraicClosure k) G ≅
      FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)
    (x : geometricCharacterGroup H.obj) (g : G) :
    geometricCharacterGroupEquivOfIso k H G i x = g ↔
      i.inv.hom x.val = _root_.MonoidAlgebra.single g 1 := by
  simp only [geometricCharacterGroupEquivOfIso, MulEquiv.trans_apply,
    TauCeti.MonoidAlgebra.groupLikeEquiv_apply_eq_iff, TauCeti.GroupLike.mapEquiv_symm,
    TauCeti.GroupLike.val_mapEquiv, bialgEquivOfBaseChangeIso_symm_apply]

end CommHopfAlgCat

namespace DiagonalizableGroup

/-- The intrinsic geometric character group of a diagonalizable coordinate ring is the finitely
generated commutative group used to construct it. -/
noncomputable def geometricCharacterGroupEquiv
    (k : Type u) [Field k] (G : FGCommGrpCat.{u}) :
    CommHopfAlgCat.geometricCharacterGroup (coordinateRing k G).obj ≃* G :=
  CommHopfAlgCat.geometricCharacterGroupEquivOfIso k (coordinateRing k G) G
    (baseChangeCoordinateRingIso k (AlgebraicClosure k) G).symm

private theorem coordinateRing_baseChangeIso_inv_apply
    (k : Type u) [Field k] (G : FGCommGrpCat.{u})
    (x : AlgebraicClosure k ⊗[k] _root_.MonoidAlgebra k G) :
    (baseChangeCoordinateRingIso k (AlgebraicClosure k) G).symm.inv.hom x =
      TauCeti.MonoidAlgebra.scalarTensorBialgEquiv k (AlgebraicClosure k) x := by
  simp only [CategoryTheory.Iso.symm_inv, CategoryTheory.ObjectProperty.isoMk_hom,
    CategoryTheory.ObjectProperty.homMk_hom, _root_.CommHopfAlgCat.isoMk_hom,
    _root_.CommHopfAlgCat.hom_ofHom, BialgEquiv.coe_coe]

/-- A geometric character corresponds to `g` exactly when base change identifies its underlying
group-like element with the standard monomial indexed by `g`. -/
@[simp]
theorem geometricCharacterGroupEquiv_apply_eq_iff
    (k : Type u) [Field k] (G : FGCommGrpCat.{u})
    (x : CommHopfAlgCat.geometricCharacterGroup (coordinateRing k G).obj) (g : G) :
    geometricCharacterGroupEquiv k G x = g ↔
      TauCeti.MonoidAlgebra.scalarTensorBialgEquiv k (AlgebraicClosure k) x.val =
        _root_.MonoidAlgebra.single g 1 := by
  rw [geometricCharacterGroupEquiv,
    CommHopfAlgCat.geometricCharacterGroupEquivOfIso_apply_eq_iff,
    coordinateRing_baseChangeIso_inv_apply]

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

/-- The absolute Galois action on the geometric character group of a diagonalizable coordinate
ring is trivial. -/
@[simp]
theorem smul_geometricCharacterGroup_eq_self (k : Type u) [Field k] (G : FGCommGrpCat.{u})
    (σ : Field.absoluteGaloisGroup k)
    (x : CommHopfAlgCat.geometricCharacterGroup (coordinateRing k G).obj) :
    σ • x = x := by
  rw [← (geometricCharacterGroupEquiv k G).symm_apply_apply x]
  apply _root_.GroupLike.val_injective
  rw [CommHopfAlgCat.val_smul, geometricCharacterGroupEquiv_symm_apply_val,
    ScalarAut.smul_tmul, map_one]

end DiagonalizableGroup

end TauCeti
