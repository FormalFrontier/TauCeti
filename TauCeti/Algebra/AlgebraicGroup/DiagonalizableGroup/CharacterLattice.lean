/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.BaseChange
public import TauCeti.Algebra.Bialgebra.GroupLike.Map
public import TauCeti.Algebra.Bialgebra.MonoidAlgebra.BaseChange
public import TauCeti.Algebra.Bialgebra.MonoidAlgebra.GroupLike

/-!
# Character groups of diagonalizable groups

The intrinsic geometric character group of a diagonalizable coordinate ring recovers the
finitely generated commutative group used to construct it.

## Main declarations

* `TauCeti.CommHopfAlgCat.geometricCharacterGroupEquivOfIso`: identify a geometric character
  group whenever its base change is a monoid algebra.
* `TauCeti.DiagonalizableGroup.geometricCharacterGroupEquiv`: the geometric character group of
  a diagonalizable coordinate ring is its defining finitely generated commutative group.

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
noncomputable def bialgEquivOfBaseChangeIso
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (G : FGCommGrpCat.{u})
    (i : DiagonalizableGroup.coordinateRing (AlgebraicClosure k) G ≅
      FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :
    _root_.MonoidAlgebra (AlgebraicClosure k) G ≃ₐc[AlgebraicClosure k]
      AlgebraicClosure k ⊗[k] H.obj :=
  _root_.CommHopfAlgCat.ofIso
    ((finiteTypeCommHopfAlgProperty (AlgebraicClosure k)).ι.mapIso i)

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
      (bialgEquivOfBaseChangeIso k H G i).symm x.val =
        _root_.MonoidAlgebra.single g 1 := by
  simp only [geometricCharacterGroupEquivOfIso, MulEquiv.trans_apply,
    TauCeti.MonoidAlgebra.groupLikeEquiv_apply_eq_iff, TauCeti.GroupLike.mapEquiv_symm,
    TauCeti.GroupLike.val_mapEquiv]

/-- Additive form of `geometricCharacterGroupEquivOfIso`. -/
noncomputable def additiveCharacterGroupEquivOfIso
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (G : FGCommGrpCat.{u})
    (i : DiagonalizableGroup.coordinateRing (AlgebraicClosure k) G ≅
      FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :
    additiveCharacterGroup H.obj ≃+ Additive G :=
  MulEquiv.toAdditive (geometricCharacterGroupEquivOfIso k H G i)

end CommHopfAlgCat

namespace DiagonalizableGroup

/-- The absolute-Galois action specialized to a diagonalizable coordinate ring. -/
noncomputable instance instGeometricCharacterGroupGaloisAction
    (k : Type u) [Field k] (G : FGCommGrpCat.{u}) :
    MulDistribMulAction (Field.absoluteGaloisGroup k)
      (CommHopfAlgCat.geometricCharacterGroup (coordinateRing k G).obj) :=
  CommHopfAlgCat.instGeometricCharacterGroupGaloisAction
    (H := (coordinateRing k G).obj)

/-- The intrinsic geometric character group of a diagonalizable coordinate ring is the finitely
generated commutative group used to construct it. -/
noncomputable def geometricCharacterGroupEquiv
    (k : Type u) [Field k] (G : FGCommGrpCat.{u}) :
    CommHopfAlgCat.geometricCharacterGroup (coordinateRing k G).obj ≃* G :=
  CommHopfAlgCat.geometricCharacterGroupEquivOfIso k (coordinateRing k G) G
    (baseChangeCoordinateRingIso k (AlgebraicClosure k) G).symm

/-- For the canonical base-change isomorphism of a diagonalizable coordinate ring, the inverse
of `bialgEquivOfBaseChangeIso` is the scalar-tensor equivalence. -/
theorem bialgEquivOfBaseChangeIso_symm_apply
    (k : Type u) [Field k] (G : FGCommGrpCat.{u})
    (x : AlgebraicClosure k ⊗[k] _root_.MonoidAlgebra k G) :
    (CommHopfAlgCat.bialgEquivOfBaseChangeIso k (coordinateRing k G) G
      (baseChangeCoordinateRingIso k (AlgebraicClosure k) G).symm).symm x =
        TauCeti.MonoidAlgebra.scalarTensorBialgEquiv k (AlgebraicClosure k) x := by
  induction x with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a x =>
      -- The full-subcategory `mapIso` and `CommHopfAlgCat.ofIso` wrappers expose no
      -- evaluation lemma. Unfold their shared underlying algebra equivalence here so that
      -- the canonical scalar-tensor pure-tensor lemma applies.
      change TauCeti.MonoidAlgebra.scalarTensorBialgEquiv k (AlgebraicClosure k)
        (a ⊗ₜ[k] x) = _
      rw [TauCeti.MonoidAlgebra.scalarTensorBialgEquiv_tmul]

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
    bialgEquivOfBaseChangeIso_symm_apply]

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
theorem smul_eq_self (k : Type u) [Field k] (G : FGCommGrpCat.{u})
    (σ : Field.absoluteGaloisGroup k)
    (x : CommHopfAlgCat.geometricCharacterGroup (coordinateRing k G).obj) :
    σ • x = x := by
  rw [← (geometricCharacterGroupEquiv k G).symm_apply_apply x]
  apply _root_.GroupLike.val_injective
  -- Expose the generic action beneath the necessary absolute-Galois and coordinate-ring bridges.
  change GaloisScalar.map
    (A := (coordinateRing k G).obj)
    (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ)
      ((geometricCharacterGroupEquiv k G).symm
        (geometricCharacterGroupEquiv k G x)).val = _
  rw [geometricCharacterGroupEquiv_symm_apply_val, GaloisScalar.map_tmul, map_one]

end DiagonalizableGroup

end TauCeti
