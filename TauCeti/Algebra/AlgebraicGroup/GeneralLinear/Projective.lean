/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import TauCeti.Algebra.AlgebraicGroup.Center.Quotient
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Center

/-!
# The projective general linear point functor

The represented center of `GLₙ` maps isomorphically onto the ordinary center of its group of
points. Consequently, its pointwise center quotient is Mathlib's projective general linear group
`PGL(n, A)` over every commutative value algebra `A`. This file proves that identification and
packages it naturally in `A`.

This is an identification of the presheaf quotient before fppf sheafification.  It does not assert
that the pointwise quotient is already an fppf sheaf, or construct a representing Hopf algebra.

## Main declarations

* `TauCeti.GeneralLinear.map_centerPointsSubgroup_pointsMulEquiv_eq_center`: the represented
  center maps onto the ordinary center of the point group.
* `TauCeti.GeneralLinear.centerPointwiseQuotientIsoPGL`: the objectwise group isomorphism.
* `TauCeti.GeneralLinear.pglPointsFunctor`: the pointwise-quotient presheaf
  `A ↦ GLₙ(A) / Z(GLₙ(A))`, with values Mathlib names `PGL(n, A)`.
* `TauCeti.GeneralLinear.centerPointwiseQuotientNatIsoPGL`: the natural identification of the
  pointwise center quotient of `GLₙ` with that presheaf.

## References

* J. S. Milne, *Algebraic Groups* (2017), Examples 5.5 and 21.4.
-/

public section

open CategoryTheory

namespace TauCeti

namespace GeneralLinear

universe u w

variable {k : Type u} [Field k]
variable (n : ℕ)

/-- The pointwise quotient of `GLₙ` by its represented center is the projective general linear
group over the same value algebra. -/
noncomputable def centerPointwiseQuotientIsoPGL (A : CommAlgCat.{u} k) :
    CommHopfAlgCat.centerPointwiseQuotient (coordinateHopfAlgebra k n) A ≅
      GrpCat.of (Matrix.ProjGenLinGroup (Fin n) A) := by
  let _ : Group (CommHopfAlgCat.centerPointwiseQuotient
      (coordinateHopfAlgebra k n) A) :=
    (CommHopfAlgCat.centerPointwiseQuotient (coordinateHopfAlgebra k n) A).str
  let _ : (CommHopfAlgCat.centerPointsSubgroup
      (coordinateHopfAlgebra k n) A).Normal :=
    CommHopfAlgCat.quotientPointsSubgroup_normal
      (coordinateHopfAlgebra k n)
      (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
      (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A
  exact (QuotientGroup.congr
    (CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A)
    (Subgroup.center (Matrix.GeneralLinearGroup (Fin n) A))
    (pointsMulEquiv (R := k) (A := A) n)
    (map_centerPointsSubgroup_pointsMulEquiv_eq_center n A)).toGrpIso

/-- The quotient equivalence sends the class of a `GLₙ`-point to the class of its associated
invertible matrix. -/
@[simp]
theorem centerPointwiseQuotientIsoPGL_hom_mk (A : CommAlgCat.{u} k)
    (q : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A) :
    (centerPointwiseQuotientIsoPGL n A).hom
        (↑q : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A ⧸
          CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A) =
      Matrix.ProjGenLinGroup.mk (pointsMulEquiv (R := k) (A := A) n q) := by
  let _ : (CommHopfAlgCat.centerPointsSubgroup
      (coordinateHopfAlgebra k n) A).Normal :=
    CommHopfAlgCat.quotientPointsSubgroup_normal
      (coordinateHopfAlgebra k n)
      (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
      (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A
  exact QuotientGroup.congr_mk'
    (CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A)
    (Subgroup.center (Matrix.GeneralLinearGroup (Fin n) A))
    (pointsMulEquiv (R := k) (A := A) n)
    (map_centerPointsSubgroup_pointsMulEquiv_eq_center n A) q

/-- The inverse quotient equivalence sends the class of an invertible matrix to the class of its
associated `GLₙ`-point. -/
@[simp]
theorem centerPointwiseQuotientIsoPGL_inv_mk (A : CommAlgCat.{u} k)
    (g : Matrix.GeneralLinearGroup (Fin n) A) :
    (centerPointwiseQuotientIsoPGL n A).inv (Matrix.ProjGenLinGroup.mk g) =
      (↑((pointsMulEquiv (R := k) (A := A) n).symm g) :
        HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A ⧸
          CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A) := by
  have h := centerPointwiseQuotientIsoPGL_hom_mk n A
    ((pointsMulEquiv (R := k) (A := A) n).symm g)
  rw [MulEquiv.apply_symm_apply] at h
  rw [← h, Iso.hom_inv_id_apply]

/-- The presheaf `A ↦ GLₙ(A) / Z(GLₙ(A))`, with values given by Mathlib's
`Matrix.ProjGenLinGroup`, packaged as a group-valued functor. This is not the functor of points of
the algebraic group `PGLₙ`; obtaining that functor requires fppf sheafification. -/
noncomputable def pglPointsFunctor {R : Type u} [CommRing R] :
    CommAlgCat.{w} R ⥤ GrpCat.{w} where
  obj A := GrpCat.of (Matrix.ProjGenLinGroup (Fin n) A)
  map φ := GrpCat.ofHom (Matrix.ProjGenLinGroup.map φ.hom.toRingHom)
  map_id A := by
    apply GrpCat.hom_ext
    exact Matrix.ProjGenLinGroup.map_id
  map_comp {A B C} φ ψ := by
    apply GrpCat.hom_ext
    exact Matrix.ProjGenLinGroup.map_comp φ.hom.toRingHom ψ.hom.toRingHom

/-- The objects of `pglPointsFunctor` are Mathlib's projective general linear groups. -/
@[simp]
theorem pglPointsFunctor_obj {R : Type u} [CommRing R] (A : CommAlgCat.{w} R) :
    (pglPointsFunctor n).obj A =
      GrpCat.of (Matrix.ProjGenLinGroup (Fin n) A) :=
  (rfl)

/-- The maps of `pglPointsFunctor` are induced by entrywise extension of scalars. -/
@[simp]
theorem pglPointsFunctor_map {R : Type u} [CommRing R]
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    (pglPointsFunctor n).map φ =
      eqToHom (pglPointsFunctor_obj n A) ≫
        GrpCat.ofHom (Matrix.ProjGenLinGroup.map (n := Fin n) φ.hom.toRingHom) ≫
          eqToHom (pglPointsFunctor_obj n B).symm :=
  (rfl)

/-- The quotient equivalence commutes with extension of scalars in the value algebra. -/
theorem centerPointwiseQuotientIsoPGL_hom_naturality {A B : CommAlgCat.{u} k} (φ : A ⟶ B) :
    CommHopfAlgCat.mapPointwiseQuotient
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
        (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) φ ≫
      (centerPointwiseQuotientIsoPGL n B).hom =
    (centerPointwiseQuotientIsoPGL n A).hom ≫
      GrpCat.ofHom (Matrix.ProjGenLinGroup.map (n := Fin n) φ.hom.toRingHom) := by
  let _ : Group (CommHopfAlgCat.centerPointwiseQuotient
      (coordinateHopfAlgebra k n) A) :=
    (CommHopfAlgCat.centerPointwiseQuotient (coordinateHopfAlgebra k n) A).str
  let _ : Group (CommHopfAlgCat.centerPointwiseQuotient
      (coordinateHopfAlgebra k n) B) :=
    (CommHopfAlgCat.centerPointwiseQuotient (coordinateHopfAlgebra k n) B).str
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  obtain ⟨q, rfl⟩ := CommHopfAlgCat.centerPointwiseQuotientMk_surjective
    (coordinateHopfAlgebra k n) A x
  simp only [GrpCat.hom_comp, MonoidHom.comp_apply, ConcreteCategory.hom_ofHom]
  rw [CommHopfAlgCat.mapPointwiseQuotient_centerPointwiseQuotientMk]
  rw [CommHopfAlgCat.centerPointwiseQuotientMk_apply,
    CommHopfAlgCat.centerPointwiseQuotientMk_apply]
  -- Normalize both projection applications to the quotient coercions used by the public API.
  change
    (centerPointwiseQuotientIsoPGL n B).hom
        (↑(HopfAlgebra.mapPoints (H := coordinateHopfAlgebra k n) φ q) :
          HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) B ⧸
            CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) B) =
      Matrix.ProjGenLinGroup.map (n := Fin n) φ.hom.toRingHom
        ((centerPointwiseQuotientIsoPGL n A).hom
          (↑q : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A ⧸
            CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A))
  rw [centerPointwiseQuotientIsoPGL_hom_mk,
    centerPointwiseQuotientIsoPGL_hom_mk, Matrix.ProjGenLinGroup.map_mk,
    HopfAlgebra.mapPoints_apply]
  exact congrArg Matrix.ProjGenLinGroup.mk (pointsMulEquiv_mapValue n φ.hom q)

/-- The pointwise center quotient of `GLₙ` is naturally isomorphic to the presheaf with values
Mathlib's projective general linear groups. This is a presheaf-level statement before fppf
sheafification, not an identification with the functor of points of the algebraic group `PGLₙ`. -/
noncomputable def centerPointwiseQuotientNatIsoPGL :
    CommHopfAlgCat.pointwiseQuotientFunctor
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
        (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) ≅
      pglPointsFunctor n :=
  NatIso.ofComponents
    (fun A =>
      eqToIso (CommHopfAlgCat.pointwiseQuotientFunctor_obj
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
        (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A) ≪≫
      centerPointwiseQuotientIsoPGL n A ≪≫
      eqToIso (pglPointsFunctor_obj n A).symm) (by
      intro A B φ
      have hprojective :
          eqToHom (pglPointsFunctor_obj n A).symm ≫
              (pglPointsFunctor n).map φ =
              GrpCat.ofHom
                (Matrix.ProjGenLinGroup.map (n := Fin n) φ.hom.toRingHom) ≫
              eqToHom (pglPointsFunctor_obj n B).symm := by
        rw [pglPointsFunctor_map]
        simp
      simpa only [Iso.trans_hom, eqToIso.hom,
        CommHopfAlgCat.pointwiseQuotientFunctor_map, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id,
        hprojective] using
        congrArg (fun z =>
          eqToHom (CommHopfAlgCat.pointwiseQuotientFunctor_obj
            (coordinateHopfAlgebra k n)
            (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
            (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A) ≫
              z ≫ eqToHom (pglPointsFunctor_obj n B).symm)
          (centerPointwiseQuotientIsoPGL_hom_naturality n φ))

/-- After transport to the concrete quotient groups, the hom component of the natural
identification is the objectwise quotient isomorphism. -/
@[simp]
theorem centerPointwiseQuotientNatIsoPGL_hom_app
    (A : CommAlgCat.{u} k) :
    eqToHom (CommHopfAlgCat.pointwiseQuotientFunctor_obj
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
        (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A).symm ≫
      (centerPointwiseQuotientNatIsoPGL n).hom.app A ≫
        eqToHom (pglPointsFunctor_obj n A) =
      (centerPointwiseQuotientIsoPGL n A).hom := by
  unfold centerPointwiseQuotientNatIsoPGL
  simp

/-- After transport to the concrete quotient groups, the inverse component of the natural
identification is the inverse objectwise quotient isomorphism. -/
@[simp]
theorem centerPointwiseQuotientNatIsoPGL_inv_app
    (A : CommAlgCat.{u} k) :
    eqToHom (pglPointsFunctor_obj n A).symm ≫
        (centerPointwiseQuotientNatIsoPGL n).inv.app A ≫
      eqToHom (CommHopfAlgCat.pointwiseQuotientFunctor_obj
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
        (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A) =
    (centerPointwiseQuotientIsoPGL n A).inv := by
  unfold centerPointwiseQuotientNatIsoPGL
  simp

/-- After transport to the concrete quotient groups, the hom component of the natural
identification sends a quotient class to the class of its associated invertible matrix. -/
@[simp]
theorem centerPointwiseQuotientNatIsoPGL_hom_app_mk (A : CommAlgCat.{u} k)
    (q : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A) :
    eqToHom (pglPointsFunctor_obj n A)
        ((centerPointwiseQuotientNatIsoPGL n).hom.app A
          (eqToHom (CommHopfAlgCat.pointwiseQuotientFunctor_obj
              (coordinateHopfAlgebra k n)
              (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
              (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A).symm
            (↑q : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A ⧸
              CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A))) =
      Matrix.ProjGenLinGroup.mk (pointsMulEquiv (R := k) (A := A) n q) := by
  have h := congrArg
    (fun f ↦ f (↑q : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A ⧸
      CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A))
    (centerPointwiseQuotientNatIsoPGL_hom_app n A)
  simp only [GrpCat.hom_comp, MonoidHom.comp_apply] at h
  rw [h, centerPointwiseQuotientIsoPGL_hom_mk]

/-- After transport to the concrete quotient groups, the inverse component of the natural
identification sends the class of an invertible matrix to its associated quotient class. -/
@[simp]
theorem centerPointwiseQuotientNatIsoPGL_inv_app_mk (A : CommAlgCat.{u} k)
    (g : Matrix.GeneralLinearGroup (Fin n) A) :
    eqToHom (CommHopfAlgCat.pointwiseQuotientFunctor_obj
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
        (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A)
      ((centerPointwiseQuotientNatIsoPGL n).inv.app A
        (eqToHom (pglPointsFunctor_obj n A).symm
          (Matrix.ProjGenLinGroup.mk g))) =
      (↑((pointsMulEquiv (R := k) (A := A) n).symm g) :
        HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A ⧸
          CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A) := by
  have h := congrArg (fun f ↦ f (Matrix.ProjGenLinGroup.mk g))
    (centerPointwiseQuotientNatIsoPGL_inv_app n A)
  simp only [GrpCat.hom_comp, MonoidHom.comp_apply] at h
  rw [h, centerPointwiseQuotientIsoPGL_inv_mk]

end GeneralLinear

end TauCeti
