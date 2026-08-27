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

The represented center of `GLₙ` maps to the ordinary center of its group of points.  Consequently,
its pointwise center quotient is Mathlib's projective general linear group
`PGL(n, A)` over every commutative value algebra `A`.  This file proves that identification and
packages it naturally in `A`.

This is an identification of the presheaf quotient before fppf sheafification.  It does not assert
that the pointwise quotient is already an fppf sheaf, or construct a representing Hopf algebra.

## Main declarations

* `TauCeti.GeneralLinear.centerPointwiseQuotientIsoPGL`: the objectwise group isomorphism.
* `TauCeti.GeneralLinear.projectivePointsFunctor`: the functor `A ↦ PGL(n, A)`.
* `TauCeti.GeneralLinear.centerPointwiseQuotientNatIsoPGL`: the natural identification of the
  pointwise center quotient of `GLₙ` with `PGLₙ`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Examples 5.5 and 21.4.
-/

public section

open CategoryTheory

namespace TauCeti

namespace GeneralLinear

universe u

variable {k : Type u} [Field k]
variable (n : ℕ)

/-- Under the standard equivalence between `GLₙ`-points and invertible matrices, the represented
center maps onto the ordinary group-theoretic center. -/
theorem map_centerPointsSubgroup_pointsMulEquiv (A : CommAlgCat.{u} k) :
    (CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A).map
        (pointsMulEquiv (R := k) (A := A) n) =
      Subgroup.center (Matrix.GeneralLinearGroup (Fin n) A) := by
  ext g
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hqcenter :
        q ∈ Subgroup.center
          (HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A) := by
      apply HopfAlgebra.center_le_center
      rw [← CommHopfAlgCat.centerPointsSubgroup_eq_center]
      exact hq
    exact (Subgroup.centerCongr (pointsMulEquiv (R := k) (A := A) n)
      ⟨q, hqcenter⟩).2
  · intro hg
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
    obtain ⟨a, ha⟩ := hg
    let f := (MultiplicativeGroup.pointsMulEquiv (R := k) (A := A)).symm a
    refine ⟨scalarTorusPoints n f, scalarTorusPoints_mem_centerPointsSubgroup n f, ?_⟩
    calc
      pointsMulEquiv n (scalarTorusPoints n f) =
          Matrix.GeneralLinearGroup.scalar (Fin n) a := by
        rw [pointsMulEquiv_apply, pointToGeneralLinear_scalarTorusPoints,
          MulEquiv.apply_symm_apply]
      _ = g := ha

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
    (map_centerPointsSubgroup_pointsMulEquiv n A)).toGrpIso

/-- The quotient equivalence sends the class of a `GLₙ`-point to the class of its associated
invertible matrix. -/
@[simp]
theorem centerPointwiseQuotientIsoPGL_hom_mk (A : CommAlgCat.{u} k)
    (q : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A) :
    (centerPointwiseQuotientIsoPGL n A).hom
        (CommHopfAlgCat.centerPointwiseQuotientMk (coordinateHopfAlgebra k n) A q) =
      Matrix.ProjGenLinGroup.mk (pointsMulEquiv (R := k) (A := A) n q) := by
  let _ : (CommHopfAlgCat.centerPointsSubgroup
      (coordinateHopfAlgebra k n) A).Normal :=
    CommHopfAlgCat.quotientPointsSubgroup_normal
      (coordinateHopfAlgebra k n)
      (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
      (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A
  rw [CommHopfAlgCat.centerPointwiseQuotientMk_apply]
  exact QuotientGroup.congr_mk'
    (CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A)
    (Subgroup.center (Matrix.GeneralLinearGroup (Fin n) A))
    (pointsMulEquiv (R := k) (A := A) n)
    (map_centerPointsSubgroup_pointsMulEquiv n A) q

/-- The inverse quotient equivalence sends the class of an invertible matrix to the class of its
associated `GLₙ`-point. -/
@[simp]
theorem centerPointwiseQuotientIsoPGL_inv_mk (A : CommAlgCat.{u} k)
    (g : Matrix.GeneralLinearGroup (Fin n) A) :
    (centerPointwiseQuotientIsoPGL n A).inv (Matrix.ProjGenLinGroup.mk g) =
      CommHopfAlgCat.centerPointwiseQuotientMk (coordinateHopfAlgebra k n) A
        ((pointsMulEquiv (R := k) (A := A) n).symm g) := by
  have h := centerPointwiseQuotientIsoPGL_hom_mk n A
    ((pointsMulEquiv (R := k) (A := A) n).symm g)
  rw [MulEquiv.apply_symm_apply] at h
  rw [← h, Iso.hom_inv_id_apply]

/-- The group-valued point functor `A ↦ PGL(n, A)`. -/
noncomputable def projectivePointsFunctor {R : Type u} [CommRing R] :
    CommAlgCat.{u} R ⥤ GrpCat.{u} where
  obj A := GrpCat.of (Matrix.ProjGenLinGroup (Fin n) A)
  map φ := GrpCat.ofHom (Matrix.ProjGenLinGroup.map φ.hom.toRingHom)
  map_id A := by
    apply GrpCat.hom_ext
    exact Matrix.ProjGenLinGroup.map_id
  map_comp {A B C} φ ψ := by
    apply GrpCat.hom_ext
    exact Matrix.ProjGenLinGroup.map_comp φ.hom.toRingHom ψ.hom.toRingHom

private theorem projectivePointsFunctor_obj_private {R : Type u} [CommRing R]
    (A : CommAlgCat.{u} R) :
    (projectivePointsFunctor n).obj A =
      GrpCat.of (Matrix.ProjGenLinGroup (Fin n) A) :=
  rfl

/-- The objects of `projectivePointsFunctor` are Mathlib's projective general linear groups. -/
@[simp]
theorem projectivePointsFunctor_obj {R : Type u} [CommRing R] (A : CommAlgCat.{u} R) :
    (projectivePointsFunctor n).obj A =
      GrpCat.of (Matrix.ProjGenLinGroup (Fin n) A) :=
  projectivePointsFunctor_obj_private n A

private theorem projectivePointsFunctor_obj_proof_eq_rfl {R : Type u} [CommRing R]
    (A : CommAlgCat.{u} R) :
    projectivePointsFunctor_obj n A = rfl :=
  Subsingleton.elim _ _

/-- The maps of `projectivePointsFunctor` are induced by entrywise extension of scalars. -/
@[simp]
theorem projectivePointsFunctor_map {R : Type u} [CommRing R]
    {A B : CommAlgCat.{u} R} (φ : A ⟶ B) :
    eqToHom (projectivePointsFunctor_obj n A).symm ≫
        (projectivePointsFunctor n).map φ =
      GrpCat.ofHom (Matrix.ProjGenLinGroup.map (n := Fin n) φ.hom.toRingHom) ≫
        eqToHom (projectivePointsFunctor_obj n B).symm := by
  rw [projectivePointsFunctor_obj_proof_eq_rfl n A,
    projectivePointsFunctor_obj_proof_eq_rfl n B]
  unfold projectivePointsFunctor
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

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
  have hmap :
      CommHopfAlgCat.mapPointwiseQuotient
          (coordinateHopfAlgebra k n)
          (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
          (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) φ
          (CommHopfAlgCat.centerPointwiseQuotientMk
            (coordinateHopfAlgebra k n) A q) =
        CommHopfAlgCat.centerPointwiseQuotientMk
          (coordinateHopfAlgebra k n) B
          (HopfAlgebra.mapPoints (H := coordinateHopfAlgebra k n) φ q) := by
    rw [CommHopfAlgCat.centerPointwiseQuotientMk_apply,
      CommHopfAlgCat.centerPointwiseQuotientMk_apply]
    rw [← CommHopfAlgCat.pointwiseQuotientMk_apply
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
        (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)),
      ← CommHopfAlgCat.pointwiseQuotientMk_apply
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
        (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n))]
    exact CommHopfAlgCat.mapPointwiseQuotient_mk
      (coordinateHopfAlgebra k n)
      (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
      (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) φ q
  simp only [GrpCat.hom_comp, MonoidHom.comp_apply, ConcreteCategory.hom_ofHom]
  rw [hmap,
    centerPointwiseQuotientIsoPGL_hom_mk,
    centerPointwiseQuotientIsoPGL_hom_mk, Matrix.ProjGenLinGroup.map_mk,
    HopfAlgebra.mapPoints_apply]
  exact congrArg Matrix.ProjGenLinGroup.mk (pointsMulEquiv_mapValue n φ.hom q)

/-- The pointwise center quotient of `GLₙ` is naturally isomorphic to the projective general
linear point functor. -/
noncomputable def centerPointwiseQuotientNatIsoPGL :
    CommHopfAlgCat.pointwiseQuotientFunctor
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
        (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) ≅
      projectivePointsFunctor n :=
  NatIso.ofComponents
    (fun A =>
      eqToIso (CommHopfAlgCat.pointwiseQuotientFunctor_obj
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
        (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A) ≪≫
      centerPointwiseQuotientIsoPGL n A ≪≫
      eqToIso (projectivePointsFunctor_obj n A).symm) (by
      intro A B φ
      have hprojective :
          eqToHom (projectivePointsFunctor_obj n A).symm ≫
              (projectivePointsFunctor n).map φ =
              GrpCat.ofHom
                (Matrix.ProjGenLinGroup.map (n := Fin n) φ.hom.toRingHom) ≫
              eqToHom (projectivePointsFunctor_obj n B).symm := by
        exact projectivePointsFunctor_map n φ
      simpa only [Iso.trans_hom, eqToIso.hom,
        CommHopfAlgCat.pointwiseQuotientFunctor_map, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id,
        hprojective] using
        congrArg (fun z =>
          eqToHom (CommHopfAlgCat.pointwiseQuotientFunctor_obj
            (coordinateHopfAlgebra k n)
            (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
            (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A) ≫
              z ≫ eqToHom (projectivePointsFunctor_obj n B).symm)
          (centerPointwiseQuotientIsoPGL_hom_naturality n φ))

private theorem centerPointwiseQuotientNatIsoPGL_hom_app_transports
    (A : CommAlgCat.{u} k) :
    eqToHom (CommHopfAlgCat.pointwiseQuotientFunctor_obj
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
        (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A).symm ≫
      (centerPointwiseQuotientNatIsoPGL n).hom.app A ≫
        eqToHom (projectivePointsFunctor_obj n A) =
      (centerPointwiseQuotientIsoPGL n A).hom := by
  unfold centerPointwiseQuotientNatIsoPGL
  simp

private theorem centerPointwiseQuotientNatIsoPGL_hom_app_mk_private
    (A : CommAlgCat.{u} k)
    (q : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A) :
    eqToHom (projectivePointsFunctor_obj n A)
        ((centerPointwiseQuotientNatIsoPGL n).hom.app A
          (eqToHom (CommHopfAlgCat.pointwiseQuotientFunctor_obj
              (coordinateHopfAlgebra k n)
              (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
              (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A).symm
            (CommHopfAlgCat.centerPointwiseQuotientMk (coordinateHopfAlgebra k n) A q))) =
      Matrix.ProjGenLinGroup.mk (pointsMulEquiv (R := k) (A := A) n q) := by
  change (eqToHom (CommHopfAlgCat.pointwiseQuotientFunctor_obj
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
        (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A).symm ≫
      (centerPointwiseQuotientNatIsoPGL n).hom.app A ≫
        eqToHom (projectivePointsFunctor_obj n A))
      (CommHopfAlgCat.centerPointwiseQuotientMk (coordinateHopfAlgebra k n) A q) = _
  rw [centerPointwiseQuotientNatIsoPGL_hom_app_transports,
    centerPointwiseQuotientIsoPGL_hom_mk]

/-- After transport to the concrete quotient groups, the hom component of the natural
identification sends a quotient class to the class of its associated invertible matrix. -/
@[simp]
theorem centerPointwiseQuotientNatIsoPGL_hom_app_mk (A : CommAlgCat.{u} k)
    (q : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A) :
    eqToHom (projectivePointsFunctor_obj n A)
        ((centerPointwiseQuotientNatIsoPGL n).hom.app A
          (eqToHom (CommHopfAlgCat.pointwiseQuotientFunctor_obj
              (coordinateHopfAlgebra k n)
              (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
              (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A).symm
            (CommHopfAlgCat.centerPointwiseQuotientMk (coordinateHopfAlgebra k n) A q))) =
      Matrix.ProjGenLinGroup.mk (pointsMulEquiv (R := k) (A := A) n q) :=
  centerPointwiseQuotientNatIsoPGL_hom_app_mk_private n A q

end GeneralLinear

end TauCeti
