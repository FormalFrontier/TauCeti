/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Quotient
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Center.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Projective

/-!
# The projective special linear point functor

For positive `n`, the represented center of `SLₙ` maps isomorphically onto the ordinary center
of its group of points. Consequently, its pointwise center quotient is Mathlib's projective
special linear group `PSL(Fin n, A)` over every commutative value algebra `A`. This file proves
that identification and packages it naturally in `A`.

Over an algebraically closed field, Mathlib's canonical inclusion from `PSLₙ` to `PGLₙ` is
bijective. Composing it with the pointwise quotient identification gives the expected
`SLₙ / Z(SLₙ) ≅ PGLₙ` on field-valued points.

These are identifications of pointwise quotients before fppf sheafification. They do not assert
that the pointwise quotient is already an fppf sheaf, or construct a representing Hopf algebra.

## Main declarations

* `TauCeti.SpecialLinear.centerPointwiseQuotientIsoPSL`: the objectwise group isomorphism.
* `TauCeti.SpecialLinear.pslPointsFunctor`: projective special linear groups under extension of
  scalars.
* `TauCeti.SpecialLinear.centerPointwiseQuotientNatIsoPSL`: the natural pointwise identification.
* `TauCeti.SpecialLinear.centerPointwiseQuotientIsoPGLOfAlgClosed`: the resulting identification
  with `PGLₙ` over an algebraically closed field.

## References

* J. S. Milne, *Algebraic Groups* (2017), Examples 5.49 and 21.4.
* The quotient equivalence, point functor, naturality proof, and natural isomorphism adapt the
  corresponding constructions in `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Projective`.
-/

public section

open CategoryTheory

namespace TauCeti

namespace SpecialLinear

universe u w

variable (n : ℕ)

variable {k : Type u} [Field k]

/-- Under the standard equivalence between `SLₙ`-points and determinant-one matrices, the
represented center maps onto the ordinary group-theoretic center. -/
theorem map_centerPointsSubgroup_pointsMulEquiv_eq_center (hn : 0 < n)
    (A : CommAlgCat.{u} k) :
    (CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A).map
        (pointsMulEquiv (R := k) (A := A) n) =
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) A) := by
  apply le_antisymm
  · rintro _ ⟨q, hq, rfl⟩
    apply MulEquivClass.apply_mem_center
    apply HopfAlgebra.center_le_center
    rw [← CommHopfAlgCat.centerPointsSubgroup_eq_center]
    exact hq
  · intro g hg
    let c : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) A) := ⟨g, hg⟩
    let ζ : rootsOfUnity n A :=
      Matrix.SpecialLinearGroup.centerMulEquivRootsOfUnityFin n hn A c
    let f := (RootsOfUnityGroup.pointsMulEquiv (R := k) (A := A) n).symm ζ
    refine ⟨(rootsOfUnityScalarCenterMulEquiv (S := k) n hn A f).1, ?_, ?_⟩
    · rw [CommHopfAlgCat.centerPointsSubgroup_eq_center]
      exact (rootsOfUnityScalarCenterMulEquiv (S := k) n hn A f).2
    -- The two established roots-of-unity equivalences identify the represented center and the
    -- matrix center. The subgroup-map witness uses the coerced equivalence, so expose its
    -- application before applying their public evaluation lemmas.
    change pointsMulEquiv (R := k) (A := A) n
      (rootsOfUnityScalarCenterMulEquiv (S := k) n hn A f).1 = g
    rw [rootsOfUnityScalarCenterMulEquiv_apply,
      pointsMulEquiv_rootsOfUnityScalarPoints, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [coe_rootsOfUnityScalarSL,
      ← Matrix.SpecialLinearGroup.coe_centerMulEquivRootsOfUnityFin_symm_apply n hn A ζ]
    simpa only [ζ, c] using congrArg
      (fun x : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) A) =>
        ((x : Matrix.SpecialLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A))
      ((Matrix.SpecialLinearGroup.centerMulEquivRootsOfUnityFin n hn A).symm_apply_apply c)

/-- The pointwise quotient of `SLₙ` by its represented center is the projective special linear
group over the same value algebra. -/
noncomputable def centerPointwiseQuotientIsoPSL (hn : 0 < n) (A : CommAlgCat.{u} k) :
    CommHopfAlgCat.centerPointwiseQuotient (coordinateHopfAlgebra k n) A ≅
      GrpCat.of (Matrix.ProjectiveSpecialLinearGroup (Fin n) A) := by
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
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) A))
    (pointsMulEquiv (R := k) (A := A) n)
    (map_centerPointsSubgroup_pointsMulEquiv_eq_center n hn A)).toGrpIso

/-- The quotient equivalence sends the class of an `SLₙ`-point to the class of its associated
determinant-one matrix. -/
@[simp]
theorem centerPointwiseQuotientIsoPSL_hom_mk (hn : 0 < n) (A : CommAlgCat.{u} k)
    (q : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A) :
    (centerPointwiseQuotientIsoPSL n hn A).hom
        (↑q : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A ⧸
          CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A) =
      QuotientGroup.mk (pointsMulEquiv (R := k) (A := A) n q) := by
  let _ : (CommHopfAlgCat.centerPointsSubgroup
      (coordinateHopfAlgebra k n) A).Normal :=
    CommHopfAlgCat.quotientPointsSubgroup_normal
      (coordinateHopfAlgebra k n)
      (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
      (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A
  exact QuotientGroup.congr_mk'
    (CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A)
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) A))
    (pointsMulEquiv (R := k) (A := A) n)
    (map_centerPointsSubgroup_pointsMulEquiv_eq_center n hn A) q

/-- The inverse quotient equivalence sends the class of a determinant-one matrix to the class of
its associated `SLₙ`-point. -/
@[simp]
theorem centerPointwiseQuotientIsoPSL_inv_mk (hn : 0 < n) (A : CommAlgCat.{u} k)
    (g : Matrix.SpecialLinearGroup (Fin n) A) :
    (centerPointwiseQuotientIsoPSL n hn A).inv (QuotientGroup.mk g) =
      (↑((pointsMulEquiv (R := k) (A := A) n).symm g) :
        HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A ⧸
          CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A) := by
  have h := centerPointwiseQuotientIsoPSL_hom_mk n hn A
    ((pointsMulEquiv (R := k) (A := A) n).symm g)
  rw [MulEquiv.apply_symm_apply] at h
  rw [← h, Iso.hom_inv_id_apply]

/-- The presheaf `A ↦ PSL(Fin n, A)`, with maps induced by entrywise extension of scalars. -/
noncomputable def pslPointsFunctor {R : Type u} [CommRing R] :
    CommAlgCat.{w} R ⥤ GrpCat.{w} where
  obj A := GrpCat.of (Matrix.ProjectiveSpecialLinearGroup (Fin n) A)
  map φ := GrpCat.ofHom (projectiveMap n φ.hom.toRingHom)
  map_id A := by
    apply GrpCat.hom_ext
    exact projectiveMap_id n
  map_comp φ ψ := by
    apply GrpCat.hom_ext
    exact (projectiveMap_comp n φ.hom.toRingHom ψ.hom.toRingHom).symm

/-- The objects of `pslPointsFunctor` are Mathlib's projective special linear groups. -/
@[simp]
theorem pslPointsFunctor_obj {R : Type u} [CommRing R] (A : CommAlgCat.{w} R) :
    (pslPointsFunctor n).obj A =
      GrpCat.of (Matrix.ProjectiveSpecialLinearGroup (Fin n) A) :=
  by unfold pslPointsFunctor; rfl

/-- The maps of `pslPointsFunctor` are induced by entrywise extension of scalars. -/
@[simp]
theorem pslPointsFunctor_map {R : Type u} [CommRing R]
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    (pslPointsFunctor n).map φ =
      eqToHom (pslPointsFunctor_obj n A) ≫
        GrpCat.ofHom (projectiveMap n φ.hom.toRingHom) ≫
          eqToHom (pslPointsFunctor_obj n B).symm :=
  by unfold pslPointsFunctor; rfl

/-- The quotient equivalence commutes with extension of scalars in the value algebra. -/
theorem centerPointwiseQuotientIsoPSL_hom_naturality (hn : 0 < n)
    {A B : CommAlgCat.{u} k} (φ : A ⟶ B) :
    CommHopfAlgCat.mapPointwiseQuotient
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
        (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) φ ≫
      (centerPointwiseQuotientIsoPSL n hn B).hom =
    (centerPointwiseQuotientIsoPSL n hn A).hom ≫
      GrpCat.ofHom (projectiveMap n φ.hom.toRingHom) := by
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
    (centerPointwiseQuotientIsoPSL n hn B).hom
        (↑(HopfAlgebra.mapPoints (H := coordinateHopfAlgebra k n) φ q) :
          HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) B ⧸
            CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) B) =
      projectiveMap n φ.hom.toRingHom
        ((centerPointwiseQuotientIsoPSL n hn A).hom
          (↑q : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A ⧸
            CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A))
  rw [centerPointwiseQuotientIsoPSL_hom_mk,
    centerPointwiseQuotientIsoPSL_hom_mk, projectiveMap_mk,
    HopfAlgebra.mapPoints_apply]
  exact congrArg QuotientGroup.mk
    (SpecialLinear.pointsMulEquiv_mapValue (R := k) (A := A) (B := B) n φ.hom q)

/-- The pointwise center quotient of `SLₙ` is naturally isomorphic to the presheaf with values
Mathlib's projective special linear groups. -/
noncomputable def centerPointwiseQuotientNatIsoPSL (hn : 0 < n) :
    CommHopfAlgCat.pointwiseQuotientFunctor
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
        (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) ≅
      pslPointsFunctor n :=
  NatIso.ofComponents
    (fun A =>
      eqToIso (CommHopfAlgCat.pointwiseQuotientFunctor_obj
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
        (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A) ≪≫
      centerPointwiseQuotientIsoPSL n hn A ≪≫
      eqToIso (pslPointsFunctor_obj n A).symm) (by
      intro A B φ
      have hprojective :
          eqToHom (pslPointsFunctor_obj n A).symm ≫
              (pslPointsFunctor n).map φ =
            GrpCat.ofHom (projectiveMap n φ.hom.toRingHom) ≫
              eqToHom (pslPointsFunctor_obj n B).symm := by
        rw [pslPointsFunctor_map]
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
              z ≫ eqToHom (pslPointsFunctor_obj n B).symm)
          (centerPointwiseQuotientIsoPSL_hom_naturality n hn φ))

/-- After transport to the concrete quotient groups, the hom component of the natural
identification is the objectwise quotient isomorphism. -/
@[simp]
theorem centerPointwiseQuotientNatIsoPSL_hom_app (hn : 0 < n)
    (A : CommAlgCat.{u} k) :
    eqToHom (CommHopfAlgCat.pointwiseQuotientFunctor_obj
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
        (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A).symm ≫
      (centerPointwiseQuotientNatIsoPSL n hn).hom.app A ≫
        eqToHom (pslPointsFunctor_obj n A) =
      (centerPointwiseQuotientIsoPSL n hn A).hom := by
  unfold centerPointwiseQuotientNatIsoPSL
  simp

/-- After transport to the concrete quotient groups, the inverse component of the natural
identification is the inverse objectwise quotient isomorphism. -/
@[simp]
theorem centerPointwiseQuotientNatIsoPSL_inv_app (hn : 0 < n)
    (A : CommAlgCat.{u} k) :
    eqToHom (pslPointsFunctor_obj n A).symm ≫
        (centerPointwiseQuotientNatIsoPSL n hn).inv.app A ≫
      eqToHom (CommHopfAlgCat.pointwiseQuotientFunctor_obj
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
        (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A) =
    (centerPointwiseQuotientIsoPSL n hn A).inv := by
  unfold centerPointwiseQuotientNatIsoPSL
  simp

/-- After transport to the concrete quotient groups, the hom component of the natural
identification sends a quotient class to the class of its associated determinant-one matrix. -/
@[simp]
theorem centerPointwiseQuotientNatIsoPSL_hom_app_mk (hn : 0 < n)
    (A : CommAlgCat.{u} k)
    (q : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A) :
    eqToHom (pslPointsFunctor_obj n A)
        ((centerPointwiseQuotientNatIsoPSL n hn).hom.app A
          (eqToHom (CommHopfAlgCat.pointwiseQuotientFunctor_obj
              (coordinateHopfAlgebra k n)
              (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
              (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A).symm
            (↑q : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A ⧸
              CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A))) =
      QuotientGroup.mk (pointsMulEquiv (R := k) (A := A) n q) := by
  have h := congrArg
    (fun f ↦ f (↑q : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A ⧸
      CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A))
    (centerPointwiseQuotientNatIsoPSL_hom_app n hn A)
  simp only [GrpCat.hom_comp, MonoidHom.comp_apply] at h
  rw [h, centerPointwiseQuotientIsoPSL_hom_mk]

/-- After transport to the concrete quotient groups, the inverse component of the natural
identification sends the class of a determinant-one matrix to its associated quotient class. -/
@[simp]
theorem centerPointwiseQuotientNatIsoPSL_inv_app_mk (hn : 0 < n)
    (A : CommAlgCat.{u} k) (g : Matrix.SpecialLinearGroup (Fin n) A) :
    eqToHom (CommHopfAlgCat.pointwiseQuotientFunctor_obj
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
        (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A)
      ((centerPointwiseQuotientNatIsoPSL n hn).inv.app A
        (eqToHom (pslPointsFunctor_obj n A).symm (QuotientGroup.mk g))) =
      (↑((pointsMulEquiv (R := k) (A := A) n).symm g) :
        HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A ⧸
          CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A) := by
  have h := congrArg (fun f ↦ f (QuotientGroup.mk g))
    (centerPointwiseQuotientNatIsoPSL_inv_app n hn A)
  simp only [GrpCat.hom_comp, MonoidHom.comp_apply] at h
  rw [h, centerPointwiseQuotientIsoPSL_inv_mk]

/-- Over an algebraically closed field, the pointwise center quotient of `SLₙ` is `PGLₙ`.
This uses Mathlib's canonical isomorphism between projective general and special linear groups. -/
noncomputable def centerPointwiseQuotientIsoPGLOfAlgClosed (hn : 0 < n)
    (F : Type u) [Field F] [IsAlgClosed F] [Algebra k F] :
    CommHopfAlgCat.centerPointwiseQuotient
        (coordinateHopfAlgebra k n) (CommAlgCat.of k F) ≅
      GrpCat.of (Matrix.ProjGenLinGroup (Fin n) F) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact centerPointwiseQuotientIsoPSL n hn (CommAlgCat.of k F) ≪≫
    (Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosedOfNonempty
      (n := Fin n) (F := F)).symm.toGrpIso

/-- The algebraically closed-field identification sends an `SLₙ`-point to the projective class
of its underlying invertible matrix. -/
@[simp]
theorem centerPointwiseQuotientIsoPGLOfAlgClosed_hom_mk (hn : 0 < n)
    (F : Type u) [Field F] [IsAlgClosed F] [Algebra k F]
    (q : HopfAlgebra.points (R := k)
      (H := coordinateHopfAlgebra k n) (CommAlgCat.of k F)) :
    (centerPointwiseQuotientIsoPGLOfAlgClosed n hn F).hom
        (↑q : HopfAlgebra.points (R := k)
            (H := coordinateHopfAlgebra k n) (CommAlgCat.of k F) ⧸
          CommHopfAlgCat.centerPointsSubgroup
            (coordinateHopfAlgebra k n) (CommAlgCat.of k F)) =
      Matrix.ProjGenLinGroup.mk
        (Matrix.SpecialLinearGroup.toGL
          (pointsMulEquiv (R := k) (A := F) n q)) := by
  let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold centerPointwiseQuotientIsoPGLOfAlgClosed
  -- The composite categorical isomorphism computes through Mathlib's underlying PSL-to-PGL map.
  change Matrix.ProjectiveSpecialLinearGroup.toPGL
      ((centerPointwiseQuotientIsoPSL n hn (CommAlgCat.of k F)).hom (↑q)) = _
  rw [centerPointwiseQuotientIsoPSL_hom_mk,
    Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]

/-- The inverse algebraically closed-field identification sends the projective class of a
determinant-one matrix to the quotient class of its associated `SLₙ`-point. -/
@[simp]
theorem centerPointwiseQuotientIsoPGLOfAlgClosed_inv_mk_toGL (hn : 0 < n)
    (F : Type u) [Field F] [IsAlgClosed F] [Algebra k F]
    (g : Matrix.SpecialLinearGroup (Fin n) F) :
    (centerPointwiseQuotientIsoPGLOfAlgClosed n hn F).inv
        (Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL g)) =
      (↑((pointsMulEquiv (R := k) (A := F) n).symm g) :
        HopfAlgebra.points (R := k)
            (H := coordinateHopfAlgebra k n) (CommAlgCat.of k F) ⧸
          CommHopfAlgCat.centerPointsSubgroup
            (coordinateHopfAlgebra k n) (CommAlgCat.of k F)) := by
  have h := centerPointwiseQuotientIsoPGLOfAlgClosed_hom_mk n hn F
    ((pointsMulEquiv (R := k) (A := F) n).symm g)
  rw [MulEquiv.apply_symm_apply] at h
  rw [← h]
  exact GrpCat.inv_hom_apply _ _

end SpecialLinear

end TauCeti
