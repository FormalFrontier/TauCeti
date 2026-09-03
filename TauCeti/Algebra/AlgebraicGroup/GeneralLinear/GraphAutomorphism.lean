/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.GraphAutomorphism

/-!
# The type-A graph automorphism on the general linear group scheme

This file transports signed reverse-inverse-transpose from general-linear matrix points to the
coordinate Hopf algebra. Its characteristic theorem identifies precomposition by the recovered
coordinate automorphism with `TauCeti.typeAGraphAutomorphism` under the standard point equivalence.

This is the ambient general-linear input for descending the graph automorphism to the type-`A`
standard carrier.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear

variable (r : ℕ)

/-- Signed reverse-inverse-transpose transported to general-linear coordinate-algebra points. -/
private noncomputable def typeAGraphPointsMulEquiv (A : CommAlgCat.{0} ℤ) :
    HopfAlgebra.points
        (R := ℤ) (H := coordinateHopfAlgebra ℤ (r + 1)) A ≃*
      HopfAlgebra.points
        (R := ℤ) (H := coordinateHopfAlgebra ℤ (r + 1)) A :=
  ((pointsMulEquiv (R := ℤ) (A := A) (r + 1)).trans
    (TauCeti.typeAGraphAutomorphism r A)).trans
      (pointsMulEquiv (R := ℤ) (A := A) (r + 1)).symm

private theorem pointsMulEquiv_typeAGraphPointsMulEquiv
    (A : CommAlgCat.{0} ℤ)
    (f : HopfAlgebra.points (R := ℤ) (H := coordinateHopfAlgebra ℤ (r + 1)) A) :
    pointsMulEquiv (r + 1) (typeAGraphPointsMulEquiv r A f) =
      TauCeti.typeAGraphAutomorphism r A (pointsMulEquiv (r + 1) f) := by
  rw [typeAGraphPointsMulEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply]
  exact (pointsMulEquiv (R := ℤ) (A := A) (r + 1)).apply_symm_apply _

/-- The pointwise graph automorphism in the object presentation used by the points functor. -/
private noncomputable def typeAGraphPointsIsoApp (A : CommAlgCat.{0} ℤ) :
    (HopfAlgebra.pointsFunctor
        (R := ℤ) (H := coordinateHopfAlgebra ℤ (r + 1))).obj A ≅
      (HopfAlgebra.pointsFunctor
        (R := ℤ) (H := coordinateHopfAlgebra ℤ (r + 1))).obj A :=
  eqToIso (HopfAlgebra.pointsFunctor_obj
      (R := ℤ) (H := coordinateHopfAlgebra ℤ (r + 1)) A) ≪≫
    (typeAGraphPointsMulEquiv r A).toGrpIso ≪≫
      eqToIso (HopfAlgebra.pointsFunctor_obj
        (R := ℤ) (H := coordinateHopfAlgebra ℤ (r + 1)) A).symm

/-- The natural automorphism of general-linear points induced by the matrix graph automorphism. -/
private noncomputable def typeAGraphPointsNatIso :
    HopfAlgebra.pointsFunctor (R := ℤ) (H := coordinateHopfAlgebra ℤ (r + 1)) ≅
      HopfAlgebra.pointsFunctor (R := ℤ) (H := coordinateHopfAlgebra ℤ (r + 1)) :=
  NatIso.ofComponents
    (fun A ↦ typeAGraphPointsIsoApp r A)
    (fun {A B} φ ↦ by
      apply (cancel_epi (eqToHom (HopfAlgebra.pointsFunctor_obj
        (R := ℤ) (H := coordinateHopfAlgebra ℤ (r + 1)) A).symm)).1
      apply (cancel_mono (eqToHom (HopfAlgebra.pointsFunctor_obj
        (R := ℤ) (H := coordinateHopfAlgebra ℤ (r + 1)) B))).1
      rw [typeAGraphPointsIsoApp, typeAGraphPointsIsoApp]
      simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, eqToHom_trans, Category.comp_id]
      simp only [← Category.assoc]
      rw [HopfAlgebra.pointsFunctor_map_eqToHom]
      slice_rhs 2 3 => rw [HopfAlgebra.pointsFunctor_map_eqToHom]
      slice_rhs 3 4 => simp
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        Category.comp_id]
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro f
      rw [GrpCat.comp_apply, GrpCat.comp_apply]
      -- `pointsFunctor_obj` presents both categorical point objects by the same `WithConv`
      -- type; rewriting cannot cross those presentation equalities inside the composites.
      change typeAGraphPointsMulEquiv r B (HopfAlgebra.mapPoints φ f) =
        HopfAlgebra.mapPoints φ (typeAGraphPointsMulEquiv r A f)
      apply (pointsMulEquiv (R := ℤ) (A := B) (r + 1)).injective
      simp only [HopfAlgebra.mapPoints]
      rw [pointsMulEquiv_typeAGraphPointsMulEquiv]
      -- Expose `mapPoints` as postcomposition by `φ`; its public naturality theorem is
      -- stated for `AlgHom.mapValue`, while the points functor retains the wrapper.
      change TauCeti.typeAGraphAutomorphism r B
          (pointsMulEquiv (r + 1) (AlgHom.mapValue φ.hom f)) =
        pointsMulEquiv (r + 1)
          (AlgHom.mapValue φ.hom (typeAGraphPointsMulEquiv r A f))
      rw [pointsMulEquiv_mapValue, pointsMulEquiv_mapValue,
        pointsMulEquiv_typeAGraphPointsMulEquiv, TauCeti.map_typeAGraphAutomorphism])

/-- The coordinate Hopf-algebra automorphism corresponding to signed reverse-inverse-transpose
on general-linear points. -/
noncomputable def typeAGraphCoordinateIso :
    coordinateHopfAlgebra ℤ (r + 1) ≅ coordinateHopfAlgebra ℤ (r + 1) :=
  ((CommHopfAlgCat.pointsFunctor (R := ℤ)).preimageIso
    (typeAGraphPointsNatIso r)).unop

/-- Mapping a general-linear coordinate point along `typeAGraphCoordinateIso` realizes the
matrix graph automorphism. -/
theorem pointsMulEquiv_mapPointsFunctor_typeAGraphCoordinateIso
    (A : CommAlgCat.{0} ℤ)
    (f : HopfAlgebra.points (R := ℤ) (H := coordinateHopfAlgebra ℤ (r + 1)) A) :
    pointsMulEquiv (r + 1)
        ((CommHopfAlgCat.mapPointsFunctor (typeAGraphCoordinateIso r).hom).app A f) =
      TauCeti.typeAGraphAutomorphism r A (pointsMulEquiv (r + 1) f) := by
  have hmap := (CommHopfAlgCat.pointsFunctor (R := ℤ)).map_preimage
    (typeAGraphPointsNatIso r).hom
  have happ := congrArg (fun α => α.app A f) hmap
  have hcoordinate : (typeAGraphCoordinateIso r).hom.op =
      (CommHopfAlgCat.pointsFunctor (R := ℤ)).preimage
        (typeAGraphPointsNatIso r).hom := rfl
  -- `mapPointsFunctor` is the same Yoneda map under the opposite-category and `WithConv`
  -- presentations; no rewrite lemma exposes both wrappers simultaneously.
  change pointsMulEquiv (r + 1)
      (((CommHopfAlgCat.pointsFunctor (R := ℤ)).map
        (typeAGraphCoordinateIso r).hom.op).app A f) = _
  rw [hcoordinate, happ]
  -- Evaluating the component of `typeAGraphPointsNatIso` reduces to its underlying point
  -- equivalence only after the `eqToIso` presentation transports cancel.
  change pointsMulEquiv (r + 1) (typeAGraphPointsMulEquiv r A f) = _
  exact pointsMulEquiv_typeAGraphPointsMulEquiv r A f

/-- Explicit precomposition form of the action of `typeAGraphCoordinateIso`. -/
theorem pointsMulEquiv_comp_typeAGraphCoordinateIso
    (A : CommAlgCat.{0} ℤ)
    (f : HopfAlgebra.points (R := ℤ) (H := coordinateHopfAlgebra ℤ (r + 1)) A) :
    pointsMulEquiv (r + 1)
        (toConv (f.ofConv.comp ((typeAGraphCoordinateIso r).hom.hom :
          coordinateHopfAlgebra ℤ (r + 1) →ₐ[ℤ] coordinateHopfAlgebra ℤ (r + 1)))) =
      TauCeti.typeAGraphAutomorphism r A (pointsMulEquiv (r + 1) f) := by
  rw [← CommHopfAlgCat.mapPointsFunctor_app_apply]
  exact pointsMulEquiv_mapPointsFunctor_typeAGraphCoordinateIso r A f

end TauCeti.GeneralLinear
