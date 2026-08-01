/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.CoordinateHopfAlgebra
public import TauCeti.Algebra.AlgebraicGroup.PointsFunctor

/-!
# The functor of points of the general linear group

For a commutative ring `R` and `n : ℕ`, this file identifies the convolution group of
algebra-valued points of the coordinate Hopf algebra

`R[Xᵢⱼ][det(X)⁻¹]`

with Mathlib's general linear group. A point is sent to the matrix of its values on the
localized generic entries. Conversely, an invertible matrix defines polynomial evaluation,
which extends uniquely across the determinant localization. The matrix-multiplication
comultiplication makes this equivalence multiplicative in the ordinary, rather than opposite,
order.

The equivalences are natural in the commutative value algebra. They therefore assemble into a
natural isomorphism from `HopfAlgebra.pointsFunctor` for `coordinateHopfAlgebra` to the functor
of invertible matrices. The construction includes rank zero and zero rings, without a
nontriviality or positive-rank assumption.

## Main declarations

* `TauCeti.GeneralLinear.pointToGeneralLinear`: the invertible matrix read from a point.
* `TauCeti.GeneralLinear.generalLinearToPoint`: the point obtained by matrix evaluation.
* `TauCeti.GeneralLinear.pointsMulEquiv`: the group equivalence between convolution points and
  invertible matrices.
* `TauCeti.GeneralLinear.generalLinearFunctor`: the group-valued functor of invertible matrices.
* `TauCeti.GeneralLinear.pointsNatIso`: the natural isomorphism between the two functors.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.8 and §§3.2--3.6.
* The Stacks Project, Tags
  [022W](https://stacks.math.columbia.edu/tag/022W),
  [022X](https://stacks.math.columbia.edu/tag/022X), and
  [00CM](https://stacks.math.columbia.edu/tag/00CM).
-/

public section

open CategoryTheory WithConv

namespace TauCeti

namespace GeneralLinear

universe u w

variable {R : Type u} [CommRing R] (n : ℕ)

section Pointwise

variable {A : Type w} [CommRing A] [Algebra R A]

/-- The matrix of values of a point on the localized generic matrix. -/
private noncomputable def matrixOfPoint
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) : Matrix (Fin n) (Fin n) A :=
  (localizedGenericMatrix R n).map
    (f.ofConv.comp (coordinateHopfAlgebraAlgEquiv R n).toAlgHom)

/-- An entry of `matrixOfPoint f` is the value of `f` on the corresponding bundled coordinate. -/
@[simp]
private theorem matrixOfPoint_apply
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) (i j : Fin n) :
    matrixOfPoint n f i j =
      f.ofConv (coordinateHopfAlgebraAlgEquiv R n
        (coordinateRingMap R n (MvPolynomial.X (i, j)))) := by
  simp [matrixOfPoint]

private theorem isUnit_det_matrixOfPoint
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    IsUnit (Matrix.det (matrixOfPoint n f)) := by
  rw [matrixOfPoint, ← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
  exact (isUnit_det_localizedGenericMatrix R n).map
    (f.ofConv.comp (coordinateHopfAlgebraAlgEquiv R n).toAlgHom)

/-- The invertible matrix obtained by evaluating a point on the localized generic matrix. -/
noncomputable def pointToGeneralLinear
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    Matrix.GeneralLinearGroup (Fin n) A :=
  Matrix.GeneralLinearGroup.mk'' (matrixOfPoint n f) (isUnit_det_matrixOfPoint n f)

/-- Reading a point as an invertible matrix evaluates it on the corresponding bundled
coordinate. -/
@[simp]
theorem pointToGeneralLinear_apply
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) (i j : Fin n) :
    pointToGeneralLinear n f i j =
      f.ofConv (coordinateHopfAlgebraAlgEquiv R n
        (coordinateRingMap R n (MvPolynomial.X (i, j)))) := by
  exact matrixOfPoint_apply n f i j

private noncomputable def evaluationOfGeneralLinear
    (g : Matrix.GeneralLinearGroup (Fin n) A) :
    MatrixMonoid.CoordinateRing R n →ₐ[R] A :=
  MvPolynomial.aeval fun ij : Fin n × Fin n ↦
    g.val ij.1 ij.2

private theorem evaluationOfGeneralLinear_determinant_isUnit
    (g : Matrix.GeneralLinearGroup (Fin n) A) :
    IsUnit (evaluationOfGeneralLinear (R := R) n g
      (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R))) := by
  rw [evaluationOfGeneralLinear, AlgHom.map_det,
    Matrix.mvPolynomialX_mapMatrix_aeval]
  exact Matrix.isUnits_det_units g

private noncomputable def localizedEvaluationOfGeneralLinear
    (g : Matrix.GeneralLinearGroup (Fin n) A) : CoordinateRing R n →ₐ[R] A :=
  IsLocalization.Away.liftAlgHom
    (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R))
    (evaluationOfGeneralLinear_determinant_isUnit (R := R) n g)

private theorem localizedEvaluationOfGeneralLinear_coordinateRingMap
    (g : Matrix.GeneralLinearGroup (Fin n) A) (x : MatrixMonoid.CoordinateRing R n) :
    localizedEvaluationOfGeneralLinear (R := R) n g (coordinateRingMap R n x) =
      evaluationOfGeneralLinear (R := R) n g x := by
  rw [coordinateRingMap_apply]
  simp [localizedEvaluationOfGeneralLinear]

/-- The point of the bundled general linear coordinate Hopf algebra obtained by evaluating the
generic matrix at an invertible matrix. -/
noncomputable def generalLinearToPoint
    (g : Matrix.GeneralLinearGroup (Fin n) A) :
    WithConv (coordinateHopfAlgebra R n →ₐ[R] A) :=
  toConv ((localizedEvaluationOfGeneralLinear (R := R) n g).comp
    (coordinateHopfAlgebraAlgEquiv R n).symm.toAlgHom)

private theorem generalLinearToPoint_ofConv
    (g : Matrix.GeneralLinearGroup (Fin n) A) :
    (generalLinearToPoint (R := R) n g).ofConv =
      (localizedEvaluationOfGeneralLinear (R := R) n g).comp
        (coordinateHopfAlgebraAlgEquiv R n).symm.toAlgHom := by
  rw [generalLinearToPoint]

/-- Evaluation at an invertible matrix sends a polynomial in the bundled coordinate ring to its
multivariable polynomial evaluation at the matrix entries. -/
@[simp]
theorem generalLinearToPoint_coordinateRingMap
    (g : Matrix.GeneralLinearGroup (Fin n) A) (x : MatrixMonoid.CoordinateRing R n) :
    (generalLinearToPoint (R := R) n g).ofConv
        (coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n x)) =
      MvPolynomial.aeval (fun ij : Fin n × Fin n ↦ g.val ij.1 ij.2) x := by
  rw [generalLinearToPoint_ofConv, AlgHom.comp_apply]
  have heq :
      (coordinateHopfAlgebraAlgEquiv R n).symm.toAlgHom
          (coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n x)) =
        coordinateRingMap R n x :=
    (coordinateHopfAlgebraAlgEquiv R n).symm_apply_apply _
  rw [heq]
  rw [localizedEvaluationOfGeneralLinear_coordinateRingMap]
  rfl

/-- The point obtained from an invertible matrix sends a bundled generic coordinate to the
corresponding matrix entry. -/
theorem generalLinearToPoint_apply
    (g : Matrix.GeneralLinearGroup (Fin n) A) (i j : Fin n) :
    (generalLinearToPoint (R := R) n g).ofConv
        (coordinateHopfAlgebraAlgEquiv R n
          (coordinateRingMap R n (MvPolynomial.X (i, j)))) =
      g.val i j := by
  rw [generalLinearToPoint_coordinateRingMap]
  exact MvPolynomial.aeval_X _ _

/-- Evaluating the point associated to an invertible matrix recovers that matrix. -/
@[simp]
theorem pointToGeneralLinear_generalLinearToPoint
    (g : Matrix.GeneralLinearGroup (Fin n) A) :
    pointToGeneralLinear (R := R) n (generalLinearToPoint (R := R) n g) = g := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [pointToGeneralLinear_apply, generalLinearToPoint_apply]

/-- Forming a point from the invertible matrix read from a point recovers the original point. -/
@[simp]
theorem generalLinearToPoint_pointToGeneralLinear
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    generalLinearToPoint (R := R) n (pointToGeneralLinear n f) = f := by
  have hraw :
      localizedEvaluationOfGeneralLinear (R := R) n (pointToGeneralLinear n f) =
        f.ofConv.comp (coordinateHopfAlgebraAlgEquiv R n).toAlgHom := by
    apply algHom_ext_away R n
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    simp only [AlgHom.comp_apply]
    rw [localizedEvaluationOfGeneralLinear_coordinateRingMap]
    simp [evaluationOfGeneralLinear]
  apply WithConv.ext
  rw [generalLinearToPoint_ofConv, hraw]
  ext x
  simp

/-- Reading points as invertible matrices carries convolution to ordinary matrix
multiplication, with the tensor-factor order unchanged. -/
theorem pointToGeneralLinear_mul
    (f g : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    pointToGeneralLinear n (f * g) = pointToGeneralLinear n f * pointToGeneralLinear n g := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [pointToGeneralLinear_apply, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.mul_apply]
  rw [AlgHom.convMul_apply, coordinateHopfAlgebra_comul_X]
  simp

/-- The convolution group of points of the general linear coordinate Hopf algebra is the
ordinary general linear group. Multiplication has the same order on both sides. -/
noncomputable def pointsMulEquiv :
    WithConv (coordinateHopfAlgebra R n →ₐ[R] A) ≃*
      Matrix.GeneralLinearGroup (Fin n) A where
  toFun := pointToGeneralLinear n
  invFun := generalLinearToPoint (R := R) n
  left_inv := generalLinearToPoint_pointToGeneralLinear n
  right_inv := pointToGeneralLinear_generalLinearToPoint n
  map_mul' := pointToGeneralLinear_mul n

/-- The forward map of `pointsMulEquiv` is evaluation on the localized generic matrix. -/
@[simp]
theorem pointsMulEquiv_apply
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    pointsMulEquiv n f = pointToGeneralLinear n f :=
  (rfl)

/-- The inverse map of `pointsMulEquiv` is the extension of matrix evaluation across the
determinant localization. -/
@[simp]
theorem pointsMulEquiv_symm_apply (g : Matrix.GeneralLinearGroup (Fin n) A) :
    (pointsMulEquiv (R := R) n).symm g = generalLinearToPoint (R := R) n g :=
  (rfl)

end Pointwise

section Naturality

variable {A B : Type w} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Reading a point as an invertible matrix commutes with maps of value algebras. -/
theorem pointToGeneralLinear_mapValue (phi : A →ₐ[R] B)
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    pointToGeneralLinear n
        (AlgHom.mapValue (H := coordinateHopfAlgebra R n) phi f) =
      Matrix.GeneralLinearGroup.map phi.toRingHom (pointToGeneralLinear n f) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp

/-- The pointwise group equivalence is natural in the value algebra. -/
theorem pointsMulEquiv_mapValue (phi : A →ₐ[R] B)
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    pointsMulEquiv n (AlgHom.mapValue (H := coordinateHopfAlgebra R n) phi f) =
      Matrix.GeneralLinearGroup.map phi.toRingHom (pointsMulEquiv n f) := by
  exact pointToGeneralLinear_mapValue n phi f

/-- Naturality of the inverse pointwise equivalence in the value algebra. -/
theorem mapValue_pointsMulEquiv_symm_apply (phi : A →ₐ[R] B)
    (g : Matrix.GeneralLinearGroup (Fin n) A) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R n) phi
        ((pointsMulEquiv (R := R) n).symm g) =
      (pointsMulEquiv (R := R) n).symm
        (Matrix.GeneralLinearGroup.map phi.toRingHom g) := by
  apply (pointsMulEquiv (R := R) (A := B) n).injective
  rw [pointsMulEquiv_mapValue]
  simp

end Naturality

section Functor

/-- The group-valued functor sending a commutative `R`-algebra to its general linear group, before
the universe lift used by `generalLinearFunctor`. -/
private noncomputable abbrev generalLinearFunctorUnlifted :
    CommAlgCat.{w} R ⥤ GrpCat.{w} where
  obj A := GrpCat.of (Matrix.GeneralLinearGroup (Fin n) (A : Type w))
  map phi := GrpCat.ofHom (Matrix.GeneralLinearGroup.map phi.hom.toRingHom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The group-valued functor sending a commutative `R`-algebra to its general linear group and
a value-algebra morphism to entrywise application. Its values are universe-lifted so that its
codomain agrees with the generic Hopf-algebra points functor. -/
noncomputable def generalLinearFunctor :
    CommAlgCat.{w} R ⥤ GrpCat.{max u w} :=
  generalLinearFunctorUnlifted (R := R) n ⋙ GrpCat.uliftFunctor.{u, w}

/-- The object part of `generalLinearFunctor` is the universe lift of the ordinary general
linear group. -/
theorem generalLinearFunctor_obj (A : CommAlgCat.{w} R) :
    (generalLinearFunctor (R := R) n).obj A =
      GrpCat.of (ULift.{u, w} (Matrix.GeneralLinearGroup (Fin n) A)) :=
  (rfl)

/-- The morphism part of `generalLinearFunctor` applies the value-algebra map entrywise. The
equality transports along `generalLinearFunctor_obj` because the functor's implementation is
opaque. -/
theorem generalLinearFunctor_map {A B : CommAlgCat.{w} R} (phi : A ⟶ B) :
    (generalLinearFunctor (R := R) n).map phi =
      eqToHom (generalLinearFunctor_obj (R := R) n A) ≫
        GrpCat.ofHom
          (MulEquiv.ulift.symm.toMonoidHom.comp
            ((Matrix.GeneralLinearGroup.map phi.hom.toRingHom).comp
              MulEquiv.ulift.toMonoidHom)) ≫
        eqToHom (generalLinearFunctor_obj (R := R) n B).symm :=
  (rfl)

/-- Entrywise computation of the value-algebra map on the general linear functor. -/
@[simp]
theorem generalLinearFunctor_map_apply_apply {A B : CommAlgCat.{w} R} (phi : A ⟶ B)
    (g : ULift.{u, w} (Matrix.GeneralLinearGroup (Fin n) A)) (i j : Fin n) :
    (eqToHom (generalLinearFunctor_obj (R := R) n B)
      ((generalLinearFunctor (R := R) n).map phi
        (eqToHom (generalLinearFunctor_obj (R := R) n A).symm g))).down i j =
      phi.hom (g.down.val i j) :=
  (rfl)

/-- The convolution-points functor of the general linear coordinate Hopf algebra is naturally
isomorphic to the ordinary general linear group functor. -/
noncomputable def pointsNatIso :
    HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R n) ≅
      generalLinearFunctor (R := R) n :=
  NatIso.ofComponents
    (fun A ↦ ((pointsMulEquiv (R := R) (A := A) n).trans
      MulEquiv.ulift.symm).toGrpIso)
    (by
      intro A B phi
      ext f
      apply ULift.ext
      exact pointsMulEquiv_mapValue n phi.hom f)

/-- After transport along `generalLinearFunctor_obj`, the forward component of `pointsNatIso` is
the pointwise general-linear equivalence. -/
@[simp]
theorem pointsNatIso_hom_app_apply (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n) A) :
    (eqToHom (generalLinearFunctor_obj (R := R) n A)
      ((pointsNatIso (R := R) n).hom.app A f)).down = pointsMulEquiv n f :=
  (rfl)

/-- After transport back along `generalLinearFunctor_obj`, the inverse component of `pointsNatIso`
is evaluation at an invertible matrix. -/
@[simp]
theorem pointsNatIso_inv_app_apply (A : CommAlgCat.{w} R)
    (g : ULift.{u, w} (Matrix.GeneralLinearGroup (Fin n) A)) :
    (pointsNatIso (R := R) n).inv.app A
        (eqToHom (generalLinearFunctor_obj (R := R) n A).symm g) =
      (pointsMulEquiv (R := R) n).symm g.down :=
  (rfl)

end Functor

end GeneralLinear

end TauCeti
