/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.PointsFunctor
public import TauCeti.Algebra.AlgebraicGroup.UpperUnitriangular.Coordinate.HopfAlgebra

/-!
# The functor of points of the upper-unitriangular group

For a commutative ring `R`, this file identifies the convolution group of algebra-valued points
of the upper-unitriangular coordinate Hopf algebra with the existing upper-unitriangular matrix
group. The equivalence is natural in the commutative value algebra and therefore assembles into
a natural isomorphism of group-valued functors.

The construction includes empty finite index types and zero rings. It does not yet package a
group scheme.

## Main declarations

* `TauCeti.UpperUnitriangular.pointsMulEquiv`: its convolution points are the existing
  `TauCeti.upperUnitriangularGroup`.
* `TauCeti.UpperUnitriangular.pointToUpperUnitriangular_mapValue`: the point identification is
  natural in the value algebra.
* `TauCeti.UpperUnitriangular.pointsMulEquiv_mapValue`: the bundled point equivalence is natural
  in the value algebra.
* `TauCeti.UpperUnitriangular.upperUnitriangularFunctor`: the group-valued matrix functor.
* `TauCeti.UpperUnitriangular.pointsNatIso`: the natural isomorphism between the points and matrix
  functors.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.

The layout follows `GeneralLinear.FunctorOfPoints`.
-/

public section

open scoped TensorProduct

namespace TauCeti.UpperUnitriangular

open Algebra.TensorProduct CategoryTheory WithConv

universe u v w

section HopfAlgebra

variable (R : Type u) [CommRing R] (m : Type v) [Fintype m] [LinearOrder m]

section Points

variable {A : Type w} [CommRing A] [Algebra R A]

/-- Evaluate a point of the coordinate Hopf algebra on the generic matrix. -/
private noncomputable def matrixOfPoint
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) : Matrix m m A :=
  (genericMatrix R m).map (f.ofConv.comp (coordinateHopfAlgebraAlgEquiv R m).toAlgHom)

private theorem isUpperUnitriangular_matrixOfPoint
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    (matrixOfPoint R m f).IsUpperUnitriangular :=
  (isUpperUnitriangular_genericMatrix R m).map
    (f.ofConv.comp (coordinateHopfAlgebraAlgEquiv R m).toAlgHom)

@[simp]
private theorem matrixOfPoint_apply
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) (i j : m) :
    matrixOfPoint R m f i j =
      f.ofConv (coordinateHopfAlgebraAlgEquiv R m (genericMatrix R m i j)) := by
  rfl

/-- The upper-unitriangular matrix obtained by evaluating a point on the generic matrix. -/
noncomputable def pointToUpperUnitriangular
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    upperUnitriangularGroup m A :=
  let h := isUpperUnitriangular_matrixOfPoint R m f
  ⟨h.toGL, UpperUnitriangularGroup.toGL_mem_upperUnitriangularGroup h⟩

/-- As a matrix, a point is evaluated entrywise on the generic matrix. -/
@[simp]
theorem coe_pointToUpperUnitriangular
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    (((pointToUpperUnitriangular R m f : upperUnitriangularGroup m A) :
      Matrix.GeneralLinearGroup m A) : Matrix m m A) =
        (genericMatrix R m).map
          (f.ofConv.comp (coordinateHopfAlgebraAlgEquiv R m).toAlgHom) := by
  simp [pointToUpperUnitriangular, matrixOfPoint]

/-- Reading a point as an upper-unitriangular matrix evaluates it on the corresponding
generic entry. -/
@[simp]
theorem pointToUpperUnitriangular_apply
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) (i j : m) :
    ((pointToUpperUnitriangular R m f : upperUnitriangularGroup m A) :
        Matrix.GeneralLinearGroup m A) i j =
      f.ofConv (coordinateHopfAlgebraAlgEquiv R m (genericMatrix R m i j)) := by
  rw [coe_pointToUpperUnitriangular]
  rfl

/-- On a strict-upper entry, point evaluation is coordinate evaluation. -/
theorem pointToUpperUnitriangular_apply_of_lt
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) {i j : m} (h : i < j) :
    ((pointToUpperUnitriangular R m f : upperUnitriangularGroup m A) :
        Matrix.GeneralLinearGroup m A) i j =
      f.ofConv (coordinateHopfAlgebraAlgEquiv R m
        (MvPolynomial.X (show Index m from ⟨(i, j), h⟩))) := by
  rw [pointToUpperUnitriangular_apply, genericMatrix_apply_of_lt R m h]

/-- Evaluate the strict-upper polynomial coordinates at an upper-unitriangular matrix. -/
noncomputable def upperUnitriangularToPoint
    (g : upperUnitriangularGroup m A) :
    WithConv (coordinateHopfAlgebra R m →ₐ[R] A) :=
  toConv ((MvPolynomial.aeval fun ij : Index m =>
    ((g : Matrix.GeneralLinearGroup m A) : Matrix m m A)
      ij.1.1 ij.1.2).comp
        (coordinateHopfAlgebraAlgEquiv R m).symm.toAlgHom)

/-- The point associated to an upper-unitriangular matrix sends each strict-upper coordinate
to the corresponding entry. -/
@[simp]
theorem upperUnitriangularToPoint_apply
    (g : upperUnitriangularGroup m A) (ij : Index m) :
    (upperUnitriangularToPoint R m g).ofConv
        (coordinateHopfAlgebraAlgEquiv R m (MvPolynomial.X ij)) =
      ((g : Matrix.GeneralLinearGroup m A) : Matrix m m A)
        ij.1.1 ij.1.2 := by
  simp [upperUnitriangularToPoint]

/-- Evaluating the point associated to an upper-unitriangular matrix recovers that matrix. -/
@[simp]
theorem pointToUpperUnitriangular_upperUnitriangularToPoint
    (g : upperUnitriangularGroup m A) :
    pointToUpperUnitriangular R m (upperUnitriangularToPoint R m g) = g := by
  apply UpperUnitriangularGroup.ext
  intro i j hij
  rw [pointToUpperUnitriangular_apply, genericMatrix_apply_of_lt R m hij,
    upperUnitriangularToPoint_apply]

/-- Forming a point from the matrix read off a point recovers the original point. -/
@[simp]
theorem upperUnitriangularToPoint_pointToUpperUnitriangular
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    upperUnitriangularToPoint R m (pointToUpperUnitriangular R m f) = f := by
  apply WithConv.ext
  apply coordinateHopfAlgebra_algHom_ext R m
  intro ij
  rw [upperUnitriangularToPoint_apply, pointToUpperUnitriangular_apply,
    genericMatrix_apply_of_lt R m ij.2]

/-- Evaluation on the generic matrix carries convolution to matrix multiplication. -/
@[simp]
theorem pointToUpperUnitriangular_mul
    (f g : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    pointToUpperUnitriangular R m (f * g) =
      pointToUpperUnitriangular R m f * pointToUpperUnitriangular R m g := by
  apply UpperUnitriangularGroup.ext
  intro i j hij
  simp only [pointToUpperUnitriangular_apply_of_lt R m _ hij]
  rw [AlgHom.convMul_apply, coordinateHopfAlgebra_comul_X]
  simp only [map_sum, lift_tmul, Subgroup.coe_mul, Units.val_mul,
    Matrix.mul_apply, pointToUpperUnitriangular_apply]

/-- The convolution group of points of the coordinate Hopf algebra is the ordinary
upper-unitriangular matrix group. -/
noncomputable def pointsMulEquiv :
    WithConv (coordinateHopfAlgebra R m →ₐ[R] A) ≃*
      upperUnitriangularGroup m A where
  toFun := pointToUpperUnitriangular R m
  invFun := upperUnitriangularToPoint R m
  left_inv := upperUnitriangularToPoint_pointToUpperUnitriangular R m
  right_inv := pointToUpperUnitriangular_upperUnitriangularToPoint R m
  map_mul' := pointToUpperUnitriangular_mul R m

/-- The forward map of `pointsMulEquiv` is evaluation on the generic matrix. -/
@[simp]
theorem pointsMulEquiv_apply
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    pointsMulEquiv R m f = pointToUpperUnitriangular R m f :=
  (rfl)

/-- The inverse map of `pointsMulEquiv` is polynomial evaluation on strict-upper entries. -/
@[simp]
theorem pointsMulEquiv_symm_apply (g : upperUnitriangularGroup m A) :
    (pointsMulEquiv R m).symm g = upperUnitriangularToPoint R m g :=
  (rfl)

/-- Reading a point as an upper-unitriangular matrix commutes with maps of value algebras. -/
theorem pointToUpperUnitriangular_mapValue {B : Type*} [CommRing B] [Algebra R B]
    (φ : A →ₐ[R] B) (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    pointToUpperUnitriangular R m
        (AlgHom.mapValue (H := coordinateHopfAlgebra R m) φ f) =
      UpperUnitriangularGroup.map φ.toRingHom (pointToUpperUnitriangular R m f) := by
  apply UpperUnitriangularGroup.ext
  intro i j hij
  rw [pointToUpperUnitriangular_apply_of_lt R m _ hij,
    UpperUnitriangularGroup.map_apply,
    pointToUpperUnitriangular_apply_of_lt R m f hij]
  simp only [AlgHom.mapValue_apply, WithConv.ofConv_toConv, AlgHom.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe]

/-- The pointwise group equivalence is natural in the value algebra. -/
theorem pointsMulEquiv_mapValue {B : Type*} [CommRing B] [Algebra R B]
    (φ : A →ₐ[R] B) (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    pointsMulEquiv R m (AlgHom.mapValue (H := coordinateHopfAlgebra R m) φ f) =
      UpperUnitriangularGroup.map φ.toRingHom (pointsMulEquiv R m f) := by
  exact pointToUpperUnitriangular_mapValue R m φ f

/-- Naturality of the inverse pointwise equivalence in the value algebra. -/
theorem mapValue_pointsMulEquiv_symm_apply {B : Type*} [CommRing B] [Algebra R B]
    (φ : A →ₐ[R] B) (g : upperUnitriangularGroup m A) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R m) φ ((pointsMulEquiv R m).symm g) =
      (pointsMulEquiv R m).symm (UpperUnitriangularGroup.map φ.toRingHom g) := by
  apply (pointsMulEquiv (R := R) (A := B) m).injective
  rw [pointsMulEquiv_mapValue]
  simp

end Points

section Functor

/-- The group-valued functor sending a commutative `R`-algebra to its upper-unitriangular group,
before the universe lift used by `upperUnitriangularFunctor`. -/
private noncomputable abbrev upperUnitriangularFunctorUnlifted :
    CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj A := GrpCat.of (upperUnitriangularGroup m (A : Type w))
  map φ := GrpCat.ofHom (UpperUnitriangularGroup.map φ.hom.toRingHom)
  map_id _ := by
    ext g i j
    simp
  map_comp _ _ := by
    ext g i j
    simp

/-- The group-valued functor sending a commutative `R`-algebra to its upper-unitriangular group
and a value-algebra morphism to entrywise application. Its values are universe-lifted so that its
codomain agrees with the generic Hopf-algebra points functor. -/
noncomputable def upperUnitriangularFunctor :
    CommAlgCat.{w} R ⥤ GrpCat.{max u v w} :=
  upperUnitriangularFunctorUnlifted (R := R) m ⋙ GrpCat.uliftFunctor.{u, max v w}

/-- The object part of `upperUnitriangularFunctor` is the universe lift of the ordinary
upper-unitriangular group. -/
theorem upperUnitriangularFunctor_obj (A : CommAlgCat.{w} R) :
    (upperUnitriangularFunctor (R := R) m).obj A =
      GrpCat.of (ULift.{u, max v w} (upperUnitriangularGroup m A)) :=
  (rfl)

/-- The morphism part of `upperUnitriangularFunctor` applies the value-algebra map entrywise. -/
theorem upperUnitriangularFunctor_map {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    (upperUnitriangularFunctor (R := R) m).map φ =
      eqToHom (upperUnitriangularFunctor_obj (R := R) m A) ≫
        GrpCat.ofHom
          (MulEquiv.ulift.symm.toMonoidHom.comp
            ((UpperUnitriangularGroup.map φ.hom.toRingHom).comp
              MulEquiv.ulift.toMonoidHom)) ≫
        eqToHom (upperUnitriangularFunctor_obj (R := R) m B).symm :=
  (rfl)

/-- Entrywise computation of a value-algebra map on the upper-unitriangular functor. -/
@[simp]
theorem upperUnitriangularFunctor_map_apply_apply {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (g : ULift.{u, max v w} (upperUnitriangularGroup m A)) (i j : m) :
    (eqToHom (upperUnitriangularFunctor_obj (R := R) m B)
      ((upperUnitriangularFunctor (R := R) m).map φ
        (eqToHom (upperUnitriangularFunctor_obj (R := R) m A).symm g))).down.val i j =
      φ.hom (g.down.val i j) :=
  UpperUnitriangularGroup.map_apply φ.hom.toRingHom g.down i j

/-- The convolution-points functor of the upper-unitriangular coordinate Hopf algebra is
naturally isomorphic to the ordinary upper-unitriangular group functor. -/
noncomputable def pointsNatIso :
    HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m) ≅
      upperUnitriangularFunctor (R := R) m :=
  NatIso.ofComponents
    (fun A ↦ ((pointsMulEquiv (R := R) (A := A) m).trans
      MulEquiv.ulift.symm).toGrpIso)
    (by
      intro A B φ
      ext f
      apply ULift.ext
      exact pointsMulEquiv_mapValue R m φ.hom f)

/-- After transport along `upperUnitriangularFunctor_obj`, the forward component of
`pointsNatIso` is the pointwise upper-unitriangular equivalence. -/
@[simp]
theorem pointsNatIso_hom_app_apply (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R m) A) :
    (eqToHom (upperUnitriangularFunctor_obj (R := R) m A)
      ((pointsNatIso (R := R) m).hom.app A f)).down = pointsMulEquiv R m f :=
  (rfl)

/-- After transport back along `upperUnitriangularFunctor_obj`, the inverse component of
`pointsNatIso` is polynomial evaluation on strict-upper entries. -/
@[simp]
theorem pointsNatIso_inv_app_apply (A : CommAlgCat.{w} R)
    (g : ULift.{u, max v w} (upperUnitriangularGroup m A)) :
    (pointsNatIso (R := R) m).inv.app A
        (eqToHom (upperUnitriangularFunctor_obj (R := R) m A).symm g) =
      (pointsMulEquiv (R := R) m).symm g.down :=
  (rfl)

end Functor

end HopfAlgebra

end TauCeti.UpperUnitriangular
