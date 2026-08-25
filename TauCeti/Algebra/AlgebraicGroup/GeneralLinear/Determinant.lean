/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map

/-!
# The determinant morphism of the general linear group

For a commutative ring `R`, this file constructs the determinant coordinate morphism

`R[Multiplicative ℤ] ⟶ R[Xᵢⱼ][det(X)⁻¹]`.

The determinant of the localized generic matrix is group-like in the bundled coordinate Hopf
algebra of `GLₙ`. The free-group property of `Multiplicative ℤ` therefore sends an integer to
the corresponding integral power of this group-like element. Extending that homomorphism to the
group algebra and evaluating group-like elements gives the coordinate morphism. Its direction is
opposite to the represented group morphism `det : GLₙ ⟶ 𝔾ₘ`.

On algebra-valued convolution points, precomposition with this coordinate morphism agrees with
the ordinary unit-valued determinant of an invertible matrix. This comparison is compatible with
both the group-algebra presentation `D(Multiplicative ℤ)` and Tau Ceti's Laurent-polynomial
multiplicative-group points API. The construction includes rank zero and the zero ring.

## Main declarations

* `TauCeti.GeneralLinear.determinantGroupLike`: the localized generic determinant as a
  group-like element.
* `TauCeti.GeneralLinear.determinantCoordinateMap`: the coordinate Hopf-algebra morphism from
  `D(Multiplicative ℤ)` to `GLₙ`.
* `TauCeti.GeneralLinear.determinantCoordinateMap_single`: its value on every group-algebra
  basis element.
* `TauCeti.GeneralLinear.determinantPoints`: the induced homomorphism on convolution points.
* `TauCeti.GeneralLinear.pointsMulEquiv_determinantPoints`: under the standard point
  equivalences, the induced homomorphism is matrix determinant.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

namespace GeneralLinear

universe u w

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The determinant of the localized generic matrix, transported to the bundled coordinate
Hopf algebra of `GLₙ`, as a group-like element. -/
noncomputable def determinantGroupLike :
    _root_.GroupLike R (coordinateHopfAlgebra R n) where
  val := coordinateHopfAlgebraAlgEquiv R n
    (Matrix.det (localizedGenericMatrix R n))
  isGroupLikeElem_val := by
    constructor
    · rw [coordinateHopfAlgebra_counit_apply,
        counit_det_localizedGenericMatrix]
    · rw [coordinateHopfAlgebra_comul_apply,
        comul_det_localizedGenericMatrix]
      simp

/-- The value of `determinantGroupLike` is the transported localized generic determinant. -/
@[simp]
theorem determinantGroupLike_val :
    (determinantGroupLike R n : coordinateHopfAlgebra R n) =
      coordinateHopfAlgebraAlgEquiv R n
        (Matrix.det (localizedGenericMatrix R n)) :=
  by rw [determinantGroupLike]

/-- The determinant coordinate morphism
`O(𝔾ₘ) = R[Multiplicative ℤ] ⟶ O(GLₙ)`, packaged between the underlying commutative
Hopf algebras of the existing finite-type coordinate objects. Relative spectrum reverses this
arrow to the represented morphism `det : GLₙ ⟶ 𝔾ₘ`. -/
noncomputable def determinantCoordinateMap :
    _root_.CommHopfAlgCat.of R (MonoidAlgebra R (Multiplicative ℤ)) ⟶
      coordinateHopfAlgebra R n :=
  _root_.CommHopfAlgCat.ofHom ((MonoidAlgebra.liftGroupLikeBialgHom
      (R := R) (A := coordinateHopfAlgebra R n)).comp
    (MonoidAlgebra.mapDomainBialgHom R
      (zpowersHom (_root_.GroupLike R (coordinateHopfAlgebra R n))
        (determinantGroupLike R n))))

/-- The determinant coordinate morphism sends the basis element indexed by `m` to the scalar
multiple of the `m`-th integral power of the group-like generic determinant. -/
theorem determinantCoordinateMap_single (m : ℤ) (r : R) :
    (determinantCoordinateMap R n).hom
        (MonoidAlgebra.single (Multiplicative.ofAdd m) r) =
      r • (↑((determinantGroupLike R n) ^ m) : coordinateHopfAlgebra R n) := by
  rw [determinantCoordinateMap, _root_.CommHopfAlgCat.hom_ofHom,
    BialgHom.comp_apply,
    MonoidAlgebra.mapDomainBialgHom_single,
    MonoidAlgebra.liftGroupLikeBialgHom_apply,
    MonoidAlgebra.lift_single, MonoidHom.coe_mk, OneHom.coe_mk,
    zpowersHom_apply, toAdd_ofAdd]

/-- The standard group-algebra generator maps to the localized generic determinant. -/
@[simp]
theorem determinantCoordinateMap_ofAdd_one :
    (determinantCoordinateMap R n).hom
        (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) 1) =
      coordinateHopfAlgebraAlgEquiv R n
        (Matrix.det (localizedGenericMatrix R n)) := by
  simpa using determinantCoordinateMap_single R n 1 1

section Points

variable {A : Type w} [CommSemiring A] [Algebra R A]

/-- Precomposition with the determinant coordinate morphism, as a homomorphism from `GLₙ`
convolution points to points of the group-algebra presentation of `𝔾ₘ`. -/
noncomputable def determinantPoints :
    WithConv (coordinateHopfAlgebra R n →ₐ[R] A) →*
      WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A) :=
  AlgHom.mapDomain
    (determinantCoordinateMap R n).hom

/-- The point induced by the determinant coordinate morphism acts by precomposition. -/
theorem determinantPoints_apply_apply
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A))
    (x : MonoidAlgebra R (Multiplicative ℤ)) :
    (determinantPoints R n f).ofConv x =
      f.ofConv
        ((determinantCoordinateMap R n).hom x) :=
  by rw [determinantPoints, AlgHom.mapDomain_apply_apply]

variable {B : Type*} [CommSemiring B] [Algebra R B]

/-- The determinant homomorphism on convolution points is natural in the value algebra. -/
theorem mapValue_determinantPoints (phi : A →ₐ[R] B) :
    (determinantPoints (A := B) R n).comp
        (AlgHom.mapValue (H := coordinateHopfAlgebra R n) phi) =
      (AlgHom.mapValue (H := MonoidAlgebra R (Multiplicative ℤ)) phi).comp
        (determinantPoints (A := A) R n) := by
  exact AlgHom.mapValue_mapDomain
    (determinantCoordinateMap R n).hom phi

end Points

section MatrixComparison

variable {A : Type w} [CommRing A] [Algebra R A]

/-- Evaluation of the group-like generic determinant at a general-linear point is the
determinant of the associated invertible matrix. -/
theorem point_apply_determinantGroupLike
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    f.ofConv (determinantGroupLike R n : coordinateHopfAlgebra R n) =
      Matrix.det (pointToGeneralLinear n f).val := by
  calc
    f.ofConv (determinantGroupLike R n : coordinateHopfAlgebra R n) =
        f.ofConv (coordinateHopfAlgebraAlgEquiv R n
          (Matrix.det (localizedGenericMatrix R n))) := by
      rw [determinantGroupLike_val]
    _ =
        (f.ofConv.comp (coordinateHopfAlgebraAlgEquiv R n).toAlgHom)
          (Matrix.det (localizedGenericMatrix R n)) := by
      rw [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply]
    _ = Matrix.det ((localizedGenericMatrix R n).map
        (f.ofConv.comp (coordinateHopfAlgebraAlgEquiv R n).toAlgHom)) := by
      rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
    _ = Matrix.det (pointToGeneralLinear n f).val := by
      congr 1
      ext i j
      simp

/-- Under the diagonalizable-group and general-linear point equivalences, precomposition with
the determinant coordinate morphism is the ordinary unit-valued matrix determinant. -/
theorem pointsMulEquiv_determinantPoints
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    DiagonalizableGroup.pointsMulEquiv
        (determinantPoints R n f) (Multiplicative.ofAdd (1 : ℤ)) =
      Matrix.GeneralLinearGroup.det (pointsMulEquiv n f) := by
  apply Units.ext
  rw [DiagonalizableGroup.pointsMulEquiv_apply,
    DiagonalizableGroup.charOfPoint_apply_coe,
    determinantPoints_apply_apply, determinantCoordinateMap_ofAdd_one,
    ← determinantGroupLike_val, point_apply_determinantGroupLike,
    Matrix.GeneralLinearGroup.val_det_apply, pointsMulEquiv_apply]

/-- Starting with an invertible matrix, the point induced by the determinant coordinate
morphism corresponds to its ordinary determinant unit. -/
theorem pointsMulEquiv_determinantPoints_symm_apply
    (g : Matrix.GeneralLinearGroup (Fin n) A) :
    DiagonalizableGroup.pointsMulEquiv
        (determinantPoints R n ((pointsMulEquiv (R := R) n).symm g))
        (Multiplicative.ofAdd (1 : ℤ)) =
      Matrix.GeneralLinearGroup.det g := by
  rw [pointsMulEquiv_determinantPoints, MulEquiv.apply_symm_apply]

/-- The determinant comparison through Tau Ceti's Laurent-polynomial multiplicative-group
points equivalence. -/
theorem multiplicativeGroup_pointEquiv_determinantPoints
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    MultiplicativeGroup.pointEquiv
        ((determinantPoints R n f).ofConv.comp
          (AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := R) R ℤ).toAlgHom) =
      Matrix.GeneralLinearGroup.det (pointsMulEquiv n f) := by
  calc
    MultiplicativeGroup.pointEquiv
        ((determinantPoints R n f).ofConv.comp
          (AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := R) R ℤ).toAlgHom) =
        DiagonalizableGroup.charOfPoint (determinantPoints R n f).ofConv
          (Multiplicative.ofAdd (1 : ℤ)) :=
      (DiagonalizableGroup.multiplicativeGroup_pointEquiv_apply
        (determinantPoints R n f).ofConv).symm
    _ = Matrix.GeneralLinearGroup.det (pointsMulEquiv n f) := by
      simpa only [DiagonalizableGroup.pointsMulEquiv_apply] using
        pointsMulEquiv_determinantPoints R n f

end MatrixComparison

end GeneralLinear

end TauCeti
