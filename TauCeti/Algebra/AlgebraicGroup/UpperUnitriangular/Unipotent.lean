/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Faithful
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Basic
public import TauCeti.Algebra.AlgebraicGroup.UpperUnitriangular.Scheme
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# The upper-unitriangular group is unipotent

For a natural number `n`, the generic upper-unitriangular matrix defines the standard comodule of
the coordinate Hopf algebra `O(U_n)` on `R^n`.  Its coordinate morphism is the closed immersion
`U_n → GL_n`, so this comodule is faithful.  At every point its action is
the corresponding upper-unitriangular matrix, hence is unipotent.  The faithful-representation
criterion then proves that every geometric point of `U_m` is unipotent.

The coordinate ring is a polynomial algebra in the entries strictly above the diagonal.  It is
therefore smooth; over a field this makes `U_m` a smooth unipotent affine group.

## Main declarations

* `TauCeti.UpperUnitriangular.standardComodule`: the standard faithful comodule of `O(U_n)`.
* `TauCeti.UpperUnitriangular.isUnipotentPoint`: every field-valued point of `U_n` is unipotent.
* `TauCeti.UpperUnitriangular.smoothUnipotentCommHopfAlgProperty_coordinateHopfAlgebra`:
  `U_n` over a field is smooth unipotent.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This supplies the upper-unitriangular model in Layer 5, "Unipotent groups", of the
ReductiveGroups roadmap.  Together with closure under smooth closed subgroups, it is the forward
direction of the roadmap's upper-unitriangular embedding characterization.
-/

public section

open Module WithConv
open scoped TensorProduct

namespace TauCeti.UpperUnitriangular

universe u w

variable (R : Type u) [CommRing R]
variable (n : ℕ)

/-- The standard coaction of `O(U_n)` on column vectors.  On the `j`-th basis vector it is the
`j`-th column of the generic upper-unitriangular matrix. -/
noncomputable def standardCoact :
    (Fin n → R) →ₗ[R] (Fin n → R) ⊗[R] coordinateHopfAlgebra R (Fin n) :=
  (Pi.basisFun R (Fin n)).constr R fun j ↦
    ∑ i, (Pi.single i (1 : R) : Fin n → R) ⊗ₜ[R]
      coordinateHopfAlgebraAlgEquiv R (Fin n) (genericMatrix R (Fin n) i j)

/-- The standard coaction on a basis vector is the corresponding column of the generic matrix. -/
@[simp]
theorem standardCoact_basis (j : Fin n) :
    standardCoact R n (Pi.single j 1) =
      ∑ i, (Pi.single i (1 : R) : Fin n → R) ⊗ₜ[R]
        coordinateHopfAlgebraAlgEquiv R (Fin n) (genericMatrix R (Fin n) i j) := by
  rw [standardCoact, ← Pi.basisFun_apply, Basis.constr_basis]

/-- The standard right comodule of the upper-unitriangular coordinate Hopf algebra. -/
@[expose, instance_reducible]
noncomputable def standardComodule :
    Comodule R (coordinateHopfAlgebra R (Fin n)) (Fin n → R) where
  coact := standardCoact R n
  coassoc := by
    apply (Pi.basisFun R (Fin n)).ext
    intro j
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [Pi.basisFun_apply, standardCoact_basis]
    simp only [map_sum, LinearMap.rTensor_tmul, standardCoact_basis,
      TensorProduct.sum_tmul, LinearEquiv.coe_coe, TensorProduct.assoc_tmul,
      LinearMap.lTensor_tmul,
      coordinateHopfAlgebra_comul_genericMatrix_apply, TensorProduct.tmul_sum]
    rw [Finset.sum_comm]
  lTensor_counit_comp_coact := by
    apply (Pi.basisFun R (Fin n)).ext
    intro j
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [Pi.basisFun_apply, standardCoact_basis]
    simp only [map_sum, LinearMap.lTensor_tmul,
      coordinateHopfAlgebra_counit_genericMatrix_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · simp

/-- The coaction of the standard comodule is `standardCoact`. -/
@[simp]
theorem standardComodule_coact :
    (standardComodule R n).coact = standardCoact R n :=
  rfl

attribute [local instance] standardComodule

/-- The coefficient matrix of the standard comodule is the generic upper-unitriangular matrix. -/
theorem coefficientMatrix_standardBasis :
    Comodule.coefficientMatrix (C := coordinateHopfAlgebra R (Fin n))
        (Pi.basisFun R (Fin n)) = fun i j ↦
          coordinateHopfAlgebraAlgEquiv R (Fin n) (genericMatrix R (Fin n) i j) := by
  ext i j
  rw [Comodule.coefficientMatrix_apply, Comodule.matrixCoefficient_def,
    standardComodule_coact, Pi.basisFun_apply, standardCoact_basis]
  simp [Pi.single_apply]

/-- The coordinate morphism of the standard comodule is the coordinate morphism of the closed
immersion `U_n → GL_n`. -/
theorem coordinateBialgHom_standardBasis :
    Comodule.coordinateBialgHom (H := coordinateHopfAlgebra R (Fin n))
        (Pi.basisFun R (Fin n)) = (coordinateMap R n).hom := by
  apply BialgHom.ext
  intro x
  have hAlg :
      (Comodule.coordinateBialgHom (H := coordinateHopfAlgebra R (Fin n))
          (Pi.basisFun R (Fin n))).toAlgHom = (coordinateMap R n).hom.toAlgHom := by
    apply GeneralLinear.coordinateHopfAlgebra_algHom_ext R n
    intro i j
    calc
      _ = Comodule.coefficientMatrix (C := coordinateHopfAlgebra R (Fin n))
            (Pi.basisFun R (Fin n)) i j :=
        Comodule.coordinateBialgHom_X (Pi.basisFun R (Fin n)) i j
      _ = coordinateHopfAlgebraAlgEquiv R (Fin n) (genericMatrix R (Fin n) i j) := by
        rw [coefficientMatrix_standardBasis]
      _ = _ := (coordinateMap_genericMatrix_apply R n i j).symm
  exact DFunLike.congr_fun hAlg x

/-- The standard comodule of `U_n` is faithful. -/
theorem isFaithful_standardComodule :
    Comodule.IsFaithful (k := R) (H := coordinateHopfAlgebra R (Fin n))
      (V := Fin n → R) := by
  rw [Comodule.isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom
      (b := Pi.basisFun R (Fin n)),
    Comodule.isClosedImmersion_coordinateGroupSchemeHom_iff,
    coordinateBialgHom_standardBasis]
  exact coordinateMap_surjective R n

section PointAction

variable {A : Type w} [CommRing A] [Algebra R A]

/-- The canonical identification of the scalar extension of the standard module with `A^n`. -/
noncomputable abbrev standardScalarExtensionEquiv :
    A ⊗[R] (Fin n → R) ≃ₗ[A] Fin n → A :=
  TensorProduct.piScalarRight R A A (Fin n)

/-- Under the canonical scalar-extension equivalence, a point acts through its associated
upper-unitriangular matrix. -/
theorem standardScalarExtensionEquiv_comp_endOfPoint
    (g : WithConv (coordinateHopfAlgebra R (Fin n) →ₐ[R] A)) :
    (standardScalarExtensionEquiv R n).toLinearMap.comp
        (Comodule.endOfPoint (Fin n → R) g.ofConv) =
      (Matrix.GeneralLinearGroup.toLin
        (pointToUpperUnitriangular R (Fin n) g : Matrix.GeneralLinearGroup (Fin n) A) :
          (Fin n → A) →ₗ[A] Fin n → A).comp
            (standardScalarExtensionEquiv R n).toLinearMap := by
  apply ((Pi.basisFun R (Fin n)).baseChange A).ext
  intro j
  simp only [LinearMap.comp_apply, Module.Basis.baseChange_apply]
  rw [Comodule.endOfPoint_tmul, standardComodule_coact, Pi.basisFun_apply,
    standardCoact_basis]
  simp only [map_sum, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply,
    TensorProduct.comm_tmul, one_smul, Matrix.GeneralLinearGroup.toLin_apply,
    Matrix.mulVecLin_apply]
  ext i
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct]
  simp [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    Pi.single_apply, pointToUpperUnitriangular_apply]

/-- Transporting the standard point action to `A^m` gives the natural linear action of the
associated upper-unitriangular matrix. -/
theorem congrLinearEquiv_pointsAction_eq_toLin
    (g : WithConv (coordinateHopfAlgebra R (Fin n) →ₐ[R] A)) :
    LinearMap.GeneralLinearGroup.congrLinearEquiv (standardScalarExtensionEquiv R n)
        (LinearMap.GeneralLinearGroup.ofLinearEquiv
          (Comodule.pointsAction (Fin n → R) g)) =
      Matrix.GeneralLinearGroup.toLin
        (pointToUpperUnitriangular R (Fin n) g : Matrix.GeneralLinearGroup (Fin n) A) := by
  apply Units.ext
  apply LinearMap.ext
  intro x
  change (standardScalarExtensionEquiv R n)
      ((Comodule.pointsAction (Fin n → R) g).toLinearMap
        ((standardScalarExtensionEquiv R n).symm x)) =
    (Matrix.GeneralLinearGroup.toLin
      (pointToUpperUnitriangular R (Fin n) g : Matrix.GeneralLinearGroup (Fin n) A) :
        Module.End A (Fin n → A)) x
  rw [Comodule.pointsAction_toLinearMap]
  have h := LinearMap.congr_fun (standardScalarExtensionEquiv_comp_endOfPoint R n g)
    ((standardScalarExtensionEquiv R n).symm x)
  simpa using h

/-- The standard representation sends every point of `U_n` to a unipotent automorphism. -/
theorem isUnipotent_pointsAction
    (g : WithConv (coordinateHopfAlgebra R (Fin n) →ₐ[R] A)) :
    GeneralLinearGroup.IsUnipotent
      (LinearMap.GeneralLinearGroup.ofLinearEquiv
        (Comodule.pointsAction (Fin n → R) g)) := by
  apply (GeneralLinearGroup.isUnipotent_congrLinearEquiv_iff
    (standardScalarExtensionEquiv R n)
    (LinearMap.GeneralLinearGroup.ofLinearEquiv
      (Comodule.pointsAction (Fin n → R) g))).mp
  change GeneralLinearGroup.IsUnipotent
    (LinearMap.GeneralLinearGroup.congrLinearEquiv (standardScalarExtensionEquiv R n)
      (LinearMap.GeneralLinearGroup.ofLinearEquiv
        (Comodule.pointsAction (Fin n → R) g)))
  rw [congrLinearEquiv_pointsAction_eq_toLin]
  exact UpperUnitriangularGroup.isUnipotent_toLin (pointToUpperUnitriangular R (Fin n) g)

end PointAction

section Unipotent

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [PerfectField K]

/-- Every point of the upper-unitriangular coordinate Hopf algebra over a perfect field is
unipotent. -/
theorem isUnipotentPoint
    (g : WithConv (coordinateHopfAlgebra k (Fin n) →ₐ[k] K)) :
    HopfAlgebra.IsUnipotentPoint g := by
  let M : FGComoduleCat.{u, u, u} k (coordinateHopfAlgebra k (Fin n)) :=
    FGComoduleCat.of (R := k) (C := coordinateHopfAlgebra k (Fin n)) (Fin n → k)
  rw [HopfAlgebra.isUnipotentPoint_iff_isUnipotent_pointsAction_of_isFaithful M
    (isFaithful_standardComodule k n) g]
  exact isUnipotent_pointsAction k n g

/-- The upper-unitriangular group has only unipotent geometric points. -/
theorem geometricallyUnipotentPointsCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] :
    geometricallyUnipotentPointsCommHopfAlgProperty k (coordinateHopfAlgebra k (Fin n)) := by
  rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff]
  exact fun g ↦ isUnipotentPoint n g

/-- The upper-unitriangular group is a smooth unipotent affine group. -/
theorem smoothUnipotentCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] :
    smoothUnipotentCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k (Fin n)) := by
  let _ : Algebra.FiniteType k (coordinateHopfAlgebra k (Fin n)) :=
    Algebra.FiniteType.equiv
      (inferInstanceAs (Algebra.FiniteType k (CoordinateRing k (Fin n))))
      (coordinateHopfAlgebraAlgEquiv k (Fin n))
  let H : FiniteTypeCommHopfAlgCat k :=
    FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra k (Fin n))
  have hH : finiteTypeCoordinateHopfAlgebra k (Fin n) = H := by
    apply CategoryTheory.ObjectProperty.FullSubcategory.ext
    exact finiteTypeCoordinateHopfAlgebra_obj k (Fin n)
  rw [hH]
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  constructor
  · let _ : Algebra.Smooth k (CoordinateRing k (Fin n)) :=
      ⟨inferInstance, inferInstance⟩
    exact Algebra.Smooth.of_equiv (coordinateHopfAlgebraAlgEquiv k (Fin n))
  · exact fun g ↦ isUnipotentPoint n g

end Unipotent

end TauCeti.UpperUnitriangular
