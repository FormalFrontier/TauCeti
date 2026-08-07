/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.HopfAlgebra
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Comul
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints

/-!
# The coordinate morphism of a finite free comodule

A right comodule structure on `Fin n → R` over a commutative Hopf algebra `H` determines a
matrix whose `(i, j)` entry is the matrix coefficient of the `j`th basis vector against the
`i`th coordinate functional.  The comodule laws say that this matrix is multiplicative under
comultiplication and specializes to the identity under the counit.  The Hopf laws make its
entrywise antipode an inverse matrix.

Consequently its determinant is a unit, so evaluation on this matrix extends from the matrix
monoid coordinate ring to the coordinate ring of `GLₙ`.  This file packages that extension as
a bialgebra morphism

```text
O(GLₙ) ⟶ H.
```

This is the coordinate-ring morphism opposite to the representation of the affine group
represented by `H` on `Fin n → R`.  Its surjectivity is the algebraic condition which the
faithful-representation criterion identifies with a closed immersion into `GLₙ`.

## Main declarations

* `TauCeti.Comodule.coordinateMatrix`: the matrix of basis coefficients of a comodule.
* `TauCeti.Comodule.coact_basis_eq_sum_coordinateMatrix`: the coaction is multiplication by
  the coordinate matrix on the standard basis.
* `TauCeti.Comodule.coordinateMatrix_mul_antipodeMatrix` and
  `TauCeti.Comodule.antipodeMatrix_mul_coordinateMatrix`: the two inverse-matrix identities.
* `TauCeti.Comodule.coordinateBialgHom`: the induced morphism `O(GLₙ) ⟶ H`.
* `TauCeti.Comodule.coordinateBialgHom_X`: the coordinate morphism sends the generic entry
  `Xᵢⱼ` to the corresponding matrix coefficient.

## References

This is the standard coordinate morphism of a finite free representation; see J. S.
Milne, *Algebraic Groups* (2017), Chapter 4, especially Remark 4.1 and Theorem 4.9.  It advances
`ReductiveGroups/README.md`, Layer 1, "Faithfulness done right".
-/

public section

open scoped TensorProduct
open Coalgebra WithConv

namespace TauCeti.Comodule

universe u v

noncomputable section

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable {n : ℕ}

/-- The matrix of basis coefficients of a comodule on `Fin n → R`.

If `eⱼ` is the standard basis and `eⁱ` its coordinate functional, then the `(i, j)` entry
is `c(eⁱ, eⱼ)`. -/
def coordinateMatrix (rho : Comodule R H (Fin n → R)) : Matrix (Fin n) (Fin n) H :=
  let _ : Comodule R H (Fin n → R) := rho
  fun i j ↦ matrixCoefficient (R := R) (C := H) ((Pi.basisFun R (Fin n)).coord i)
    (Pi.basisFun R (Fin n) j)

/-- An entry of the coordinate matrix is the corresponding standard-basis matrix coefficient. -/
theorem coordinateMatrix_apply (rho : Comodule R H (Fin n → R)) (i j : Fin n) :
    coordinateMatrix rho i j =
      let _ : Comodule R H (Fin n → R) := rho
      matrixCoefficient (R := R) (C := H) ((Pi.basisFun R (Fin n)).coord i)
        (Pi.basisFun R (Fin n) j) :=
  (rfl)

/-- The coaction of a standard basis vector is its column in the coordinate matrix. -/
theorem coact_basis_eq_sum_coordinateMatrix
    (rho : Comodule R H (Fin n → R)) (j : Fin n) :
    rho.coact (Pi.basisFun R (Fin n) j) =
      ∑ i : Fin n, Pi.basisFun R (Fin n) i ⊗ₜ[R] coordinateMatrix rho i j := by
  let _ : Comodule R H (Fin n → R) := rho
  exact coact_eq_sum_basis_matrixCoefficient (C := H) (Pi.basisFun R (Fin n))
    (Pi.basisFun R (Fin n) j)

/-- Comultiplication of a coordinate entry is matrix multiplication across the two tensor
factors. -/
@[simp]
theorem comul_coordinateMatrix (rho : Comodule R H (Fin n → R)) (i j : Fin n) :
    Coalgebra.comul (R := R) (A := H) (coordinateMatrix rho i j) =
      ∑ k : Fin n, coordinateMatrix rho i k ⊗ₜ[R] coordinateMatrix rho k j := by
  let _ : Comodule R H (Fin n → R) := rho
  exact comul_matrixCoefficient_eq_sum (C := H) (Pi.basisFun R (Fin n))
    ((Pi.basisFun R (Fin n)).coord i) (Pi.basisFun R (Fin n) j)

/-- The counit of a coordinate entry is the corresponding identity-matrix entry. -/
@[simp]
theorem counit_coordinateMatrix (rho : Comodule R H (Fin n → R)) (i j : Fin n) :
    Coalgebra.counit (R := R) (A := H) (coordinateMatrix rho i j) =
      if i = j then 1 else 0 := by
  let _ : Comodule R H (Fin n → R) := rho
  rw [coordinateMatrix_apply, counit_matrixCoefficient]
  simpa only [Module.Basis.coord_apply, eq_comm] using
    (Pi.basisFun R (Fin n)).repr_self_apply j i

/-- The entrywise antipode of the coordinate matrix is a right inverse. -/
@[simp]
theorem coordinateMatrix_mul_antipodeMatrix
    (rho : Comodule R H (Fin n → R)) :
    coordinateMatrix rho * (coordinateMatrix rho).map (HopfAlgebra.antipode R) = 1 := by
  classical
  let _ : Comodule R H (Fin n → R) := rho
  ext i j
  have hconv := congrArg
    (fun f : WithConv (H →ₗ[R] H) ↦ f.ofConv (coordinateMatrix rho i j))
    (LinearMap.id_mul_antipode (R := R) (C := H))
  simp only [LinearMap.convMul_def, LinearMap.comp_apply, ofConv_toConv] at hconv
  rw [comul_coordinateMatrix rho i j] at hconv
  simpa [Matrix.mul_apply, Matrix.one_apply, LinearMap.convOne_def, Pi.single_apply]
    using hconv

/-- The entrywise antipode of the coordinate matrix is a left inverse. -/
@[simp]
theorem antipodeMatrix_mul_coordinateMatrix
    (rho : Comodule R H (Fin n → R)) :
    (coordinateMatrix rho).map (HopfAlgebra.antipode R) * coordinateMatrix rho = 1 := by
  classical
  let _ : Comodule R H (Fin n → R) := rho
  ext i j
  have hconv := congrArg
    (fun f : WithConv (H →ₗ[R] H) ↦ f.ofConv (coordinateMatrix rho i j))
    (LinearMap.antipode_mul_id (R := R) (C := H))
  simp only [LinearMap.convMul_def, LinearMap.comp_apply, ofConv_toConv] at hconv
  rw [comul_coordinateMatrix rho i j] at hconv
  simpa [Matrix.mul_apply, Matrix.one_apply, LinearMap.convOne_def, Pi.single_apply]
    using hconv

/-- The determinant of the coordinate matrix is a unit. -/
theorem isUnit_det_coordinateMatrix (rho : Comodule R H (Fin n → R)) :
    IsUnit (Matrix.det (coordinateMatrix rho)) := by
  classical
  exact Matrix.isUnit_det_of_right_inverse (coordinateMatrix_mul_antipodeMatrix rho)

private noncomputable def coordinateAlgHom (rho : Comodule R H (Fin n → R)) :
    GeneralLinear.coordinateHopfAlgebra R n →ₐ[R] H :=
  (GeneralLinear.generalLinearToPoint (R := R) n
    (Matrix.GeneralLinearGroup.mk'' (coordinateMatrix rho)
      (isUnit_det_coordinateMatrix rho))).ofConv

@[simp]
private theorem coordinateAlgHom_X (rho : Comodule R H (Fin n → R)) (i j : Fin n) :
    coordinateAlgHom rho
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
          (GeneralLinear.coordinateRingMap R n (MvPolynomial.X (i, j)))) =
      coordinateMatrix rho i j := by
  exact GeneralLinear.generalLinearToPoint_apply (R := R) n _ i j

private theorem coordinateAlgHom_ext
    {A : Type*} [Semiring A] [Algebra R A]
    {f g : GeneralLinear.coordinateHopfAlgebra R n →ₐ[R] A}
    (h : ∀ i j, f (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
      (GeneralLinear.coordinateRingMap R n (MvPolynomial.X (i, j)))) =
        g (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
          (GeneralLinear.coordinateRingMap R n (MvPolynomial.X (i, j))))) :
    f = g := by
  let e := GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
  have hcomp : f.comp e.toAlgHom = g.comp e.toAlgHom := by
    apply GeneralLinear.algHom_ext_away R n
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, e] using h i j
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  exact DFunLike.congr_fun hcomp y

private theorem coordinateAlgHom_counit
    (rho : Comodule R H (Fin n → R)) :
    (Bialgebra.counitAlgHom R H).comp (coordinateAlgHom rho) =
      Bialgebra.counitAlgHom R (GeneralLinear.coordinateHopfAlgebra R n) := by
  apply coordinateAlgHom_ext
  intro i j
  simp

private theorem coordinateAlgHom_comul
    (rho : Comodule R H (Fin n → R)) :
    (Algebra.TensorProduct.map (coordinateAlgHom rho) (coordinateAlgHom rho)).comp
        (Bialgebra.comulAlgHom R (GeneralLinear.coordinateHopfAlgebra R n)) =
      (Bialgebra.comulAlgHom R H).comp (coordinateAlgHom rho) := by
  apply coordinateAlgHom_ext
  intro i j
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
    GeneralLinear.coordinateHopfAlgebra_comul_X, map_sum,
    Algebra.TensorProduct.map_tmul, coordinateAlgHom_X]
  exact (comul_coordinateMatrix rho i j).symm

/-- The coordinate Hopf-algebra morphism associated to a comodule on `Fin n → R`.

Contravariantly, this is the morphism from the affine group represented by `H` to `GLₙ`
defined by the corresponding representation. -/
def coordinateBialgHom (rho : Comodule R H (Fin n → R)) :
    GeneralLinear.coordinateHopfAlgebra R n →ₐc[R] H :=
  BialgHom.ofAlgHom (coordinateAlgHom rho) (coordinateAlgHom_counit rho)
    (coordinateAlgHom_comul rho)

/-- The coordinate Hopf-algebra morphism sends a generic matrix entry to the corresponding
matrix coefficient. -/
@[simp]
theorem coordinateBialgHom_X (rho : Comodule R H (Fin n → R)) (i j : Fin n) :
    coordinateBialgHom rho
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
          (GeneralLinear.coordinateRingMap R n (MvPolynomial.X (i, j)))) =
      coordinateMatrix rho i j := by
  exact coordinateAlgHom_X rho i j

end

end TauCeti.Comodule
