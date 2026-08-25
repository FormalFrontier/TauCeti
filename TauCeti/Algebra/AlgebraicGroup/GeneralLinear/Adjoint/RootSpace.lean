/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace

/-!
# Adjoint root spaces of the general linear group

For `GL_n` over a field, restrict the adjoint representation to its diagonal split torus.  The
matrix unit `E_ij` is a weight vector of character `e_i - e_j`: conjugation by
`diag(t_0, ..., t_{n-1})` multiplies it by `t_i t_j⁻¹`.  This file turns the pointwise matrix
calculation in `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Basic` into membership in the
actual comodule weight space `Derivation.adjointWeightSpace`.

The character is written multiplicatively because the coordinate algebra of the split torus is
the group algebra on `Multiplicative (ULift (Fin n) →₀ ℤ)`.  Off the diagonal it is nontrivial,
so every ordered pair `i ≠ j` gives an element of
`Derivation.nontrivialAdjointWeights`.  On the diagonal the matrix units have trivial weight,
identifying the diagonal tangent directions as torus-fixed vectors.

## Main declarations

* `TauCeti.GeneralLinear.matrixUnitWeight`: the weight `e_i - e_j`.
* `TauCeti.GeneralLinear.matrixUnitTangent`: the tangent vector corresponding to `E_ij`.
* `tangentMatrix_tangentScalarExtensionEquiv_adjointAction_diagonalTorus_apply`:
  the universal diagonal adjoint action on an arbitrary matrix entry.
* `TauCeti.GeneralLinear.matrixUnitTangent_mem_adjointWeightSpace`: `E_ij` has weight
  `e_i - e_j` under the diagonal torus.
* `TauCeti.GeneralLinear.matrixUnitWeight_mem_nontrivialAdjointWeights`: every off-diagonal
  character `e_i - e_j` is a root read from the adjoint representation.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3.

This is the first worked root calculation for Layer 7, "Root datum of `(G,T)`", of the
ReductiveGroups roadmap.  It connects the diagonal torus of `GL_n` to the abstract adjoint
weight-space API from which the root set of a split pair is read.
-/

public section

open CategoryTheory TensorProduct WithConv

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable {k : Type u} [Field k] {n : ℕ}

/-- The diagonal-torus weight `e_i - e_j` of the matrix unit `E_ij`, written as an element of
the multiplicative character group of the rank-`n` split torus. -/
def matrixUnitWeight (i j : Fin n) :
    Multiplicative (ULift.{u} (Fin n) →₀ ℤ) :=
  Multiplicative.ofAdd
    (Finsupp.single (ULift.up i) 1 - Finsupp.single (ULift.up j) 1)

/-- The exponent of `e_i - e_j` at a torus coordinate. -/
@[simp]
theorem toAdd_matrixUnitWeight_apply (i j : Fin n) (a : ULift.{u} (Fin n)) :
    Multiplicative.toAdd (matrixUnitWeight i j) a =
      (if a = ULift.up i then 1 else 0) - (if a = ULift.up j then 1 else 0) := by
  -- `Multiplicative` is a type synonym, so expose the underlying finitely supported function
  -- before applying the `Finsupp.single` evaluation API.
  change
    ((Finsupp.single (ULift.up i) (1 : ℤ) - Finsupp.single (ULift.up j) 1) :
      ULift.{u} (Fin n) →₀ ℤ) a = _
  classical
  simp [Finsupp.single_apply, eq_comm]

/-- The diagonal character `e_i - e_i` is trivial. -/
@[simp]
theorem matrixUnitWeight_self (i : Fin n) : matrixUnitWeight i i = 1 := by
  apply Multiplicative.toAdd.injective
  simp [matrixUnitWeight]

/-- The matrix-unit weight `e_i - e_j` is trivial exactly on the diagonal. -/
@[simp]
theorem matrixUnitWeight_eq_one_iff (i j : Fin n) :
    matrixUnitWeight i j =
      (1 : Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) ↔ i = j := by
  constructor
  · intro h
    by_contra hij
    have hvalue := congrArg
      (fun alpha : Multiplicative (ULift.{u} (Fin n) →₀ ℤ) ↦
        Multiplicative.toAdd alpha (ULift.up i)) h
    simp [toAdd_matrixUnitWeight_apply, hij] at hvalue
  · rintro rfl
    exact matrixUnitWeight_self i

/-- An off-diagonal root character `e_i - e_j` is nontrivial. -/
theorem matrixUnitWeight_ne_one {i j : Fin n} (hij : i ≠ j) :
    matrixUnitWeight i j ≠
      (1 : Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) := by
  intro h
  exact hij ((matrixUnitWeight_eq_one_iff i j).mp h)

/-- Off the diagonal, the character `e_i - e_j` determines the ordered pair `(i, j)`.  This
follows in the torsion-free character lattice `ULift (Fin n) →₀ ℤ`, independently of the base
field. -/
@[simp]
theorem matrixUnitWeight_eq_matrixUnitWeight_iff {i j : Fin n} (hij : i ≠ j) (a b : Fin n) :
    (matrixUnitWeight a b : Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) =
      matrixUnitWeight i j ↔ a = i ∧ b = j := by
  constructor
  · intro h
    have hi := congrArg
      (fun alpha : Multiplicative (ULift.{u} (Fin n) →₀ ℤ) ↦
        Multiplicative.toAdd alpha (ULift.up i)) h
    have hai : a = i := by
      by_contra hai
      by_cases hbi : b = i
      · subst b
        simp [toAdd_matrixUnitWeight_apply, Ne.symm hai, hij] at hi
      · simp [toAdd_matrixUnitWeight_apply, Ne.symm hai, Ne.symm hbi, hij] at hi
    subst a
    have hj := congrArg
      (fun alpha : Multiplicative (ULift.{u} (Fin n) →₀ ℤ) ↦
        Multiplicative.toAdd alpha (ULift.up j)) h
    have hbj : b = j := by
      by_contra hbj
      simp [Ne.symm hij, Ne.symm hbj] at hj
    exact ⟨rfl, hbj⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem universalPoint_coordinate_mul_inv (i j : Fin n) :
    (SplitTorus.pointsMulEquiv
        (toConv (AlgHom.id k
          (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))))
        (ULift.up i) :
      MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) *
        (((SplitTorus.pointsMulEquiv
          (toConv (AlgHom.id k
            (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))))
          (ULift.up j))⁻¹ :
            (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))ˣ) :
          MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) =
      MonoidAlgebra.single (matrixUnitWeight i j) 1 := by
  have hi : (SplitTorus.pointsMulEquiv
      (toConv (AlgHom.id k
        (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))))
      (ULift.up i) :
      MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) =
      MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1)) 1 := by
    rw [SplitTorus.pointsMulEquiv_apply_coe]
    rfl
  have hj : (((SplitTorus.pointsMulEquiv
      (toConv (AlgHom.id k
        (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))))
      (ULift.up j))⁻¹ :
      (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))ˣ) :
      MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) =
      MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.single (ULift.up j) 1))⁻¹ 1 := by
    rw [SplitTorus.pointsMulEquiv_eq_freeAbelianCharEquiv,
      freeAbelianCharEquiv_apply]
    exact DiagonalizableGroup.charOfPoint_apply_inv_coe _ _
  rw [hi, hj, MonoidAlgebra.single_mul_single, one_mul]
  congr 1
  apply Multiplicative.toAdd.injective
  simp [matrixUnitWeight, sub_eq_add_neg]

private theorem universalPoint_diagonalTorusCoordinateMap :
    toConv ((diagonalTorusCoordinateMap (R := k) (N := n)).hom :
      coordinateHopfAlgebra k n →ₐ[k]
        MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) =
      diagonalTorusPoints
        (toConv (AlgHom.id k
          (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))) :
            WithConv
              (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) →ₐ[k]
                MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  have hvalue := congrArg (fun q ↦ q.ofConv h)
    (mapPointsFunctor_diagonalTorusCoordinateMap_app
      (R := k) (N := n)
      (CommAlgCat.of k (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))))
      (toConv (AlgHom.id k
        (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))))))
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply_apply] at hvalue
  rw [AlgHom.id_apply] at hvalue
  exact hvalue

private theorem pointInCounitAlgebra_universalPoint_diagonalTorus :
    Derivation.pointInCounitAlgebra
        (CommAlgCat.of k (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))))
        (toConv ((diagonalTorusCoordinateMap (R := k) (N := n)).hom :
          coordinateHopfAlgebra k n →ₐ[k]
            MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))) =
      (Bialgebra.CounitAlgebra.pointsMulEquiv k (coordinateHopfAlgebra k n)
        (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))).symm
          (diagonalTorusPoints
            (toConv (AlgHom.id k
              (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))))) := by
  rw [← universalPoint_diagonalTorusCoordinateMap]
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  rw [Bialgebra.CounitAlgebra.pointsMulEquiv_symm_apply]
  exact (Derivation.pointInCounitAlgebra_apply
      (R := k) (H := coordinateHopfAlgebra k n)
      (CommAlgCat.of k (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))))
      (toConv ((diagonalTorusCoordinateMap (R := k) (N := n)).hom :
        coordinateHopfAlgebra k n →ₐ[k]
          MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))) h).trans
    (Bialgebra.CounitAlgebra.algEquivSelf_symm_apply
      (R := k) (A := coordinateHopfAlgebra k n)
      (B := MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) _).symm

/-- The cotangent-dual tangent vector of `GL_n` corresponding to the matrix unit `E_ij`. -/
def matrixUnitTangent (i j : Fin n) :
    Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)) :=
  cotangentDualMatrixEquiv.symm (Matrix.single i j 1)

/-- The matrix of `matrixUnitTangent i j` is the matrix unit `E_ij`. -/
@[simp]
theorem cotangentDualMatrixEquiv_matrixUnitTangent (i j : Fin n) :
    cotangentDualMatrixEquiv (matrixUnitTangent (k := k) i j) = Matrix.single i j 1 := by
  exact LinearEquiv.apply_symm_apply _ _

/-- The universal diagonal-torus adjoint action multiplies the `(i, j)` matrix entry by the
character `e_i - e_j`.  Unlike the matrix-unit specialization below, this formula applies to an
arbitrary tangent vector and is the coefficient calculation used to classify all nontrivial
adjoint weight spaces of `GL_n`. -/
theorem tangentMatrix_tangentScalarExtensionEquiv_adjointAction_diagonalTorus_apply
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
    (i j : Fin n) :
    tangentMatrix n
        (Derivation.tangentScalarExtensionEquiv
          (R := k) (A := coordinateHopfAlgebra k n)
          (B := MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))
          ((Derivation.adjointAction
            (CommAlgCat.of k
              (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))))
            (toConv ((diagonalTorusCoordinateMap (R := k) (N := n)).hom :
              coordinateHopfAlgebra k n →ₐ[k]
                MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))))).val
              (1 ⊗ₜ[k] x))) i j =
      MonoidAlgebra.single (matrixUnitWeight i j)
        ((cotangentDualMatrixEquiv (k := k) (n := n) x) i j) := by
  let M := Multiplicative (ULift.{u} (Fin n) →₀ ℤ)
  let K := MonoidAlgebra k M
  rw [Derivation.tangentScalarExtensionEquiv_adjointAction
    (CommAlgCat.of k K)
    (toConv ((diagonalTorusCoordinateMap (R := k) (N := n)).hom :
      coordinateHopfAlgebra k n →ₐ[k] K))]
  rw [pointInCounitAlgebra_universalPoint_diagonalTorus]
  rw [tangentMatrix_adDerivation_apply_diagonalTorusPoints,
    tangentMatrix_tangentScalarExtensionEquiv_one_tmul, Matrix.map_apply]
  rw [mul_assoc, mul_comm
    (algebraMap k K ((cotangentDualMatrixEquiv (k := k) (n := n) x) i j)), ← mul_assoc]
  rw [universalPoint_coordinate_mul_inv]
  rw [mul_comm (MonoidAlgebra.single (matrixUnitWeight i j) (1 : k)),
    ← MonoidAlgebra.of_apply, ← MonoidAlgebra.single_eq_algebraMap_mul_of]

/-- The matrix unit `E_ij` belongs to the adjoint weight space of the diagonal-torus character
`e_i - e_j`.  This is the formal root-space version of diagonal conjugation scaling the
`(i, j)` matrix entry by `t_i t_j⁻¹`. -/
theorem matrixUnitTangent_mem_adjointWeightSpace (i j : Fin n) :
    matrixUnitTangent (k := k) i j ∈
      Derivation.adjointWeightSpace
        (diagonalTorusCoordinateMap (R := k) (N := n)).hom
        (matrixUnitWeight i j) := by
  rw [Derivation.mem_adjointWeightSpace_iff_universalPointAction]
  let M := Multiplicative (ULift.{u} (Fin n) →₀ ℤ)
  let K := MonoidAlgebra k M
  apply (Derivation.tangentScalarExtensionEquiv
    (R := k) (A := coordinateHopfAlgebra k n) (B := K)).injective
  apply (tangentLinearEquivMatrix n).injective
  apply Matrix.ext
  intro a b
  rw [tangentLinearEquivMatrix_apply, tangentLinearEquivMatrix_apply,
    tangentMatrix_tangentScalarExtensionEquiv_adjointAction_diagonalTorus_apply,
    tangentMatrix_tangentScalarExtensionEquiv_tmul,
    cotangentDualMatrixEquiv_matrixUnitTangent]
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hai : a = i
  · subst a
    by_cases hbj : b = j
    · subst b
      simp
    · simp [Ne.symm hbj]
  · simp [Ne.symm hai]

/-- A diagonal matrix unit is fixed by the adjoint action of the diagonal torus. -/
theorem matrixUnitTangent_mem_trivialAdjointWeightSpace (i : Fin n) :
    matrixUnitTangent (k := k) i i ∈
      Derivation.adjointWeightSpace
        (diagonalTorusCoordinateMap (R := k) (N := n)).hom 1 := by
  simpa using matrixUnitTangent_mem_adjointWeightSpace (k := k) i i

/-- Every matrix-unit tangent vector is nonzero. -/
theorem matrixUnitTangent_ne_zero (i j : Fin n) :
    matrixUnitTangent (k := k) i j ≠ 0 := by
  intro hzero
  have hmatrix := congrArg (cotangentDualMatrixEquiv (k := k) (n := n)) hzero
  have hentry := congrArg (fun X : Matrix (Fin n) (Fin n) k ↦ X i j) hmatrix
  simp at hentry

/-- Every off-diagonal character `e_i - e_j` occurs as a nontrivial adjoint weight of `GL_n`
relative to its diagonal torus. -/
theorem matrixUnitWeight_mem_nontrivialAdjointWeights {i j : Fin n} (hij : i ≠ j) :
    matrixUnitWeight i j ∈
      Derivation.nontrivialAdjointWeights
        (diagonalTorusCoordinateMap (R := k) (N := n)).hom := by
  rw [Derivation.mem_nontrivialAdjointWeights]
  refine ⟨matrixUnitWeight_ne_one hij, ?_⟩
  intro hspace
  have hx := matrixUnitTangent_mem_adjointWeightSpace (k := k) i j
  rw [hspace] at hx
  apply matrixUnitTangent_ne_zero (k := k) i j
  simpa using hx

end

end TauCeti.GeneralLinear
