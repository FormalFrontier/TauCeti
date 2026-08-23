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

* `TauCeti.GeneralLinear.adjointRootCharacter`: the character `e_i - e_j`.
* `TauCeti.GeneralLinear.cotangentDualMatrixEquiv`: the cotangent-dual Lie algebra of `GL_n`
  identified with matrices.
* `TauCeti.GeneralLinear.matrixUnitTangent`: the tangent vector corresponding to `E_ij`.
* `TauCeti.GeneralLinear.matrixUnitTangent_mem_adjointWeightSpace`: `E_ij` has weight
  `e_i - e_j` under the diagonal torus.
* `TauCeti.GeneralLinear.adjointRootCharacter_mem_nontrivialAdjointWeights`: every off-diagonal
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

namespace Derivation

open TauCeti

universe u

variable {R H : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
variable [Module.Projective R (Bialgebra.CotangentSpace R H)]
variable {M : Type u} [CommGroup M]

/-- Membership in an adjoint weight space can be tested on the universal point of the
diagonalizable group.  The universal point acts on a weight vector of weight `alpha` by the
group-algebra basis element `[alpha]`.

This is the converse to `endOfPoint_tmul_of_mem_adjointWeightSpace` at the universal point. -/
theorem mem_adjointWeightSpace_iff_universalPointAction
    (pi : H →ₐc[R] MonoidAlgebra R M) (alpha : M)
    (x : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    x ∈ adjointWeightSpace pi alpha ↔
      (adjointAction (CommAlgCat.of R (MonoidAlgebra R M))
          (toConv (pi : H →ₐ[R] MonoidAlgebra R M))).val (1 ⊗ₜ[R] x) =
        MonoidAlgebra.single alpha (1 : R) ⊗ₜ[R] x := by
  let V := Module.Dual R (Bialgebra.CotangentSpace R H)
  let U := ULift.{u} H
  let K := MonoidAlgebra R M
  let phi : U →ₐ[R] K :=
    (pi : H →ₐ[R] K).comp (ULift.algEquiv (R := R) : U ≃ₐ[R] H).toAlgHom
  let g : HopfAlgebra.points (H := H) (CommAlgCat.of R U) :=
    toConv (ULift.algEquiv (R := R) : U ≃ₐ[R] H).symm.toAlgHom
  have hmapPoint : HopfAlgebra.mapPoints (H := H) (CommAlgCat.ofHom phi) g =
      toConv (pi : H →ₐ[R] K) := by
    apply WithConv.ofConv_injective
    ext h
    rfl
  have hnatural :=
    (adjointPointRepresentation (R := R) (H := H)).action_mapPoints_one_tmul
      (CommAlgCat.ofHom phi) g x
  rw [adjointPointRepresentation_action, hmapPoint] at hnatural
  have hcore :
      TensorProduct.comm R V K
          (TensorProduct.map LinearMap.id (pi : H →ₗc[R] K).toLinearMap
            ((adjointComodule (R := R) (H := H)).coact x)) =
        (adjointAction (CommAlgCat.of R K) (toConv (pi : H →ₐ[R] K))).val
          (1 ⊗ₜ[R] x) := by
    rw [adjointComodule_coact_apply]
    rw [hnatural]
    let z :=
      (((adjointPointRepresentation (R := R) (H := H)).action
        (CommAlgCat.of R U) g).val (1 ⊗ₜ[R] x))
    change
      TensorProduct.comm R V K
          (TensorProduct.map LinearMap.id (pi : H →ₗc[R] K).toLinearMap
            (TensorProduct.comm R H V
              (TensorProduct.map
                (ULift.algEquiv (R := R) : U ≃ₐ[R] H).toLinearMap LinearMap.id z))) =
        GeneralLinear.scalarExtensionMap (V := V) (CommAlgCat.ofHom phi) z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) ha hb
    | tmul a y =>
        simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.comm_tmul]
        rw [GeneralLinear.scalarExtensionMap_tmul]
        rfl
  rw [mem_adjointWeightSpace]
  constructor
  · intro hx
    rw [← hcore, hx, TensorProduct.comm_tmul]
  · intro hx
    apply (TensorProduct.comm R V K).injective
    rw [hcore, hx, TensorProduct.comm_tmul]

end Derivation

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The coordinate Hopf algebra of `GL_n` carries the finite-type instance recorded by its
bundled finite-type coordinate algebra. -/
instance instAlgebraFiniteTypeCoordinateHopfAlgebra :
    Algebra.FiniteType R (coordinateHopfAlgebra R n) :=
  by
    rw [← finiteTypeCoordinateHopfAlgebra_obj (R := R) n]
    exact (finiteTypeCommHopfAlgProperty_iff _).mp
      (finiteTypeCoordinateHopfAlgebra R n).property

variable {k : Type u} [Field k] {n : ℕ}

/-- The diagonal-torus character `e_i - e_j` of `GL_n`, written as an element of the
multiplicative character group of the rank-`n` split torus. -/
def adjointRootCharacter (i j : Fin n) :
    Multiplicative (ULift.{u} (Fin n) →₀ ℤ) :=
  Multiplicative.ofAdd
    (Finsupp.single (ULift.up i) 1 - Finsupp.single (ULift.up j) 1)

/-- The exponent of `e_i - e_j` at a torus coordinate. -/
@[simp]
theorem toAdd_adjointRootCharacter_apply (i j : Fin n) (a : ULift.{u} (Fin n)) :
    Multiplicative.toAdd (adjointRootCharacter i j) a =
      (if a = ULift.up i then 1 else 0) - (if a = ULift.up j then 1 else 0) := by
  change
    ((Finsupp.single (ULift.up i) (1 : ℤ) - Finsupp.single (ULift.up j) 1) :
      ULift.{u} (Fin n) →₀ ℤ) a = _
  classical
  simp [Finsupp.single_apply, eq_comm]

/-- The diagonal character `e_i - e_i` is trivial. -/
@[simp]
theorem adjointRootCharacter_self (i : Fin n) : adjointRootCharacter i i = 1 := by
  apply Multiplicative.toAdd.injective
  simp [adjointRootCharacter]

/-- An off-diagonal root character `e_i - e_j` is nontrivial. -/
theorem adjointRootCharacter_ne_one {i j : Fin n} (hij : i ≠ j) :
    adjointRootCharacter i j ≠
      (1 : Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) := by
  intro h
  have hvalue := congrArg
    (fun alpha : Multiplicative (ULift.{u} (Fin n) →₀ ℤ) ↦
      Multiplicative.toAdd alpha (ULift.up i)) h
  simp [toAdd_adjointRootCharacter_apply, hij] at hvalue

/-- The cotangent-dual Lie algebra of `GL_n` identified linearly with `n × n` matrices. -/
def cotangentDualMatrixEquiv :
    Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)) ≃ₗ[k]
      Matrix (Fin n) (Fin n) k :=
  Derivation.cotangentLinearEquiv (R := k) (A := coordinateHopfAlgebra k n) (B := k) ≪≫ₗ
    tangentLinearEquivMatrix n

/-- Scalar extension of a cotangent-dual tangent vector applies the scalar map entrywise to its
matrix.  This is the compatibility that lets computations on coefficient-valued derivations be
read back in the fixed cotangent-dual Lie algebra. -/
theorem tangentMatrix_tangentScalarExtensionEquiv_one_tmul
    {A : Type u} [CommRing A] [Algebra k A]
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n))) :
    tangentMatrix n
        (Derivation.tangentScalarExtensionEquiv
          (R := k) (A := coordinateHopfAlgebra k n) (B := A) (1 ⊗ₜ[k] x)) =
      (cotangentDualMatrixEquiv x).map (algebraMap k A) := by
  ext i j
  rw [tangentMatrix_apply, Derivation.tangentScalarExtensionEquiv_tmul_apply,
    Matrix.map_apply]
  simp only [one_mul, cotangentDualMatrixEquiv, LinearEquiv.trans_apply,
    tangentLinearEquivMatrix_apply, tangentMatrix_apply,
    Derivation.cotangentLinearEquiv_apply_apply]
  let r := x (Bialgebra.cotangentMap k (coordinateHopfAlgebra k n)
    (coordinateHopfAlgebraAlgEquiv k n
      (coordinateRingMap k n (MvPolynomial.X (i, j)))))
  trans algebraMap k A r
  · exact Bialgebra.CounitAlgebra.algEquivSelf_apply
      (R := k) (A := coordinateHopfAlgebra k n) (B := A) _
  · exact congrArg (algebraMap k A)
      (Bialgebra.CounitAlgebra.algEquivSelf_apply
        (R := k) (A := coordinateHopfAlgebra k n) (B := k) _).symm

/-- The matrix form of scalar extension on a pure tensor. -/
theorem tangentMatrix_tangentScalarExtensionEquiv_tmul
    {A : Type u} [CommRing A] [Algebra k A] (a : A)
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n))) :
    tangentMatrix n
        (Derivation.tangentScalarExtensionEquiv
          (R := k) (A := coordinateHopfAlgebra k n) (B := A) (a ⊗ₜ[k] x)) =
      a • (cotangentDualMatrixEquiv x).map (algebraMap k A) := by
  rw [show a ⊗ₜ[k] x = a • (1 ⊗ₜ[k] x) by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
  rw [map_smul, map_smul, tangentMatrix_tangentScalarExtensionEquiv_one_tmul]

private theorem universalPoint_coordinate_mul_inv (i j : Fin n) :
    let M := Multiplicative (ULift.{u} (Fin n) →₀ ℤ)
    let K := MonoidAlgebra k M
    let p : WithConv (K →ₐ[k] K) := toConv (AlgHom.id k K)
    (SplitTorus.pointsMulEquiv p (ULift.up i) : K) *
        (((SplitTorus.pointsMulEquiv p (ULift.up j))⁻¹ : Kˣ) : K) =
      MonoidAlgebra.single (adjointRootCharacter i j) 1 := by
  dsimp only
  let p := toConv (AlgHom.id k
    (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))))
  have hi : (SplitTorus.pointsMulEquiv p (ULift.up i) :
      MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) =
      MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1)) 1 := by
    rw [SplitTorus.pointsMulEquiv_apply_coe]
    rfl
  have hj : (((SplitTorus.pointsMulEquiv p (ULift.up j))⁻¹ :
      (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))ˣ) :
      MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) =
      MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.single (ULift.up j) 1))⁻¹ 1 := by
    change (↑((SplitTorus.pointsMulEquiv
      (toConv (AlgHom.id k
        (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))))
      (ULift.up j))⁻¹ :
        (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))ˣ) :
          MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) =
      (MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.single (ULift.up j) (1 : ℤ)))⁻¹ (1 : k) :
          MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))
    rw [SplitTorus.pointsMulEquiv_eq_freeAbelianCharEquiv,
      freeAbelianCharEquiv_apply]
    exact DiagonalizableGroup.charOfPoint_apply_inv_coe _ _
  change
    (SplitTorus.pointsMulEquiv p (ULift.up i) :
        MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) *
      (↑((SplitTorus.pointsMulEquiv p (ULift.up j))⁻¹ :
        (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))ˣ) :
          MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) = _
  rw [hi, hj, MonoidAlgebra.single_mul_single, one_mul]
  congr 1
  apply Multiplicative.toAdd.injective
  simp [adjointRootCharacter, sub_eq_add_neg]

/-- The cotangent-dual tangent vector of `GL_n` corresponding to the matrix unit `E_ij`. -/
def matrixUnitTangent (i j : Fin n) :
    Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)) :=
  cotangentDualMatrixEquiv.symm (Matrix.single i j 1)

/-- The matrix of `matrixUnitTangent i j` is the matrix unit `E_ij`. -/
@[simp]
theorem cotangentDualMatrixEquiv_matrixUnitTangent (i j : Fin n) :
    cotangentDualMatrixEquiv (matrixUnitTangent (k := k) i j) = Matrix.single i j 1 := by
  exact LinearEquiv.apply_symm_apply _ _

/-- The matrix unit `E_ij` belongs to the adjoint weight space of the diagonal-torus character
`e_i - e_j`.  This is the formal root-space version of diagonal conjugation scaling the
`(i, j)` matrix entry by `t_i t_j⁻¹`. -/
theorem matrixUnitTangent_mem_adjointWeightSpace (i j : Fin n) :
    matrixUnitTangent (k := k) i j ∈
      Derivation.adjointWeightSpace
        (diagonalTorusCoordinateMap (R := k) (N := n)).hom
        (adjointRootCharacter i j) := by
  rw [Derivation.mem_adjointWeightSpace_iff_universalPointAction]
  let M := Multiplicative (ULift.{u} (Fin n) →₀ ℤ)
  let K := MonoidAlgebra k M
  let p : WithConv (K →ₐ[k] K) := toConv (AlgHom.id k K)
  have hmap :
      toConv ((diagonalTorusCoordinateMap (R := k) (N := n)).hom :
        coordinateHopfAlgebra k n →ₐ[k] K) = diagonalTorusPoints p := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro h
    have hvalue := congrArg (fun q ↦ q.ofConv h)
      (mapPointsFunctor_diagonalTorusCoordinateMap_app
        (R := k) (N := n) (CommAlgCat.of k K) p)
    rw [CommHopfAlgCat.mapPointsFunctor_app_apply_apply] at hvalue
    rw [AlgHom.id_apply] at hvalue
    exact hvalue
  apply (Derivation.tangentScalarExtensionEquiv
    (R := k) (A := coordinateHopfAlgebra k n) (B := K)).injective
  rw [Derivation.tangentScalarExtensionEquiv_adjointAction
    (CommAlgCat.of k K)
    (toConv ((diagonalTorusCoordinateMap (R := k) (N := n)).hom :
      coordinateHopfAlgebra k n →ₐ[k] K))]
  have hpoint :
      Derivation.pointInCounitAlgebra (CommAlgCat.of k K)
          (toConv ((diagonalTorusCoordinateMap (R := k) (N := n)).hom :
            coordinateHopfAlgebra k n →ₐ[k] K)) =
        (Bialgebra.CounitAlgebra.pointsMulEquiv k
          (coordinateHopfAlgebra k n) K).symm (diagonalTorusPoints p) := by
    rw [← hmap]
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro h
    rw [Bialgebra.CounitAlgebra.pointsMulEquiv_symm_apply]
    exact (Derivation.pointInCounitAlgebra_apply
        (R := k) (H := coordinateHopfAlgebra k n) (CommAlgCat.of k K)
        (toConv ((diagonalTorusCoordinateMap (R := k) (N := n)).hom :
          coordinateHopfAlgebra k n →ₐ[k] K)) h).trans
      (Bialgebra.CounitAlgebra.algEquivSelf_symm_apply
        (R := k) (A := coordinateHopfAlgebra k n) (B := K) _).symm
  rw [hpoint]
  apply (tangentLinearEquivMatrix n).injective
  rw [tangentLinearEquivMatrix_apply, tangentLinearEquivMatrix_apply]
  apply Matrix.ext
  intro a b
  rw [tangentMatrix_adDerivation_apply_diagonalTorusPoints,
    tangentMatrix_tangentScalarExtensionEquiv_one_tmul,
    tangentMatrix_tangentScalarExtensionEquiv_tmul,
    cotangentDualMatrixEquiv_matrixUnitTangent]
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hai : a = i
  · subst a
    by_cases hbj : b = j
    · subst b
      rw [Matrix.single_apply_same, map_one, mul_one, mul_one]
      simpa only [p] using
        universalPoint_coordinate_mul_inv (k := k) i j
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
theorem adjointRootCharacter_mem_nontrivialAdjointWeights {i j : Fin n} (hij : i ≠ j) :
    adjointRootCharacter i j ∈
      Derivation.nontrivialAdjointWeights
        (diagonalTorusCoordinateMap (R := k) (N := n)).hom := by
  rw [Derivation.mem_nontrivialAdjointWeights]
  refine ⟨adjointRootCharacter_ne_one hij, ?_⟩
  intro hspace
  have hx := matrixUnitTangent_mem_adjointWeightSpace (k := k) i j
  rw [hspace] at hx
  apply matrixUnitTangent_ne_zero (k := k) i j
  simpa using hx

end

end TauCeti.GeneralLinear
