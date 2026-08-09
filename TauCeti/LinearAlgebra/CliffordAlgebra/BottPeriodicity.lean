/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti Project
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm
public import Mathlib.RingTheory.MatrixAlgebra

/-!
# Hyperbolic Bott periodicity for real Clifford algebras

This file proves the `(1, 1)` periodicity step for Clifford algebras. Adding one positive and one
negative generator is equivalent to tensoring with two-by-two real matrices.

## Main results

* `TauCeti.CliffordAlgebra.hyperbolicEquivTensor`: adjoining a hyperbolic plane to an arbitrary
  real quadratic module tensors its Clifford algebra with `M₂(ℝ)`;
* `TauCeti.realCliffordBottEquiv`: the corresponding equivalence for the standard signature forms.
-/

public section

open Module QuadraticMap
open scoped Matrix TensorProduct

namespace TauCeti.CliffordAlgebra

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable (Q : QuadraticForm ℝ M)

private def hyperbolicMatrixGenerator :
    M × (Fin (1 + 1) → ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) (_root_.CliffordAlgebra Q) :=
  { toFun := fun x =>
      !![algebraMap ℝ _ (x.2 0), _root_.CliffordAlgebra.ι Q x.1 + algebraMap ℝ _ (x.2 1);
         _root_.CliffordAlgebra.ι Q x.1 - algebraMap ℝ _ (x.2 1), -algebraMap ℝ _ (x.2 0)]
    map_add' := by
      intro x y
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> abel
    map_smul' := by
      intro r x
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Algebra.smul_def, mul_add, mul_sub] }

private theorem hyperbolicMatrixGenerator_sq (x : M × (Fin (1 + 1) → ℝ)) :
    hyperbolicMatrixGenerator Q x * hyperbolicMatrixGenerator Q x =
      algebraMap ℝ _ ((Q.prod (TauCeti.realCliffordForm 1 1)) x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicMatrixGenerator, Matrix.mul_apply, Fin.sum_univ_two,
      TauCeti.realCliffordForm_one_one_apply, Algebra.algebraMap_eq_smul_one,
      mul_add, add_mul, mul_sub, sub_mul] <;>
    module

private def hyperbolicToMatrix :
    _root_.CliffordAlgebra (Q.prod (TauCeti.realCliffordForm 1 1)) →ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) (_root_.CliffordAlgebra Q) :=
  _root_.CliffordAlgebra.lift _ ⟨hyperbolicMatrixGenerator Q, hyperbolicMatrixGenerator_sq Q⟩

private theorem hyperbolicToMatrix_ι (x : M × (Fin (1 + 1) → ℝ)) :
    hyperbolicToMatrix Q (_root_.CliffordAlgebra.ι _ x) =
      !![algebraMap ℝ _ (x.2 0), _root_.CliffordAlgebra.ι Q x.1 + algebraMap ℝ _ (x.2 1);
         _root_.CliffordAlgebra.ι Q x.1 - algebraMap ℝ _ (x.2 1), -algebraMap ℝ _ (x.2 0)] := by
  exact _root_.CliffordAlgebra.lift_ι_apply _ _ x

private def hyperbolicToTensor :
    _root_.CliffordAlgebra (Q.prod (TauCeti.realCliffordForm 1 1)) →ₐ[ℝ]
      (_root_.CliffordAlgebra Q ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℝ) :=
  (matrixEquivTensor (Fin 2) ℝ (_root_.CliffordAlgebra Q)).toAlgHom.comp
    (hyperbolicToMatrix Q)

private theorem hyperbolicToTensor_ι_base (m : M) :
    hyperbolicToTensor Q (_root_.CliffordAlgebra.ι _ (m, 0)) =
      _root_.CliffordAlgebra.ι Q m ⊗ₜ[ℝ] !![0, 1; 1, 0] := by
  apply (matrixEquivTensor (Fin 2) ℝ (_root_.CliffordAlgebra Q)).symm.injective
  rw [hyperbolicToTensor, AlgHom.comp_apply, hyperbolicToMatrix_ι]
  simp only [Pi.zero_apply, map_zero, add_zero, sub_zero, neg_zero, AlgEquiv.coe_toAlgHom,
    matrixEquivTensor_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, map_sum,
    matrixEquivTensor_apply_symm, Matrix.map_single, map_one, Matrix.smul_single, smul_eq_mul,
    mul_one]
  ext i j
  rw [Matrix.sum_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]

private theorem hyperbolicToTensor_ι_hyperbolic (v : Fin (1 + 1) → ℝ) :
    hyperbolicToTensor Q (_root_.CliffordAlgebra.ι _ (0, v)) =
      1 ⊗ₜ[ℝ] !![v 0, v 1; -v 1, -v 0] := by
  apply (matrixEquivTensor (Fin 2) ℝ (_root_.CliffordAlgebra Q)).symm.injective
  rw [hyperbolicToTensor, AlgHom.comp_apply, hyperbolicToMatrix_ι]
  simp only [Fin.isValue, map_zero, zero_add, zero_sub, AlgEquiv.coe_toAlgHom,
    matrixEquivTensor_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, map_sum,
    matrixEquivTensor_apply_symm, Matrix.map_single, map_one, Matrix.smul_single, smul_eq_mul,
    mul_one, one_smul]
  ext i j
  rw [Matrix.sum_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]

private def hyperbolicRightInclusion :
    _root_.CliffordAlgebra (TauCeti.realCliffordForm 1 1) →ₐ[ℝ]
      _root_.CliffordAlgebra (Q.prod (TauCeti.realCliffordForm 1 1)) :=
  _root_.CliffordAlgebra.map
    (QuadraticMap.Isometry.inr Q (TauCeti.realCliffordForm 1 1))

private theorem hyperbolicToMatrix_comp_rightInclusion :
    (hyperbolicToMatrix Q).comp (hyperbolicRightInclusion Q) =
      (Algebra.ofId ℝ (_root_.CliffordAlgebra Q)).mapMatrix.comp
        TauCeti.realCliffordOneOneEquivMatrix.toAlgHom := by
  apply _root_.CliffordAlgebra.hom_ext
  ext v i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicRightInclusion, hyperbolicToMatrix_ι,
      TauCeti.realCliffordOneOneEquivMatrix_ι]

private theorem hyperbolicToMatrix_scalar_unit (i j : Fin 2) :
    ∃ x, hyperbolicToMatrix Q x = Matrix.single i j 1 := by
  refine ⟨hyperbolicRightInclusion Q
    ((TauCeti.realCliffordOneOneEquivMatrix).symm (Matrix.single i j 1)), ?_⟩
  rw [← AlgHom.comp_apply, hyperbolicToMatrix_comp_rightInclusion, AlgHom.comp_apply]
  simp

private theorem hyperbolicToMatrix_scalar_surjective
    (x : _root_.CliffordAlgebra Q) :
    ∃ y, hyperbolicToMatrix Q y = Matrix.scalar (Fin 2) x := by
  induction x using _root_.CliffordAlgebra.induction with
  | algebraMap r =>
      refine ⟨algebraMap ℝ _ r, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.scalar_apply, Matrix.algebraMap_matrix_apply]
  | ι m =>
      let e₀ : Fin (1 + 1) → ℝ := Pi.single 0 1
      let e₁ : Fin (1 + 1) → ℝ := Pi.single 1 1
      let a := _root_.CliffordAlgebra.ι (Q.prod (TauCeti.realCliffordForm 1 1)) (0, e₀)
      let b := _root_.CliffordAlgebra.ι (Q.prod (TauCeti.realCliffordForm 1 1)) (0, e₁)
      refine ⟨_root_.CliffordAlgebra.ι _ (m, 0) * (a * b), ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [a, b, e₀, e₁, hyperbolicToMatrix_ι, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.scalar_apply, Algebra.algebraMap_eq_smul_one]
  | mul x y hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      refine ⟨x' * y', ?_⟩
      rw [map_mul, hx', hy']
      exact (map_mul (Matrix.scalar (Fin 2)) x y).symm
  | add x y hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      refine ⟨x' + y', ?_⟩
      rw [map_add, hx', hy']
      exact (map_add (Matrix.scalar (Fin 2)) x y).symm

private theorem hyperbolicToMatrix_single_surjective
    (i j : Fin 2) (x : _root_.CliffordAlgebra Q) :
    ∃ y, hyperbolicToMatrix Q y = Matrix.single i j x := by
  obtain ⟨sx, hsx⟩ := hyperbolicToMatrix_scalar_surjective Q x
  obtain ⟨eij, heij⟩ := hyperbolicToMatrix_scalar_unit Q i j
  refine ⟨sx * eij, ?_⟩
  rw [map_mul, hsx, heij]
  ext k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Matrix.scalar_apply, Matrix.mul_apply, Matrix.single_apply]

private theorem hyperbolicToMatrix_surjective :
    Function.Surjective (hyperbolicToMatrix Q) := by
  intro x
  induction x using Matrix.induction_on' with
  | h_zero => exact ⟨0, map_zero _⟩
  | h_add x y hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      exact ⟨x' + y', by rw [map_add, hx', hy']⟩
  | h_std_basis i j x => exact hyperbolicToMatrix_single_surjective Q i j x

private abbrev HyperbolicAlgebra :=
  _root_.CliffordAlgebra (Q.prod (TauCeti.realCliffordForm 1 1))

private def hyperbolicE₀ : HyperbolicAlgebra Q :=
  _root_.CliffordAlgebra.ι _ (0, Pi.single 0 1)

private def hyperbolicE₁ : HyperbolicAlgebra Q :=
  _root_.CliffordAlgebra.ι _ (0, Pi.single 1 1)

private def hyperbolicVolume : HyperbolicAlgebra Q := hyperbolicE₀ Q * hyperbolicE₁ Q

private theorem hyperbolicVolume_sq : hyperbolicVolume Q * hyperbolicVolume Q = 1 := by
  let a : HyperbolicAlgebra Q := hyperbolicE₀ Q
  let b : HyperbolicAlgebra Q := hyperbolicE₁ Q
  have h : (Q.prod (TauCeti.realCliffordForm 1 1)).IsOrtho
      (0, Pi.single 1 1) (0, Pi.single 0 1) := by
    simp [QuadraticMap.isOrtho_def, TauCeti.realCliffordForm_one_one_apply]
  have hba : b * a = -(a * b) :=
    _root_.CliffordAlgebra.ι_mul_ι_comm_of_isOrtho h
  have haa : a * a = 1 := by
    dsimp [a, hyperbolicE₀]
    rw [_root_.CliffordAlgebra.ι_sq_scalar]
    simp [TauCeti.realCliffordForm_one_one_apply]
  have hbb : b * b = -1 := by
    dsimp [b, hyperbolicE₁]
    rw [_root_.CliffordAlgebra.ι_sq_scalar]
    simp [TauCeti.realCliffordForm_one_one_apply]
  change a * b * (a * b) = 1
  calc
    a * b * (a * b) = a * (b * a) * b := by simp [mul_assoc]
    _ = a * (-(a * b)) * b := by rw [hba]
    _ = -(a * a) * (b * b) := by simp [mul_assoc]
    _ = 1 := by rw [haa, hbb]; simp

private theorem hyperbolicBase_comm_volume (m : M) :
    Commute (_root_.CliffordAlgebra.ι _ (m, 0)) (hyperbolicVolume Q) := by
  let i : HyperbolicAlgebra Q := _root_.CliffordAlgebra.ι _ (m, 0)
  let a : HyperbolicAlgebra Q := hyperbolicE₀ Q
  let b : HyperbolicAlgebra Q := hyperbolicE₁ Q
  have h0 : (Q.prod (TauCeti.realCliffordForm 1 1)).IsOrtho
      (m, 0) (0, Pi.single 0 1) := QuadraticMap.IsOrtho.inl_inr _ _
  have h1 : (Q.prod (TauCeti.realCliffordForm 1 1)).IsOrtho
      (m, 0) (0, Pi.single 1 1) := QuadraticMap.IsOrtho.inl_inr _ _
  have hcomm0 : i * a = -(a * i) :=
    _root_.CliffordAlgebra.ι_mul_ι_comm_of_isOrtho h0
  have hcomm1 : i * b = -(b * i) :=
    _root_.CliffordAlgebra.ι_mul_ι_comm_of_isOrtho h1
  rw [Commute]
  change i * (a * b) = a * b * i
  calc
    i * (a * b) = (i * a) * b := by simp [mul_assoc]
    _ = (-(a * i)) * b := by rw [hcomm0]
    _ = -a * (i * b) := by simp [mul_assoc]
    _ = -a * (-(b * i)) := by rw [hcomm1]
    _ = a * b * i := by simp [mul_assoc]

private def hyperbolicBaseGenerator : M →ₗ[ℝ] HyperbolicAlgebra Q :=
  (LinearMap.mulRight ℝ (hyperbolicVolume Q)).comp
    ((_root_.CliffordAlgebra.ι _).comp
      (LinearMap.inl ℝ M (Fin (1 + 1) → ℝ)))

private theorem hyperbolicBaseGenerator_sq (m : M) :
    hyperbolicBaseGenerator Q m * hyperbolicBaseGenerator Q m = algebraMap ℝ _ (Q m) := by
  change (_root_.CliffordAlgebra.ι _ (m, 0) * hyperbolicVolume Q) *
    (_root_.CliffordAlgebra.ι _ (m, 0) * hyperbolicVolume Q) = _
  rw [← pow_two, (hyperbolicBase_comm_volume Q m).mul_pow, pow_two, pow_two,
    _root_.CliffordAlgebra.ι_sq_scalar, hyperbolicVolume_sq]
  simp [QuadraticMap.prod_apply]

private def hyperbolicBaseInclusion :
    _root_.CliffordAlgebra Q →ₐ[ℝ] HyperbolicAlgebra Q :=
  _root_.CliffordAlgebra.lift Q ⟨hyperbolicBaseGenerator Q, hyperbolicBaseGenerator_sq Q⟩

private noncomputable def hyperbolicMatrixInclusion :
    Matrix (Fin 2) (Fin 2) ℝ →ₐ[ℝ] HyperbolicAlgebra Q :=
  (hyperbolicRightInclusion Q).comp TauCeti.realCliffordOneOneEquivMatrix.symm.toAlgHom

private theorem hyperbolicVolume_anticomm_rightGenerator (v : Fin (1 + 1) → ℝ) :
    hyperbolicVolume Q * _root_.CliffordAlgebra.ι _ (0, v) =
      -(_root_.CliffordAlgebra.ι _ (0, v) * hyperbolicVolume Q) := by
  let h0 := _root_.CliffordAlgebra.ι (TauCeti.realCliffordForm 1 1) (Pi.single 0 1)
  let h1 := _root_.CliffordAlgebra.ι (TauCeti.realCliffordForm 1 1) (Pi.single 1 1)
  have hh : h0 * h1 * _root_.CliffordAlgebra.ι _ v =
      -(_root_.CliffordAlgebra.ι _ v * (h0 * h1)) := by
    apply TauCeti.realCliffordOneOneEquivMatrix.injective
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h0, h1, TauCeti.realCliffordOneOneEquivMatrix_ι,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hm := congrArg (hyperbolicRightInclusion Q) hh
  dsimp [h0, h1] at hm
  simpa [hyperbolicVolume, hyperbolicE₀, hyperbolicE₁,
    hyperbolicRightInclusion, map_mul] using hm

private theorem hyperbolicBaseInclusion_comm_rightInclusion
    (x : _root_.CliffordAlgebra Q)
    (y : _root_.CliffordAlgebra (TauCeti.realCliffordForm 1 1)) :
    Commute (hyperbolicBaseInclusion Q x) (hyperbolicRightInclusion Q y) := by
  have hgen : ∀ (m : M) (z : _root_.CliffordAlgebra (TauCeti.realCliffordForm 1 1)),
      Commute (hyperbolicBaseInclusion Q (_root_.CliffordAlgebra.ι Q m))
        (hyperbolicRightInclusion Q z) := by
    intro m z
    induction z using _root_.CliffordAlgebra.induction with
    | algebraMap r =>
        rw [(hyperbolicRightInclusion Q).commutes]
        exact (Algebra.commutes r _).symm
    | ι v =>
        rw [hyperbolicBaseInclusion, _root_.CliffordAlgebra.lift_ι_apply]
        simp only [hyperbolicBaseGenerator, LinearMap.comp_apply, LinearMap.mulRight_apply,
          LinearMap.inl_apply, hyperbolicRightInclusion,
          _root_.CliffordAlgebra.map_apply_ι, QuadraticMap.Isometry.inr_apply]
        rw [Commute]
        have hic := _root_.CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
          (QuadraticMap.IsOrtho.inl_inr (Q₁ := Q)
            (Q₂ := TauCeti.realCliffordForm 1 1) m v)
        have hoc := hyperbolicVolume_anticomm_rightGenerator Q v
        calc
          _ = _root_.CliffordAlgebra.ι _ (m, 0) *
              (hyperbolicVolume Q * _root_.CliffordAlgebra.ι _ (0, v)) := by simp [mul_assoc]
          _ = _root_.CliffordAlgebra.ι _ (m, 0) *
              (-(_root_.CliffordAlgebra.ι _ (0, v) * hyperbolicVolume Q)) := by rw [hoc]
          _ = -(_root_.CliffordAlgebra.ι _ (m, 0) *
              _root_.CliffordAlgebra.ι _ (0, v)) * hyperbolicVolume Q := by simp [mul_assoc]
          _ = -(-(_root_.CliffordAlgebra.ι _ (0, v) *
              _root_.CliffordAlgebra.ι _ (m, 0))) * hyperbolicVolume Q := by rw [hic]
          _ = _ := by simp [mul_assoc]
    | mul a b ha hb => simpa only [map_mul] using ha.mul_right hb
    | add a b ha hb => simpa only [map_add] using ha.add_right hb
  induction x using _root_.CliffordAlgebra.induction with
  | algebraMap r =>
      rw [(hyperbolicBaseInclusion Q).commutes]
      exact Algebra.commutes r _
  | ι m => exact hgen m y
  | mul a b ha hb => simpa only [map_mul] using ha.mul_left hb
  | add a b ha hb => simpa only [map_add] using ha.add_left hb

private noncomputable def tensorToHyperbolic :
    (_root_.CliffordAlgebra Q ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℝ) →ₐ[ℝ]
      HyperbolicAlgebra Q :=
  Algebra.TensorProduct.lift (hyperbolicBaseInclusion Q) (hyperbolicMatrixInclusion Q) (by
    intro x y
    change Commute (hyperbolicBaseInclusion Q x)
      (hyperbolicRightInclusion Q (TauCeti.realCliffordOneOneEquivMatrix.symm.toAlgHom y))
    exact hyperbolicBaseInclusion_comm_rightInclusion Q x
      (TauCeti.realCliffordOneOneEquivMatrix.symm.toAlgHom y))

private theorem hyperbolicMatrixInclusion_sigmaX :
    hyperbolicMatrixInclusion Q !![(0 : ℝ), 1; 1, 0] = hyperbolicVolume Q := by
  let h0 := _root_.CliffordAlgebra.ι (TauCeti.realCliffordForm 1 1) (Pi.single 0 1)
  let h1 := _root_.CliffordAlgebra.ι (TauCeti.realCliffordForm 1 1) (Pi.single 1 1)
  have he : TauCeti.realCliffordOneOneEquivMatrix (h0 * h1) = !![(0 : ℝ), 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h0, h1, TauCeti.realCliffordOneOneEquivMatrix_ι,
        Matrix.mul_apply, Fin.sum_univ_two]
  rw [hyperbolicMatrixInclusion, AlgHom.comp_apply, ← he]
  change hyperbolicRightInclusion Q
    ((TauCeti.realCliffordOneOneEquivMatrix.symm.toAlgHom.comp
      TauCeti.realCliffordOneOneEquivMatrix.toAlgHom) (h0 * h1)) = _
  rw [AlgEquiv.symm_comp, AlgHom.id_apply]
  dsimp [h0, h1, hyperbolicVolume, hyperbolicE₀, hyperbolicE₁]
  rw [hyperbolicRightInclusion, map_mul, _root_.CliffordAlgebra.map_apply_ι,
    _root_.CliffordAlgebra.map_apply_ι]
  rfl

private theorem hyperbolicMatrixInclusion_hyperbolic (v : Fin (1 + 1) → ℝ) :
    hyperbolicMatrixInclusion Q !![v 0, v 1; -v 1, -v 0] =
      _root_.CliffordAlgebra.ι _ (0, v) := by
  rw [hyperbolicMatrixInclusion, AlgHom.comp_apply,
    ← TauCeti.realCliffordOneOneEquivMatrix_ι v]
  change hyperbolicRightInclusion Q
    ((TauCeti.realCliffordOneOneEquivMatrix.symm.toAlgHom.comp
      TauCeti.realCliffordOneOneEquivMatrix.toAlgHom)
        (_root_.CliffordAlgebra.ι _ v)) = _
  rw [AlgEquiv.symm_comp, AlgHom.id_apply]
  simp [hyperbolicRightInclusion]

private theorem tensorToHyperbolic_ι_base (m : M) :
    tensorToHyperbolic Q
        (_root_.CliffordAlgebra.ι Q m ⊗ₜ[ℝ] !![(0 : ℝ), 1; 1, 0]) =
      _root_.CliffordAlgebra.ι _ (m, 0) := by
  rw [tensorToHyperbolic, Algebra.TensorProduct.lift_tmul,
    hyperbolicBaseInclusion, _root_.CliffordAlgebra.lift_ι_apply,
    hyperbolicMatrixInclusion_sigmaX]
  change (_root_.CliffordAlgebra.ι _ (m, 0) * hyperbolicVolume Q) *
    hyperbolicVolume Q = _
  rw [mul_assoc, hyperbolicVolume_sq]
  simp

private theorem tensorToHyperbolic_ι_hyperbolic (v : Fin (1 + 1) → ℝ) :
    tensorToHyperbolic Q (1 ⊗ₜ[ℝ] !![v 0, v 1; -v 1, -v 0]) =
      _root_.CliffordAlgebra.ι _ (0, v) := by
  rw [tensorToHyperbolic, Algebra.TensorProduct.lift_tmul, map_one, one_mul,
    hyperbolicMatrixInclusion_hyperbolic]

private theorem tensorToHyperbolic_comp_hyperbolicToTensor :
    (tensorToHyperbolic Q).comp (hyperbolicToTensor Q) = AlgHom.id ℝ _ := by
  apply _root_.CliffordAlgebra.hom_ext
  apply LinearMap.ext
  rintro ⟨m, v⟩
  change tensorToHyperbolic Q
      (hyperbolicToTensor Q (_root_.CliffordAlgebra.ι _ (m, v))) =
    _root_.CliffordAlgebra.ι _ (m, v)
  rw [show (m, v) = (m, 0) + (0, v) by ext <;> simp, map_add, map_add,
    hyperbolicToTensor_ι_base, hyperbolicToTensor_ι_hyperbolic]
  rw [map_add, tensorToHyperbolic_ι_base, tensorToHyperbolic_ι_hyperbolic]

private theorem hyperbolicToTensor_surjective :
    Function.Surjective (hyperbolicToTensor Q) :=
  (matrixEquivTensor (Fin 2) ℝ (_root_.CliffordAlgebra Q)).surjective.comp
    (hyperbolicToMatrix_surjective Q)

private theorem hyperbolicToTensor_comp_tensorToHyperbolic :
    (hyperbolicToTensor Q).comp (tensorToHyperbolic Q) = AlgHom.id ℝ _ := by
  apply DFunLike.ext _ _
  have hleft : Function.LeftInverse (tensorToHyperbolic Q) (hyperbolicToTensor Q) :=
    fun x ↦ DFunLike.congr_fun (tensorToHyperbolic_comp_hyperbolicToTensor Q) x
  exact hleft.rightInverse_of_surjective (hyperbolicToTensor_surjective Q)

/-- Adjoining a hyperbolic plane to a real quadratic module tensors its
Clifford algebra with two-by-two real matrices. -/
noncomputable def hyperbolicEquivTensor :
    _root_.CliffordAlgebra (Q.prod (TauCeti.realCliffordForm 1 1)) ≃ₐ[ℝ]
      (_root_.CliffordAlgebra Q ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℝ) :=
  AlgEquiv.ofAlgHom (hyperbolicToTensor Q) (tensorToHyperbolic Q)
    (hyperbolicToTensor_comp_tensorToHyperbolic Q)
    (tensorToHyperbolic_comp_hyperbolicToTensor Q)

private theorem hyperbolicEquivTensor_toAlgHom :
    (hyperbolicEquivTensor Q).toAlgHom = hyperbolicToTensor Q := by
  exact AlgEquiv.toAlgHom_ofAlgHom _ _ _ _

/-- The image of a generator under `hyperbolicEquivTensor`, split into its original-module and
hyperbolic-plane components. -/
@[simp]
theorem hyperbolicEquivTensor_ι
    (x : M × (Fin (1 + 1) → ℝ)) :
    hyperbolicEquivTensor Q (_root_.CliffordAlgebra.ι _ x) =
      _root_.CliffordAlgebra.ι Q x.1 ⊗ₜ[ℝ] !![0, 1; 1, 0] +
        1 ⊗ₜ[ℝ] !![x.2 0, x.2 1; -x.2 1, -x.2 0] := by
  rw [show hyperbolicEquivTensor Q _ =
    (hyperbolicEquivTensor Q).toAlgHom _ from rfl, hyperbolicEquivTensor_toAlgHom]
  conv_lhs =>
    rw [show x = (x.1, 0) + (0, x.2) by ext <;> simp]
  rw [map_add, map_add, hyperbolicToTensor_ι_base, hyperbolicToTensor_ι_hyperbolic]

/-- The image of an original-module generator under `hyperbolicEquivTensor`. -/
@[simp 1100]
theorem hyperbolicEquivTensor_ι_base (m : M) :
    hyperbolicEquivTensor Q (_root_.CliffordAlgebra.ι _ (m, 0)) =
      _root_.CliffordAlgebra.ι Q m ⊗ₜ[ℝ] !![0, 1; 1, 0] := by
  rw [show hyperbolicEquivTensor Q _ =
    (hyperbolicEquivTensor Q).toAlgHom _ from rfl, hyperbolicEquivTensor_toAlgHom]
  exact hyperbolicToTensor_ι_base Q m

/-- The inverse of `hyperbolicEquivTensor` on the tensor representing an original generator. -/
@[simp]
theorem hyperbolicEquivTensor_symm_ι_base (m : M) :
    (hyperbolicEquivTensor Q).symm
        (_root_.CliffordAlgebra.ι Q m ⊗ₜ[ℝ] !![0, 1; 1, 0]) =
      _root_.CliffordAlgebra.ι _ (m, 0) := by
  apply (hyperbolicEquivTensor Q).injective
  rw [AlgEquiv.apply_symm_apply, hyperbolicEquivTensor_ι_base]

/-- The inverse of `hyperbolicEquivTensor` on a tensor representing a hyperbolic generator. -/
@[simp]
theorem hyperbolicEquivTensor_symm_ι_hyperbolic
    (v : Fin (1 + 1) → ℝ) :
    (hyperbolicEquivTensor Q).symm (1 ⊗ₜ[ℝ] !![v 0, v 1; -v 1, -v 0]) =
      _root_.CliffordAlgebra.ι _ (0, v) := by
  apply (hyperbolicEquivTensor Q).injective
  rw [AlgEquiv.apply_symm_apply, hyperbolicEquivTensor_ι]
  simp

end TauCeti.CliffordAlgebra

namespace TauCeti

private def splitLastEquiv (n : ℕ) : Fin (n + 1) ≃ Fin n ⊕ Fin 1 :=
  (finSuccEquivLast).trans <|
    (Equiv.optionEquivSumPUnit.{0, 0} _).trans <|
      Equiv.sumCongr (Equiv.refl _) (Equiv.equivPUnit.{1, 1} (Fin 1)).symm

private def realBottIndexEquiv (p q : ℕ) :
    Fin ((p + 1) + (q + 1)) ≃ Fin (p + q) ⊕ Fin 2 :=
  finSumFinEquiv.symm |>.trans
    (Equiv.sumCongr (splitLastEquiv p) (splitLastEquiv q)) |>.trans
    (Equiv.sumSumSumComm (Fin p) (Fin 1) (Fin q) (Fin 1)) |>.trans
    (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)

private def realBottSplitLinearEquiv (p q : ℕ) :
    (Fin ((p + 1) + (q + 1)) → ℝ) ≃ₗ[ℝ]
      (Fin (p + q) → ℝ) × (Fin 2 → ℝ) :=
  (LinearEquiv.piCongrLeft' ℝ (fun _ : Fin ((p + 1) + (q + 1)) ↦ ℝ)
      (realBottIndexEquiv p q)).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ)

private theorem realBottIndexEquiv_symm_inl_pos (p q : ℕ) (i : Fin p) :
    (realBottIndexEquiv p q).symm (Sum.inl (finSumFinEquiv (Sum.inl i))) =
      finSumFinEquiv (Sum.inl i.castSucc) := by
  simp [realBottIndexEquiv, splitLastEquiv]

private theorem realBottIndexEquiv_symm_inl_neg (p q : ℕ) (i : Fin q) :
    (realBottIndexEquiv p q).symm (Sum.inl (finSumFinEquiv (Sum.inr i))) =
      finSumFinEquiv (Sum.inr i.castSucc) := by
  simp [realBottIndexEquiv, splitLastEquiv]

private theorem realBottIndexEquiv_symm_inr_zero (p q : ℕ) :
    (realBottIndexEquiv p q).symm (Sum.inr (0 : Fin 2)) =
      finSumFinEquiv (Sum.inl (Fin.last p)) := by
  apply Fin.ext
  -- After forgetting the dependent `Fin` bounds, both index constructions have value `p`.
  change p = p
  rfl

private theorem realBottIndexEquiv_symm_inr_one (p q : ℕ) :
    (realBottIndexEquiv p q).symm (Sum.inr (1 : Fin 2)) =
      finSumFinEquiv (Sum.inr (Fin.last q)) := by
  apply Fin.ext
  -- After forgetting the dependent `Fin` bounds, both index constructions have value `p + 1 + q`.
  change p + 1 + q = p + 1 + q
  rfl

private theorem realBottWeight_inl (p q : ℕ) (i : Fin (p + q)) :
    realCliffordWeight (p + 1) (q + 1)
        ((realBottIndexEquiv p q).symm (Sum.inl i)) =
      realCliffordWeight p q i := by
  rw [← finSumFinEquiv.apply_symm_apply i]
  rcases finSumFinEquiv.symm i with i | i
  · rw [realBottIndexEquiv_symm_inl_pos]
    have hs :
        (finSumFinEquiv (Sum.inl i.castSucc : Fin (p + 1) ⊕ Fin (q + 1)) : ℕ) < p + 1 := by
      simp
    have ht : (finSumFinEquiv (Sum.inl i : Fin p ⊕ Fin q) : ℕ) < p := by simp
    rw [realCliffordWeight_of_lt hs, realCliffordWeight_of_lt ht]
  · rw [realBottIndexEquiv_symm_inl_neg]
    have hs : p + 1 ≤
        (finSumFinEquiv (Sum.inr i.castSucc : Fin (p + 1) ⊕ Fin (q + 1)) : ℕ) := by
      simp
    have ht : p ≤ (finSumFinEquiv (Sum.inr i : Fin p ⊕ Fin q) : ℕ) := by simp
    rw [realCliffordWeight_of_le hs, realCliffordWeight_of_le ht]

private theorem realBottWeight_inr (p q : ℕ) (i : Fin 2) :
    realCliffordWeight (p + 1) (q + 1)
        ((realBottIndexEquiv p q).symm (Sum.inr i)) =
      realCliffordWeight 1 1 i := by
  fin_cases i
  · -- Expose the `Fin 2` coordinate so the corresponding index-conversion lemma rewrites.
    change realCliffordWeight (p + 1) (q + 1)
        ((realBottIndexEquiv p q).symm (Sum.inr (0 : Fin 2))) =
      realCliffordWeight 1 1 (0 : Fin 2)
    rw [realBottIndexEquiv_symm_inr_zero]
    rw [realCliffordWeight_of_lt (by simp), realCliffordWeight_of_lt (by norm_num)]
  · -- Expose the `Fin 2` coordinate so the corresponding index-conversion lemma rewrites.
    change realCliffordWeight (p + 1) (q + 1)
        ((realBottIndexEquiv p q).symm (Sum.inr (1 : Fin 2))) =
      realCliffordWeight 1 1 (1 : Fin 2)
    rw [realBottIndexEquiv_symm_inr_one]
    rw [realCliffordWeight_of_le (by simp), realCliffordWeight_of_le (by norm_num)]

/-- The coordinate isometry which separates the last positive and negative coordinates of the
signature form as a hyperbolic plane. -/
def realBottSplitIsometry (p q : ℕ) :
    (realCliffordForm (p + 1) (q + 1)).IsometryEquiv
      ((realCliffordForm p q).prod (realCliffordForm 1 1)) :=
  { realBottSplitLinearEquiv p q with
    map_app' := by
      intro x
      rw [QuadraticMap.prod_apply, realCliffordForm_apply, realCliffordForm_apply,
        realCliffordForm_apply]
      let y := realBottSplitLinearEquiv p q x
      calc
        (∑ i, realCliffordWeight p q i * (y.1 i * y.1 i)) +
            ∑ i, realCliffordWeight 1 1 i * (y.2 i * y.2 i) =
          ∑ s : Fin (p + q) ⊕ Fin 2, Sum.elim
            (fun i => realCliffordWeight p q i * (y.1 i * y.1 i))
            (fun i => realCliffordWeight 1 1 i * (y.2 i * y.2 i)) s :=
              (Fintype.sum_sum_type (Sum.elim
                (fun i => realCliffordWeight p q i * (y.1 i * y.1 i))
                (fun i => realCliffordWeight 1 1 i * (y.2 i * y.2 i)))).symm
        _ = ∑ i, realCliffordWeight (p + 1) (q + 1) i * (x i * x i) := by
          refine Fintype.sum_equiv (realBottIndexEquiv p q).symm _ _ ?_
          rintro (i | i)
          · simp [y, realBottSplitLinearEquiv, realBottWeight_inl]
          · simp [y, realBottSplitLinearEquiv, realBottWeight_inr] }

/-- The positive coordinates retained by `realBottSplitIsometry`. -/
@[simp]
theorem realBottSplitIsometry_fst_pos (p q : ℕ)
    (v : Fin ((p + 1) + (q + 1)) → ℝ) (i : Fin p) :
    (realBottSplitIsometry p q v).1 (Fin.castAdd q i) =
      v (Fin.castAdd (q + 1) i.castSucc) := by
  change (realBottSplitLinearEquiv p q v).1 _ = _
  simp [realBottSplitLinearEquiv, realBottIndexEquiv, splitLastEquiv]

/-- The negative coordinates retained by `realBottSplitIsometry`. -/
@[simp]
theorem realBottSplitIsometry_fst_neg (p q : ℕ)
    (v : Fin ((p + 1) + (q + 1)) → ℝ) (i : Fin q) :
    (realBottSplitIsometry p q v).1 (Fin.natAdd p i) =
      v (Fin.natAdd (p + 1) i.castSucc) := by
  change (realBottSplitLinearEquiv p q v).1 _ = _
  simp [realBottSplitLinearEquiv, realBottIndexEquiv, splitLastEquiv]

/-- The last positive coordinate extracted by `realBottSplitIsometry`. -/
@[simp]
theorem realBottSplitIsometry_snd_zero (p q : ℕ)
    (v : Fin ((p + 1) + (q + 1)) → ℝ) :
    (realBottSplitIsometry p q v).2 0 =
      v (Fin.castAdd (q + 1) (Fin.last p)) := by
  rfl

/-- The last negative coordinate extracted by `realBottSplitIsometry`. -/
@[simp]
theorem realBottSplitIsometry_snd_one (p q : ℕ)
    (v : Fin ((p + 1) + (q + 1)) → ℝ) :
    (realBottSplitIsometry p q v).2 1 =
      v (Fin.natAdd (p + 1) (Fin.last q)) := by
  rfl

/-- The hyperbolic Bott step for the standard real signature forms:
`Cliff(p + 1, q + 1) ≅ Cliff(p, q) ⊗ M₂(ℝ)`. -/
noncomputable def realCliffordBottEquiv (p q : ℕ) :
    _root_.CliffordAlgebra (realCliffordForm (p + 1) (q + 1)) ≃ₐ[ℝ]
      (_root_.CliffordAlgebra (realCliffordForm p q) ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℝ) :=
  (_root_.CliffordAlgebra.equivOfIsometry (realBottSplitIsometry p q)).trans
    (CliffordAlgebra.hyperbolicEquivTensor (realCliffordForm p q))

/-- `realCliffordBottEquiv` first separates the last positive and negative coordinates, then
applies the hyperbolic-plane equivalence. -/
@[simp]
theorem realCliffordBottEquiv_ι (p q : ℕ)
    (v : Fin ((p + 1) + (q + 1)) → ℝ) :
    realCliffordBottEquiv p q (_root_.CliffordAlgebra.ι _ v) =
      _root_.CliffordAlgebra.ι (realCliffordForm p q)
          (realBottSplitIsometry p q v).1 ⊗ₜ[ℝ] !![0, 1; 1, 0] +
        1 ⊗ₜ[ℝ]
          !![(realBottSplitIsometry p q v).2 0, (realBottSplitIsometry p q v).2 1;
             -(realBottSplitIsometry p q v).2 1, -(realBottSplitIsometry p q v).2 0] := by
  rw [realCliffordBottEquiv, AlgEquiv.trans_apply,
    _root_.CliffordAlgebra.equivOfIsometry_apply,
    _root_.CliffordAlgebra.map_apply_ι,
    CliffordAlgebra.hyperbolicEquivTensor_ι]
  rfl

end TauCeti
