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
  real quadratic module tensors its Clifford algebra with `M₂(ℝ)`.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 7;
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I.
-/

public section

open Module QuadraticMap
open scoped Matrix TensorProduct

namespace TauCeti.CliffordAlgebra

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable (Q : QuadraticForm ℝ M)

omit [Module ℝ M] in
private theorem hyperbolicGenerator_eq_components
    (x : M × (Fin (1 + 1) → ℝ)) : x = (x.1, 0) + (0, x.2) := by
  ext <;> simp

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
  -- Expose the local generator abbreviations so the anticommutation calculation is explicit.
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
  -- Expose the local generator abbreviations so the two anticommutation steps can be applied.
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
  rw [hyperbolicBaseGenerator, LinearMap.comp_apply, LinearMap.mulRight_apply,
    LinearMap.comp_apply, LinearMap.inl_apply]
  rw [← pow_two, (hyperbolicBase_comm_volume Q m).mul_pow, pow_two, pow_two,
    _root_.CliffordAlgebra.ι_sq_scalar, hyperbolicVolume_sq]
  simp [QuadraticMap.prod_apply]

private def hyperbolicBaseInclusion :
    _root_.CliffordAlgebra Q →ₐ[ℝ] HyperbolicAlgebra Q :=
  _root_.CliffordAlgebra.lift Q ⟨hyperbolicBaseGenerator Q, hyperbolicBaseGenerator_sq Q⟩

private theorem hyperbolicBaseInclusion_ι (m : M) :
    hyperbolicBaseInclusion Q (_root_.CliffordAlgebra.ι Q m) =
      _root_.CliffordAlgebra.ι _ (m, 0) * hyperbolicVolume Q := by
  rw [hyperbolicBaseInclusion, _root_.CliffordAlgebra.lift_ι_apply]
  simp [hyperbolicBaseGenerator]

private noncomputable def hyperbolicMatrixInclusion :
    Matrix (Fin 2) (Fin 2) ℝ →ₐ[ℝ] HyperbolicAlgebra Q :=
  (hyperbolicRightInclusion Q).comp TauCeti.realCliffordOneOneEquivMatrix.symm.toAlgHom

private theorem hyperbolicMatrixInclusion_apply
    (x : _root_.CliffordAlgebra (TauCeti.realCliffordForm 1 1)) :
    hyperbolicMatrixInclusion Q (TauCeti.realCliffordOneOneEquivMatrix x) =
      hyperbolicRightInclusion Q x := by
  simp [hyperbolicMatrixInclusion]

private theorem hyperbolicMatrixInclusion_comp_oneOneEquiv :
    (hyperbolicMatrixInclusion Q).comp
        TauCeti.realCliffordOneOneEquivMatrix.toAlgHom =
      hyperbolicRightInclusion Q := by
  apply AlgHom.ext
  exact hyperbolicMatrixInclusion_apply Q

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
    simpa only [hyperbolicMatrixInclusion, AlgHom.comp_apply] using
      hyperbolicBaseInclusion_comm_rightInclusion Q x
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
  rw [← he, hyperbolicMatrixInclusion_apply]
  dsimp [h0, h1, hyperbolicVolume, hyperbolicE₀, hyperbolicE₁]
  rw [hyperbolicRightInclusion, map_mul, _root_.CliffordAlgebra.map_apply_ι,
    _root_.CliffordAlgebra.map_apply_ι]
  rfl

private theorem hyperbolicMatrixInclusion_hyperbolic (v : Fin (1 + 1) → ℝ) :
    hyperbolicMatrixInclusion Q !![v 0, v 1; -v 1, -v 0] =
      _root_.CliffordAlgebra.ι _ (0, v) := by
  rw [← TauCeti.realCliffordOneOneEquivMatrix_ι v,
    hyperbolicMatrixInclusion_apply]
  simp [hyperbolicRightInclusion]

private theorem tensorToHyperbolic_ι_base (m : M) :
    tensorToHyperbolic Q
        (_root_.CliffordAlgebra.ι Q m ⊗ₜ[ℝ] !![(0 : ℝ), 1; 1, 0]) =
      _root_.CliffordAlgebra.ι _ (m, 0) := by
  rw [tensorToHyperbolic, Algebra.TensorProduct.lift_tmul,
    hyperbolicBaseInclusion_ι, hyperbolicMatrixInclusion_sigmaX]
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
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
    AlgHom.id_apply]
  rw [hyperbolicGenerator_eq_components (m, v), map_add, map_add,
    hyperbolicToTensor_ι_base, hyperbolicToTensor_ι_hyperbolic]
  rw [map_add, tensorToHyperbolic_ι_base, tensorToHyperbolic_ι_hyperbolic]

private theorem hyperbolicToTensor_volume :
    hyperbolicToTensor Q (hyperbolicVolume Q) =
      1 ⊗ₜ[ℝ] !![(0 : ℝ), 1; 1, 0] := by
  rw [hyperbolicVolume, map_mul]
  simp [hyperbolicE₀, hyperbolicE₁, hyperbolicToTensor_ι_hyperbolic]

private theorem hyperbolicToTensor_comp_baseInclusion :
    (hyperbolicToTensor Q).comp (hyperbolicBaseInclusion Q) =
      Algebra.TensorProduct.includeLeft := by
  apply _root_.CliffordAlgebra.hom_ext
  ext m
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [AlgHom.comp_apply, hyperbolicBaseInclusion_ι,
    map_mul, hyperbolicToTensor_ι_base, hyperbolicToTensor_volume]
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    Algebra.TensorProduct.includeLeft_apply]
  have hsigmaX_sq :
      (!![(0 : ℝ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) * !![0, 1; 1, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hsigmaX_sq]

private theorem hyperbolicToTensor_baseInclusion (x : _root_.CliffordAlgebra Q) :
    hyperbolicToTensor Q (hyperbolicBaseInclusion Q x) =
      (Algebra.TensorProduct.includeLeft :
        _root_.CliffordAlgebra Q →ₐ[ℝ]
          (_root_.CliffordAlgebra Q ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℝ)) x := by
  exact DFunLike.congr_fun (hyperbolicToTensor_comp_baseInclusion Q) x

private theorem hyperbolicToTensor_comp_matrixInclusion :
    (hyperbolicToTensor Q).comp (hyperbolicMatrixInclusion Q) =
      Algebra.TensorProduct.includeRight := by
  apply (AlgHom.cancel_right (R := ℝ)
    (f := TauCeti.realCliffordOneOneEquivMatrix.toAlgHom)
    TauCeti.realCliffordOneOneEquivMatrix.surjective).mp
  rw [AlgHom.comp_assoc, hyperbolicMatrixInclusion_comp_oneOneEquiv]
  apply _root_.CliffordAlgebra.hom_ext
  ext v
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [AlgHom.comp_apply, AlgHom.comp_apply, hyperbolicRightInclusion,
    _root_.CliffordAlgebra.map_apply_ι, QuadraticMap.Isometry.inr_apply,
    hyperbolicToTensor_ι_hyperbolic, Algebra.TensorProduct.includeRight_apply]
  congr 1
  exact (TauCeti.realCliffordOneOneEquivMatrix_ι _).symm

private theorem hyperbolicToTensor_matrixInclusion
    (x : Matrix (Fin 2) (Fin 2) ℝ) :
    hyperbolicToTensor Q (hyperbolicMatrixInclusion Q x) =
      Algebra.TensorProduct.includeRight x := by
  exact DFunLike.congr_fun (hyperbolicToTensor_comp_matrixInclusion Q) x

private theorem hyperbolicToTensor_comp_tensorToHyperbolic :
    (hyperbolicToTensor Q).comp (tensorToHyperbolic Q) = AlgHom.id ℝ _ := by
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.ext'
  intro x y
  simp only [AlgHom.toLinearMap_apply]
  rw [AlgHom.comp_apply, tensorToHyperbolic, Algebra.TensorProduct.lift_tmul, map_mul,
    hyperbolicToTensor_baseInclusion, hyperbolicToTensor_matrixInclusion]
  simp

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

private theorem hyperbolicEquivTensor_apply (x : HyperbolicAlgebra Q) :
    hyperbolicEquivTensor Q x = hyperbolicToTensor Q x := by
  exact DFunLike.congr_fun (hyperbolicEquivTensor_toAlgHom Q) x

/-- The image of a generator under `hyperbolicEquivTensor`, split into its original-module and
hyperbolic-plane components. -/
@[simp]
theorem hyperbolicEquivTensor_ι
    (x : M × (Fin (1 + 1) → ℝ)) :
    hyperbolicEquivTensor Q (_root_.CliffordAlgebra.ι _ x) =
      _root_.CliffordAlgebra.ι Q x.1 ⊗ₜ[ℝ] !![0, 1; 1, 0] +
        1 ⊗ₜ[ℝ] !![x.2 0, x.2 1; -x.2 1, -x.2 0] := by
  rw [hyperbolicEquivTensor_apply]
  conv_lhs =>
    rw [hyperbolicGenerator_eq_components x]
  rw [map_add, map_add, hyperbolicToTensor_ι_base, hyperbolicToTensor_ι_hyperbolic]

/-- The image of an original-module generator under `hyperbolicEquivTensor`. -/
@[simp 1100]
theorem hyperbolicEquivTensor_ι_base (m : M) :
    hyperbolicEquivTensor Q (_root_.CliffordAlgebra.ι _ (m, 0)) =
      _root_.CliffordAlgebra.ι Q m ⊗ₜ[ℝ] !![0, 1; 1, 0] := by
  rw [hyperbolicEquivTensor_apply]
  exact hyperbolicToTensor_ι_base Q m

/-- The image of a hyperbolic-plane generator under `hyperbolicEquivTensor`. -/
theorem hyperbolicEquivTensor_ι_hyperbolic (v : Fin (1 + 1) → ℝ) :
    hyperbolicEquivTensor Q (_root_.CliffordAlgebra.ι _ (0, v)) =
      1 ⊗ₜ[ℝ] !![v 0, v 1; -v 1, -v 0] := by
  rw [hyperbolicEquivTensor_apply]
  exact hyperbolicToTensor_ι_hyperbolic Q v

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
