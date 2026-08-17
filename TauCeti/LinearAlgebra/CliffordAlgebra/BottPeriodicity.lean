/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm
public import TauCeti.LinearAlgebra.CliffordAlgebra.SignSwitch
public import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
public import Mathlib.RingTheory.MatrixAlgebra

import Mathlib.LinearAlgebra.Matrix.Unique

/-!
# Hyperbolic Bott periodicity for real Clifford algebras

This file proves the `(1, 1)` periodicity step for Clifford algebras: adding one positive and one
negative generator is equivalent to tensoring with two-by-two real matrices. It also derives the
signature-switch recurrence `Cliff(p + 2, q) ≅ Cliff(q, p) ⊗ M₂(ℝ)` from
`CliffordAlgebra.signSwitchEquiv`.

## Main results

* `CliffordAlgebra.hyperbolicEquivTensor`: adjoining a hyperbolic plane to an arbitrary
  real quadratic module tensors its Clifford algebra with `M₂(ℝ)`;
* `TauCeti.realCliffordBottEquiv`: the corresponding equivalence for the standard signature forms;
* `TauCeti.realCliffordBottIterEquiv`: the iterated standard-signature equivalence, with matrix
  size `2 ^ n` after adjoining `n` hyperbolic planes;
* `TauCeti.realCliffordSignatureReductionEquiv`: the reduction of a standard signature by its
  common positive and negative part;
* `TauCeti.realCliffordSignatureSwitchRecurrenceEquiv`: the recurrence which switches a real
  signature while adding two positive generators.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 7;
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I.
-/

public section

open Module QuadraticMap
open scoped Matrix TensorProduct

namespace CliffordAlgebra

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
  rw [hyperbolicToTensor, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply,
    hyperbolicToMatrix_ι, matrixEquivTensor_apply_symm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one]

private theorem hyperbolicToTensor_ι_hyperbolic (v : Fin (1 + 1) → ℝ) :
    hyperbolicToTensor Q (_root_.CliffordAlgebra.ι _ (0, v)) =
      1 ⊗ₜ[ℝ] !![v 0, v 1; -v 1, -v 0] := by
  apply (matrixEquivTensor (Fin 2) ℝ (_root_.CliffordAlgebra Q)).symm.injective
  rw [hyperbolicToTensor, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply,
    hyperbolicToMatrix_ι, matrixEquivTensor_apply_symm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one]

private def hyperbolicRightInclusion :
    _root_.CliffordAlgebra (TauCeti.realCliffordForm 1 1) →ₐ[ℝ]
      _root_.CliffordAlgebra (Q.prod (TauCeti.realCliffordForm 1 1)) :=
  _root_.CliffordAlgebra.map
    (QuadraticMap.Isometry.inr Q (TauCeti.realCliffordForm 1 1))

private abbrev HyperbolicAlgebra :=
  _root_.CliffordAlgebra (Q.prod (TauCeti.realCliffordForm 1 1))

private theorem realCliffordOneOneEquivMatrix_e₀_mul_e₁ :
    TauCeti.realCliffordOneOneEquivMatrix
        (_root_.CliffordAlgebra.ι (TauCeti.realCliffordForm 1 1) (Pi.single 0 1) *
          _root_.CliffordAlgebra.ι _ (Pi.single 1 1)) =
      !![(0 : ℝ), 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [TauCeti.realCliffordOneOneEquivMatrix_ι, Matrix.mul_apply, Fin.sum_univ_two]

private def hyperbolicE₀ : HyperbolicAlgebra Q :=
  _root_.CliffordAlgebra.ι _ (0, Pi.single 0 1)

private def hyperbolicE₁ : HyperbolicAlgebra Q :=
  _root_.CliffordAlgebra.ι _ (0, Pi.single 1 1)

private def hyperbolicVolume : HyperbolicAlgebra Q := hyperbolicE₀ Q * hyperbolicE₁ Q

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

private theorem hyperbolicMatrixInclusion_sigmaX :
    hyperbolicMatrixInclusion Q !![(0 : ℝ), 1; 1, 0] = hyperbolicVolume Q := by
  rw [← realCliffordOneOneEquivMatrix_e₀_mul_e₁, hyperbolicMatrixInclusion_apply]
  dsimp [hyperbolicVolume, hyperbolicE₀, hyperbolicE₁]
  rw [hyperbolicRightInclusion, map_mul, _root_.CliffordAlgebra.map_apply_ι,
    _root_.CliffordAlgebra.map_apply_ι]
  rfl

private theorem sigmaX_sq :
    (!![(0 : ℝ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) * !![0, 1; 1, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem hyperbolicVolume_sq : hyperbolicVolume Q * hyperbolicVolume Q = 1 := by
  rw [← hyperbolicMatrixInclusion_sigmaX, ← map_mul, sigmaX_sq, map_one]

private theorem hyperbolicBase_comm_volume (m : M) :
    Commute (_root_.CliffordAlgebra.ι _ (m, 0)) (hyperbolicVolume Q) := by
  simpa [hyperbolicVolume, hyperbolicE₀, hyperbolicE₁] using
    (_root_.CliffordAlgebra.commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_right
      (f₁ := QuadraticMap.Isometry.inl Q (TauCeti.realCliffordForm 1 1))
      (f₂ := QuadraticMap.Isometry.inr Q (TauCeti.realCliffordForm 1 1))
      (hf := fun _ _ => QuadraticMap.IsOrtho.inl_inr _ _)
      (_root_.CliffordAlgebra.ι Q m)
      (_root_.CliffordAlgebra.ι _ (Pi.single 0 1) * _root_.CliffordAlgebra.ι _ (Pi.single 1 1))
      (_root_.CliffordAlgebra.ι_mem_evenOdd_one Q m)
      (_root_.CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (TauCeti.realCliffordForm 1 1)
        (Pi.single 0 1) (Pi.single 1 1)))

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

private theorem hyperbolicVolume_anticomm_rightGenerator (v : Fin (1 + 1) → ℝ) :
    hyperbolicVolume Q * _root_.CliffordAlgebra.ι _ (0, v) =
      -(_root_.CliffordAlgebra.ι _ (0, v) * hyperbolicVolume Q) := by
  let h0 := _root_.CliffordAlgebra.ι (TauCeti.realCliffordForm 1 1) (Pi.single 0 1)
  let h1 := _root_.CliffordAlgebra.ι (TauCeti.realCliffordForm 1 1) (Pi.single 1 1)
  have hh : h0 * h1 * _root_.CliffordAlgebra.ι _ v =
      -(_root_.CliffordAlgebra.ι _ v * (h0 * h1)) := by
    -- Rewrite the volume factor as the preimage of `σₓ` before calculating with matrices.
    rw [show h0 * h1 = TauCeti.realCliffordOneOneEquivMatrix.symm !![(0 : ℝ), 1; 1, 0] by
      apply TauCeti.realCliffordOneOneEquivMatrix.injective
      dsimp [h0, h1]
      rw [realCliffordOneOneEquivMatrix_e₀_mul_e₁, AlgEquiv.apply_symm_apply]]
    apply TauCeti.realCliffordOneOneEquivMatrix.injective
    simp only [map_mul, map_neg, AlgEquiv.apply_symm_apply,
      TauCeti.realCliffordOneOneEquivMatrix_ι]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
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
  rw [← Prod.fst_add_snd (m, v), map_add, map_add,
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
  rw [sigmaX_sq]

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

@[simp]
private theorem one_tmul_zeroMatrix :
    (1 : _root_.CliffordAlgebra Q) ⊗ₜ[ℝ]
      !![(0 : ℝ), 0; 0, 0] = 0 := by
  rw [← TensorProduct.tmul_zero (Matrix (Fin 2) (Fin 2) ℝ) 1]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The image of a generator under `hyperbolicEquivTensor`, split into its original-module and
hyperbolic-plane components. -/
@[simp]
theorem hyperbolicEquivTensor_ι
    (x : M × (Fin (1 + 1) → ℝ)) :
    hyperbolicEquivTensor Q (_root_.CliffordAlgebra.ι _ x) =
      _root_.CliffordAlgebra.ι Q x.1 ⊗ₜ[ℝ] !![0, 1; 1, 0] +
        1 ⊗ₜ[ℝ] !![x.2 0, x.2 1; -x.2 1, -x.2 0] := by
  -- `AlgEquiv.ofAlgHom` exposes `hyperbolicToTensor` as the forward map.
  change hyperbolicToTensor Q (_root_.CliffordAlgebra.ι _ x) = _
  conv_lhs =>
    rw [← Prod.fst_add_snd x]
  rw [map_add, map_add, hyperbolicToTensor_ι_base, hyperbolicToTensor_ι_hyperbolic]

/-- The inverse of `hyperbolicEquivTensor` on the tensor representing an original generator. -/
@[simp]
theorem hyperbolicEquivTensor_symm_apply_ι_base (m : M) :
    (hyperbolicEquivTensor Q).symm
        (_root_.CliffordAlgebra.ι Q m ⊗ₜ[ℝ] !![0, 1; 1, 0]) =
      _root_.CliffordAlgebra.ι _ (m, 0) := by
  apply (hyperbolicEquivTensor Q).injective
  rw [AlgEquiv.apply_symm_apply, hyperbolicEquivTensor_ι]
  simp only [Pi.zero_apply, neg_zero, one_tmul_zeroMatrix, add_zero]

/-- The inverse of `hyperbolicEquivTensor` on a tensor representing a hyperbolic generator. -/
@[simp]
theorem hyperbolicEquivTensor_symm_apply_ι_hyperbolic
    (v : Fin (1 + 1) → ℝ) :
    (hyperbolicEquivTensor Q).symm (1 ⊗ₜ[ℝ] !![v 0, v 1; -v 1, -v 0]) =
      _root_.CliffordAlgebra.ι _ (0, v) := by
  apply (hyperbolicEquivTensor Q).injective
  rw [AlgEquiv.apply_symm_apply, hyperbolicEquivTensor_ι]
  simp

end CliffordAlgebra

namespace TauCeti

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

/-! ### Iterated hyperbolic reduction -/

private def tensorMatrixMulEquiv (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    (m n : ℕ) :
    (A ⊗[R] Matrix (Fin m) (Fin m) R) ⊗[R] Matrix (Fin n) (Fin n) R ≃ₐ[R]
      A ⊗[R] Matrix (Fin (m * n)) (Fin (m * n)) R :=
  (Algebra.TensorProduct.assoc R R R A
      (Matrix (Fin m) (Fin m) R) (Matrix (Fin n) (Fin n) R)).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[R] A)
      ((Matrix.kroneckerAlgEquiv (Fin m) (Fin n) R).trans
        (Matrix.reindexAlgEquiv R R finProdFinEquiv)))

private def tensorMatrixOneEquiv (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] :
    A ≃ₐ[R] A ⊗[R] Matrix (Fin 1) (Fin 1) R :=
  ((Matrix.uniqueAlgEquiv (R := R) (A := A) (m := Unit)).symm.trans
      (Matrix.reindexAlgEquiv R A (Equiv.ofUnique Unit (Fin 1)))).trans
    (matrixEquivTensor (Fin 1) R A)

private noncomputable def realCliffordBottIterEquivImpl (p q : ℕ) : (n : ℕ) →
    _root_.CliffordAlgebra (realCliffordForm (p + n) (q + n)) ≃ₐ[ℝ]
      _root_.CliffordAlgebra (realCliffordForm p q) ⊗[ℝ]
        Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ
  | 0 => by
      simpa using tensorMatrixOneEquiv ℝ (_root_.CliffordAlgebra (realCliffordForm p q))
  | n + 1 =>
      (realCliffordBottEquiv (p + n) (q + n)).trans
        ((Algebra.TensorProduct.congr (realCliffordBottIterEquivImpl p q n)
          (AlgEquiv.refl : Matrix (Fin 2) (Fin 2) ℝ ≃ₐ[ℝ] _)).trans
            (tensorMatrixMulEquiv ℝ (_root_.CliffordAlgebra (realCliffordForm p q)) (2 ^ n) 2))

/-- Iterating the hyperbolic Bott step `n` times identifies
`Cliff(p + n, q + n)` with `Cliff(p, q) ⊗ M_(2 ^ n)(ℝ)`. -/
@[irreducible]
noncomputable def realCliffordBottIterEquiv (p q n : ℕ) :
    _root_.CliffordAlgebra (realCliffordForm (p + n) (q + n)) ≃ₐ[ℝ]
      _root_.CliffordAlgebra (realCliffordForm p q) ⊗[ℝ]
        Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ :=
  realCliffordBottIterEquivImpl p q n

private noncomputable def castRealCliffordMatrixEquiv
    {p q p' q' r s r' s' n n' : ℕ}
    (hp : p = p') (hq : q = q') (hr : r = r') (hs : s = s') (hn : n = n')
    (e : _root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      _root_.CliffordAlgebra (realCliffordForm r s) ⊗[ℝ]
        Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) :
    _root_.CliffordAlgebra (realCliffordForm p' q') ≃ₐ[ℝ]
      _root_.CliffordAlgebra (realCliffordForm r' s') ⊗[ℝ]
        Matrix (Fin (2 ^ n')) (Fin (2 ^ n')) ℝ :=
  hp ▸ hq ▸ hr ▸ hs ▸ hn ▸ e

/-- Removing the common positive and negative part of a real Clifford signature leaves a
one-sided signature and a matrix factor of size `2 ^ min p q`. -/
noncomputable def realCliffordSignatureReductionEquiv (p q : ℕ) :
    _root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      _root_.CliffordAlgebra (realCliffordForm (p - min p q) (q - min p q)) ⊗[ℝ]
        Matrix (Fin (2 ^ min p q)) (Fin (2 ^ min p q)) ℝ :=
  castRealCliffordMatrixEquiv
    (Nat.sub_add_cancel (Nat.min_le_left p q))
    (Nat.sub_add_cancel (Nat.min_le_right p q)) rfl rfl rfl
    (realCliffordBottIterEquiv (p - min p q) (q - min p q) (min p q))

/-- If `p ≤ q`, reducing the common part of a real Clifford signature leaves only negative
generators. -/
noncomputable def realCliffordNegativeAxisReductionEquiv (p q : ℕ) (h : p ≤ q) :
    _root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      _root_.CliffordAlgebra (realCliffordForm 0 (q - p)) ⊗[ℝ]
        Matrix (Fin (2 ^ p)) (Fin (2 ^ p)) ℝ :=
  castRealCliffordMatrixEquiv rfl rfl (by simp [Nat.min_eq_left h])
    (by simp [Nat.min_eq_left h]) (Nat.min_eq_left h)
    (realCliffordSignatureReductionEquiv p q)

/-- If `q ≤ p`, reducing the common part of a real Clifford signature leaves only positive
generators. -/
noncomputable def realCliffordPositiveAxisReductionEquiv (p q : ℕ) (h : q ≤ p) :
    _root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      _root_.CliffordAlgebra (realCliffordForm (p - q) 0) ⊗[ℝ]
        Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℝ :=
  castRealCliffordMatrixEquiv rfl rfl (by simp [Nat.min_eq_right h])
    (by simp [Nat.min_eq_right h]) (Nat.min_eq_right h)
    (realCliffordSignatureReductionEquiv p q)

/-- At zero iterations, `realCliffordBottIterEquiv` is the canonical identification with a
one-by-one matrix tensor factor. -/
@[simp]
theorem realCliffordBottIterEquiv_zero_apply (p q : ℕ)
    (x : _root_.CliffordAlgebra (realCliffordForm p q)) :
    let e : _root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
        _root_.CliffordAlgebra (realCliffordForm p q) ⊗[ℝ]
          Matrix (Fin 1) (Fin 1) ℝ := realCliffordBottIterEquiv p q 0
    e x = x ⊗ₜ[ℝ] (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  unfold realCliffordBottIterEquiv
  -- Expose the zero branch of the private recursive implementation.
  change tensorMatrixOneEquiv ℝ (_root_.CliffordAlgebra (realCliffordForm p q)) x = _
  rw [tensorMatrixOneEquiv, AlgEquiv.trans_apply, matrixEquivTensor_apply,
    Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_one]
  -- The unfolded tensor equivalence leaves the unique matrix unit to identify with `1`.
  change x ⊗ₜ[ℝ] Matrix.single 0 0 1 = x ⊗ₜ[ℝ] 1
  congr 1
  ext i j
  fin_cases i
  fin_cases j
  simp

/-- The successor iteration first applies one hyperbolic Bott step, transports the previous
iteration through the left tensor factor, and absorbs the two matrix factors by the Kronecker
equivalence. -/
@[simp]
theorem realCliffordBottIterEquiv_succ (p q n : ℕ) :
    realCliffordBottIterEquiv p q (n + 1) =
      (realCliffordBottEquiv (p + n) (q + n)).trans
        ((Algebra.TensorProduct.congr (realCliffordBottIterEquiv p q n)
          (AlgEquiv.refl : Matrix (Fin 2) (Fin 2) ℝ ≃ₐ[ℝ] _)).trans
          ((Algebra.TensorProduct.assoc ℝ ℝ ℝ
              (_root_.CliffordAlgebra (realCliffordForm p q))
              (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ)
              (Matrix (Fin 2) (Fin 2) ℝ)).trans
            (Algebra.TensorProduct.congr
              (AlgEquiv.refl : _root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ] _)
              ((Matrix.kroneckerAlgEquiv (Fin (2 ^ n)) (Fin 2) ℝ).trans
                (Matrix.reindexAlgEquiv ℝ ℝ finProdFinEquiv))))) := by
  unfold realCliffordBottIterEquiv
  rw [realCliffordBottIterEquivImpl]
  rfl

/-! ### Signature-switch recurrence -/

/-- One sign switch followed by the hyperbolic Bott step gives the signature-switch recurrence
`Cliff(p + 2, q) ≅ Cliff(q, p) ⊗ M₂(ℝ)`. -/
noncomputable def realCliffordSignatureSwitchRecurrenceEquiv (p q : ℕ) :
    _root_.CliffordAlgebra (realCliffordForm (p + 1 + 1) q) ≃ₐ[ℝ]
      _root_.CliffordAlgebra (realCliffordForm q p) ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  (_root_.CliffordAlgebra.equivOfIsometry
    (realCliffordPositiveSplitIsometry (p + 1) q)).trans
    ((CliffordAlgebra.signSwitchEquiv (realCliffordForm (p + 1) q)).trans
      ((_root_.CliffordAlgebra.equivOfIsometry
        (realCliffordSignSwitchStandardIsometry (p + 1) q)).trans
          (realCliffordBottEquiv q p)))

/-- The signature-switch recurrence sends a Clifford generator through its two coordinate
isometries and the sign-switch generator formula, then transports the result through
`realCliffordBottEquiv q p`. -/
@[simp]
theorem realCliffordSignatureSwitchRecurrenceEquiv_ι (p q : ℕ)
    (v : Fin ((p + 1 + 1) + q) → ℝ) :
    realCliffordSignatureSwitchRecurrenceEquiv p q (_root_.CliffordAlgebra.ι _ v) =
      realCliffordBottEquiv q p (_root_.CliffordAlgebra.ι _
        (realCliffordSignSwitchStandardIsometry (p + 1) q (0, 1))) *
        realCliffordBottEquiv q p (_root_.CliffordAlgebra.ι _
          (realCliffordSignSwitchStandardIsometry (p + 1) q
            ((realCliffordPositiveSplitIsometry (p + 1) q v).1, 0))) +
          (realCliffordPositiveSplitIsometry (p + 1) q v).2 •
            realCliffordBottEquiv q p (_root_.CliffordAlgebra.ι _
              (realCliffordSignSwitchStandardIsometry (p + 1) q (0, 1))) := by
  simp only [realCliffordSignatureSwitchRecurrenceEquiv, AlgEquiv.trans_apply,
    _root_.CliffordAlgebra.equivOfIsometry_apply,
    _root_.CliffordAlgebra.map_apply_ι, AlgEquiv.trans_apply,
    CliffordAlgebra.signSwitchEquiv_ι, map_add, map_mul, map_smul,
    AlgEquiv.trans_apply, _root_.CliffordAlgebra.equivOfIsometry_apply,
    _root_.CliffordAlgebra.map_apply_ι, QuadraticMap.IsometryEquiv.toIsometry_apply]

end TauCeti
