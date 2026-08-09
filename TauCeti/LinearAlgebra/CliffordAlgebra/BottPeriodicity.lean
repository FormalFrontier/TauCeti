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
  finite-dimensional real quadratic module tensors its Clifford algebra with `M₂(ℝ)`;
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

private theorem hyperbolicToMatrix_bijective [FiniteDimensional ℝ M] :
    Function.Bijective (hyperbolicToMatrix Q) := by
  have hrank :
      finrank ℝ (_root_.CliffordAlgebra (Q.prod (TauCeti.realCliffordForm 1 1))) =
        finrank ℝ (Matrix (Fin 2) (Fin 2) (_root_.CliffordAlgebra Q)) := by
    rw [Module.finrank_matrix, TauCeti.CliffordAlgebra.finrank_eq_two_pow,
      Module.finrank_prod, TauCeti.CliffordAlgebra.finrank_eq_two_pow,
      Module.finrank_pi, Fintype.card_fin]
    ring
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (hyperbolicToMatrix Q).toLinearMap) hrank).2 (hyperbolicToMatrix_surjective Q),
    hyperbolicToMatrix_surjective Q⟩

/-- Adjoining a hyperbolic plane to a finite-dimensional real quadratic module tensors its
Clifford algebra with two-by-two real matrices. -/
noncomputable def hyperbolicEquivTensor [FiniteDimensional ℝ M] :
    _root_.CliffordAlgebra (Q.prod (TauCeti.realCliffordForm 1 1)) ≃ₐ[ℝ]
      (_root_.CliffordAlgebra Q ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℝ) :=
  (AlgEquiv.ofBijective (hyperbolicToMatrix Q) (hyperbolicToMatrix_bijective Q)).trans
    (matrixEquivTensor (Fin 2) ℝ (_root_.CliffordAlgebra Q))

/-- The image of a generator under `hyperbolicEquivTensor`, split into its original-module and
hyperbolic-plane components. -/
@[simp]
theorem hyperbolicEquivTensor_ι [FiniteDimensional ℝ M]
    (x : M × (Fin (1 + 1) → ℝ)) :
    hyperbolicEquivTensor Q (_root_.CliffordAlgebra.ι _ x) =
      _root_.CliffordAlgebra.ι Q x.1 ⊗ₜ[ℝ] !![0, 1; 1, 0] +
        1 ⊗ₜ[ℝ] !![x.2 0, x.2 1; -x.2 1, -x.2 0] := by
  -- Expose the defining hom before splitting the generator into its two summands.
  change hyperbolicToTensor Q (_root_.CliffordAlgebra.ι _ x) = _
  conv_lhs =>
    rw [show x = (x.1, 0) + (0, x.2) by ext <;> simp]
  rw [map_add, map_add, hyperbolicToTensor_ι_base, hyperbolicToTensor_ι_hyperbolic]

/-- The image of an original-module generator under `hyperbolicEquivTensor`. -/
@[simp 1100]
theorem hyperbolicEquivTensor_ι_base [FiniteDimensional ℝ M] (m : M) :
    hyperbolicEquivTensor Q (_root_.CliffordAlgebra.ι _ (m, 0)) =
      _root_.CliffordAlgebra.ι Q m ⊗ₜ[ℝ] !![0, 1; 1, 0] := by
  -- Expose the defining hom so its generator equation applies directly.
  change hyperbolicToTensor Q (_root_.CliffordAlgebra.ι _ (m, 0)) = _
  exact hyperbolicToTensor_ι_base Q m

/-- The inverse of `hyperbolicEquivTensor` on the tensor representing an original generator. -/
@[simp]
theorem hyperbolicEquivTensor_symm_ι_base [FiniteDimensional ℝ M] (m : M) :
    (hyperbolicEquivTensor Q).symm
        (_root_.CliffordAlgebra.ι Q m ⊗ₜ[ℝ] !![0, 1; 1, 0]) =
      _root_.CliffordAlgebra.ι _ (m, 0) := by
  apply (hyperbolicEquivTensor Q).injective
  rw [AlgEquiv.apply_symm_apply, hyperbolicEquivTensor_ι_base]

/-- The inverse of `hyperbolicEquivTensor` on a tensor representing a hyperbolic generator. -/
@[simp]
theorem hyperbolicEquivTensor_symm_ι_hyperbolic [FiniteDimensional ℝ M]
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
