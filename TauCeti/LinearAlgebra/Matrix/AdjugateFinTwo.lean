/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# Adjugation of two-by-two matrices

This file contains the characteristic-not-two-independent linear algebra used by the Spin(3)
matrix model: the adjugate is linear in size two, and it is characterized by reversal of products
and scalar translates of the negative. These results are generic matrix facts and are kept outside
the Clifford algebra file so downstream matrix users can reuse them directly.
-/

public section

namespace Matrix

variable {K : Type*} [CommRing K]

/-- The adjugate of a two-by-two matrix is its trace times the identity minus itself. -/
theorem adjugate_eq_trace_smul_one_sub (A : Matrix (Fin 2) (Fin 2) K) :
    Matrix.adjugate A = Matrix.trace A • 1 - A := by
  rw [Matrix.adjugate_fin_two, Matrix.trace_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The adjugate as a linear map on `2 × 2` matrices over a commutative ring. -/
noncomputable def adjugateLinearMap :
    Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun := Matrix.adjugate
  map_add' A B := by
    simp only [adjugate_eq_trace_smul_one_sub, Matrix.trace_add, add_smul]
    module
  map_smul' r A := by
    simp only [adjugate_eq_trace_smul_one_sub, Matrix.trace_smul, smul_sub, smul_smul,
      RingHom.id_apply, smul_eq_mul]

/-- Applying `adjugateLinearMap` computes the ordinary matrix adjugate. -/
@[simp] theorem adjugateLinearMap_apply (A : Matrix (Fin 2) (Fin 2) K) :
    adjugateLinearMap A = Matrix.adjugate A := by
  simp [adjugateLinearMap]

section NoZeroDivisors

variable [NoZeroDivisors K]

omit [NoZeroDivisors K] in
private theorem adjugate_single_diag (i j : Fin 2) (hij : i ≠ j) :
    Matrix.adjugate (Matrix.single i i (1 : K)) = Matrix.single j j (1 : K) := by
  fin_cases i <;> fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp_all [Matrix.adjugate_fin_two, Matrix.single]

omit [NoZeroDivisors K] in
private theorem adjugate_single_offdiag (i j : Fin 2) (hij : i ≠ j) :
    Matrix.adjugate (Matrix.single i j (1 : K)) = -(Matrix.single i j (1 : K)) := by
  fin_cases i <;> fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp_all [Matrix.adjugate_fin_two, Matrix.single]

omit [NoZeroDivisors K] in
private theorem one_sub_single_diag (i j : Fin 2) (hij : i ≠ j) :
    (1 : Matrix (Fin 2) (Fin 2) K) - Matrix.single i i (1 : K) =
      Matrix.single j j (1 : K) := by
  fin_cases i <;> fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp_all [Matrix.single]

/-- An anti-multiplicative linear map with scalar translates sends an off-diagonal unit
to its negative. -/
theorem map_single_eq_neg_of_ne
    (f : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hmul : ∀ A B, f (A * B) = f B * f A)
    (hscalar : ∀ A, ∃ r : K, A + f A = r • 1)
    (i j : Fin 2) (hij : i ≠ j) :
    f (Matrix.single i j 1) = -(Matrix.single i j 1) := by
  let E : Matrix (Fin 2) (Fin 2) K := Matrix.single i j 1
  obtain ⟨r, hr⟩ := hscalar E
  have hf : f E = r • 1 - E := eq_sub_of_add_eq (by simpa [add_comm] using hr)
  have hE2 : E * E = 0 := by
    simpa [E] using Matrix.single_mul_single_of_ne (1 : K) i j i (Ne.symm hij) (1 : K)
  have hsquare : f E * f E = 0 := by
    rw [← hmul, hE2, map_zero]
  rw [hf] at hsquare
  have hrii := congr_fun (congr_fun hsquare j) j
  have hrr : r * r = 0 := by
    simpa [E, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single, Matrix.one_apply,
      hij, Ne.symm hij] using hrii
  have hr0 : r = 0 := mul_self_eq_zero.mp hrr
  have hneg : f E = -E := by
    rw [hf, hr0]
    simp
  simpa only [E] using hneg

/-- Such a map exchanges the two diagonal matrix units. -/
theorem map_single_self_eq_single_of_ne
    (f : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hmul : ∀ A B, f (A * B) = f B * f A)
    (hscalar : ∀ A, ∃ r : K, A + f A = r • 1)
    (i j : Fin 2) (hij : i ≠ j) :
    f (Matrix.single i i 1) = Matrix.single j j 1 := by
  let D : Matrix (Fin 2) (Fin 2) K := Matrix.single i i 1
  let E : Matrix (Fin 2) (Fin 2) K := Matrix.single i j 1
  obtain ⟨r, hr⟩ := hscalar D
  have hfD : f D = r • 1 - D := eq_sub_of_add_eq (by simpa [add_comm] using hr)
  have hfE := map_single_eq_neg_of_ne f hmul hscalar i j hij
  have hDE : D * E = E := by
    simp [D, E]
  have hp := hmul D E
  rw [hDE, hfE, hfD] at hp
  have hpij := congr_fun (congr_fun hp i) j
  have hr1 : r = 1 := by
    have hr1' : (1 : K) = r := by
      simpa [D, E, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single, Matrix.one_apply,
        hij, Ne.symm hij] using hpij
    exact hr1'.symm
  rw [hfD, hr1]
  simpa [D, smul_eq_mul] using one_sub_single_diag i j hij

/-- Such a map agrees with adjugation on every standard matrix unit. -/
theorem map_single_eq_adjugate
    (f : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hmul : ∀ A B, f (A * B) = f B * f A)
    (hscalar : ∀ A, ∃ r : K, A + f A = r • 1) (i j : Fin 2) :
    f (Matrix.single i j 1) = Matrix.adjugate (Matrix.single i j 1) := by
  by_cases hij : i = j
  · subst j
    fin_cases i
    · calc
        f (Matrix.single _ _ 1) = Matrix.single (1 : Fin 2) (1 : Fin 2) 1 := by
          simpa using
            map_single_self_eq_single_of_ne f hmul hscalar (0 : Fin 2) (1 : Fin 2) (by decide)
        _ = Matrix.adjugate (Matrix.single _ _ 1) :=
          (adjugate_single_diag (0 : Fin 2) (1 : Fin 2) (by decide)).symm
    · calc
        f (Matrix.single _ _ 1) = Matrix.single (0 : Fin 2) (0 : Fin 2) 1 := by
          simpa using
            map_single_self_eq_single_of_ne f hmul hscalar (1 : Fin 2) (0 : Fin 2) (by decide)
        _ = Matrix.adjugate (Matrix.single _ _ 1) :=
          (adjugate_single_diag (1 : Fin 2) (0 : Fin 2) (by decide)).symm
  · rw [map_single_eq_neg_of_ne f hmul hscalar i j hij]
    exact (adjugate_single_offdiag i j hij).symm

/-- A linear anti-multiplicative map whose scalar translate is the negative is adjugation. -/
theorem linearMap_antimultiplicative_eq_adjugateLinearMap
    (f : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hmul : ∀ A B, f (A * B) = f B * f A)
    (hscalar : ∀ A, ∃ r : K, A + f A = r • 1) :
    f = adjugateLinearMap := by
  refine (Matrix.stdBasis K (Fin 2) (Fin 2)).ext ?_
  rintro ⟨i, j⟩
  rw [Matrix.stdBasis_eq_single]
  simpa only [adjugateLinearMap, LinearMap.coe_mk, AddHom.coe_mk] using
    map_single_eq_adjugate f hmul hscalar i j

end NoZeroDivisors


end Matrix
