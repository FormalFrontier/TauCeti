/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.StdBasis

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
theorem adjugate_fin_two_eq_trace_smul_one_sub (A : Matrix (Fin 2) (Fin 2) K) :
    Matrix.adjugate A = Matrix.trace A • 1 - A := by
  rw [Matrix.adjugate_fin_two, Matrix.trace_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The adjugate as a linear map on `2 × 2` matrices over a commutative ring. -/
noncomputable def adjugateFinTwoLinearMap :
    Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K :=
  (Matrix.traceLinearMap (Fin 2) K K).smulRight (1 : Matrix (Fin 2) (Fin 2) K) -
    LinearMap.id

/-- Applying `adjugateFinTwoLinearMap` computes the ordinary matrix adjugate. -/
@[simp] theorem adjugateFinTwoLinearMap_apply (A : Matrix (Fin 2) (Fin 2) K) :
    adjugateFinTwoLinearMap A = Matrix.adjugate A := by
  simp [adjugateFinTwoLinearMap, adjugate_fin_two_eq_trace_smul_one_sub]

section

private theorem one_sub_single_diag (i j : Fin 2) (hij : i ≠ j) :
    (1 : Matrix (Fin 2) (Fin 2) K) - Matrix.single i i (1 : K) =
      Matrix.single j j (1 : K) := by
  fin_cases i <;> fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp_all [Matrix.single]

private theorem neg_single_offdiag_mul_smul_one_sub_single_diag_entry
    (r : K) (i j : Fin 2) (hij : i ≠ j) :
    let E : Matrix (Fin 2) (Fin 2) K := Matrix.single i j 1
    let D : Matrix (Fin 2) (Fin 2) K := r • 1 - Matrix.single i i 1
    ((-E) * D) i j = -r := by
  dsimp
  rw [neg_mul]
  rw [Matrix.neg_apply, Matrix.single_mul_apply_same]
  simp [hij]

/-- An anti-multiplicative linear map with scalar translates sends an off-diagonal unit
to its negative. -/
private theorem map_single_eq_neg_of_ne
    (f : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hmul : ∀ A B, f (A * B) = f B * f A)
    (hscalar : ∀ A, ∃ r : K, A + f A = r • 1)
    (i j : Fin 2) (hij : i ≠ j) :
    f (Matrix.single i j 1) = -(Matrix.single i j 1) := by
  let E : Matrix (Fin 2) (Fin 2) K := Matrix.single i j 1
  obtain ⟨r, hr⟩ := hscalar E
  have hf : f E = r • 1 - E := eq_sub_of_add_eq (by simpa [add_comm] using hr)
  let F : Matrix (Fin 2) (Fin 2) K := Matrix.single j i 1
  obtain ⟨s, hs⟩ := hscalar F
  have hfF : f F = s • 1 - F := eq_sub_of_add_eq (by simpa [add_comm] using hs)
  have hEF : E * F = Matrix.single i i 1 := by simp [E, F]
  obtain ⟨t, ht⟩ := hscalar (Matrix.single i i 1)
  have hfD : f (Matrix.single i i 1) = t • 1 - Matrix.single i i 1 :=
    eq_sub_of_add_eq (by simpa [add_comm] using ht)
  have hp := hmul E F
  rw [hEF, hfD, hfF, hf] at hp
  have hpji := congr_fun (congr_fun hp j) i
  have hr0 : r = 0 := by
    have hpji' : (0 : K) = -r := by
      simpa [E, F, sub_mul, mul_sub, hij, Ne.symm hij] using hpji
    exact neg_eq_zero.mp hpji'.symm
  have hneg : f E = -E := by
    rw [hf, hr0]
    simp
  simpa only [E] using hneg

/-- Such a map exchanges the two diagonal matrix units. -/
private theorem map_single_self_eq_single_of_ne
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
    have hpij' : (-1 : K) = -r := by
      have hpij'' := hpij
      simp only [D] at hpij''
      rw [neg_single_offdiag_mul_smul_one_sub_single_diag_entry r i j hij] at hpij''
      calc
        (-1 : K) = (-(Matrix.single i j (1 : K))) i j := by simp
        _ = -r := hpij''
    have hr1' : (1 : K) = r := by simpa using congrArg Neg.neg hpij'
    exact hr1'.symm
  rw [hfD, hr1]
  simpa [D, smul_eq_mul] using one_sub_single_diag i j hij

/-- Such a map agrees with adjugation on every standard matrix unit. -/
private theorem map_single_eq_adjugate
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
        _ = Matrix.adjugate (Matrix.single _ _ 1) := by
          rw [adjugate_fin_two_eq_trace_smul_one_sub]
          simpa using
            (one_sub_single_diag (0 : Fin 2) (1 : Fin 2) (by decide)).symm
    · calc
        f (Matrix.single _ _ 1) = Matrix.single (0 : Fin 2) (0 : Fin 2) 1 := by
          simpa using
            map_single_self_eq_single_of_ne f hmul hscalar (1 : Fin 2) (0 : Fin 2) (by decide)
        _ = Matrix.adjugate (Matrix.single _ _ 1) := by
          rw [adjugate_fin_two_eq_trace_smul_one_sub]
          simpa using
            (one_sub_single_diag (1 : Fin 2) (0 : Fin 2) (by decide)).symm
  · rw [map_single_eq_neg_of_ne f hmul hscalar i j hij,
      adjugate_fin_two_eq_trace_smul_one_sub]
    simp [hij]

/-- A linear anti-multiplicative map whose scalar translate is the negative is adjugation. -/
theorem eq_adjugateFinTwoLinearMap_of_antimultiplicative_of_exists_add_eq_smul_one
    (f : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hmul : ∀ A B, f (A * B) = f B * f A)
    (hscalar : ∀ A, ∃ r : K, A + f A = r • 1) :
    f = adjugateFinTwoLinearMap := by
  refine (Matrix.stdBasis K (Fin 2) (Fin 2)).ext ?_
  rintro ⟨i, j⟩
  rw [Matrix.stdBasis_eq_single]
  simpa only [adjugateFinTwoLinearMap_apply] using
    map_single_eq_adjugate f hmul hscalar i j

end


end Matrix
