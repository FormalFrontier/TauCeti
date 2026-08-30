/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.MinusculeWeight
public import Mathlib.Algebra.Lie.Sl2

import TauCeti.Algebra.Lie.Sl2.WeightString

/-!
# A 27-dimensional representation of the type-E6 Serre presentation

This file constructs a 27-dimensional representation of the type-`E₆` Serre presentation. The
coordinate basis is indexed by the Weyl orbit of the first fundamental weight enumerated by
`TauCeti.DynkinType.e6MinusculeWeight`.

For a simple root `i`, the raising matrix sends the basis vector of weight `μ` to the basis vector
of weight `μ + αᵢ` when `⟨μ, αᵢ∨⟩ = -1`, and to zero otherwise. The lowering matrix is defined
dually. The Cartan generator acts diagonally by the simple-coroot coordinate of the weight. These
integral matrices satisfy the Serre relations for the transposed type-`E₆` Cartan matrix.
Identifying this presentation with the split semisimple Lie algebra of type `E₆`, and hence
interpreting these matrices as a representation of that algebra, remains downstream.

This is the representation-theoretic input for the full-weight type-`E₆` Chevalley--Demazure
carrier required by Layer 9 of the ReductiveGroups roadmap. The weights span the full character
lattice by `TauCeti.DynkinType.span_range_e6MinusculeWeight_eq_top`; constructing the associated
Kostant carrier and its group scheme remains downstream.

## Main declarations

* `TauCeti.E6Minuscule.raisingMatrix`, `loweringMatrix`, and `cartanGeneratorMatrix`: the
  integral Chevalley generators on the minuscule weight basis.
* `TauCeti.E6Minuscule.isSerreSystem`: the generators satisfy the type-`E₆` Serre relations.
* `TauCeti.E6Minuscule.serreRepresentation`: the induced homomorphism from the integral
  type-`E₆` Serre presentation.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§13.4 and 27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.2.
-/

public section

open scoped Matrix

namespace TauCeti.E6Minuscule

open TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The target of the `i`-th raising operator on a minuscule weight-basis vector, when nonzero. -/
private def raisingTarget (i : Fin 6) (a : Fin 27) : Option (Fin 27) :=
  if e6MinusculeWeight a i = -1 then some (e6MinusculeReflection i a) else none

/-- The target of the `i`-th lowering operator on a minuscule weight-basis vector, when nonzero. -/
private def loweringTarget (i : Fin 6) (a : Fin 27) : Option (Fin 27) :=
  if e6MinusculeWeight a i = 1 then some (e6MinusculeReflection i a) else none

/-- The zero-one matrix of a partial map between finite coordinate bases. -/
private def matrixOfTarget (f : Fin 27 → Option (Fin 27)) : Matrix (Fin 27) (Fin 27) ℤ :=
  fun a b ↦ if some a = f b then 1 else 0

/-- The raising matrix of the `i`-th simple root on the integral minuscule weight basis. -/
def raisingMatrix (i : Fin 6) : Matrix (Fin 27) (Fin 27) ℤ :=
  matrixOfTarget (raisingTarget i)

/-- The lowering matrix of the `i`-th simple root on the integral minuscule weight basis. -/
def loweringMatrix (i : Fin 6) : Matrix (Fin 27) (Fin 27) ℤ :=
  matrixOfTarget (loweringTarget i)

/-- The diagonal matrix of the `i`-th simple coroot on the integral minuscule weight basis. -/
def cartanGeneratorMatrix (i : Fin 6) : Matrix (Fin 27) (Fin 27) ℤ :=
  Matrix.diagonal (fun b ↦ e6MinusculeWeight b i)

/-- The entry formula for a simple raising matrix. -/
@[simp]
theorem raisingMatrix_apply (i : Fin 6) (a b : Fin 27) :
    raisingMatrix i a b =
      if e6MinusculeWeight b i = -1 ∧ a = e6MinusculeReflection i b then 1 else 0 :=
  by simp [raisingMatrix, matrixOfTarget, raisingTarget, eq_comm]

/-- The entry formula for a simple lowering matrix. -/
@[simp]
theorem loweringMatrix_apply (i : Fin 6) (a b : Fin 27) :
    loweringMatrix i a b =
      if e6MinusculeWeight b i = 1 ∧ a = e6MinusculeReflection i b then 1 else 0 :=
  by simp [loweringMatrix, matrixOfTarget, loweringTarget, eq_comm]

/-- The entry formula for a simple Cartan generator matrix. -/
@[simp]
theorem cartanGeneratorMatrix_apply (i : Fin 6) (a b : Fin 27) :
    cartanGeneratorMatrix i a b = if a = b then e6MinusculeWeight b i else 0 := by
  rw [cartanGeneratorMatrix, Matrix.diagonal_apply]
  split_ifs with h
  · subst b
    rfl
  · rfl

private theorem matrixOfTarget_mul (f g : Fin 27 → Option (Fin 27)) :
    matrixOfTarget f * matrixOfTarget g = matrixOfTarget (fun a ↦ (g a).bind f) := by
  ext a b
  cases h : g b with
  | none => simp [matrixOfTarget, Matrix.mul_apply, h]
  | some x => simp [matrixOfTarget, Matrix.mul_apply, h]

/-- Reflection in a simple root negates the corresponding simple-coroot coordinate of a
minuscule weight. -/
@[simp]
private theorem e6MinusculeWeight_reflection_apply_self (i : Fin 6) (a : Fin 27) :
    e6MinusculeWeight (e6MinusculeReflection i a) i = -e6MinusculeWeight a i := by
  have h := congrFun (e6MinusculeWeight_reflection i a) i
  rw [root_e6SimpleIndex] at h
  simp [CartanMatrix.E_diag] at h
  omega

/-- The coordinate change under a simple reflection, in the fundamental-weight basis. -/
private theorem e6MinusculeWeight_reflection_apply (i : Fin 6) (a : Fin 27) (j : Fin 6) :
    e6MinusculeWeight (e6MinusculeReflection i a) j =
      e6MinusculeWeight a j - e6MinusculeWeight a i * CartanMatrix.E 6 i j := by
  have h := congrFun (e6MinusculeWeight_reflection i a) j
  rw [root_e6SimpleIndex] at h
  simpa using h

@[simp]
private theorem raisingTarget_eq_some_iff (i : Fin 6) (a b : Fin 27) :
    raisingTarget i a = some b ↔
      e6MinusculeWeight a i = -1 ∧ b = e6MinusculeReflection i a := by
  simp [raisingTarget, eq_comm]

@[simp]
private theorem loweringTarget_eq_some_iff (i : Fin 6) (a b : Fin 27) :
    loweringTarget i a = some b ↔
      e6MinusculeWeight a i = 1 ∧ b = e6MinusculeReflection i a := by
  simp [loweringTarget, eq_comm]

private theorem cartanMatrix_E_six_apply_eq_zero_or_neg_one_of_ne (i j : Fin 6) (hij : i ≠ j) :
    CartanMatrix.E 6 i j = 0 ∨ CartanMatrix.E 6 i j = -1 := by
  fin_cases i <;> fin_cases j <;> simp_all [CartanMatrix.E]

private theorem e6MinusculeReflection_comm_of_cartan_eq_zero (i j : Fin 6) (a : Fin 27)
    (hij : CartanMatrix.E 6 i j = 0) :
    e6MinusculeReflection i (e6MinusculeReflection j a) =
      e6MinusculeReflection j (e6MinusculeReflection i a) := by
  have hsym : CartanMatrix.E 6 j i = CartanMatrix.E 6 i j := by
    have h := congrFun (congrFun (CartanMatrix.E_transpose 6) i) j
    simpa [Matrix.transpose_apply] using h
  have horth : e6SimplyConnectedRootDatum.IsOrthogonal
      (e6SimpleIndex i) (e6SimpleIndex j) := by
    rw [RootPairing.IsOrthogonal, pairing_e6SimpleIndex, pairing_e6SimpleIndex, hsym, hij]
    exact ⟨rfl, rfl⟩
  have hcomm := RootPairing.isOrthogonal_comm e6SimplyConnectedRootDatum
    (e6SimpleIndex i) (e6SimpleIndex j) horth
  apply e6MinusculeWeight_injective
  have happ := congrArg (fun f ↦ f (e6MinusculeWeight a)) hcomm.eq
  simpa only [LinearEquiv.mul_apply,
    e6SimplyConnectedRootDatum_reflection_e6MinusculeWeight] using happ

private theorem raisingTarget_bind_loweringTarget_of_ne (i j : Fin 6) (hij : i ≠ j)
    (a : Fin 27) :
    (loweringTarget j a).bind (raisingTarget i) =
      (raisingTarget i a).bind (loweringTarget j) := by
  have hsym : CartanMatrix.E 6 j i = CartanMatrix.E 6 i j := by
    have h := congrFun (congrFun (CartanMatrix.E_transpose 6) i) j
    simpa [Matrix.transpose_apply] using h
  rcases cartanMatrix_E_six_apply_eq_zero_or_neg_one_of_ne i j hij with hA | hA
  all_goals
    rcases e6MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a i with hi | hi | hi
  all_goals
    rcases e6MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a j with hj | hj | hj
  all_goals simp [raisingTarget, loweringTarget, hi, hj,
    e6MinusculeWeight_reflection_apply, hA, hsym,
    e6MinusculeReflection_comm_of_cartan_eq_zero]

private theorem lie_raisingMatrix_loweringMatrix_of_ne (i j : Fin 6) (hij : i ≠ j) :
    ⁅raisingMatrix i, loweringMatrix j⁆ = 0 := by
  rw [Ring.lie_def, raisingMatrix, loweringMatrix, matrixOfTarget_mul, matrixOfTarget_mul]
  have hcomp :
      (fun a ↦ (loweringTarget j a).bind (raisingTarget i)) =
        fun a ↦ (raisingTarget i a).bind (loweringTarget j) :=
    funext (raisingTarget_bind_loweringTarget_of_ne i j hij)
  rw [hcomp, sub_self]

private theorem lie_cartanGeneratorMatrix_cartanGeneratorMatrix (i j : Fin 6) :
    ⁅cartanGeneratorMatrix i, cartanGeneratorMatrix j⁆ = 0 :=
  (Matrix.commute_diagonal _ _).lie_eq

private theorem lie_raisingMatrix_loweringMatrix_self (i : Fin 6) :
    ⁅raisingMatrix i, loweringMatrix i⁆ = cartanGeneratorMatrix i := by
  ext a b
  simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, raisingMatrix_apply,
    loweringMatrix_apply, mul_ite, mul_one, mul_zero, cartanGeneratorMatrix,
    Matrix.diagonal_apply]
  rcases e6MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one b i with h | h | h
  all_goals simp [h, e6MinusculeWeight_reflection_apply_self,
    e6MinusculeReflection_apply_apply]
  all_goals by_cases hab : a = b <;> simp_all

private theorem lie_cartanGeneratorMatrix_raisingMatrix (i j : Fin 6) :
    ⁅cartanGeneratorMatrix i, raisingMatrix j⁆ =
      (CartanMatrix.E 6)ᵀ i j • raisingMatrix j := by
  ext a b
  simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, cartanGeneratorMatrix,
    Matrix.diagonal_apply, raisingMatrix_apply, Matrix.transpose_apply, Matrix.smul_apply,
    mul_ite, ite_mul, mul_one, mul_zero]
  by_cases h : e6MinusculeWeight b j = -1
  · have href := congrFun (e6MinusculeWeight_reflection j b) i
    rw [root_e6SimpleIndex] at href
    simp [h] at href
    simp [h]
    split_ifs with hab
    · subst a
      omega
    · rfl
  · simp [h]

private theorem lie_cartanGeneratorMatrix_loweringMatrix (i j : Fin 6) :
    ⁅cartanGeneratorMatrix i, loweringMatrix j⁆ =
      -((CartanMatrix.E 6)ᵀ i j • loweringMatrix j) := by
  ext a b
  simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, cartanGeneratorMatrix,
    Matrix.diagonal_apply, loweringMatrix_apply, Matrix.transpose_apply, Matrix.neg_apply,
    Matrix.smul_apply, mul_ite, ite_mul, mul_one, mul_zero]
  by_cases h : e6MinusculeWeight b j = 1
  · have href := congrFun (e6MinusculeWeight_reflection j b) i
    rw [root_e6SimpleIndex] at href
    simp [h] at href
    simp [h]
    split_ifs with hab
    · subst a
      omega
    · rfl
  · simp [h]

private theorem cartanGeneratorMatrix_ne_zero (i : Fin 6) : cartanGeneratorMatrix i ≠ 0 := by
  intro hzero
  have hweight (a : Fin 27) : e6MinusculeWeight a i = 0 := by
    have h := congrFun (congrFun hzero a) a
    simpa [cartanGeneratorMatrix, Matrix.diagonal_apply] using h
  have hbasis : Pi.single i 1 ∈ Submodule.span ℤ (Set.range e6MinusculeWeight) := by
    rw [span_range_e6MinusculeWeight_eq_top]
    exact Submodule.mem_top
  have hcoord : (Pi.single i 1 : Fin 6 → ℤ) i = 0 := by
    refine Submodule.span_induction (p := fun x _ ↦ x i = 0) ?_ ?_ ?_ ?_ hbasis
    · rintro x ⟨a, rfl⟩
      exact hweight a
    · rfl
    · intro x y _ _ hx hy
      simp [hx, hy]
    · intro r x _ hx
      simp [hx]
  simp at hcoord

/-- At each simple node, the three integral minuscule matrices form an `sl₂` triple. -/
theorem isSl2Triple (i : Fin 6) :
    _root_.IsSl2Triple (cartanGeneratorMatrix i) (raisingMatrix i) (loweringMatrix i) where
  h_ne_zero := cartanGeneratorMatrix_ne_zero i
  lie_e_f := lie_raisingMatrix_loweringMatrix_self i
  lie_h_e_nsmul := by
    rw [lie_cartanGeneratorMatrix_raisingMatrix, Matrix.transpose_apply, CartanMatrix.E_diag]
    simp
  lie_h_f_nsmul := by
    rw [lie_cartanGeneratorMatrix_loweringMatrix, Matrix.transpose_apply, CartanMatrix.E_diag]
    simp

/-- **The integral 27-dimensional minuscule matrices satisfy the Serre relations of type
`E₆`.** The transpose is the convention in which the coroot index precedes the root index. -/
theorem isSerreSystem :
    TauCeti.IsSerreSystem ℤ (CartanMatrix.E 6)ᵀ cartanGeneratorMatrix raisingMatrix
      loweringMatrix where
  lie_H_H := lie_cartanGeneratorMatrix_cartanGeneratorMatrix
  lie_E_F_self := lie_raisingMatrix_loweringMatrix_self
  lie_E_F_of_ne := lie_raisingMatrix_loweringMatrix_of_ne
  lie_H_E := lie_cartanGeneratorMatrix_raisingMatrix
  lie_H_F := lie_cartanGeneratorMatrix_loweringMatrix
  ad_pow_lie_E_E i j := by
    rcases eq_or_ne i j with rfl | hij
    · simp
    · rw [Matrix.transpose_apply]
      exact TauCeti.ad_pow_lie_eq_zero_of_isSl2Triple_of_lie_h_eq_smul_of_lie_f_eq_zero
        (isSl2Triple i) (lie_cartanGeneratorMatrix_raisingMatrix i j)
        (by rw [← lie_skew, lie_raisingMatrix_loweringMatrix_of_ne j i hij.symm, neg_zero])
  ad_pow_lie_F_F i j := by
    rcases eq_or_ne i j with rfl | hij
    · simp
    · rw [Matrix.transpose_apply]
      exact TauCeti.ad_pow_lie_eq_zero_of_isSl2Triple_of_lie_h_eq_smul_of_lie_f_eq_zero
        (isSl2Triple i).symm
        (by
          rw [neg_lie, lie_cartanGeneratorMatrix_loweringMatrix i j, Matrix.transpose_apply,
            neg_neg]
          simp only [Int.cast_id])
        (lie_raisingMatrix_loweringMatrix_of_ne i j hij)

/-- The integral 27-dimensional minuscule representation of the type-`E₆` Serre presentation. -/
noncomputable def serreRepresentation :
    Matrix.ToLieAlgebra ℤ (CartanMatrix.E 6)ᵀ →ₗ⁅ℤ⁆ Matrix (Fin 27) (Fin 27) ℤ :=
  TauCeti.serreLift isSerreSystem

/-- The minuscule representation sends a Cartan generator to its diagonal matrix. -/
@[simp]
theorem serreRepresentation_serreH (i : Fin 6) :
    serreRepresentation (TauCeti.serreH ℤ (CartanMatrix.E 6)ᵀ i) = cartanGeneratorMatrix i :=
  TauCeti.serreLift_serreH isSerreSystem i

/-- The minuscule representation sends a positive simple generator to its raising matrix. -/
@[simp]
theorem serreRepresentation_serreE (i : Fin 6) :
    serreRepresentation (TauCeti.serreE ℤ (CartanMatrix.E 6)ᵀ i) = raisingMatrix i :=
  TauCeti.serreLift_serreE isSerreSystem i

/-- The minuscule representation sends a negative simple generator to its lowering matrix. -/
@[simp]
theorem serreRepresentation_serreF (i : Fin 6) :
    serreRepresentation (TauCeti.serreF ℤ (CartanMatrix.E 6)ᵀ i) = loweringMatrix i :=
  TauCeti.serreLift_serreF isSerreSystem i

end TauCeti.E6Minuscule
