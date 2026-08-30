/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E7.MinusculeWeight
import TauCeti.Algebra.Lie.Sl2.WeightString

/-!
# The integral minuscule representation of type E7

This file realizes the Chevalley generators of type `E₇` on the fifty-six-element weight
diagram `TauCeti.DynkinType.e7MinusculeWeight`. On the coordinate vector belonging to a weight
`lambda`, the Cartan generator `H_i` acts by the simple-coroot coordinate `lambda_i`; the raising
generator `E_i` carries `lambda` to its simple reflection when `lambda_i = -1`; and the lowering
generator `F_i` makes the reverse move when `lambda_i = 1`.

The resulting integer matrices satisfy the Chevalley--Serre relations for the Bourbaki Cartan
matrix. The universal property of the Serre presentation gives the explicit integral
fifty-six-dimensional minuscule representation. Each raising and lowering matrix squares to
zero. See `TauCeti.Algebra.Lie.E7.Minuscule.AdmissibleLattice` for the rational extension and
the admissibility of its coordinate lattice.

No identification with the abstract irreducible highest-weight module is asserted here. The
construction is explicit: every matrix entry is read from the already audited weight and
reflection tables.

## Main definitions

* `TauCeti.E7Minuscule.cartanMatrix`, `raisingMatrix`, and `loweringMatrix`: the integral Cartan,
  raising, and lowering matrices.
* `TauCeti.E7Minuscule.isSerreSystem`: the Chevalley--Serre relations between them over `ℤ`.
* `TauCeti.E7Minuscule.serreRepresentation`: the induced representation of the type-`E₇` Serre
  Lie algebra.

## References

The numbering and weight diagram follow Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate VI. The minuscule action follows J. E. Humphreys, *Introduction to Lie Algebras and
Representation Theory*, §13.4, and J. C. Jantzen, *Representations of Algebraic Groups*, II.2.

This advances the explicit Chevalley--Demazure construction in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. Its consumer is milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md`, which needs an explicit simply connected type-`E₇`
carrier.
-/

public section

open scoped Matrix

namespace TauCeti.E7Minuscule

open LieAlgebra TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## The integral generator matrices -/

/-- The Cartan generator `H_i` in the minuscule weight basis. -/
def cartanMatrix (i : Fin 7) : Matrix (Fin 56) (Fin 56) ℤ :=
  Matrix.diagonal fun a => e7MinusculeWeight a i

/-- The matrix carrying a weight vector across the `i`th simple-reflection edge when its
`i`th coordinate is `c`. -/
private def stepMatrix (i : Fin 7) (c : ℤ) : Matrix (Fin 56) (Fin 56) ℤ :=
  fun a b => if e7MinusculeWeight b i = c ∧ a = e7MinusculeReflection i b then 1 else 0

private theorem stepMatrix_apply (i : Fin 7) (c : ℤ) (a b : Fin 56) :
    stepMatrix i c a b =
      if e7MinusculeWeight b i = c ∧ a = e7MinusculeReflection i b then 1 else 0 := rfl

/-- The raising generator `E_i` in the minuscule weight basis. -/
def raisingMatrix (i : Fin 7) : Matrix (Fin 56) (Fin 56) ℤ :=
  stepMatrix i (-1)

/-- The lowering generator `F_i` in the minuscule weight basis. -/
def loweringMatrix (i : Fin 7) : Matrix (Fin 56) (Fin 56) ℤ :=
  stepMatrix i 1

/-- The entrywise formula for the diagonal Cartan generator matrix. -/
@[simp]
theorem cartanMatrix_apply (i : Fin 7) (a b : Fin 56) :
    cartanMatrix i a b = if a = b then e7MinusculeWeight a i else 0 := by
  classical
  rw [cartanMatrix, Matrix.diagonal_apply]

/-- The entrywise formula for the raising generator matrix. -/
@[simp]
theorem raisingMatrix_apply (i : Fin 7) (a b : Fin 56) :
    raisingMatrix i a b =
      if e7MinusculeWeight b i = -1 ∧ a = e7MinusculeReflection i b then 1 else 0 :=
  by rw [raisingMatrix, stepMatrix]

/-- The entrywise formula for the lowering generator matrix. -/
@[simp]
theorem loweringMatrix_apply (i : Fin 7) (a b : Fin 56) :
    loweringMatrix i a b =
      if e7MinusculeWeight b i = 1 ∧ a = e7MinusculeReflection i b then 1 else 0 :=
  by rw [loweringMatrix, stepMatrix]

/-! ## Chevalley--Serre relations -/

private theorem stepMatrix_mul_apply (i j : Fin 7) (c d : ℤ) (a b : Fin 56) :
    (stepMatrix i c * stepMatrix j d) a b =
      if e7MinusculeWeight b j = d ∧
          e7MinusculeWeight (e7MinusculeReflection j b) i = c ∧
          a = e7MinusculeReflection i (e7MinusculeReflection j b) then 1 else 0 := by
  classical
  by_cases h : e7MinusculeWeight b j = d
  · simp [stepMatrix, Matrix.mul_apply, h]
  · simp [stepMatrix, Matrix.mul_apply, h]

@[simp]
private theorem e7MinusculeWeight_reflection_self (i : Fin 7) (a : Fin 56) :
    e7MinusculeWeight (e7MinusculeReflection i a) i = -e7MinusculeWeight a i := by
  have h := congrFun (e7MinusculeWeight_reflection i a) i
  rw [root_e7SimpleIndex] at h
  simp only [Pi.sub_apply, Pi.smul_apply, CartanMatrix.E_diag, smul_eq_mul] at h
  rw [h]
  ring

private theorem e7MinusculeWeight_reflection_apply (i : Fin 7) (a : Fin 56) (j : Fin 7) :
    e7MinusculeWeight (e7MinusculeReflection i a) j =
      e7MinusculeWeight a j - e7MinusculeWeight a i * CartanMatrix.E 7 i j := by
  have h := congrFun (e7MinusculeWeight_reflection i a) j
  rw [root_e7SimpleIndex] at h
  simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h

private theorem cartanMatrix_lie_H (i j : Fin 7) :
    ⁅cartanMatrix i, cartanMatrix j⁆ = 0 := by
  simp [Ring.lie_def, cartanMatrix, Matrix.diagonal_mul_diagonal, mul_comm]

private theorem raisingMatrix_lie_F_self (i : Fin 7) :
    ⁅raisingMatrix i, loweringMatrix i⁆ = cartanMatrix i := by
  rw [Ring.lie_def]
  ext a b
  rw [Matrix.sub_apply, raisingMatrix, loweringMatrix,
    stepMatrix_mul_apply, stepMatrix_mul_apply]
  simp only [e7MinusculeReflection_apply_apply, e7MinusculeWeight_reflection_self,
    e7MinusculeReflection_apply_apply, e7MinusculeWeight_reflection_self]
  rw [cartanMatrix_apply]
  rcases e7MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one b i with h | h | h <;>
    by_cases hab : a = b <;> simp_all

private theorem cartanMatrix_lie_step (i j : Fin 7) (c : ℤ) :
    ⁅cartanMatrix i, stepMatrix j c⁆ =
      (-c * CartanMatrix.E 7 i j) • stepMatrix j c := by
  rw [Ring.lie_def]
  ext a b
  rw [Matrix.sub_apply, cartanMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.smul_apply, stepMatrix_apply, smul_eq_mul]
  by_cases h : e7MinusculeWeight b j = c ∧ a = e7MinusculeReflection j b
  · rcases h with ⟨hweight, rfl⟩
    rw [e7MinusculeWeight_reflection_apply]
    rw [(CartanMatrix.E_isSymm 7).apply]
    simp [hweight]
  · simp [h]

private theorem e7Cartan_apply_of_ne (i j : Fin 7) (hij : i ≠ j) :
    CartanMatrix.E 7 i j = 0 ∨ CartanMatrix.E 7 i j = -1 := by
  rw [CartanMatrix.E_seven_eq]
  fin_cases i <;> fin_cases j <;> simp_all

private theorem e7MinusculeReflection_commute_of_cartan_eq_zero (i j : Fin 7)
    (hij : CartanMatrix.E 7 i j = 0) (a : Fin 56) :
    e7MinusculeReflection i (e7MinusculeReflection j a) =
      e7MinusculeReflection j (e7MinusculeReflection i a) := by
  have hji : CartanMatrix.E 7 j i = 0 := by
    rw [(CartanMatrix.E_isSymm 7).apply]
    exact hij
  apply e7MinusculeWeight_injective
  funext k
  simp only [e7MinusculeWeight_reflection_apply]
  rw [hij, hji]
  ring

private theorem raisingMatrix_lie_F_of_ne (i j : Fin 7) (hij : i ≠ j) :
    ⁅raisingMatrix i, loweringMatrix j⁆ = 0 := by
  have hsymm : CartanMatrix.E 7 j i = CartanMatrix.E 7 i j :=
    (CartanMatrix.E_isSymm 7).apply i j
  rw [Ring.lie_def]
  ext a b
  rw [Matrix.sub_apply, raisingMatrix, loweringMatrix,
    stepMatrix_mul_apply, stepMatrix_mul_apply]
  rcases e7Cartan_apply_of_ne i j hij with hzero | hneg
  · rw [e7MinusculeWeight_reflection_apply, e7MinusculeWeight_reflection_apply,
      hzero, hsymm, hzero, e7MinusculeReflection_commute_of_cartan_eq_zero i j hzero]
    split <;> split <;> simp_all
  · rw [e7MinusculeWeight_reflection_apply, e7MinusculeWeight_reflection_apply,
      hneg, hsymm, hneg]
    rcases e7MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one b i with hi | hi | hi <;>
      rcases e7MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one b j with hj | hj | hj <;>
      simp [hi, hj]

private theorem cartanMatrix_lie_E (i j : Fin 7) :
    ⁅cartanMatrix i, raisingMatrix j⁆ =
      (CartanMatrix.E 7) i j • raisingMatrix j := by
  simpa [raisingMatrix] using cartanMatrix_lie_step i j (-1)

private theorem cartanMatrix_lie_F (i j : Fin 7) :
    ⁅cartanMatrix i, loweringMatrix j⁆ =
      -((CartanMatrix.E 7) i j • loweringMatrix j) := by
  simpa [loweringMatrix, neg_smul] using cartanMatrix_lie_step i j 1

private theorem cartanMatrix_ne_zero (i : Fin 7) : cartanMatrix i ≠ 0 := by
  intro hzero
  have hweight (a : Fin 56) : e7MinusculeWeight a i = 0 := by
    have h := congrFun₂ hzero a a
    simpa using h
  let p : (Fin 7 → ℤ) →ₗ[ℤ] ℤ := LinearMap.proj i
  have hrange : Set.range e7MinusculeWeight ⊆ LinearMap.ker p := by
    rintro _ ⟨a, rfl⟩
    simpa [p] using hweight a
  have htop : (⊤ : Submodule ℤ (Fin 7 → ℤ)) ≤ LinearMap.ker p := by
    rw [← span_range_e7MinusculeWeight_eq_top]
    exact Submodule.span_le.mpr hrange
  have hsingle : Pi.single i 1 ∈ LinearMap.ker p := htop Submodule.mem_top
  simp [p] at hsingle

private theorem isSl2Triple (i : Fin 7) :
    IsSl2Triple (cartanMatrix i) (raisingMatrix i) (loweringMatrix i) where
  h_ne_zero := cartanMatrix_ne_zero i
  lie_e_f := raisingMatrix_lie_F_self i
  lie_h_e_nsmul := by
    rw [cartanMatrix_lie_E, CartanMatrix.E_diag]
    norm_num
  lie_h_f_nsmul := by
    rw [cartanMatrix_lie_F, CartanMatrix.E_diag]
    norm_num

private theorem raisingMatrix_lie_E_lie_E (i j : Fin 7) :
    (ad ℤ _ (raisingMatrix i) ^ (-(CartanMatrix.E 7) i j).toNat)
      ⁅raisingMatrix i, raisingMatrix j⁆ = 0 := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  · exact ad_pow_lie_eq_zero_of_isSl2Triple_of_lie_h_eq_smul_of_lie_f_eq_zero
      (isSl2Triple i)
      (cartanMatrix_lie_E i j)
      (by rw [← lie_skew, raisingMatrix_lie_F_of_ne j i hij.symm, neg_zero])

private theorem loweringMatrix_lie_F_lie_F (i j : Fin 7) :
    (ad ℤ _ (loweringMatrix i) ^ (-(CartanMatrix.E 7) i j).toNat)
      ⁅loweringMatrix i, loweringMatrix j⁆ = 0 := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  · exact ad_pow_lie_eq_zero_of_isSl2Triple_of_lie_h_eq_smul_of_lie_f_eq_zero
      (isSl2Triple i).symm
      (by
        rw [neg_lie, cartanMatrix_lie_F, neg_neg]
        simp only [Int.cast_id])
      (raisingMatrix_lie_F_of_ne i j hij)

/-- The integral minuscule generator matrices satisfy the Chevalley--Serre relations of type
`E₇`, in Bourbaki numbering. -/
theorem isSerreSystem :
    IsSerreSystem ℤ (CartanMatrix.E 7)
      cartanMatrix raisingMatrix loweringMatrix where
  lie_H_H := cartanMatrix_lie_H
  lie_E_F_self := raisingMatrix_lie_F_self
  lie_E_F_of_ne := raisingMatrix_lie_F_of_ne
  lie_H_E := cartanMatrix_lie_E
  lie_H_F := cartanMatrix_lie_F
  ad_pow_lie_E_E := raisingMatrix_lie_E_lie_E
  ad_pow_lie_F_F := loweringMatrix_lie_F_lie_F

/-- The explicit integral fifty-six-dimensional representation of the type-`E₇` Serre Lie
algebra. -/
noncomputable def serreRepresentation :
    Matrix.ToLieAlgebra ℤ (CartanMatrix.E 7) →ₗ⁅ℤ⁆ Matrix (Fin 56) (Fin 56) ℤ :=
  serreLift isSerreSystem

/-- The integral Serre representation sends `H_i` to the Cartan generator matrix. -/
@[simp]
theorem serreRepresentation_serreH (i : Fin 7) :
    serreRepresentation (serreH ℤ (CartanMatrix.E 7) i) = cartanMatrix i :=
  serreLift_serreH isSerreSystem i

/-- The integral Serre representation sends `E_i` to the raising generator matrix. -/
@[simp]
theorem serreRepresentation_serreE (i : Fin 7) :
    serreRepresentation (serreE ℤ (CartanMatrix.E 7) i) = raisingMatrix i :=
  serreLift_serreE isSerreSystem i

/-- The integral Serre representation sends `F_i` to the lowering generator matrix. -/
@[simp]
theorem serreRepresentation_serreF (i : Fin 7) :
    serreRepresentation (serreF ℤ (CartanMatrix.E 7) i) = loweringMatrix i :=
  serreLift_serreF isSerreSystem i

/-- Every minuscule raising generator squares to zero. -/
@[simp]
theorem raisingMatrix_mul_self (i : Fin 7) : raisingMatrix i * raisingMatrix i = 0 := by
  ext a b
  rw [raisingMatrix, stepMatrix_mul_apply,
    e7MinusculeWeight_reflection_self]
  rcases e7MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one b i with h | h | h <;>
    simp [h]

/-- Every minuscule lowering generator squares to zero. -/
@[simp]
theorem loweringMatrix_mul_self (i : Fin 7) : loweringMatrix i * loweringMatrix i = 0 := by
  ext a b
  rw [loweringMatrix, stepMatrix_mul_apply,
    e7MinusculeWeight_reflection_self]
  rcases e7MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one b i with h | h | h <;>
    simp [h]

end TauCeti.E7Minuscule
