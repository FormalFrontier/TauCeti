/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.RootBivectors

/-!
# Serre relations for the type-D spin bivectors

Let `P` be a polarization of a quadratic module and let `b` be a basis of its first isotropic
summand. This file proves that the integral positive, negative, and coroot Clifford products
attached to the Bourbaki simple roots of type `Dₙ` satisfy the complete Chevalley--Serre
relations for `CartanMatrix.D n`.

All relations are integral: they hold over an arbitrary commutative ring, including `ℤ` and
rings of characteristic two. When `2` is invertible, the same generators lie in the canonical
quadratic Lie subalgebra and are packaged there as a second Serre system.

## Main results

* `TauCeti.SpinPolarizationData.isSerreSystem_typeDSimpleRootBivector`: the integral Clifford
  products form a type-`D` Serre system in the ambient Clifford algebra.
* `TauCeti.SpinPolarizationData.isSerreSystem_typeDSimpleRootBivector_quadraticLieSubalgebra`:
  when `2` is invertible, the corresponding subtype-valued system in the quadratic Lie
  subalgebra.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J.-P. Serre, *Complex Semisimple Lie Algebras*, Chapter VI, Appendix.
* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.

This advances the Chevalley--Demazure construction in Layer 9 of the ReductiveGroups roadmap.
-/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti.SpinPolarizationData

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [CommRing K]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
variable {n : Nat} (b : Module.Basis (Fin n) K P.W)

private theorem ι_basis_mul_ι_basis_eq_zero_of_eq (i j : Fin n) (hij : i = j) :
    ι Q (b i : V) * ι Q (b j : V) = 0 := by
  subst j
  rw [ι_sq_scalar]
  simp [P.isotropic_W]

private theorem ι_dualVector_mul_ι_dualVector_eq_zero_of_eq (i j : Fin n) (hij : i = j) :
    ι Q (P.dualVector b i : V) * ι Q (P.dualVector b j : V) = 0 := by
  subst j
  rw [ι_sq_scalar]
  simp [P.isotropic_W']

/-- The ordered Clifford product of a polarized basis vector with its dual. -/
private noncomputable def diagonalProduct (i : Fin n) : CliffordAlgebra Q :=
  ι Q (b i : V) * ι Q (P.dualVector b i : V)

private theorem lie_diagonalProduct_diagonalProduct (i j : Fin n) :
    ⁅P.diagonalProduct b i, P.diagonalProduct b j⁆ = 0 := by
  rw [diagonalProduct, diagonalProduct, lie_ι_mul_ι_ι_mul_ι]
  by_cases hij : i = j
  · subst j
    simp [P.polar_W_eq_zero, P.polar_W'_eq_zero]
  · simp [P.polar_W_eq_zero, P.polar_W'_eq_zero, hij, Ne.symm hij]

private theorem typeDSimpleCorootBivector_eq_diagonalProduct (hn : 2 ≤ n) (i : Fin n) :
    P.typeDSimpleCorootBivector b hn i =
      if h : (i : ℕ) + 1 < n then
        P.diagonalProduct b i - P.diagonalProduct b ⟨(i : ℕ) + 1, h⟩
      else
        P.diagonalProduct b ⟨n - 2, by omega⟩ +
          P.diagonalProduct b ⟨n - 1, by omega⟩ - 1 := by
  rw [P.typeDSimpleCorootBivector_def b]
  rfl

/-- The simple coroot representatives commute over every commutative base ring. -/
@[simp]
theorem lie_typeDSimpleCorootBivector_typeDSimpleCorootBivector
    (hn : 2 ≤ n) (i j : Fin n) :
    ⁅P.typeDSimpleCorootBivector b hn i,
      P.typeDSimpleCorootBivector b hn j⁆ = 0 := by
  rw [P.typeDSimpleCorootBivector_eq_diagonalProduct b hn,
    P.typeDSimpleCorootBivector_eq_diagonalProduct b hn]
  split <;> split <;>
    simp only [lie_sub, sub_lie, lie_add, add_lie,
      P.lie_diagonalProduct_diagonalProduct b, sub_self, add_zero] <;>
    simp [Ring.lie_def]

private theorem lie_diagonalProduct_typeDSimpleRootBivector
    (hn : 4 ≤ n) (i j : Fin n) :
    ⁅P.diagonalProduct b i, P.typeDSimpleRootBivector b (by omega) j⁆ =
      algebraMap ℤ K (DynkinType.typeDSimpleRoot n hn j i) •
        P.typeDSimpleRootBivector b (by omega) j := by
  rw [diagonalProduct, P.typeDSimpleRootBivector_def b]
  split
  · rename_i h
    rw [lie_ι_mul_ι_ι_mul_ι, DynkinType.typeDSimpleRoot_of_add_one_lt hn h]
    simp only [P.polar_W_eq_zero, P.polar_W'_eq_zero, P.polar_dualVector,
      zero_smul, add_zero, sub_zero, Pi.sub_apply, Pi.single_apply]
    by_cases h1 : i = j
    · subst i
      simp [Fin.ext_iff]
    · by_cases h2 : i = ⟨(j : ℕ) + 1, h⟩
      · subst i
        simp [Fin.ext_iff, h1]
      · simp [h1, h2, Ne.symm h1]
  · rename_i h
    rw [lie_ι_mul_ι_ι_mul_ι, DynkinType.typeDSimpleRoot_of_not_add_one_lt hn h]
    simp only [P.polar_W_eq_zero, P.polar_dualVector,
      zero_smul, sub_zero, Pi.add_apply, Pi.single_apply]
    by_cases h1 : i = ⟨n - 2, by omega⟩
    · subst i
      have hne : n - 2 ≠ n - 1 := by omega
      simp [Fin.ext_iff, hne]
    · by_cases h2 : i = ⟨n - 1, by omega⟩
      · subst i
        simp [Fin.ext_iff, h1]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]

private theorem lie_diagonalProduct_typeDSimpleNegativeRootBivector
    (hn : 4 ≤ n) (i j : Fin n) :
    ⁅P.diagonalProduct b i, P.typeDSimpleNegativeRootBivector b (by omega) j⁆ =
      -algebraMap ℤ K (DynkinType.typeDSimpleRoot n hn j i) •
        P.typeDSimpleNegativeRootBivector b (by omega) j := by
  rw [diagonalProduct, P.typeDSimpleNegativeRootBivector_def b]
  split
  · rename_i h
    rw [lie_ι_mul_ι_ι_mul_ι, DynkinType.typeDSimpleRoot_of_add_one_lt hn h]
    simp only [P.polar_W_eq_zero, P.polar_W'_eq_zero, P.polar_dualVector,
      zero_smul, add_zero, sub_zero, Pi.sub_apply, Pi.single_apply]
    by_cases h1 : i = ⟨(j : ℕ) + 1, h⟩
    · subst i
      simp [Fin.ext_iff]
    · by_cases h2 : i = j
      · subst i
        simp [Fin.ext_iff, h1]
      · simp [h1, h2, Ne.symm h1]
  · rename_i h
    rw [lie_ι_mul_ι_ι_mul_ι, DynkinType.typeDSimpleRoot_of_not_add_one_lt hn h]
    simp only [P.polar_W'_eq_zero, P.polar_dualVector, P.polar_dualVector_left,
      zero_smul, add_zero, Pi.add_apply, Pi.single_apply]
    by_cases h1 : i = ⟨n - 1, by omega⟩
    · subst i
      have hne : n - 1 ≠ n - 2 := by omega
      simp [Fin.ext_iff, hne]
    · by_cases h2 : i = ⟨n - 2, by omega⟩
      · subst i
        simp [h1]
      · simp [h1, h2]

/-- The `j`-th positive root representative is an eigenvector of the `i`-th simple coroot with
eigenvalue given by the type-`D` Cartan matrix. -/
@[simp]
theorem lie_typeDSimpleCorootBivector_typeDSimpleRootBivector
    (hn : 4 ≤ n) (i j : Fin n) :
    ⁅P.typeDSimpleCorootBivector b (by omega) i,
        P.typeDSimpleRootBivector b (by omega) j⁆ =
      algebraMap ℤ K (CartanMatrix.D n i j) •
        P.typeDSimpleRootBivector b (by omega) j := by
  rw [P.typeDSimpleCorootBivector_eq_diagonalProduct b (by omega)]
  by_cases hi : (i : ℕ) + 1 < n
  · rw [dite_eq_left hi, sub_lie,
      P.lie_diagonalProduct_typeDSimpleRootBivector b hn,
      P.lie_diagonalProduct_typeDSimpleRootBivector b hn]
    have hdot := DynkinType.typeDSimpleRoot_dotProduct_typeDSimpleRoot hn i j
    rw [DynkinType.typeDSimpleRoot_of_add_one_lt hn hi, sub_dotProduct,
      single_dotProduct, single_dotProduct, one_mul] at hdot
    have hcoeff := congrArg (algebraMap ℤ K) hdot
    simp only [map_sub, one_mul] at hcoeff
    rw [← sub_smul, hcoeff]
  · rw [dite_eq_right hi, sub_lie, add_lie,
      P.lie_diagonalProduct_typeDSimpleRootBivector b hn,
      P.lie_diagonalProduct_typeDSimpleRootBivector b hn]
    have hone : ⁅(1 : CliffordAlgebra Q), P.typeDSimpleRootBivector b (by omega) j⁆ = 0 := by
      simp [Ring.lie_def]
    rw [hone, sub_zero]
    have hdot := DynkinType.typeDSimpleRoot_dotProduct_typeDSimpleRoot hn i j
    rw [DynkinType.typeDSimpleRoot_of_not_add_one_lt hn hi, add_dotProduct,
      single_dotProduct, single_dotProduct, one_mul] at hdot
    have hcoeff := congrArg (algebraMap ℤ K) hdot
    simp only [map_add, one_mul] at hcoeff
    rw [← add_smul, hcoeff]

/-- The `j`-th negative root representative is an eigenvector of the `i`-th simple coroot with
the negative type-`D` Cartan eigenvalue. -/
@[simp]
theorem lie_typeDSimpleCorootBivector_typeDSimpleNegativeRootBivector
    (hn : 4 ≤ n) (i j : Fin n) :
    ⁅P.typeDSimpleCorootBivector b (by omega) i,
        P.typeDSimpleNegativeRootBivector b (by omega) j⁆ =
      -(algebraMap ℤ K (CartanMatrix.D n i j) •
        P.typeDSimpleNegativeRootBivector b (by omega) j) := by
  rw [P.typeDSimpleCorootBivector_eq_diagonalProduct b (by omega)]
  by_cases hi : (i : ℕ) + 1 < n
  · rw [dite_eq_left hi, sub_lie,
      P.lie_diagonalProduct_typeDSimpleNegativeRootBivector b hn,
      P.lie_diagonalProduct_typeDSimpleNegativeRootBivector b hn]
    have hdot := DynkinType.typeDSimpleRoot_dotProduct_typeDSimpleRoot hn i j
    rw [DynkinType.typeDSimpleRoot_of_add_one_lt hn hi, sub_dotProduct,
      single_dotProduct, single_dotProduct, one_mul] at hdot
    rw [← congrArg (algebraMap ℤ K) hdot]
    module
  · rw [dite_eq_right hi, sub_lie, add_lie,
      P.lie_diagonalProduct_typeDSimpleNegativeRootBivector b hn,
      P.lie_diagonalProduct_typeDSimpleNegativeRootBivector b hn]
    have hone : ⁅(1 : CliffordAlgebra Q),
        P.typeDSimpleNegativeRootBivector b (by omega) j⁆ = 0 := by
      simp [Ring.lie_def]
    rw [hone, sub_zero]
    have hdot := DynkinType.typeDSimpleRoot_dotProduct_typeDSimpleRoot hn i j
    rw [DynkinType.typeDSimpleRoot_of_not_add_one_lt hn hi, add_dotProduct,
      single_dotProduct, single_dotProduct, one_mul] at hdot
    rw [← congrArg (algebraMap ℤ K) hdot]
    module

/-- Positive and negative type-`D` simple-root representatives at distinct nodes commute. -/
@[simp]
theorem lie_typeDSimpleRootBivector_typeDSimpleNegativeRootBivector_of_ne
    (hn : 4 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    ⁅P.typeDSimpleRootBivector b (by omega) i,
        P.typeDSimpleNegativeRootBivector b (by omega) j⁆ = 0 := by
  by_cases hi : (i : ℕ) + 1 < n
  · by_cases hj : (j : ℕ) + 1 < n
    · rw [P.typeDSimpleRootBivector_def b, dite_eq_left hi,
        P.typeDSimpleNegativeRootBivector_def b, dite_eq_left hj,
        lie_ι_mul_ι_ι_mul_ι]
      have hijVal : (i : ℕ) ≠ (j : ℕ) := by
        simpa [Fin.ext_iff] using hij
      simp [P.polar_W_eq_zero, P.polar_W'_eq_zero, P.polar_dualVector,
        hij, Ne.symm hijVal]
    · rw [P.typeDSimpleRootBivector_def b, dite_eq_left hi,
        P.typeDSimpleNegativeRootBivector_def b, dite_eq_right hj,
        lie_ι_mul_ι_ι_mul_ι]
      have hiLast : (i : ℕ) ≠ n - 1 := by omega
      by_cases hiPenultimate : (i : ℕ) = n - 2
      · have hnextLast : (⟨(i : ℕ) + 1, hi⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
          ext
          simp only
          omega
        rw [hnextLast]
        have hne : n - 2 ≠ n - 1 := by omega
        simp [P.polar_W'_eq_zero, P.polar_dualVector, P.polar_dualVector_left,
          Fin.ext_iff, hiPenultimate, hne]
      · simp [P.polar_W'_eq_zero, P.polar_dualVector, P.polar_dualVector_left,
          Fin.ext_iff, hiLast, hiPenultimate]
  · by_cases hj : (j : ℕ) + 1 < n
    · rw [P.typeDSimpleRootBivector_def b, dite_eq_right hi,
        P.typeDSimpleNegativeRootBivector_def b, dite_eq_left hj,
        lie_ι_mul_ι_ι_mul_ι]
      have hjLast : (j : ℕ) ≠ n - 1 := by omega
      by_cases hjPenultimate : (j : ℕ) = n - 2
      · have hnextLast : (⟨(j : ℕ) + 1, hj⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
          ext
          simp only
          omega
        rw [hnextLast]
        have hne : n - 2 ≠ n - 1 := by omega
        simp [P.polar_W_eq_zero, P.polar_dualVector, P.polar_dualVector_left,
          Fin.ext_iff, hjPenultimate, Ne.symm hne]
      · simp [P.polar_W_eq_zero, P.polar_dualVector, P.polar_dualVector_left,
          Fin.ext_iff, Ne.symm hjLast, Ne.symm hjPenultimate]
    · exfalso
      apply hij
      ext
      omega

private theorem lie_ι_mul_ι_lie_ι_mul_ι_eq_zero (x y z w : V)
    (hxx : polar Q x x = 0) (hxy : polar Q x y = 0) (hyy : polar Q y y = 0)
    (hxSq : ι Q x * ι Q x = 0) (hySq : ι Q y * ι Q y = 0)
    (hdet : polar Q z y * polar Q x w = polar Q z x * polar Q y w) :
    ⁅ι Q x * ι Q y, ⁅ι Q x * ι Q y, ι Q z * ι Q w⁆⁆ = 0 := by
  have hyx : ι Q y * ι Q x = -(ι Q x * ι Q y) := by
    rw [ι_mul_ι_comm, polar_comm Q y x, hxy, map_zero, zero_sub]
  rw [polar_comm Q y w] at hdet
  rw [lie_ι_mul_ι_ι_mul_ι, lie_sub, lie_add, lie_sub,
    lie_smul, lie_smul, lie_smul, lie_smul,
    lie_ι_mul_ι_ι_mul_ι, lie_ι_mul_ι_ι_mul_ι,
    lie_ι_mul_ι_ι_mul_ι, lie_ι_mul_ι_ι_mul_ι]
  simp only [hxx, hxy, hyy, polar_comm Q y x, zero_smul, add_zero, sub_zero,
    hxSq, hySq, hyx, smul_zero, smul_neg]
  have hcoeff : -(polar Q z y * polar Q x w * 2) +
      polar Q z x * polar Q w y * 2 = 0 := by
    rw [hdet]
    ring
  linear_combination (norm := module) hcoeff • (ι Q x * ι Q y)

/-- Applying the adjoint action of a positive type-`D` simple-root representative twice to any
other positive simple-root representative gives zero. -/
@[simp]
theorem lie_typeDSimpleRootBivector_lie_typeDSimpleRootBivector
    (hn : 4 ≤ n) (i j : Fin n) :
    ⁅P.typeDSimpleRootBivector b (by omega) i,
      ⁅P.typeDSimpleRootBivector b (by omega) i,
        P.typeDSimpleRootBivector b (by omega) j⁆⁆ = 0 := by
  rw [P.typeDSimpleRootBivector_def b, P.typeDSimpleRootBivector_def b]
  split
  · rename_i hi
    split
    · rename_i hj
      apply lie_ι_mul_ι_lie_ι_mul_ι_eq_zero
      · exact P.polar_W_eq_zero _ _
      · simp [P.polar_dualVector, Fin.ext_iff]
      · exact P.polar_W'_eq_zero _ _
      · exact P.ι_basis_mul_ι_basis_eq_zero_of_eq b _ _ rfl
      · exact P.ι_dualVector_mul_ι_dualVector_eq_zero_of_eq b _ _ rfl
      · simp only [P.polar_W_eq_zero, P.polar_W'_eq_zero, P.polar_dualVector,
          mul_zero]
        split_ifs <;> simp only [Fin.ext_iff, zero_mul, one_mul] at *
        omega
    · apply lie_ι_mul_ι_lie_ι_mul_ι_eq_zero
      · exact P.polar_W_eq_zero _ _
      · simp [P.polar_dualVector, Fin.ext_iff]
      · exact P.polar_W'_eq_zero _ _
      · exact P.ι_basis_mul_ι_basis_eq_zero_of_eq b _ _ rfl
      · exact P.ι_dualVector_mul_ι_dualVector_eq_zero_of_eq b _ _ rfl
      · simp [P.polar_W_eq_zero]
  · split
    · apply lie_ι_mul_ι_lie_ι_mul_ι_eq_zero
      · exact P.polar_W_eq_zero _ _
      · exact P.polar_W_eq_zero _ _
      · exact P.polar_W_eq_zero _ _
      · exact P.ι_basis_mul_ι_basis_eq_zero_of_eq b _ _ rfl
      · exact P.ι_basis_mul_ι_basis_eq_zero_of_eq b _ _ rfl
      · simp [P.polar_W_eq_zero]
    · apply lie_ι_mul_ι_lie_ι_mul_ι_eq_zero
      · exact P.polar_W_eq_zero _ _
      · exact P.polar_W_eq_zero _ _
      · exact P.polar_W_eq_zero _ _
      · exact P.ι_basis_mul_ι_basis_eq_zero_of_eq b _ _ rfl
      · exact P.ι_basis_mul_ι_basis_eq_zero_of_eq b _ _ rfl
      · simp [P.polar_W_eq_zero]

/-- Applying the adjoint action of a negative type-`D` simple-root representative twice to any
other negative simple-root representative gives zero. -/
@[simp]
theorem lie_typeDSimpleNegativeRootBivector_lie_typeDSimpleNegativeRootBivector
    (hn : 4 ≤ n) (i j : Fin n) :
    ⁅P.typeDSimpleNegativeRootBivector b (by omega) i,
      ⁅P.typeDSimpleNegativeRootBivector b (by omega) i,
        P.typeDSimpleNegativeRootBivector b (by omega) j⁆⁆ = 0 := by
  rw [P.typeDSimpleNegativeRootBivector_def b, P.typeDSimpleNegativeRootBivector_def b]
  split
  · rename_i hi
    split
    · rename_i hj
      apply lie_ι_mul_ι_lie_ι_mul_ι_eq_zero
      · exact P.polar_W_eq_zero _ _
      · simp [P.polar_dualVector, Fin.ext_iff]
      · exact P.polar_W'_eq_zero _ _
      · exact P.ι_basis_mul_ι_basis_eq_zero_of_eq b _ _ rfl
      · exact P.ι_dualVector_mul_ι_dualVector_eq_zero_of_eq b _ _ rfl
      · simp only [P.polar_W_eq_zero, P.polar_W'_eq_zero, P.polar_dualVector,
          mul_zero]
        split_ifs <;> simp only [Fin.ext_iff, zero_mul, one_mul] at *
        omega
    · apply lie_ι_mul_ι_lie_ι_mul_ι_eq_zero
      · exact P.polar_W_eq_zero _ _
      · simp [P.polar_dualVector, Fin.ext_iff]
      · exact P.polar_W'_eq_zero _ _
      · exact P.ι_basis_mul_ι_basis_eq_zero_of_eq b _ _ rfl
      · exact P.ι_dualVector_mul_ι_dualVector_eq_zero_of_eq b _ _ rfl
      · simp [P.polar_W'_eq_zero]
  · split
    · apply lie_ι_mul_ι_lie_ι_mul_ι_eq_zero
      · exact P.polar_W'_eq_zero _ _
      · exact P.polar_W'_eq_zero _ _
      · exact P.polar_W'_eq_zero _ _
      · exact P.ι_dualVector_mul_ι_dualVector_eq_zero_of_eq b _ _ rfl
      · exact P.ι_dualVector_mul_ι_dualVector_eq_zero_of_eq b _ _ rfl
      · simp [P.polar_W'_eq_zero]
    · apply lie_ι_mul_ι_lie_ι_mul_ι_eq_zero
      · exact P.polar_W'_eq_zero _ _
      · exact P.polar_W'_eq_zero _ _
      · exact P.polar_W'_eq_zero _ _
      · exact P.ι_dualVector_mul_ι_dualVector_eq_zero_of_eq b _ _ rfl
      · exact P.ι_dualVector_mul_ι_dualVector_eq_zero_of_eq b _ _ rfl
      · simp [P.polar_W'_eq_zero]

/-- Whether two vertices are adjacent in the Bourbaki type-`D` Dynkin diagram. -/
private def typeDAdjacent (n : ℕ) (i j : Fin n) : Prop :=
  ((i : ℕ) + 1 = j ∧ (j : ℕ) + 2 < n) ∨
    ((j : ℕ) + 1 = i ∧ (i : ℕ) + 2 < n) ∨
    ((i : ℕ) + 3 = n ∧ ((j : ℕ) + 2 = n ∨ (j : ℕ) + 1 = n)) ∨
    ((j : ℕ) + 3 = n ∧ ((i : ℕ) + 2 = n ∨ (i : ℕ) + 1 = n))

private instance instDecidableTypeDAdjacent (n : ℕ) (i j : Fin n) :
    Decidable (typeDAdjacent n i j) := by
  unfold typeDAdjacent
  infer_instance

private theorem neg_typeDCartan_toNat (hn : 4 ≤ n) (i j : Fin n) :
    (-CartanMatrix.D n i j).toNat = if typeDAdjacent n i j then 1 else 0 := by
  classical
  have hD : CartanMatrix.D n i j = if typeDAdjacent n i j then -1 else if i = j then 2 else 0 := by
    simp only [CartanMatrix.D, Matrix.of_apply, typeDAdjacent]
    split_ifs <;> omega
  rw [hD]
  split_ifs <;> norm_num

private theorem lie_typeDSimpleRootBivector_of_not_adjacent
    (hn : 4 ≤ n) (i j : Fin n) (hij : ¬typeDAdjacent n i j) :
    ⁅P.typeDSimpleRootBivector b (by omega) i,
        P.typeDSimpleRootBivector b (by omega) j⁆ = 0 := by
  have hn1 : n - 1 + 1 = n := by omega
  have hn2 : n - 2 + 2 = n := by omega
  rw [P.typeDSimpleRootBivector_def b, P.typeDSimpleRootBivector_def b]
  split <;> split <;> rw [lie_ι_mul_ι_ι_mul_ι]
  all_goals
    simp only [P.polar_W_eq_zero, P.polar_W'_eq_zero,
      P.polar_dualVector, P.polar_dualVector_left, zero_smul, add_zero, sub_zero,
      Fin.mk.injEq] at *
  all_goals unfold typeDAdjacent at hij
  all_goals split_ifs
  all_goals try simp only [Fin.ext_iff] at *
  all_goals try omega
  all_goals simp only [zero_smul, one_smul, add_zero, zero_add, sub_zero]
  all_goals apply P.ι_basis_mul_ι_basis_eq_zero_of_eq b
  · exact Fin.ext_iff.mpr (by simp only; omega)
  · exact Fin.ext_iff.mpr (by simp only; omega)

private theorem lie_typeDSimpleNegativeRootBivector_of_not_adjacent
    (hn : 4 ≤ n) (i j : Fin n) (hij : ¬typeDAdjacent n i j) :
    ⁅P.typeDSimpleNegativeRootBivector b (by omega) i,
        P.typeDSimpleNegativeRootBivector b (by omega) j⁆ = 0 := by
  have hn1 : n - 1 + 1 = n := by omega
  have hn2 : n - 2 + 2 = n := by omega
  rw [P.typeDSimpleNegativeRootBivector_def b,
    P.typeDSimpleNegativeRootBivector_def b]
  split <;> split <;> rw [lie_ι_mul_ι_ι_mul_ι]
  all_goals
    simp only [P.polar_W_eq_zero, P.polar_W'_eq_zero,
      P.polar_dualVector, P.polar_dualVector_left, zero_smul, add_zero, sub_zero,
      Fin.mk.injEq] at *
  all_goals unfold typeDAdjacent at hij
  all_goals split_ifs
  all_goals try simp only [Fin.ext_iff] at *
  all_goals try omega
  all_goals simp only [zero_smul, one_smul, sub_zero, zero_sub, neg_eq_zero]
  all_goals apply P.ι_dualVector_mul_ι_dualVector_eq_zero_of_eq b
  · exact Fin.ext_iff.mpr (by simp only; omega)
  · exact Fin.ext_iff.mpr (by simp only; omega)

/-- The higher Serre relation for the positive type-`D` spin representatives. -/
@[simp]
theorem ad_pow_lie_typeDSimpleRootBivector_typeDSimpleRootBivector
    (hn : 4 ≤ n) (i j : Fin n) :
    (LieAlgebra.ad K (CliffordAlgebra Q)
        (P.typeDSimpleRootBivector b (by omega) i) ^
      (-CartanMatrix.D n i j).toNat)
        ⁅P.typeDSimpleRootBivector b (by omega) i,
          P.typeDSimpleRootBivector b (by omega) j⁆ = 0 := by
  classical
  rw [neg_typeDCartan_toNat hn]
  by_cases hij : typeDAdjacent n i j
  · rw [ite_eq_left hij, pow_one, LieAlgebra.ad_apply]
    exact P.lie_typeDSimpleRootBivector_lie_typeDSimpleRootBivector b hn i j
  · rw [ite_eq_right hij, pow_zero, Module.End.one_apply]
    exact P.lie_typeDSimpleRootBivector_of_not_adjacent b hn i j hij

/-- The higher Serre relation for the negative type-`D` spin representatives. -/
@[simp]
theorem ad_pow_lie_typeDSimpleNegativeRootBivector_typeDSimpleNegativeRootBivector
    (hn : 4 ≤ n) (i j : Fin n) :
    (LieAlgebra.ad K (CliffordAlgebra Q)
        (P.typeDSimpleNegativeRootBivector b (by omega) i) ^
      (-CartanMatrix.D n i j).toNat)
        ⁅P.typeDSimpleNegativeRootBivector b (by omega) i,
          P.typeDSimpleNegativeRootBivector b (by omega) j⁆ = 0 := by
  classical
  rw [neg_typeDCartan_toNat hn]
  by_cases hij : typeDAdjacent n i j
  · rw [ite_eq_left hij, pow_one, LieAlgebra.ad_apply]
    exact P.lie_typeDSimpleNegativeRootBivector_lie_typeDSimpleNegativeRootBivector b hn i j
  · rw [ite_eq_right hij, pow_zero, Module.End.one_apply]
    exact P.lie_typeDSimpleNegativeRootBivector_of_not_adjacent b hn i j hij

/-- The Bourbaki-numbered coroot and root representatives of the type-`D` spin representation
satisfy the complete Chevalley--Serre relations over every commutative ring. -/
theorem isSerreSystem_typeDSimpleRootBivector (hn : 4 ≤ n) :
    TauCeti.IsSerreSystem K (CartanMatrix.D n)
      (P.typeDSimpleCorootBivector b (by omega))
      (P.typeDSimpleRootBivector b (by omega))
      (P.typeDSimpleNegativeRootBivector b (by omega)) where
  lie_H_H := P.lie_typeDSimpleCorootBivector_typeDSimpleCorootBivector b (by omega)
  lie_E_F_self := P.lie_typeDSimpleRootBivector_typeDSimpleNegativeRootBivector b (by omega)
  lie_E_F_of_ne := P.lie_typeDSimpleRootBivector_typeDSimpleNegativeRootBivector_of_ne b hn
  lie_H_E i j := by
    simpa only [eq_intCast, Int.cast_smul_eq_zsmul] using
      P.lie_typeDSimpleCorootBivector_typeDSimpleRootBivector b hn i j
  lie_H_F i j := by
    simpa only [eq_intCast, Int.cast_smul_eq_zsmul] using
      P.lie_typeDSimpleCorootBivector_typeDSimpleNegativeRootBivector b hn i j
  ad_pow_lie_E_E := P.ad_pow_lie_typeDSimpleRootBivector_typeDSimpleRootBivector b hn
  ad_pow_lie_F_F :=
    P.ad_pow_lie_typeDSimpleNegativeRootBivector_typeDSimpleNegativeRootBivector b hn

variable [Invertible (2 : K)]

/-- The canonical subtype-valued type-`D` Serre system in the quadratic Clifford Lie
subalgebra. -/
theorem isSerreSystem_typeDSimpleRootBivector_quadraticLieSubalgebra (hn : 4 ≤ n) :
    TauCeti.IsSerreSystem K (CartanMatrix.D n)
      (fun i : Fin n ↦ (⟨P.typeDSimpleCorootBivector b (by omega) i,
        P.typeDSimpleCorootBivector_mem_quadraticLieSubalgebra b (by omega) i⟩ :
          quadraticLieSubalgebra Q))
      (fun i : Fin n ↦ (⟨P.typeDSimpleRootBivector b (by omega) i,
        P.typeDSimpleRootBivector_mem_quadraticLieSubalgebra b (by omega) i⟩ :
          quadraticLieSubalgebra Q))
      (fun i : Fin n ↦ (⟨P.typeDSimpleNegativeRootBivector b (by omega) i,
        P.typeDSimpleNegativeRootBivector_mem_quadraticLieSubalgebra b (by omega) i⟩ :
          quadraticLieSubalgebra Q)) := by
  let S := P.isSerreSystem_typeDSimpleRootBivector b hn
  have ad_pow_lie_eq_zero_of_coe (x y : quadraticLieSubalgebra Q) (m : ℕ)
      (h : (LieAlgebra.ad K (CliffordAlgebra Q) (x : CliffordAlgebra Q) ^ m)
        ⁅(x : CliffordAlgebra Q), (y : CliffordAlgebra Q)⁆ = 0) :
      (LieAlgebra.ad K (quadraticLieSubalgebra Q) x ^ m) ⁅x, y⁆ = 0 := by
    apply Subtype.ext
    calc
      ↑((LieAlgebra.ad K (quadraticLieSubalgebra Q) x ^ m) ⁅x, y⁆) =
          (quadraticLieSubalgebra Q).incl
            ((LieAlgebra.ad K (quadraticLieSubalgebra Q) x ^ m) ⁅x, y⁆) := rfl
      _ = (LieAlgebra.ad K (CliffordAlgebra Q)
            ((quadraticLieSubalgebra Q).incl x) ^ m)
          ((quadraticLieSubalgebra Q).incl ⁅x, y⁆) :=
        TauCeti.LieHom.map_ad_pow (quadraticLieSubalgebra Q).incl x m ⁅x, y⁆
      _ = (LieAlgebra.ad K (CliffordAlgebra Q) (x : CliffordAlgebra Q) ^ m)
          ⁅(x : CliffordAlgebra Q), (y : CliffordAlgebra Q)⁆ := by
        simp only [LieHom.map_lie, LieSubalgebra.coe_incl]
      _ = 0 := h
      _ = ↑(0 : quadraticLieSubalgebra Q) := rfl
  refine
    { lie_H_H := fun i j ↦ Subtype.ext (S.lie_H_H i j)
      lie_E_F_self := fun i ↦ Subtype.ext (S.lie_E_F_self i)
      lie_E_F_of_ne := fun i j hij ↦ Subtype.ext (S.lie_E_F_of_ne i j hij)
      lie_H_E := fun i j ↦ Subtype.ext (S.lie_H_E i j)
      lie_H_F := fun i j ↦ Subtype.ext (S.lie_H_F i j)
      ad_pow_lie_E_E := fun i j ↦ ad_pow_lie_eq_zero_of_coe _ _ _ (S.ad_pow_lie_E_E i j)
      ad_pow_lie_F_F := fun i j ↦ ad_pow_lie_eq_zero_of_coe _ _ _ (S.ad_pow_lie_F_F i j) }

end TauCeti.SpinPolarizationData
