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
summand. The positive and negative Clifford bivectors attached to the Bourbaki simple roots of
type `D_n` were constructed in
`TauCeti.RepresentationTheory.Spin.Polarization.TypeD.RootBivectors`. This file proves that,
together with the corresponding diagonal coroot bivectors, they satisfy the complete
Chevalley--Serre relations for `CartanMatrix.D n`.

The result is stated over an arbitrary commutative ring in which `2` is invertible. In
particular it applies over `Q`, where the root bivectors preserve the integral spinor lattice.
It supplies the Serre-system input for mapping the presented type-D Lie algebra, and hence its
Kostant form, into the full-weight integral spin representation used by the type-D
Chevalley--Demazure carrier.

## Main definitions and results

* `TauCeti.SpinPolarizationData.typeDSimpleCorootBivector`: the diagonal Clifford bivector for a
  Bourbaki simple coroot.
* `TauCeti.SpinPolarizationData.isSerreSystem_typeDSimpleRootBivector`: the positive, negative,
  and coroot bivectors form a Serre system for `CartanMatrix.D n`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J.-P. Serre, *Complex Semisimple Lie Algebras*, Chapter VI, Appendix.
* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.

This advances the Chevalley--Demazure construction in Layer 9 of the ReductiveGroups roadmap.
The type-D full-weight carrier consumes these relations to extend its numbered Clifford
generators to the Serre Lie algebra and its Kostant integral form.
-/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti.SpinPolarizationData

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [CommRing K]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
variable {n : Nat} (b : Module.Basis (Fin n) K P.W)
variable [Invertible (2 : K)]

@[simp] private theorem bivector_zero_left (x : V) : bivector Q 0 x = 0 := by
  rw [bivector_def]
  simp

@[simp] private theorem bivector_zero_right (x : V) : bivector Q x 0 = 0 := by
  rw [bivector_def]
  simp

@[simp] private theorem bivector_ite_zero_left (p : Prop) [Decidable p] (x y : V) :
    bivector Q (if p then x else 0) y = if p then bivector Q x y else 0 := by
  by_cases h : p <;> simp [h]

@[simp] private theorem bivector_ite_zero_right (p : Prop) [Decidable p] (x y : V) :
    bivector Q x (if p then y else 0) = if p then bivector Q x y else 0 := by
  by_cases h : p <;> simp [h]

@[simp] private theorem bivector_neg_left (x y : V) : bivector Q (-x) y = -bivector Q x y := by
  let v : Fin 2 → V := ![x, y]
  calc
    bivector Q (-x) y = bivectorAlternating Q ![-x, y] :=
      (bivectorAlternating_apply Q (-x) y).symm
    _ = bivectorAlternating Q (Function.update v 0 (-x)) := by
      congr 1
      funext i
      fin_cases i <;> simp [v]
    _ = -bivectorAlternating Q (Function.update v 0 x) :=
      (bivectorAlternating Q).map_update_neg v 0 x
    _ = -bivectorAlternating Q ![x, y] := by
      congr 1
      congr 1
      funext i
      fin_cases i <;> simp [v]
    _ = -bivector Q x y := congrArg Neg.neg (bivectorAlternating_apply Q x y)

@[simp] private theorem bivector_neg_right (x y : V) : bivector Q x (-y) = -bivector Q x y := by
  let v : Fin 2 → V := ![x, y]
  calc
    bivector Q x (-y) = bivectorAlternating Q ![x, -y] :=
      (bivectorAlternating_apply Q x (-y)).symm
    _ = bivectorAlternating Q (Function.update v 1 (-y)) := by
      congr 1
      funext i
      fin_cases i <;> simp [v]
    _ = -bivectorAlternating Q (Function.update v 1 y) :=
      (bivectorAlternating Q).map_update_neg v 1 y
    _ = -bivectorAlternating Q ![x, y] := by
      congr 1
      congr 1
      funext i
      fin_cases i <;> simp [v]
    _ = -bivector Q x y := congrArg Neg.neg (bivectorAlternating_apply Q x y)

omit [Invertible (2 : K)] in
@[simp] private theorem polar_dualVector_basis (i j : Fin n) :
    polar Q (P.dualVector b i : V) (b j : V) = if j = i then 1 else 0 := by
  rw [polar_comm, P.polar_dualVector]

/-- The diagonal Clifford bivector representing the `i`-th Bourbaki simple coroot of type
`D_n`. Along the chain this is `H_i - H_(i+1)`; at the fork it is
`H_(n-2) + H_(n-1)`. -/
noncomputable def typeDSimpleCorootBivector (hn : 4 ≤ n) (i : Fin n) :
    CliffordAlgebra Q :=
  if h : (i : Nat) + 1 < n then
    P.diagonalBivector b i -
      P.diagonalBivector b ⟨(i : Nat) + 1, h⟩
  else
    P.diagonalBivector b ⟨n - 2, by omega⟩ +
      P.diagonalBivector b ⟨n - 1, by omega⟩

/-- The coordinate formula for a type-D simple coroot bivector. -/
theorem typeDSimpleCorootBivector_def (hn : 4 ≤ n) (i : Fin n) :
    P.typeDSimpleCorootBivector b hn i =
      if h : (i : Nat) + 1 < n then
        P.diagonalBivector b i -
          P.diagonalBivector b ⟨(i : Nat) + 1, h⟩
      else
        P.diagonalBivector b ⟨n - 2, by omega⟩ +
          P.diagonalBivector b ⟨n - 1, by omega⟩ :=
  (rfl)

/-- The simple coroot bivectors commute. -/
@[simp]
theorem lie_typeDSimpleCorootBivector_typeDSimpleCorootBivector
    (hn : 4 <= n) (i j : Fin n) :
    ⁅P.typeDSimpleCorootBivector b hn i, P.typeDSimpleCorootBivector b hn j⁆ = 0 := by
  rw [typeDSimpleCorootBivector_def, typeDSimpleCorootBivector_def]
  split <;> split <;>
    simp only [lie_sub, sub_lie, lie_add, add_lie,
      P.lie_diagonalBivector_diagonalBivector, sub_self, add_zero]

/-- A positive and its corresponding negative type-D root bivector bracket to the simple
coroot bivector. -/
theorem lie_typeDSimpleRootBivector_typeDSimpleNegativeRootBivector_eq_coroot
    (hn : 4 <= n) (i : Fin n) :
    ⁅P.typeDSimpleRootBivector b (by omega) i,
        P.typeDSimpleNegativeRootBivector b (by omega) i⁆ =
      P.typeDSimpleCorootBivector b hn i := by
  rw [P.lie_typeDSimpleRootBivector_typeDSimpleNegativeRootBivector b (by omega),
    typeDSimpleCorootBivector_def]

/-- The `j`-th positive root bivector is an eigenvector of the `i`-th simple coroot bivector
with eigenvalue given by the type-D Cartan matrix. -/
@[simp]
theorem lie_typeDSimpleCorootBivector_typeDSimpleRootBivector
    (hn : 4 <= n) (i j : Fin n) :
    ⁅P.typeDSimpleCorootBivector b hn i,
        P.typeDSimpleRootBivector b (by omega) j⁆ =
      algebraMap Int K (CartanMatrix.D n i j) •
        P.typeDSimpleRootBivector b (by omega) j := by
  rw [typeDSimpleCorootBivector_def]
  by_cases hi : (i : Nat) + 1 < n
  · rw [dite_eq_left hi, sub_lie,
      P.lie_diagonalBivector_typeDSimpleRootBivector b hn j i,
      P.lie_diagonalBivector_typeDSimpleRootBivector b hn j ⟨(i : Nat) + 1, hi⟩]
    have hdot := DynkinType.typeDSimpleRoot_dotProduct_typeDSimpleRoot hn i j
    rw [DynkinType.typeDSimpleRoot_of_add_one_lt hn hi, sub_dotProduct,
      single_dotProduct, single_dotProduct, one_mul] at hdot
    have hcoeff := congrArg (algebraMap Int K) hdot
    simp only [map_sub, one_mul] at hcoeff
    rw [← sub_smul, hcoeff]
  · rw [dite_eq_right hi, add_lie,
      P.lie_diagonalBivector_typeDSimpleRootBivector b hn j ⟨n - 2, by omega⟩,
      P.lie_diagonalBivector_typeDSimpleRootBivector b hn j ⟨n - 1, by omega⟩]
    have hdot := DynkinType.typeDSimpleRoot_dotProduct_typeDSimpleRoot hn i j
    rw [DynkinType.typeDSimpleRoot_of_not_add_one_lt hn hi, add_dotProduct,
      single_dotProduct, single_dotProduct, one_mul] at hdot
    have hcoeff := congrArg (algebraMap Int K) hdot
    simp only [map_add, one_mul] at hcoeff
    rw [← add_smul, hcoeff]

/-- The `j`-th negative root bivector is an eigenvector of the `i`-th simple coroot bivector
with the negative type-D Cartan eigenvalue. -/
@[simp]
theorem lie_typeDSimpleCorootBivector_typeDSimpleNegativeRootBivector
    (hn : 4 <= n) (i j : Fin n) :
    ⁅P.typeDSimpleCorootBivector b hn i,
        P.typeDSimpleNegativeRootBivector b (by omega) j⁆ =
      -(algebraMap Int K (CartanMatrix.D n i j) •
        P.typeDSimpleNegativeRootBivector b (by omega) j) := by
  rw [typeDSimpleCorootBivector_def]
  by_cases hi : (i : Nat) + 1 < n
  · rw [dite_eq_left hi, sub_lie,
      P.lie_diagonalBivector_typeDSimpleNegativeRootBivector b hn j i,
      P.lie_diagonalBivector_typeDSimpleNegativeRootBivector b hn j ⟨(i : Nat) + 1, hi⟩]
    have hdot := DynkinType.typeDSimpleRoot_dotProduct_typeDSimpleRoot hn i j
    rw [DynkinType.typeDSimpleRoot_of_add_one_lt hn hi, sub_dotProduct,
      single_dotProduct, single_dotProduct, one_mul] at hdot
    have hcoeff := congrArg (algebraMap Int K) hdot
    rw [← hcoeff]
    module
  · rw [dite_eq_right hi, add_lie,
      P.lie_diagonalBivector_typeDSimpleNegativeRootBivector b hn j ⟨n - 2, by omega⟩,
      P.lie_diagonalBivector_typeDSimpleNegativeRootBivector b hn j ⟨n - 1, by omega⟩]
    have hdot := DynkinType.typeDSimpleRoot_dotProduct_typeDSimpleRoot hn i j
    rw [DynkinType.typeDSimpleRoot_of_not_add_one_lt hn hi, add_dotProduct,
      single_dotProduct, single_dotProduct, one_mul] at hdot
    have hcoeff := congrArg (algebraMap Int K) hdot
    rw [← hcoeff]
    module

/-- Positive and negative type-D simple-root bivectors at distinct nodes commute. -/
@[simp]
theorem lie_typeDSimpleRootBivector_typeDSimpleNegativeRootBivector_of_ne
    (hn : 4 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    ⁅P.typeDSimpleRootBivector b (by omega) i,
        P.typeDSimpleNegativeRootBivector b (by omega) j⁆ = 0 := by
  by_cases hi : (i : ℕ) + 1 < n
  · by_cases hj : (j : ℕ) + 1 < n
    · rw [P.typeDSimpleRootBivector_of_add_one_lt b (by omega) hi,
        P.typeDSimpleNegativeRootBivector_of_add_one_lt b (by omega) hj,
        lie_bivector_bivector]
      have hnext : (⟨(i : ℕ) + 1, hi⟩ : Fin n) ≠ ⟨(j : ℕ) + 1, hj⟩ := by
        intro h
        apply hij
        ext
        simpa using congrArg Fin.val h
      have hpolar : polar Q (P.dualVector b ⟨(i : ℕ) + 1, hi⟩ : V)
          (b ⟨(j : ℕ) + 1, hj⟩ : V) = 0 := by
        rw [polar_comm, P.polar_dualVector]
        simp [Ne.symm hnext]
      rw [hpolar]
      simp [P.polar_W_eq_zero, P.polar_W'_eq_zero, P.polar_dualVector, hij, bivector_def]
    · rw [P.typeDSimpleRootBivector_of_add_one_lt b (by omega) hi,
        P.typeDSimpleNegativeRootBivector_of_not_add_one_lt b (by omega) hj,
        lie_bivector_bivector]
      have hiLast : (i : ℕ) ≠ n - 1 := by omega
      by_cases hiPenultimate : (i : ℕ) = n - 2
      · have hnextLast : (⟨(i : ℕ) + 1, hi⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
          apply Fin.ext
          change (i : ℕ) + 1 = n - 1
          omega
        rw [hnextLast]
        have hne : n - 2 ≠ n - 1 := by omega
        simp [P.polar_W'_eq_zero, P.polar_dualVector, Fin.ext_iff, hiPenultimate, hne,
          bivector_self]
      · simp [P.polar_W'_eq_zero, P.polar_dualVector, Fin.ext_iff, hiLast,
          hiPenultimate]
  · by_cases hj : (j : ℕ) + 1 < n
    · rw [P.typeDSimpleRootBivector_of_not_add_one_lt b (by omega) hi,
        P.typeDSimpleNegativeRootBivector_of_add_one_lt b (by omega) hj,
        lie_bivector_bivector]
      have hjLast : (j : ℕ) ≠ n - 1 := by omega
      by_cases hjPenultimate : (j : ℕ) = n - 2
      · have hnextLast : (⟨(j : ℕ) + 1, hj⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
          apply Fin.ext
          change (j : ℕ) + 1 = n - 1
          omega
        rw [hnextLast]
        have hne : n - 2 ≠ n - 1 := by omega
        simp [P.polar_W_eq_zero, P.polar_dualVector, Fin.ext_iff, hjPenultimate,
          Ne.symm hne,
          bivector_self]
      · simp [P.polar_W_eq_zero, P.polar_dualVector, Fin.ext_iff, Ne.symm hjLast,
          Ne.symm hjPenultimate]
    · rw [P.typeDSimpleRootBivector_of_not_add_one_lt b (by omega) hi,
        P.typeDSimpleNegativeRootBivector_of_not_add_one_lt b (by omega) hj,
        lie_bivector_bivector]
      exfalso
      apply hij
      apply Fin.ext
      omega

private theorem lie_positiveChainBivector_positiveChainBivector
    {i j : Fin n} (hi : (i : ℕ) + 1 < n) (hj : (j : ℕ) + 1 < n) :
    ⁅bivector Q (b i : V) (P.dualVector b ⟨(i : ℕ) + 1, hi⟩ : V),
        bivector Q (b j : V) (P.dualVector b ⟨(j : ℕ) + 1, hj⟩ : V)⁆ =
      (if (⟨(i : ℕ) + 1, hi⟩ : Fin n) = j then
          bivector Q (b i : V) (P.dualVector b ⟨(j : ℕ) + 1, hj⟩ : V)
        else 0) +
      -(if i = (⟨(j : ℕ) + 1, hj⟩ : Fin n) then
          bivector Q (b j : V) (P.dualVector b ⟨(i : ℕ) + 1, hi⟩ : V)
        else 0) := by
  rw [lie_bivector_bivector]
  by_cases hij : (⟨(i : ℕ) + 1, hi⟩ : Fin n) = j
  · have hji : i ≠ (⟨(j : ℕ) + 1, hj⟩ : Fin n) := by
      intro h
      have hij' := congrArg Fin.val hij
      have h' := congrArg Fin.val h
      simp only at hij' h'
      omega
    simp [P.polar_W_eq_zero, P.polar_W'_eq_zero, P.polar_dualVector,
      P.polar_dualVector_basis b, hij, hji]
  · by_cases hji : i = (⟨(j : ℕ) + 1, hj⟩ : Fin n)
    · simp [P.polar_W_eq_zero, P.polar_W'_eq_zero, P.polar_dualVector,
        P.polar_dualVector_basis b, hji]
      simp only [eq_comm]
    · simp [P.polar_W_eq_zero, P.polar_W'_eq_zero, P.polar_dualVector,
        P.polar_dualVector_basis b, hij, Ne.symm hij, hji]

private theorem lie_positiveChainBivector_lie_positiveChainBivector
    {i j : Fin n} (hi : (i : ℕ) + 1 < n) (hj : (j : ℕ) + 1 < n) :
    ⁅bivector Q (b i : V) (P.dualVector b ⟨(i : ℕ) + 1, hi⟩ : V),
      ⁅bivector Q (b i : V) (P.dualVector b ⟨(i : ℕ) + 1, hi⟩ : V),
        bivector Q (b j : V) (P.dualVector b ⟨(j : ℕ) + 1, hj⟩ : V)⁆⁆ = 0 := by
  rw [P.lie_positiveChainBivector_positiveChainBivector b hi hj]
  by_cases hij : (⟨(i : ℕ) + 1, hi⟩ : Fin n) = j
  · have hji : i ≠ (⟨(j : ℕ) + 1, hj⟩ : Fin n) := by
      intro h
      have hij' := congrArg Fin.val hij
      have h' := congrArg Fin.val h
      simp only at hij' h'
      omega
    have hself : i ≠ (⟨(i : ℕ) + 1, hi⟩ : Fin n) := by
      intro h
      have h' := congrArg Fin.val h
      simp only at h'
      omega
    rw [ite_eq_left hij, ite_eq_right hji, neg_zero, add_zero, lie_bivector_bivector]
    simp [P.polar_W_eq_zero, P.polar_W'_eq_zero, P.polar_dualVector,
      P.polar_dualVector_basis b, hself, hji]
  · by_cases hji : i = (⟨(j : ℕ) + 1, hj⟩ : Fin n)
    · rw [ite_eq_right hij, ite_eq_left hji, zero_add, lie_neg, lie_bivector_bivector]
      have hself : i ≠ (⟨(i : ℕ) + 1, hi⟩ : Fin n) := by
        intro h
        have h' := congrArg Fin.val h
        simp only at h'
        omega
      simp [P.polar_W_eq_zero, P.polar_W'_eq_zero, P.polar_dualVector,
        P.polar_dualVector_basis b, Ne.symm hij, hself]
    · rw [ite_eq_right hij, ite_eq_right hji, neg_zero, add_zero, lie_zero]

/-- Applying the adjoint action of a positive type-D simple-root bivector twice to any other
positive simple-root bivector gives zero. This is the higher Serre relation in the simply-laced
type-D diagram. -/
@[simp]
theorem lie_typeDSimpleRootBivector_lie_typeDSimpleRootBivector
    (hn : 4 ≤ n) (i j : Fin n) :
    ⁅P.typeDSimpleRootBivector b (by omega) i,
      ⁅P.typeDSimpleRootBivector b (by omega) i,
        P.typeDSimpleRootBivector b (by omega) j⁆⁆ = 0 := by
  by_cases hi : (i : ℕ) + 1 < n
  · by_cases hj : (j : ℕ) + 1 < n
    · rw [P.typeDSimpleRootBivector_of_add_one_lt b (by omega) hi,
        P.typeDSimpleRootBivector_of_add_one_lt b (by omega) hj]
      exact P.lie_positiveChainBivector_lie_positiveChainBivector b hi hj
    · rw [P.typeDSimpleRootBivector_of_add_one_lt b (by omega) hi,
        P.typeDSimpleRootBivector_of_not_add_one_lt b (by omega) hj]
      rw [lie_bivector_bivector]
      simp only [polar_dualVector_basis, Fin.mk.injEq, ite_smul, one_smul, zero_smul,
        Nat.pred_eq_succ_iff, lie_add]
      split_ifs <;>
        simp_all only [zero_sub, bivector_neg_right, bivector_neg_left, lie_neg, lie_skew]
      all_goals
        rw [lie_bivector_bivector]
        simp [P.polar_W_eq_zero, P.polar_dualVector_basis b, Fin.ext_iff] <;> omega
  · by_cases hj : (j : ℕ) + 1 < n
    · rw [P.typeDSimpleRootBivector_of_not_add_one_lt b (by omega) hi,
        P.typeDSimpleRootBivector_of_add_one_lt b (by omega) hj]
      rw [lie_bivector_bivector]
      simp [P.polar_W_eq_zero, P.polar_dualVector, Fin.ext_iff]
      simp only [lie_bivector_bivector]
      split_ifs <;> simp [P.polar_W_eq_zero]
    · rw [P.typeDSimpleRootBivector_of_not_add_one_lt b (by omega) hi,
        P.typeDSimpleRootBivector_of_not_add_one_lt b (by omega) hj, lie_self, lie_zero]

private theorem lie_negativeChainBivector_negativeChainBivector
    {i j : Fin n} (hi : (i : ℕ) + 1 < n) (hj : (j : ℕ) + 1 < n) :
    ⁅bivector Q (b ⟨(i : ℕ) + 1, hi⟩ : V) (P.dualVector b i : V),
        bivector Q (b ⟨(j : ℕ) + 1, hj⟩ : V) (P.dualVector b j : V)⁆ =
      (if (⟨(j : ℕ) + 1, hj⟩ : Fin n) = i then
          bivector Q (b ⟨(i : ℕ) + 1, hi⟩ : V) (P.dualVector b j : V)
        else 0) +
      -(if j = (⟨(i : ℕ) + 1, hi⟩ : Fin n) then
          bivector Q (b ⟨(j : ℕ) + 1, hj⟩ : V) (P.dualVector b i : V)
        else 0) := by
  rw [lie_bivector_bivector]
  by_cases hij : j = (⟨(i : ℕ) + 1, hi⟩ : Fin n)
  · have hji : (⟨(j : ℕ) + 1, hj⟩ : Fin n) ≠ i := by
      intro h
      have hij' := congrArg Fin.val hij
      have h' := congrArg Fin.val h
      simp only at hij' h'
      omega
    simp [P.polar_W_eq_zero, P.polar_W'_eq_zero, P.polar_dualVector,
      P.polar_dualVector_basis b, hij]
  · by_cases hji : (⟨(j : ℕ) + 1, hj⟩ : Fin n) = i
    · simp [P.polar_W_eq_zero, P.polar_W'_eq_zero, P.polar_dualVector,
        P.polar_dualVector_basis b, hij, Ne.symm hij, hji]
    · simp [P.polar_W_eq_zero, P.polar_W'_eq_zero, P.polar_dualVector,
        P.polar_dualVector_basis b, hij, Ne.symm hij, hji]

private theorem lie_negativeChainBivector_lie_negativeChainBivector
    {i j : Fin n} (hi : (i : ℕ) + 1 < n) (hj : (j : ℕ) + 1 < n) :
    ⁅bivector Q (b ⟨(i : ℕ) + 1, hi⟩ : V) (P.dualVector b i : V),
      ⁅bivector Q (b ⟨(i : ℕ) + 1, hi⟩ : V) (P.dualVector b i : V),
        bivector Q (b ⟨(j : ℕ) + 1, hj⟩ : V) (P.dualVector b j : V)⁆⁆ = 0 := by
  rw [P.lie_negativeChainBivector_negativeChainBivector b hi hj]
  by_cases hji : (⟨(j : ℕ) + 1, hj⟩ : Fin n) = i
  · have hij : j ≠ (⟨(i : ℕ) + 1, hi⟩ : Fin n) := by
      intro h
      have hji' := congrArg Fin.val hji
      have h' := congrArg Fin.val h
      simp only at hji' h'
      omega
    have hself : i ≠ (⟨(i : ℕ) + 1, hi⟩ : Fin n) := by
      intro h
      have h' := congrArg Fin.val h
      simp only at h'
      omega
    rw [ite_eq_left hji, ite_eq_right hij, neg_zero, add_zero, lie_bivector_bivector]
    simp [P.polar_W_eq_zero, P.polar_W'_eq_zero, P.polar_dualVector,
      P.polar_dualVector_basis b, Ne.symm hij, Ne.symm hself]
  · by_cases hij : j = (⟨(i : ℕ) + 1, hi⟩ : Fin n)
    · rw [ite_eq_right hji, ite_eq_left hij, zero_add, lie_neg, lie_bivector_bivector]
      have hself : i ≠ (⟨(i : ℕ) + 1, hi⟩ : Fin n) := by
        intro h
        have h' := congrArg Fin.val h
        simp only at h'
        omega
      simp [P.polar_W_eq_zero, P.polar_W'_eq_zero, P.polar_dualVector,
        P.polar_dualVector_basis b, hji, Ne.symm hself]
    · rw [ite_eq_right hji, ite_eq_right hij, neg_zero, add_zero, lie_zero]

/-- Applying the adjoint action of a negative type-D simple-root bivector twice to any other
negative simple-root bivector gives zero. -/
@[simp]
theorem lie_typeDSimpleNegativeRootBivector_lie_typeDSimpleNegativeRootBivector
    (hn : 4 ≤ n) (i j : Fin n) :
    ⁅P.typeDSimpleNegativeRootBivector b (by omega) i,
      ⁅P.typeDSimpleNegativeRootBivector b (by omega) i,
        P.typeDSimpleNegativeRootBivector b (by omega) j⁆⁆ = 0 := by
  by_cases hi : (i : ℕ) + 1 < n
  · by_cases hj : (j : ℕ) + 1 < n
    · rw [P.typeDSimpleNegativeRootBivector_of_add_one_lt b (by omega) hi,
        P.typeDSimpleNegativeRootBivector_of_add_one_lt b (by omega) hj]
      exact P.lie_negativeChainBivector_lie_negativeChainBivector b hi hj
    · rw [P.typeDSimpleNegativeRootBivector_of_add_one_lt b (by omega) hi,
        P.typeDSimpleNegativeRootBivector_of_not_add_one_lt b (by omega) hj]
      rw [lie_bivector_bivector]
      simp [P.polar_W'_eq_zero, P.polar_dualVector, Fin.ext_iff]
      split_ifs <;> simp_all <;> try omega
      all_goals
        simp only [lie_bivector_bivector]
        simp [P.polar_W'_eq_zero, P.polar_dualVector_basis b, Fin.ext_iff]
        split_ifs <;> simp_all
  · by_cases hj : (j : ℕ) + 1 < n
    · rw [P.typeDSimpleNegativeRootBivector_of_not_add_one_lt b (by omega) hi,
        P.typeDSimpleNegativeRootBivector_of_add_one_lt b (by omega) hj]
      rw [lie_bivector_bivector]
      simp [P.polar_W'_eq_zero,
        P.polar_dualVector_basis b, Fin.ext_iff]
      simp only [lie_bivector_bivector]
      split_ifs <;> simp [P.polar_W'_eq_zero]
    · rw [P.typeDSimpleNegativeRootBivector_of_not_add_one_lt b (by omega) hi,
        P.typeDSimpleNegativeRootBivector_of_not_add_one_lt b (by omega) hj, lie_self, lie_zero]

/-- Adjacency in the Bourbaki type-D diagram, written in the coordinates used by
`CartanMatrix.D`. -/
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
  by_cases hi : (i : ℕ) + 1 < n
  · by_cases hj : (j : ℕ) + 1 < n
    · rw [P.typeDSimpleRootBivector_of_add_one_lt b (by omega) hi,
        P.typeDSimpleRootBivector_of_add_one_lt b (by omega) hj,
        P.lie_positiveChainBivector_positiveChainBivector b hi hj]
      have hforward : (⟨i.val + 1, hi⟩ : Fin n) ≠ j := by
        intro h
        apply hij
        unfold typeDAdjacent
        have hval := congrArg Fin.val h
        simp only at hval
        omega
      have hbackward : i ≠ (⟨j.val + 1, hj⟩ : Fin n) := by
        intro h
        apply hij
        unfold typeDAdjacent
        have hval := congrArg Fin.val h
        simp only at hval
        omega
      rw [ite_eq_right hforward, ite_eq_right hbackward, neg_zero, add_zero]
    · rw [P.typeDSimpleRootBivector_of_add_one_lt b (by omega) hi,
        P.typeDSimpleRootBivector_of_not_add_one_lt b (by omega) hj,
        lie_bivector_bivector]
      simp only [polar_W_eq_zero, polar_dualVector_basis, Fin.mk.injEq, ite_smul, one_smul,
        zero_smul, Nat.pred_eq_succ_iff]
      split_ifs <;> (simp_all; try omega)
      all_goals
        exfalso
        apply hij
        unfold typeDAdjacent
        omega
  · by_cases hj : (j : ℕ) + 1 < n
    · rw [P.typeDSimpleRootBivector_of_not_add_one_lt b (by omega) hi,
        P.typeDSimpleRootBivector_of_add_one_lt b (by omega) hj,
        lie_bivector_bivector]
      simp only [polar_W_eq_zero, polar_dualVector, Fin.mk.injEq, Nat.pred_eq_succ_iff,
        ite_smul, one_smul, zero_smul]
      split_ifs <;> (simp_all; try omega)
      all_goals
        exfalso
        apply hij
        unfold typeDAdjacent
        omega
    · have hEq : i = j := by apply Fin.ext; omega
      rw [hEq, lie_self]

private theorem lie_typeDSimpleNegativeRootBivector_of_not_adjacent
    (hn : 4 ≤ n) (i j : Fin n) (hij : ¬typeDAdjacent n i j) :
    ⁅P.typeDSimpleNegativeRootBivector b (by omega) i,
        P.typeDSimpleNegativeRootBivector b (by omega) j⁆ = 0 := by
  by_cases hi : (i : ℕ) + 1 < n
  · by_cases hj : (j : ℕ) + 1 < n
    · rw [P.typeDSimpleNegativeRootBivector_of_add_one_lt b (by omega) hi,
        P.typeDSimpleNegativeRootBivector_of_add_one_lt b (by omega) hj,
        P.lie_negativeChainBivector_negativeChainBivector b hi hj]
      have hforward : j ≠ (⟨i.val + 1, hi⟩ : Fin n) := by
        intro h
        apply hij
        unfold typeDAdjacent
        have hval := congrArg Fin.val h
        simp only at hval
        omega
      have hbackward : (⟨j.val + 1, hj⟩ : Fin n) ≠ i := by
        intro h
        apply hij
        unfold typeDAdjacent
        have hval := congrArg Fin.val h
        simp only at hval
        omega
      rw [ite_eq_right hbackward, ite_eq_right hforward, neg_zero, add_zero]
    · rw [P.typeDSimpleNegativeRootBivector_of_add_one_lt b (by omega) hi,
        P.typeDSimpleNegativeRootBivector_of_not_add_one_lt b (by omega) hj,
        lie_bivector_bivector]
      simp only [polar_W'_eq_zero, polar_dualVector, Fin.mk.injEq, ite_smul, one_smul, zero_smul]
      split_ifs <;> (simp_all; try omega)
      all_goals
        by_cases hsibling : (i : ℕ) + 1 = n - 1
        · try omega
          all_goals
            have hpenultimate : i = (⟨n - 2, by omega⟩ : Fin n) := by
              apply Fin.ext
              change (i : ℕ) = n - 2
              omega
            simp only [hpenultimate, bivector_self]
        · exfalso
          apply hij
          unfold typeDAdjacent
          omega
  · by_cases hj : (j : ℕ) + 1 < n
    · rw [P.typeDSimpleNegativeRootBivector_of_not_add_one_lt b (by omega) hi,
        P.typeDSimpleNegativeRootBivector_of_add_one_lt b (by omega) hj,
        lie_bivector_bivector]
      simp only [polar_W'_eq_zero, polar_dualVector_basis, Fin.mk.injEq, ite_smul, one_smul,
        zero_smul]
      split_ifs <;> (simp_all; try omega)
      all_goals
        by_cases hsibling : (j : ℕ) + 1 = n - 1
        · try omega
          all_goals
            have hpenultimate : j = (⟨n - 2, by omega⟩ : Fin n) := by
              apply Fin.ext
              change (j : ℕ) = n - 2
              omega
            simp only [hpenultimate, bivector_self]
        · exfalso
          apply hij
          unfold typeDAdjacent
          omega
    · have hEq : i = j := by apply Fin.ext; omega
      rw [hEq, lie_self]

/-- The higher Serre relation for the positive type-D spin bivectors. -/
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

/-- The higher Serre relation for the negative type-D spin bivectors. -/
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

/-- The Bourbaki-numbered coroot and root bivectors of the type-D spin representation satisfy
the complete Chevalley--Serre relations. -/
theorem isSerreSystem_typeDSimpleRootBivector (hn : 4 ≤ n) :
    TauCeti.IsSerreSystem K (CartanMatrix.D n)
      (P.typeDSimpleCorootBivector b hn)
      (P.typeDSimpleRootBivector b (by omega))
      (P.typeDSimpleNegativeRootBivector b (by omega)) where
  lie_H_H := P.lie_typeDSimpleCorootBivector_typeDSimpleCorootBivector b hn
  lie_E_F_self := P.lie_typeDSimpleRootBivector_typeDSimpleNegativeRootBivector_eq_coroot b hn
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

end TauCeti.SpinPolarizationData
