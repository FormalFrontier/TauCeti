/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.EightPeriodicity

import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Algebra.BrauerGroup.Basic
import TauCeti.Algebra.CentralSimple.Quaternion
import TauCeti.Algebra.CentralSimple.Splitting

/-!
# Classification of real Clifford algebras

The signature recurrences reduce every standard real Clifford algebra to one of eight matrix,
complex, quaternionic, or split matrix models.

## Main results

* `realCliffordResidue` records `(q - p) mod 8` without integer coercions.
* `RealCliffordClassification` states the exact algebra in each residue class.
* `realClifford_classification` proves the classification for every signature.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Chapter I.
-/

public section

open scoped Matrix Quaternion TensorProduct

namespace TauCeti

private abbrev C (p q : ℕ) :=
  _root_.CliffordAlgebra (realCliffordForm p q)

/-- The residue `q - p` modulo eight, represented as a natural number in `[0, 8)`. -/
def realCliffordResidue (p q : ℕ) : ℕ :=
  (q + 8 - p % 8) % 8

@[simp]
private theorem realCliffordResidue_add_both (p q n : ℕ) :
    realCliffordResidue (p + n) (q + n) = realCliffordResidue p q := by
  simp only [realCliffordResidue]
  omega

/-- The exact real algebra classification of the standard Clifford algebra of signature `(p,q)`.
The matrix size is stated uniformly in terms of the total dimension. -/
def RealCliffordClassification (p q : ℕ) : Prop :=
  match realCliffordResidue p q with
  | 0 => Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q) / 2))) (Fin (2 ^ ((p + q) / 2))) ℝ)
  | 1 => Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q - 1) / 2))) (Fin (2 ^ ((p + q - 1) / 2))) ℂ)
  | 2 => Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q - 2) / 2))) (Fin (2 ^ ((p + q - 2) / 2))) ℍ[ℝ])
  | 3 => Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q - 3) / 2))) (Fin (2 ^ ((p + q - 3) / 2))) ℍ[ℝ] ×
        Matrix (Fin (2 ^ ((p + q - 3) / 2))) (Fin (2 ^ ((p + q - 3) / 2))) ℍ[ℝ])
  | 4 => Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q - 2) / 2))) (Fin (2 ^ ((p + q - 2) / 2))) ℍ[ℝ])
  | 5 => Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q - 1) / 2))) (Fin (2 ^ ((p + q - 1) / 2))) ℂ)
  | 6 => Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q) / 2))) (Fin (2 ^ ((p + q) / 2))) ℝ)
  | 7 => Nonempty (_root_.CliffordAlgebra (realCliffordForm p q) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ ((p + q - 1) / 2))) (Fin (2 ^ ((p + q - 1) / 2))) ℝ ×
        Matrix (Fin (2 ^ ((p + q - 1) / 2))) (Fin (2 ^ ((p + q - 1) / 2))) ℝ)
  | _ => False

private noncomputable def realCliffordZeroZeroEquiv :
    _root_.CliffordAlgebra (realCliffordForm 0 0) ≃ₐ[ℝ] ℝ :=
  AlgEquiv.ofAlgHom
    (_root_.CliffordAlgebra.lift (realCliffordForm 0 0)
      ⟨0, fun v ↦ by
        have hv : v = 0 := funext fun i ↦ Fin.elim0 i
        subst v
        simp⟩)
    (Algebra.ofId ℝ _)
    (by ext)
    (by ext v; exact Fin.elim0 v)

private def matrixOneEquiv (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] :
    A ≃ₐ[R] Matrix (Fin 1) (Fin 1) A :=
  (Matrix.uniqueAlgEquiv (R := R) (A := A) (m := Unit)).symm.trans
    (Matrix.reindexAlgEquiv R A (Equiv.ofUnique Unit (Fin 1)))

private def matrixTensorMatrixEquiv (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    (m n : ℕ) :
    Matrix (Fin m) (Fin m) A ⊗[R] Matrix (Fin n) (Fin n) R ≃ₐ[R]
      Matrix (Fin (m * n)) (Fin (m * n)) A :=
  (Matrix.kroneckerTMulFinAlgEquiv m n R A R).trans
    (Algebra.TensorProduct.rid R R A).mapMatrix

private def prodTensorAlgebraEquiv (R A B : Type*) [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] :
    (A × A) ⊗[R] B ≃ₐ[R] (A ⊗[R] B) × (A ⊗[R] B) :=
  (Algebra.TensorProduct.comm R _ _).trans <|
    (Algebra.TensorProduct.prodRight R R B A A).trans <|
    AlgEquiv.prodCongr (Algebra.TensorProduct.comm R B A)
      (Algebra.TensorProduct.comm R B A)

private def matrixProdTensorMatrixEquiv (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    (m n : ℕ) :
    (Matrix (Fin m) (Fin m) A × Matrix (Fin m) (Fin m) A) ⊗[R]
        Matrix (Fin n) (Fin n) R ≃ₐ[R]
      Matrix (Fin (m * n)) (Fin (m * n)) A ×
        Matrix (Fin (m * n)) (Fin (m * n)) A :=
  (prodTensorAlgebraEquiv R (Matrix (Fin m) (Fin m) A)
    (Matrix (Fin n) (Fin n) R)).trans <|
    AlgEquiv.prodCongr (matrixTensorMatrixEquiv R A m n) (matrixTensorMatrixEquiv R A m n)

private noncomputable def complexTensorQuaternionEquiv :
    ℂ ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ := by
  have hdeg : Algebra.deg ℝ ℍ[ℝ] = 2 :=
    Algebra.deg_eq_of_finrank_eq_sq (by rw [Quaternion.finrank_eq_four]; norm_num)
  let e : ℂ ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
    Classical.choice <| hdeg ▸
      (Algebra.isSplittingField_of_isSepClosed ℝ ℍ[ℝ] ℂ).nonempty_algEquiv_matrix_deg ..
  exact e.restrictScalars ℝ

private def matrixTensorAlgebraEquiv (R A B : Type*) [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] (m : ℕ) :
    Matrix (Fin m) (Fin m) A ⊗[R] B ≃ₐ[R]
      Matrix (Fin m) (Fin m) (A ⊗[R] B) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : Matrix (Fin m) (Fin m) A ≃ₐ[R] _)
    (matrixOneEquiv R B)).trans <|
  (Matrix.kroneckerTMulFinAlgEquiv m 1 R A B).trans <|
  Matrix.reindexAlgEquiv R _ (finCongr (Nat.mul_one m))

private def flattenMatrixEquiv (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    (m n : ℕ) :
    Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) A) ≃ₐ[R]
      Matrix (Fin (m * n)) (Fin (m * n)) A :=
  (Matrix.compAlgEquiv (Fin m) (Fin n) A R).trans
    (Matrix.reindexAlgEquiv R A finProdFinEquiv)

private noncomputable def realMatrixTensorQuaternionEquiv (m : ℕ) :
    Matrix (Fin m) (Fin m) ℝ ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ]
      Matrix (Fin m) (Fin m) ℍ[ℝ] :=
  (matrixTensorAlgebraEquiv ℝ ℝ ℍ[ℝ] m).trans
    (Algebra.TensorProduct.lid ℝ ℍ[ℝ]).mapMatrix

private noncomputable def complexMatrixTensorQuaternionEquiv (m : ℕ) :
    Matrix (Fin m) (Fin m) ℂ ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ]
      Matrix (Fin (m * 2)) (Fin (m * 2)) ℂ :=
  (matrixTensorAlgebraEquiv ℝ ℂ ℍ[ℝ] m).trans <|
    complexTensorQuaternionEquiv.mapMatrix.trans <| flattenMatrixEquiv ℝ ℂ m 2

private noncomputable def quaternionMatrixTensorQuaternionEquiv (m : ℕ) :
    Matrix (Fin m) (Fin m) ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ]
      Matrix (Fin (m * 4)) (Fin (m * 4)) ℝ :=
  (matrixTensorAlgebraEquiv ℝ ℍ[ℝ] ℍ[ℝ] m).trans <|
    Quaternion.tensorSelfAlgEquivMatrix.mapMatrix.trans <| flattenMatrixEquiv ℝ ℝ m 4

private noncomputable def realMatrixProdTensorQuaternionEquiv (m : ℕ) :
    (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin m) ℝ) ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ]
      Matrix (Fin m) (Fin m) ℍ[ℝ] × Matrix (Fin m) (Fin m) ℍ[ℝ] :=
  (prodTensorAlgebraEquiv ℝ (Matrix (Fin m) (Fin m) ℝ) ℍ[ℝ]).trans <|
    AlgEquiv.prodCongr (realMatrixTensorQuaternionEquiv m)
      (realMatrixTensorQuaternionEquiv m)

private noncomputable def quaternionMatrixProdTensorQuaternionEquiv (m : ℕ) :
    (Matrix (Fin m) (Fin m) ℍ[ℝ] × Matrix (Fin m) (Fin m) ℍ[ℝ]) ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ]
      Matrix (Fin (m * 4)) (Fin (m * 4)) ℝ ×
        Matrix (Fin (m * 4)) (Fin (m * 4)) ℝ :=
  (prodTensorAlgebraEquiv ℝ (Matrix (Fin m) (Fin m) ℍ[ℝ]) ℍ[ℝ]).trans <|
    AlgEquiv.prodCongr (quaternionMatrixTensorQuaternionEquiv m)
      (quaternionMatrixTensorQuaternionEquiv m)

private def castMatrixTargetEquiv {R S A : Type*} [CommSemiring R]
    [Semiring S] [Semiring A] [Algebra R S] [Algebra R A] {m n : ℕ} (h : m = n)
    (e : S ≃ₐ[R] Matrix (Fin m) (Fin m) A) :
    S ≃ₐ[R] Matrix (Fin n) (Fin n) A :=
  h ▸ e

private def castMatrixProdTargetEquiv {R S A : Type*} [CommSemiring R]
    [Semiring S] [Semiring A] [Algebra R S] [Algebra R A] {m n : ℕ} (h : m = n)
    (e : S ≃ₐ[R]
      Matrix (Fin m) (Fin m) A × Matrix (Fin m) (Fin m) A) :
    S ≃ₐ[R] Matrix (Fin n) (Fin n) A × Matrix (Fin n) (Fin n) A :=
  h ▸ e

private theorem pow_half_sub_add_eight (n d : ℕ) (h : d ≤ n) :
    2 ^ ((n + 8 - d) / 2) = 2 ^ ((n - d) / 2) * 16 := by
  rw [show (n + 8 - d) / 2 = (n - d) / 2 + 4 by omega, pow_add]
  norm_num

private noncomputable def realCliffordPositiveZeroEquiv :
    C 0 0 ≃ₐ[ℝ] Matrix (Fin 1) (Fin 1) ℝ :=
  realCliffordZeroZeroEquiv.trans (matrixOneEquiv ℝ ℝ)

private noncomputable def realCliffordPositiveOneEquiv :
    C 1 0 ≃ₐ[ℝ]
      Matrix (Fin 1) (Fin 1) ℝ × Matrix (Fin 1) (Fin 1) ℝ :=
  realCliffordOneZeroEquivProd.trans <|
    AlgEquiv.prodCongr (matrixOneEquiv ℝ ℝ) (matrixOneEquiv ℝ ℝ)

private noncomputable def realCliffordPositiveTwoEquiv :
    C 2 0 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  (realCliffordSignatureSwitchRecurrenceEquiv 0 0).trans <|
    (Algebra.TensorProduct.congr realCliffordZeroZeroEquiv
      (AlgEquiv.refl : Matrix (Fin 2) (Fin 2) ℝ ≃ₐ[ℝ] _)).trans <|
    Algebra.TensorProduct.lid ℝ _

private noncomputable def realCliffordPositiveThreeEquiv :
    C 3 0 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  (realCliffordSignatureSwitchRecurrenceEquiv 1 0).trans <|
    (Algebra.TensorProduct.congr realCliffordZeroOneEquivComplex
      (AlgEquiv.refl : Matrix (Fin 2) (Fin 2) ℝ ≃ₐ[ℝ] _)).trans <|
    (matrixEquivTensor (Fin 2) ℝ ℂ).symm

private noncomputable def realCliffordPositiveFourEquiv :
    C 4 0 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ] :=
  (realCliffordSignatureSwitchRecurrenceEquiv 2 0).trans <|
    (Algebra.TensorProduct.congr realCliffordZeroTwoEquivQuaternion
      (AlgEquiv.refl : Matrix (Fin 2) (Fin 2) ℝ ≃ₐ[ℝ] _)).trans <|
    (matrixEquivTensor (Fin 2) ℝ ℍ[ℝ]).symm

private noncomputable def realCliffordZeroThreeEquiv :
    C 0 3 ≃ₐ[ℝ]
      Matrix (Fin 1) (Fin 1) ℍ[ℝ] × Matrix (Fin 1) (Fin 1) ℍ[ℝ] :=
  (realCliffordQuaternionRecurrenceEquiv 0 1).trans <|
    (Algebra.TensorProduct.congr realCliffordOneZeroEquivProd
      (AlgEquiv.refl : ℍ[ℝ] ≃ₐ[ℝ] ℍ[ℝ])).trans <|
    (prodTensorAlgebraEquiv ℝ ℝ ℍ[ℝ]).trans <|
    AlgEquiv.prodCongr
      ((Algebra.TensorProduct.lid ℝ ℍ[ℝ]).trans (matrixOneEquiv ℝ ℍ[ℝ]))
      ((Algebra.TensorProduct.lid ℝ ℍ[ℝ]).trans (matrixOneEquiv ℝ ℍ[ℝ]))

private noncomputable def realCliffordPositiveFiveEquiv :
    C 5 0 ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) ℍ[ℝ] × Matrix (Fin 2) (Fin 2) ℍ[ℝ] :=
  (realCliffordSignatureSwitchRecurrenceEquiv 3 0).trans <|
    (Algebra.TensorProduct.congr realCliffordZeroThreeEquiv
      (AlgEquiv.refl : Matrix (Fin 2) (Fin 2) ℝ ≃ₐ[ℝ] _)).trans <|
    matrixProdTensorMatrixEquiv ℝ ℍ[ℝ] 1 2

private noncomputable def realCliffordZeroFourEquiv :
    C 0 4 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ] :=
  (realCliffordQuaternionRecurrenceEquiv 0 2).trans <|
    (Algebra.TensorProduct.congr realCliffordPositiveTwoEquiv
      (AlgEquiv.refl : ℍ[ℝ] ≃ₐ[ℝ] ℍ[ℝ])).trans <|
    realMatrixTensorQuaternionEquiv 2

private noncomputable def realCliffordPositiveSixEquiv :
    C 6 0 ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℍ[ℝ] :=
  (realCliffordSignatureSwitchRecurrenceEquiv 4 0).trans <|
    (Algebra.TensorProduct.congr realCliffordZeroFourEquiv
      (AlgEquiv.refl : Matrix (Fin 2) (Fin 2) ℝ ≃ₐ[ℝ] _)).trans <|
    matrixTensorMatrixEquiv ℝ ℍ[ℝ] 2 2

private noncomputable def realCliffordZeroFiveEquiv :
    C 0 5 ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℂ :=
  (realCliffordQuaternionRecurrenceEquiv 0 3).trans <|
    (Algebra.TensorProduct.congr realCliffordPositiveThreeEquiv
      (AlgEquiv.refl : ℍ[ℝ] ≃ₐ[ℝ] ℍ[ℝ])).trans <|
    complexMatrixTensorQuaternionEquiv 2

private noncomputable def realCliffordPositiveSevenEquiv :
    C 7 0 ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℂ :=
  (realCliffordSignatureSwitchRecurrenceEquiv 5 0).trans <|
    (Algebra.TensorProduct.congr realCliffordZeroFiveEquiv
      (AlgEquiv.refl : Matrix (Fin 2) (Fin 2) ℝ ≃ₐ[ℝ] _)).trans <|
    matrixTensorMatrixEquiv ℝ ℂ 4 2

private theorem realClifford_positiveAxis_base (p : ℕ) (hp : p < 8) :
    RealCliffordClassification p 0 := by
  interval_cases p <;>
    simp only [RealCliffordClassification, realCliffordResidue, zero_add, Nat.zero_mod,
      tsub_zero, Nat.mod_self, Nat.add_zero, Nat.reduceDiv, Nat.pow_zero, Nat.one_mod,
      Nat.add_one_sub_one, Nat.mod_succ, Nat.reduceMod, Nat.reduceSub, Nat.reducePow] <;>
    first
    | exact ⟨realCliffordPositiveZeroEquiv⟩
    | exact ⟨realCliffordPositiveOneEquiv⟩
    | exact ⟨realCliffordPositiveTwoEquiv⟩
    | exact ⟨realCliffordPositiveThreeEquiv⟩
    | exact ⟨realCliffordPositiveFourEquiv⟩
    | exact ⟨realCliffordPositiveFiveEquiv⟩
    | exact ⟨realCliffordPositiveSixEquiv⟩
    | exact ⟨realCliffordPositiveSevenEquiv⟩

private theorem realClifford_positiveAxis_classification (p : ℕ) :
    RealCliffordClassification p 0 := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
      by_cases hp : p < 8
      · exact realClifford_positiveAxis_base p hp
      · obtain ⟨n, rfl⟩ : ∃ n, p = n + 8 := ⟨p - 8, by omega⟩
        have prev := ih n (by omega)
        have hmod : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
        interval_cases hn : n % 8 <;>
          simp only [RealCliffordClassification, realCliffordResidue, zero_add, hn,
            tsub_zero, Nat.mod_self, Nat.add_zero, Nat.add_mod_right, Nat.add_one_sub_one,
            Nat.mod_succ, Nat.reduceSub, Nat.reduceMod, Nat.one_mod] at prev ⊢
        all_goals obtain ⟨e⟩ := prev
        all_goals
          refine ⟨(realCliffordEightPeriodicityEquiv n 0).trans
            ((Algebra.TensorProduct.congr e
              (AlgEquiv.refl : Matrix (Fin 16) (Fin 16) ℝ ≃ₐ[ℝ] _)).trans ?_)⟩
        · exact castMatrixTargetEquiv (pow_half_sub_add_eight n 0 (by omega)).symm
            (matrixTensorMatrixEquiv ℝ ℝ (2 ^ (n / 2)) 16)
        · exact castMatrixProdTargetEquiv (pow_half_sub_add_eight n 1 (by omega)).symm
            (matrixProdTensorMatrixEquiv ℝ ℝ (2 ^ ((n - 1) / 2)) 16)
        · exact castMatrixTargetEquiv (pow_half_sub_add_eight n 0 (by omega)).symm
            (matrixTensorMatrixEquiv ℝ ℝ (2 ^ (n / 2)) 16)
        · exact castMatrixTargetEquiv (pow_half_sub_add_eight n 1 (by omega)).symm
            (matrixTensorMatrixEquiv ℝ ℂ (2 ^ ((n - 1) / 2)) 16)
        · exact castMatrixTargetEquiv (pow_half_sub_add_eight n 2 (by omega)).symm
            (matrixTensorMatrixEquiv ℝ ℍ[ℝ] (2 ^ ((n - 2) / 2)) 16)
        · exact castMatrixProdTargetEquiv (pow_half_sub_add_eight n 3 (by omega)).symm
            (matrixProdTensorMatrixEquiv ℝ ℍ[ℝ] (2 ^ ((n - 3) / 2)) 16)
        · exact castMatrixTargetEquiv (pow_half_sub_add_eight n 2 (by omega)).symm
            (matrixTensorMatrixEquiv ℝ ℍ[ℝ] (2 ^ ((n - 2) / 2)) 16)
        · exact castMatrixTargetEquiv (pow_half_sub_add_eight n 1 (by omega)).symm
            (matrixTensorMatrixEquiv ℝ ℂ (2 ^ ((n - 1) / 2)) 16)

private theorem realClifford_negativeAxis_classification (q : ℕ) :
    RealCliffordClassification 0 q := by
  rcases q with _ | _ | n
  · exact realClifford_positiveAxis_classification 0
  · simp only [RealCliffordClassification, realCliffordResidue, zero_add, Nat.reduceAdd,
      Nat.zero_mod, tsub_zero, Nat.reduceMod, Nat.add_one_sub_one, Nat.reduceDiv, Nat.pow_zero]
    exact ⟨realCliffordZeroOneEquivComplex.trans (matrixOneEquiv ℝ ℂ)⟩
  · have prev := realClifford_positiveAxis_classification n
    have hmod : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
    interval_cases hn : n % 8 <;>
      simp only [RealCliffordClassification, realCliffordResidue, zero_add, hn, tsub_zero,
        Nat.mod_self, Nat.add_zero, Nat.zero_mod, Nat.add_mod_right, Nat.add_mod, Nat.one_mod,
        Nat.reduceAdd, Nat.reduceMod, Nat.add_one_sub_one, Nat.add_succ_sub_one,
        Nat.mod_succ] at prev ⊢
    all_goals obtain ⟨e⟩ := prev
    all_goals
      refine ⟨(realCliffordQuaternionRecurrenceEquiv 0 n).trans
        ((Algebra.TensorProduct.congr e (AlgEquiv.refl : ℍ[ℝ] ≃ₐ[ℝ] ℍ[ℝ])).trans ?_)⟩
    · have hsize : 2 ^ (n / 2) = 2 ^ ((0 + (n + 1 + 1) - 2) / 2) := by
        congr 1
        omega
      exact castMatrixTargetEquiv hsize (realMatrixTensorQuaternionEquiv (2 ^ (n / 2)))
    · have hsize : 2 ^ ((n - 1) / 2) = 2 ^ ((0 + (n + 1 + 1) - 3) / 2) := by
        congr 1
        omega
      exact castMatrixProdTargetEquiv hsize
        (realMatrixProdTensorQuaternionEquiv (2 ^ ((n - 1) / 2)))
    · have hsize : 2 ^ (n / 2) = 2 ^ ((0 + (n + 1 + 1) - 2) / 2) := by
        congr 1
        omega
      exact castMatrixTargetEquiv hsize (realMatrixTensorQuaternionEquiv (2 ^ (n / 2)))
    · have hsize : 2 ^ ((n - 1) / 2) * 2 = 2 ^ ((0 + (n + 1)) / 2) := by
        rw [show (0 + (n + 1)) / 2 = (n - 1) / 2 + 1 by omega, pow_add]
        norm_num
      exact castMatrixTargetEquiv hsize
        (complexMatrixTensorQuaternionEquiv (2 ^ ((n - 1) / 2)))
    · have hsize : 2 ^ ((n - 2) / 2) * 4 = 2 ^ ((0 + (n + 1 + 1)) / 2) := by
        rw [show (0 + (n + 1 + 1)) / 2 = (n - 2) / 2 + 2 by omega, pow_add]
        norm_num
      exact castMatrixTargetEquiv hsize
        (quaternionMatrixTensorQuaternionEquiv (2 ^ ((n - 2) / 2)))
    · have hsize : 2 ^ ((n - 3) / 2) * 4 = 2 ^ ((0 + (n + 1)) / 2) := by
        rw [show (0 + (n + 1)) / 2 = (n - 3) / 2 + 2 by omega, pow_add]
        norm_num
      exact castMatrixProdTargetEquiv hsize
        (quaternionMatrixProdTensorQuaternionEquiv (2 ^ ((n - 3) / 2)))
    · have hsize : 2 ^ ((n - 2) / 2) * 4 = 2 ^ ((0 + (n + 1 + 1)) / 2) := by
        rw [show (0 + (n + 1 + 1)) / 2 = (n - 2) / 2 + 2 by omega, pow_add]
        norm_num
      exact castMatrixTargetEquiv hsize
        (quaternionMatrixTensorQuaternionEquiv (2 ^ ((n - 2) / 2)))
    · have hsize : 2 ^ ((n - 1) / 2) * 2 = 2 ^ ((0 + (n + 1)) / 2) := by
        rw [show (0 + (n + 1)) / 2 = (n - 1) / 2 + 1 by omega, pow_add]
        norm_num
      exact castMatrixTargetEquiv hsize
        (complexMatrixTensorQuaternionEquiv (2 ^ ((n - 1) / 2)))

private theorem realCliffordClassification_add_both (p q n : ℕ)
    (h : RealCliffordClassification p q) :
    RealCliffordClassification (p + n) (q + n) := by
  rw [RealCliffordClassification, realCliffordResidue_add_both]
  rw [RealCliffordClassification] at h
  generalize hr : realCliffordResidue p q = r at h
  have hrlt : r < 8 := by
    rw [← hr]
    exact Nat.mod_lt _ (by norm_num)
  interval_cases r <;> simp only at h ⊢
  all_goals obtain ⟨e⟩ := h
  all_goals
    refine ⟨(realCliffordBottIterEquiv p q n).trans
      ((Algebra.TensorProduct.congr e
        (AlgEquiv.refl : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ ≃ₐ[ℝ] _)).trans ?_)⟩
  · have hsize : 2 ^ ((p + q) / 2) * 2 ^ n = 2 ^ (((p + n) + (q + n)) / 2) := by
      rw [← pow_add]
      congr 1
      omega
    exact castMatrixTargetEquiv hsize
      (matrixTensorMatrixEquiv ℝ ℝ (2 ^ ((p + q) / 2)) (2 ^ n))
  · have hsize : 2 ^ ((p + q - 1) / 2) * 2 ^ n =
        2 ^ (((p + n) + (q + n) - 1) / 2) := by
      rw [← pow_add]
      congr 1
      simp [realCliffordResidue] at hr
      omega
    exact castMatrixTargetEquiv hsize
      (matrixTensorMatrixEquiv ℝ ℂ (2 ^ ((p + q - 1) / 2)) (2 ^ n))
  · have hsize : 2 ^ ((p + q - 2) / 2) * 2 ^ n =
        2 ^ (((p + n) + (q + n) - 2) / 2) := by
      rw [← pow_add]
      congr 1
      simp [realCliffordResidue] at hr
      omega
    exact castMatrixTargetEquiv hsize
      (matrixTensorMatrixEquiv ℝ ℍ[ℝ] (2 ^ ((p + q - 2) / 2)) (2 ^ n))
  · have hsize : 2 ^ ((p + q - 3) / 2) * 2 ^ n =
        2 ^ (((p + n) + (q + n) - 3) / 2) := by
      rw [← pow_add]
      congr 1
      simp [realCliffordResidue] at hr
      omega
    exact castMatrixProdTargetEquiv hsize
      (matrixProdTensorMatrixEquiv ℝ ℍ[ℝ] (2 ^ ((p + q - 3) / 2)) (2 ^ n))
  · have hsize : 2 ^ ((p + q - 2) / 2) * 2 ^ n =
        2 ^ (((p + n) + (q + n) - 2) / 2) := by
      rw [← pow_add]
      congr 1
      simp [realCliffordResidue] at hr
      omega
    exact castMatrixTargetEquiv hsize
      (matrixTensorMatrixEquiv ℝ ℍ[ℝ] (2 ^ ((p + q - 2) / 2)) (2 ^ n))
  · have hsize : 2 ^ ((p + q - 1) / 2) * 2 ^ n =
        2 ^ (((p + n) + (q + n) - 1) / 2) := by
      rw [← pow_add]
      congr 1
      simp [realCliffordResidue] at hr
      omega
    exact castMatrixTargetEquiv hsize
      (matrixTensorMatrixEquiv ℝ ℂ (2 ^ ((p + q - 1) / 2)) (2 ^ n))
  · have hsize : 2 ^ ((p + q) / 2) * 2 ^ n = 2 ^ (((p + n) + (q + n)) / 2) := by
      rw [← pow_add]
      congr 1
      omega
    exact castMatrixTargetEquiv hsize
      (matrixTensorMatrixEquiv ℝ ℝ (2 ^ ((p + q) / 2)) (2 ^ n))
  · have hsize : 2 ^ ((p + q - 1) / 2) * 2 ^ n =
        2 ^ (((p + n) + (q + n) - 1) / 2) := by
      rw [← pow_add]
      congr 1
      simp [realCliffordResidue] at hr
      omega
    exact castMatrixProdTargetEquiv hsize
      (matrixProdTensorMatrixEquiv ℝ ℝ (2 ^ ((p + q - 1) / 2)) (2 ^ n))

/-- The real Clifford algebra of every finite signature is the full matrix algebra, complex
matrix algebra, quaternionic matrix algebra, or split algebra prescribed by `(q - p) mod 8`. -/
theorem realClifford_classification (p q : ℕ) :
    RealCliffordClassification p q := by
  rcases le_total p q with hpq | hqp
  · have h := realCliffordClassification_add_both 0 (q - p) p
      (realClifford_negativeAxis_classification (q - p))
    simpa [Nat.sub_add_cancel hpq] using h
  · have h := realCliffordClassification_add_both (p - q) 0 q
      (realClifford_positiveAxis_classification (p - q))
    simpa [Nat.sub_add_cancel hqp] using h

end TauCeti
