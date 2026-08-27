/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.NegativePlane

import TauCeti.Algebra.CentralSimple.Quaternion

/-!
# Eight-step periodicity for real Clifford algebras

The matrix and quaternion recurrences combine to identify adding eight positive generators with
tensoring by sixteen-by-sixteen real matrices.

## Main result

* `nonempty_realCliffordEightPeriodicityEquiv` gives the eight-step equivalence for every real
  signature.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Chapter I.
* [TauCeti SpinRepresentations roadmap, Layer 7](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md#layer-7-real-clifford-algebras-bott-periodicity-and-spinp-q)
-/

public section

open scoped Matrix Quaternion TensorProduct

namespace TauCeti

private abbrev C (p q : ℕ) :=
  _root_.CliffordAlgebra (realCliffordForm p q)

private abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ
private abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ
private abbrev M16 := Matrix (Fin 16) (Fin 16) ℝ

private def matrixTensorSelf (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ ≃ₐ[ℝ]
      Matrix (Fin (n * n)) (Fin (n * n)) ℝ :=
  (Matrix.kroneckerAlgEquiv (Fin n) (Fin n) ℝ).trans
    (Matrix.reindexAlgEquiv ℝ ℝ finProdFinEquiv)

private noncomputable def realCliffordEightPeriodicityEquivImpl (p q : ℕ) :
    _root_.CliffordAlgebra (realCliffordForm (p + 8) q) ≃ₐ[ℝ]
      _root_.CliffordAlgebra (realCliffordForm p q) ⊗[ℝ]
        Matrix (Fin 16) (Fin 16) ℝ := by
  letI : Semiring (ℍ[ℝ] ⊗[ℝ] M2) := Algebra.TensorProduct.instSemiring
  letI : Algebra ℝ (ℍ[ℝ] ⊗[ℝ] M2) := Algebra.TensorProduct.instAlgebra
  letI : Semiring (M2 ⊗[ℝ] (ℍ[ℝ] ⊗[ℝ] M2)) := Algebra.TensorProduct.instSemiring
  letI : Algebra ℝ (M2 ⊗[ℝ] (ℍ[ℝ] ⊗[ℝ] M2)) := Algebra.TensorProduct.instAlgebra
  letI : Semiring (ℍ[ℝ] ⊗[ℝ] (M2 ⊗[ℝ] (ℍ[ℝ] ⊗[ℝ] M2))) :=
    Algebra.TensorProduct.instSemiring
  letI : Algebra ℝ (ℍ[ℝ] ⊗[ℝ] (M2 ⊗[ℝ] (ℍ[ℝ] ⊗[ℝ] M2))) :=
    Algebra.TensorProduct.instAlgebra
  letI : Semiring (C p q ⊗[ℝ] (ℍ[ℝ] ⊗[ℝ] (M2 ⊗[ℝ] (ℍ[ℝ] ⊗[ℝ] M2)))) :=
    Algebra.TensorProduct.instSemiring
  letI : Algebra ℝ (C p q ⊗[ℝ] (ℍ[ℝ] ⊗[ℝ] (M2 ⊗[ℝ] (ℍ[ℝ] ⊗[ℝ] M2)))) :=
    Algebra.TensorProduct.instAlgebra
  let chain : C (p + 8) q ≃ₐ[ℝ]
      C p q ⊗[ℝ] (ℍ[ℝ] ⊗[ℝ] (M2 ⊗[ℝ] (ℍ[ℝ] ⊗[ℝ] M2))) :=
    (realCliffordSignatureSwitchRecurrenceEquiv (p + 6) q).trans <|
      (Algebra.TensorProduct.congr (realCliffordFourNegativeRecurrenceEquiv q (p + 2))
        (AlgEquiv.refl : M2 ≃ₐ[ℝ] M2)).trans <|
      (Algebra.TensorProduct.assoc ℝ ℝ ℝ (C q (p + 2) ⊗[ℝ] M2) ℍ[ℝ] M2).trans <|
      (Algebra.TensorProduct.assoc ℝ ℝ ℝ (C q (p + 2)) M2
        (ℍ[ℝ] ⊗[ℝ] M2)).trans <|
      (Algebra.TensorProduct.congr (realCliffordQuaternionRecurrenceEquiv q p)
        (AlgEquiv.refl : M2 ⊗[ℝ] (ℍ[ℝ] ⊗[ℝ] M2) ≃ₐ[ℝ]
          M2 ⊗[ℝ] (ℍ[ℝ] ⊗[ℝ] M2))).trans <|
      Algebra.TensorProduct.assoc ℝ ℝ ℝ (C p q) ℍ[ℝ]
        (M2 ⊗[ℝ] (ℍ[ℝ] ⊗[ℝ] M2))
  let normalize :
      C p q ⊗[ℝ] (ℍ[ℝ] ⊗[ℝ] (M2 ⊗[ℝ] (ℍ[ℝ] ⊗[ℝ] M2))) ≃ₐ[ℝ]
        C p q ⊗[ℝ] M16 :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : C p q ≃ₐ[ℝ] C p q) <|
      (Algebra.TensorProduct.leftComm ℝ ℍ[ℝ] M2 (ℍ[ℝ] ⊗[ℝ] M2)).trans <|
      (Algebra.TensorProduct.congr (AlgEquiv.refl : M2 ≃ₐ[ℝ] M2)
        (Algebra.TensorProduct.assoc ℝ ℝ ℝ ℍ[ℝ] ℍ[ℝ] M2).symm).trans <|
      (Algebra.TensorProduct.congr (AlgEquiv.refl : M2 ≃ₐ[ℝ] M2)
        (Algebra.TensorProduct.congr Quaternion.tensorSelfAlgEquivMatrix
          (AlgEquiv.refl : M2 ≃ₐ[ℝ] M2))).trans <|
      (Algebra.TensorProduct.leftComm ℝ M2 M4 M2).trans <|
      (Algebra.TensorProduct.congr (AlgEquiv.refl : M4 ≃ₐ[ℝ] M4)
        (matrixTensorSelf 2)).trans (matrixTensorSelf 4)
  exact chain.trans normalize

/-- Eight-step periodicity for standard real Clifford algebras. -/
theorem nonempty_realCliffordEightPeriodicityEquiv (p q : ℕ) :
    Nonempty (_root_.CliffordAlgebra (realCliffordForm (p + 8) q) ≃ₐ[ℝ]
      _root_.CliffordAlgebra (realCliffordForm p q) ⊗[ℝ]
        Matrix (Fin 16) (Fin 16) ℝ) :=
  ⟨realCliffordEightPeriodicityEquivImpl p q⟩

end TauCeti
