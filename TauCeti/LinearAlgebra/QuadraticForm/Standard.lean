/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# The orthogonal Lie algebra of the standard quadratic form

Mathlib's standard quadratic form on `n → R` is
`QuadraticMap.weightedSumSquares R (1 : n → R)`. When `2` is invertible, its polar bilinear form
is twice the identity-matrix form. Scaling a bilinear form by an invertible scalar does not change
its skew-adjoint endomorphisms, so Mathlib's endomorphism-to-matrix equivalence identifies those
endomorphisms with `LieAlgebra.Orthogonal.so n R`.

This supplies the coordinate bridge used in the standard-form statement that exterior bivectors
are the orthogonal Lie algebra. It does not choose a basis for an abstract quadratic module.

## Main results

* `TauCeti.QuadraticForm.polarBilin_weightedSumSquares_one`: the polar form of the sum of squares
  is twice the identity-matrix form.
* `TauCeti.QuadraticForm.standardSkewAdjointLieEquiv`: the Lie equivalence from the skew-adjoint
  endomorphisms of its polar form to Mathlib's matrix orthogonal Lie algebra.

## References

* [Tau Ceti Roadmap](https://github.com/TauCetiProject/TauCetiRoadmap), Representation Theory / Spin
  Representations, Layer 3, "Bivectors as a Lie subalgebra".
-/

public section

open scoped Matrix

universe u

namespace TauCeti.QuadraticForm

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type u) (n : Type*) [CommRing R] [Fintype n] [DecidableEq n]

/-- The polar bilinear form of the standard quadratic form is twice the identity-matrix form. -/
@[simp]
theorem polarBilin_weightedSumSquares_one :
    QuadraticMap.polarBilin (QuadraticMap.weightedSumSquares R (1 : n → R)) =
      2 • Matrix.toLinearMap₂' R (1 : Matrix n n R) := by
  have h : QuadraticMap.weightedSumSquares R (1 : n → R) =
      Matrix.toQuadraticForm' (1 : Matrix n n R) := by
    ext x
    simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply, Matrix.one_apply,
      QuadraticMap.weightedSumSquares_apply]
  rw [h, Matrix.toQuadraticForm', LinearMap.BilinMap.polarBilin_toQuadraticMap]
  ext x y
  simp [Matrix.toLinearMap₂'_apply, Matrix.one_apply, mul_comm, two_mul]

private theorem lieEquivMatrix'_mem_skewAdjoint (J : Matrix n n R)
    (f : Module.End R (n → R)) :
    lieEquivMatrix' f ∈ skewAdjointMatricesLieSubalgebra J ↔
      f ∈ skewAdjointLieSubalgebra (Matrix.toLinearMap₂' R J) := by
  rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  -- Expose matrix skew-adjointness as the `IsAdjointPair` relation used by the bridge theorem.
  change Matrix.IsAdjointPair J J (LinearMap.toMatrix' f) (-LinearMap.toMatrix' f) ↔
    f ∈ (Matrix.toLinearMap₂' R J).skewAdjointSubmodule
  rw [LinearMap.mem_skewAdjointSubmodule]
  -- Expose linear-map skew-adjointness in the same adjoint-pair representation.
  change Matrix.IsAdjointPair J J (LinearMap.toMatrix' f) (-LinearMap.toMatrix' f) ↔
    LinearMap.IsAdjointPair (Matrix.toLinearMap₂' R J) (Matrix.toLinearMap₂' R J) f (-f)
  simpa using (isAdjointPair_toLinearMap₂' (R := R) (J := J) (J' := J)
    (A := LinearMap.toMatrix' f) (A' := -(LinearMap.toMatrix' f))).symm

variable [Invertible (2 : R)]

/-- The skew-adjoint endomorphisms of the polar form of the standard quadratic form are Mathlib's
matrix orthogonal Lie algebra. -/
noncomputable def standardSkewAdjointLieEquiv :
    skewAdjointLieSubalgebra
        (QuadraticMap.polarBilin (QuadraticMap.weightedSumSquares R (1 : n → R))) ≃ₗ⁅R⁆
      LieAlgebra.Orthogonal.so n R :=
  LieEquiv.ofSubalgebras _ _ lieEquivMatrix' <| by
    ext A
    simp only [Submodule.mem_map_equiv, LieSubalgebra.mem_map_submodule]
    -- Expose the inverse-image carrier required by the subalgebra restriction.
    change (lieEquivMatrix' (R := R) (n := n)).symm A ∈
      skewAdjointLieSubalgebra
          (QuadraticMap.polarBilin (QuadraticMap.weightedSumSquares R (1 : n → R))) ↔
        A ∈ LieAlgebra.Orthogonal.so n R
    rw [polarBilin_weightedSumSquares_one, ← Nat.cast_smul_eq_nsmul R]
    rw [← ((Matrix.toLinearMap₂' R : Matrix n n R ≃ₗ[R]
      LinearMap.BilinForm R (n → R)).map_smul (↑(2 : ℕ) : R) (1 : Matrix n n R))]
    change (lieEquivMatrix' (R := R) (n := n)).symm A ∈ skewAdjointLieSubalgebra
      (Matrix.toLinearMap₂' R ((2 : R) • (1 : Matrix n n R))) ↔ _
    conv_lhs => rw [← val_unitOfInvertible (2 : R)]
    rw [← Units.smul_def, ← lieEquivMatrix'_mem_skewAdjoint R n
      ((unitOfInvertible (2 : R)) • (1 : Matrix n n R)), LieAlgebra.Orthogonal.so]
    simpa using (mem_skewAdjointMatricesLieSubalgebra_unit_smul
      (unitOfInvertible (2 : R)) (1 : Matrix n n R) A)

/-- The standard skew-adjoint equivalence sends an endomorphism to its matrix. -/
@[simp]
theorem coe_standardSkewAdjointLieEquiv_apply
    (f : skewAdjointLieSubalgebra
      (QuadraticMap.polarBilin (QuadraticMap.weightedSumSquares R (1 : n → R)))) :
    ((standardSkewAdjointLieEquiv R n f : LieAlgebra.Orthogonal.so n R) : Matrix n n R) =
      lieEquivMatrix' f := by
  rw [standardSkewAdjointLieEquiv, LieEquiv.ofSubalgebras_apply]

/-- The inverse standard skew-adjoint equivalence sends a matrix to its endomorphism. -/
@[simp]
theorem coe_standardSkewAdjointLieEquiv_symm_apply (A : LieAlgebra.Orthogonal.so n R) :
    (((standardSkewAdjointLieEquiv R n).symm A :
      skewAdjointLieSubalgebra
        (QuadraticMap.polarBilin (QuadraticMap.weightedSumSquares R (1 : n → R)))) :
      Module.End R (n → R)) =
      (lieEquivMatrix' (R := R) (n := n)).symm A := by
  rw [standardSkewAdjointLieEquiv, LieEquiv.ofSubalgebras_symm_apply]

end TauCeti.QuadraticForm
