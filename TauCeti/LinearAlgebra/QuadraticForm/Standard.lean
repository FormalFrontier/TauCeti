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

variable [Invertible (2 : R)]

private theorem associated_weightedSumSquares_one :
    (QuadraticMap.weightedSumSquares R (1 : n → R)).associated =
      Matrix.toLinearMap₂' R (1 : Matrix n n R) := by
  have h : QuadraticMap.weightedSumSquares R (1 : n → R) =
      Matrix.toQuadraticForm' (1 : Matrix n n R) := by
    ext x
    simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply, Matrix.one_apply,
      QuadraticMap.weightedSumSquares_apply]
  rw [h, Matrix.toQuadraticForm']
  apply QuadraticMap.associated_left_inverse R
  intro x y
  simp [Matrix.toLinearMap₂'_apply, Matrix.one_apply, mul_comm]

/-- The polar bilinear form of the standard quadratic form is twice the identity-matrix form. -/
theorem polarBilin_weightedSumSquares_one :
    QuadraticMap.polarBilin (QuadraticMap.weightedSumSquares R (1 : n → R)) =
      2 • Matrix.toLinearMap₂' R (1 : Matrix n n R) := by
  rw [← QuadraticMap.two_nsmul_associated
    (S := R) (QuadraticMap.weightedSumSquares R (1 : n → R)),
    associated_weightedSumSquares_one]

omit [Fintype n] [DecidableEq n] in
private theorem skewAdjointLieSubalgebra_two_smul
    (B : LinearMap.BilinForm R (n → R)) :
    skewAdjointLieSubalgebra (2 • B) = skewAdjointLieSubalgebra B := by
  ext f
  -- Expose the carrier predicate so the two skew-adjoint conditions can be compared directly.
  change f ∈ (2 • B).skewAdjointSubmodule ↔ f ∈ B.skewAdjointSubmodule
  rw [LinearMap.mem_skewAdjointSubmodule, LinearMap.mem_skewAdjointSubmodule]
  constructor
  · intro hf x y
    apply (isUnit_of_invertible (2 : R)).smul_left_cancel.mp
    simpa using hf x y
  · intro hf x y
    simp [hf x y]

omit [Invertible (2 : R)] in
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

omit [Invertible (2 : R)] in
private noncomputable def skewAdjointLieEquivMatrix (J : Matrix n n R) :
    skewAdjointLieSubalgebra (Matrix.toLinearMap₂' R J) ≃ₗ⁅R⁆
      skewAdjointMatricesLieSubalgebra J :=
  LieEquiv.ofSubalgebras _ _ lieEquivMatrix' <| by
    ext A
    simp only [Submodule.mem_map_equiv, LieSubalgebra.mem_map_submodule]
    -- Expose the inverse-image carrier required by `LieEquiv.ofSubalgebras`.
    change (lieEquivMatrix' (R := R) (n := n)).symm A ∈
      skewAdjointLieSubalgebra (Matrix.toLinearMap₂' R J) ↔
        A ∈ skewAdjointMatricesLieSubalgebra J
    rw [lieEquivMatrix'_symm_apply]
    simpa using (lieEquivMatrix'_mem_skewAdjoint R n J
      ((lieEquivMatrix' (R := R) (n := n)).symm A)).symm

/-- The skew-adjoint endomorphisms of the polar form of the standard quadratic form are Mathlib's
matrix orthogonal Lie algebra. -/
noncomputable def standardSkewAdjointLieEquiv :
    skewAdjointLieSubalgebra
        (QuadraticMap.polarBilin (QuadraticMap.weightedSumSquares R (1 : n → R))) ≃ₗ⁅R⁆
      LieAlgebra.Orthogonal.so n R :=
  (LieEquiv.ofEq _ _ (by
    rw [polarBilin_weightedSumSquares_one, skewAdjointLieSubalgebra_two_smul])).trans
      (skewAdjointLieEquivMatrix R n (1 : Matrix n n R))

@[simp]
theorem coe_standardSkewAdjointLieEquiv_apply
    (f : skewAdjointLieSubalgebra
      (QuadraticMap.polarBilin (QuadraticMap.weightedSumSquares R (1 : n → R)))) :
    ((standardSkewAdjointLieEquiv R n f : LieAlgebra.Orthogonal.so n R) : Matrix n n R) =
      lieEquivMatrix' f := by
  rfl

@[simp]
theorem coe_standardSkewAdjointLieEquiv_symm_apply (A : LieAlgebra.Orthogonal.so n R) :
    (((standardSkewAdjointLieEquiv R n).symm A :
      skewAdjointLieSubalgebra
        (QuadraticMap.polarBilin (QuadraticMap.weightedSumSquares R (1 : n → R)))) :
      Module.End R (n → R)) =
      (lieEquivMatrix' (R := R) (n := n)).symm A := by
  rfl

end TauCeti.QuadraticForm
