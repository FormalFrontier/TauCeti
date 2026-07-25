/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Orthogonal matrices as linear isometries

This file relates Mathlib's matrix orthogonal group to the linear isometry group of the
corresponding Euclidean space.

## Main definitions

* `TauCeti.orthogonalGroupToLinearIsometryEquiv`: the group homomorphism from orthogonal
  matrices to linear isometry equivalences of Euclidean space.
-/

public section

namespace TauCeti

open scoped EuclideanSpace

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An orthogonal matrix acts on Euclidean space as a linear isometry equivalence. -/
noncomputable def orthogonalGroupToLinearIsometryEquiv :
    Matrix.orthogonalGroup ι ℝ →*
      (EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) := by
  classical
  exact
    { toFun := fun A =>
        { toLinearEquiv :=
            (WithLp.linearEquiv 2 ℝ (ι → ℝ)).trans
              ((Matrix.UnitaryGroup.toLinearEquiv A).trans
                (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm)
          norm_map' := fun x => by
            apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
            rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
            simp only [Real.norm_eq_abs, sq_abs]
            -- Unfold the composite through `WithLp` to expose the matrix action; Mathlib has no
            -- application lemma for this particular conjugate of `UnitaryGroup.toLinearEquiv`.
            change ∑ i, ((A : Matrix ι ι ℝ).mulVec x.ofLp i) ^ 2 =
              ∑ i, (x.ofLp i) ^ 2
            simp only [pow_two]
            rw [← dotProduct, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
              (Matrix.mem_orthogonalGroup_iff' ι ℝ).1 A.2, Matrix.vecMul_one]
            rfl }
      map_one' := _root_.LinearIsometryEquiv.ext fun x => by
        -- Reduce the same `WithLp` conjugate to its matrix action.
        change WithLp.toLp 2 ((1 : Matrix ι ι ℝ).mulVec x.ofLp) = x
        rw [Matrix.one_mulVec, WithLp.toLp_ofLp]
      map_mul' := fun A B => _root_.LinearIsometryEquiv.ext fun x => by
        -- Reduce both sides to matrix actions before using compatibility of `mulVec` with `(*)`.
        change WithLp.toLp 2 (((A * B : Matrix.orthogonalGroup ι ℝ) :
          Matrix ι ι ℝ).mulVec x.ofLp) =
            WithLp.toLp 2 ((A : Matrix ι ι ℝ).mulVec
              ((B : Matrix ι ι ℝ).mulVec x.ofLp))
        exact congrArg (WithLp.toLp 2) (Matrix.mulVec_mulVec _ _ _).symm }

/-- The linear isometry equivalence associated to an orthogonal matrix acts by matrix-vector
multiplication in Euclidean coordinates. -/
@[simp]
theorem orthogonalGroupToLinearIsometryEquiv_apply
    (A : Matrix.orthogonalGroup ι ℝ) (x : EuclideanSpace ℝ ι) :
    orthogonalGroupToLinearIsometryEquiv A x =
      WithLp.toLp 2 ((A : Matrix ι ι ℝ).mulVec x.ofLp) := by
  classical
  rfl

/-- The conversion from orthogonal matrices to linear isometry equivalences is injective. -/
theorem orthogonalGroupToLinearIsometryEquiv_injective :
    Function.Injective
      (orthogonalGroupToLinearIsometryEquiv :
        Matrix.orthogonalGroup ι ℝ → EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) := by
  intro A B h
  apply Subtype.ext
  apply Matrix.toEuclideanLin.injective
  exact LinearMap.ext fun x => by
    simpa only [orthogonalGroupToLinearIsometryEquiv_apply, Matrix.toLpLin_apply] using
      _root_.LinearIsometryEquiv.congr_fun h x

end

end TauCeti
