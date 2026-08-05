/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
-- supplies the `FaithfulSMul PGL(2, ℝ) ℍ` instance behind the projective faithfulness
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints

/-!
# The `PSL(2)` actions on the upper half-plane

The projective special linear groups `PSL(2, ℤ)` and `PSL(2, ℝ)` (quotients of `SL(2, ·)`
by their centers `{±I}`) act faithfully on the upper half-plane `ℍ`. The `PSL(2, ℝ)`-action
is the central-quotient descent of the `SL(2, R)`-action, uniformly in the coefficients;
it agrees with Mathlib's `PGL(2, ℝ)`-action along `toPGL` (`toPGL_smul`) and with
the `PSL(2, ℤ)`-action along the injective descent `psl2zToPSL2R` from
`TauCeti/LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup.lean`. The actions are
measurable and preserve the invariant measure `volume : Measure ℍ` (inherited from
Mathlib's `GL(2, ℝ)`-invariance).

## Main results

* `UpperHalfPlane.smul_eq_self_of_mem_center` — the center of `SL(2, R)` acts trivially,
  for any coefficients mapping to `ℝ`.
* `UpperHalfPlane.instMulActionPSL2` — the `PSL(2, R)`-action for any coefficients mapping
  to `ℝ`, descending the `SL(2, R)`-action along the central quotient, with the
  representative compatibility `pslMk_smul`.
* `FaithfulSMul` instances for `PSL(2, ℤ)` and `PSL(2, ℝ)` on `ℍ`, restricting Mathlib's
  faithful `PGL(2, ℝ)`-action along the injective `toPGL` and `psl2zToPSL2R`.
* `SMulInvariantMeasure` instances for `SL(2, R)` and `PSL(2, R)` (any coefficients
  mapping to `ℝ`) on `(ℍ, volume)`.
* `UpperHalfPlane.smul_eq_smul_of_coe_eq_smul` — matrices differing by a nonzero scalar act
  identically on `ℍ`.
* `UpperHalfPlane.glPosToPSL2R_smul` — the det-normalized projective representative of a
  `GL(2, ℝ)⁺` element (multiplicative by `Real.sqrt_mul` together with the centrality of
  positive scalars) acts on `ℍ` exactly as the original element.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/Modularforms/PSL2Action.lean`); the AINTLIB Jacobian computation of
`SL(2, ℤ)`-invariance of the hyperbolic measure is **not** ported — Mathlib's
`SMulInvariantMeasure (GL (Fin 2) ℝ) ℍ volume` subsumes it, and all invariance instances
here descend from it.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.4
* [Shi] Shimura, *Arithmetic Theory of Automorphic Functions*, §1.5
* The AINTLIB `LeanModularForms` project,
  <https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>
  (`Modularforms/PSL2Action.lean`)
-/

public section

noncomputable section

open scoped MatrixGroups Pointwise

open ModularGroup UpperHalfPlane Matrix.SpecialLinearGroup MeasureTheory

namespace UpperHalfPlane

variable {R : Type*} [CommRing R] [Algebra R ℝ]

instance : MeasurableConstSMul SL(2, R) ℍ where
  measurable_const_smul g := by
    -- the `SL(2, R)`-action on `ℍ` is `MulAction.compHom` along `mapGL ℝ`
    simp only [MulAction.compHom_smul_def]
    exact (continuous_const_smul (mapGL ℝ g)).measurable

/-- `SL(2, R)` preserves the invariant measure on `ℍ` for any coefficients mapping to `ℝ`;
the action factors through `GL(2, ℝ)`, whose invariance is Mathlib's. -/
instance : SMulInvariantMeasure SL(2, R) ℍ volume where
  measure_preimage_smul g s hs := by
    -- as above, rewrite through the `compHom` definition of the action
    simp only [MulAction.compHom_smul_def]
    exact (measurePreserving_smul (mapGL ℝ g) volume).measure_preimage hs.nullMeasurableSet

/-- Nonzero-scalar action invariance for `GL (Fin 2) ℝ`: a matrix that is a nonzero
scalar multiple of another acts identically on `ℍ`, through Mathlib's scalar-matrix
action `glScalar_smul`. -/
lemma smul_eq_smul_of_coe_eq_smul {g h : GL (Fin 2) ℝ} {c : ℝ} (hc : c ≠ 0)
    (h_eq : ((h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      c • ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
    (τ : ℍ) :
    h • τ = g • τ := by
  have h_mul : h = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc) * g := by
    refine Units.ext ?_
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, h_eq]
    ext i j
    simp [Matrix.scalar, Matrix.diagonal_mul]
  rw [h_mul, mul_smul, glScalar_smul]

/-- Central elements of `SL(2, R)` fix every point of `ℍ`, for any coefficients mapping
to `ℝ`: they are the scalar matrices `r • 1` with `r ^ 2 = 1`, and nonzero-scalar
matrices act as the identity Möbius transformation. -/
@[simp]
theorem smul_eq_self_of_mem_center (c : SL(2, R)) (hc : c ∈ Subgroup.center SL(2, R))
    (τ : ℍ) : c • τ = τ := by
  obtain ⟨r, hr, hrc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hr' : r ^ 2 = 1 := by simpa using hr
  have hr2 : algebraMap R ℝ r ^ 2 = 1 := by rw [← map_pow, hr', map_one]
  have ha : algebraMap R ℝ r ≠ 0 := by
    intro h
    rw [h] at hr2
    simp at hr2
  -- the representative acts as the nonzero scalar matrix `algebraMap R ℝ r • 1`, which is
  -- the identity Möbius transformation
  have h1 : mapGL ℝ c • τ = (1 : GL (Fin 2) ℝ) • τ := by
    refine smul_eq_smul_of_coe_eq_smul ha ?_ τ
    rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      ← hrc, Matrix.scalar, Matrix.diagonal_apply, Matrix.one_apply,
      apply_ite (algebraMap R ℝ)]
  -- rewrite the action through its `compHom` definition
  rw [MulAction.compHom_smul_def, h1, one_smul]

/-- The `PSL(2, R)`-action on `ℍ` for any coefficients mapping to `ℝ`: the descent of the
`SL(2, R)`-action along the central quotient, well-defined since central elements fix
every point (`smul_eq_self_of_mem_center`). The underlying permutation homomorphism is
recoverable as `MulAction.toPermHom`. -/
noncomputable instance instMulActionPSL2 : MulAction PSL(2, R) ℍ :=
  MulAction.compHom ℍ <| QuotientGroup.lift (Subgroup.center SL(2, R))
    (MulAction.toPermHom SL(2, R) ℍ) fun c hc ↦ Equiv.ext fun τ ↦ by
      simpa only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.one_apply]
        using smul_eq_self_of_mem_center c hc τ

/-- The `PSL(2, R)` action of a representative coincides with the `SL(2, R)` action. -/
@[simp]
theorem pslMk_smul (g : SL(2, R)) (τ : ℍ) : (↑g : PSL(2, R)) • τ = g • τ := (rfl)

noncomputable instance : MeasurableConstSMul PSL(2, R) ℍ where
  measurable_const_smul g := by
    refine QuotientGroup.induction_on g fun a ↦ ?_
    simp only [pslMk_smul]
    exact measurable_const_smul a

/-- `PSL(2, R)` preserves the invariant measure on `ℍ`, descending the `SL(2, R)`
invariance. -/
noncomputable instance : SMulInvariantMeasure PSL(2, R) ℍ volume where
  measure_preimage_smul g s hs := by
    refine QuotientGroup.induction_on g fun a ↦ ?_
    simp only [pslMk_smul]
    exact (measurePreserving_smul a (volume : Measure ℍ)).measure_preimage
      hs.nullMeasurableSet

/-- Mathlib's `PGL(2, ℝ)`-action along `toPGL` agrees with the `PSL(2, ℝ)`-action. -/
@[simp]
theorem toPGL_smul (g : PSL(2, ℝ)) (τ : ℍ) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL g • τ = g • τ := by
  refine QuotientGroup.induction_on g fun a ↦ ?_
  rw [pslMk_smul, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, pglMk_smul]
  -- the `SL(2, ℝ)`-action is definitionally the `GL(2, ℝ)`-action of the coercion;
  -- no rewriting lemma crosses this definitional boundary
  rfl

/-- The `PSL(2, ℝ)`-action on `ℍ` is faithful, through the faithful `PGL(2, ℝ)`-action
and the injective `toPGL`. -/
instance : FaithfulSMul PSL(2, ℝ) ℍ where
  eq_of_smul_eq_smul {g₁ g₂} h :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective <| eq_of_smul_eq_smul
      fun τ : ℍ ↦ by rw [toPGL_smul, toPGL_smul, h τ]

/-- The `PSL(2, ℤ)`-action factors through the `PSL(2, ℝ)`-action along the descent
`psl2zToPSL2R`. -/
@[simp]
theorem psl2zToPSL2R_smul (g : PSL(2, ℤ)) (τ : ℍ) : psl2zToPSL2R g • τ = g • τ := by
  refine QuotientGroup.induction_on g fun a ↦ ?_
  rw [psl2zToPSL2R_mk, sl2zToPSL2R_apply, pslMk_smul, pslMk_smul]
  -- the `SL(2, ℤ)`-action and the cast `SL(2, ℝ)`-action are definitionally the
  -- `GL(2, ℝ)`-action of the common `mapGL ℝ` image
  rfl

/-- The `PSL(2, ℤ)`-action on `ℍ` is faithful, through the injective descent
`psl2zToPSL2R` and the faithfulness of the `PSL(2, ℝ)`-action. -/
instance : FaithfulSMul PSL(2, ℤ) ℍ where
  eq_of_smul_eq_smul {g₁ g₂} h :=
    psl2zToPSL2R_injective <| eq_of_smul_eq_smul
      fun τ : ℍ ↦ by rw [psl2zToPSL2R_smul, psl2zToPSL2R_smul, h τ]

/-- Action equivariance: the projective representative `glPosToPSL2R g` acts on
`ℍ` exactly as `g` does, even though `det g` need not be `1`. -/
-- not `@[simp]`: `glPosToPSL2R_apply` rewrites the left-hand side out of simp normal
-- form first (simp-NF lint)
theorem glPosToPSL2R_smul (g : GL(2, ℝ)⁺) (τ : ℍ) :
    glPosToPSL2R g • τ = g • τ := by
  have hg_pos : 0 < ((g : GL (Fin 2) ℝ).det.val : ℝ) := g.property
  have h_sqrt_ne : (Real.sqrt ((g : GL (Fin 2) ℝ).det.val))⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_ne_zero'.mpr hg_pos)
  rw [glPosToPSL2R_apply, pslMk_smul]
  -- the `SL(2, ℝ)`-action is definitionally the `GL(2, ℝ)`-action of the `mapGL ℝ` image
  change (mapGL ℝ (glPosToSL2R g) : GL (Fin 2) ℝ) • τ = (g : GL (Fin 2) ℝ) • τ
  refine smul_eq_smul_of_coe_eq_smul h_sqrt_ne ?_ τ
  -- read off the matrix of the normalized representative through `mapGL`
  change ((mapGL ℝ (glPosToSL2R g) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    (Real.sqrt ((g : GL (Fin 2) ℝ).det.val))⁻¹ •
      ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  -- `algebraMap ℝ ℝ` is the identity, so the `map` leaves the matrix unchanged
  have hmap : (((Matrix.SpecialLinearGroup.map (algebraMap ℝ ℝ)) (glPosToSL2R g) :
      SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((glPosToSL2R g : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    simp [Algebra.algebraMap_self]
  rw [hmap]
  exact glPosToSL2R_coe_matrix g

end UpperHalfPlane
