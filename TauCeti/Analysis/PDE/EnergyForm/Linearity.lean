/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Basic

/-!
# Linearity of pointwise PDE energy integrands

The divergence-form energy integrand
`energyIntegrand A b c` is linear in the coefficient triple `(A, b, c)`.  This file records
that bookkeeping as bundled continuous-bilinear-map equalities and as pointwise evaluation
lemmas.

These lemmas are pointwise finite-dimensional prerequisites for Lane D of the PDE roadmap.
When the later weak energy form is an integral of `energyIntegrand (a x) (b x) (c x)`, this
API lets bounded perturbations and decompositions into principal, drift, and mass pieces be
rewritten before applying the boundedness and Gårding estimates.

## Main declarations

* `TauCeti.PDE.energyIntegrand_add`, `TauCeti.PDE.energyIntegrand_smul`,
  `TauCeti.PDE.energyIntegrand_neg`, and `TauCeti.PDE.energyIntegrand_sub`: bundled
  coefficient-linearity of the pointwise energy integrand.
* `TauCeti.PDE.energyIntegrand_principal_add_lowerOrder` and
  `TauCeti.PDE.energyIntegrand_principal_drift_mass`: decomposition into the principal,
  drift, and mass pieces.
* `TauCeti.PDE.energyIntegrand_add_apply`, `TauCeti.PDE.energyIntegrand_neg_apply`,
  `TauCeti.PDE.energyIntegrand_sub_apply`, and `TauCeti.PDE.energyIntegrand_smul_apply`:
  pointwise evaluation forms of coefficient linearity.
* `TauCeti.PDE.energyIntegrand_eq_one_zero_baseMass_add_perturbation` and its `_apply`
  form: shifted-Laplacian-plus-residual decomposition with a chosen base mass.
-/

public section

namespace TauCeti

namespace PDE

open Matrix

variable {n : Type*} [Fintype n]

variable (A B : Matrix n n ℝ) (b d : EuclideanSpace ℝ n) (c e m r : ℝ)
variable (U V : ℝ × EuclideanSpace ℝ n)

/-- The zero coefficient triple has zero pointwise energy integrand. -/
@[simp]
lemma energyIntegrand_zero :
    energyIntegrand (0 : Matrix n n ℝ) (0 : EuclideanSpace ℝ n) 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro U
  apply ContinuousLinearMap.ext
  intro V
  simp [energyIntegrand_apply]

/-- The pointwise energy integrand is additive in its coefficient triple. -/
@[simp]
lemma energyIntegrand_add :
    energyIntegrand (A + B) (b + d) (c + e) =
      energyIntegrand A b c + energyIntegrand B d e := by
  apply ContinuousLinearMap.ext
  intro U
  apply ContinuousLinearMap.ext
  intro V
  simp [energyIntegrand_apply, Matrix.add_mulVec, dotProduct_add, driftForm_apply,
    massForm_apply, inner_add_left]
  ring_nf

/-- Pointwise evaluation form of `energyIntegrand_add`. -/
lemma energyIntegrand_add_apply :
    energyIntegrand (A + B) (b + d) (c + e) U V =
      energyIntegrand A b c U V + energyIntegrand B d e U V := by
  simp

/-- The pointwise energy integrand is compatible with negating all coefficients. -/
@[simp]
lemma energyIntegrand_neg :
    energyIntegrand (-A) (-b) (-c) = -energyIntegrand A b c := by
  apply ContinuousLinearMap.ext
  intro U
  apply ContinuousLinearMap.ext
  intro V
  simp [energyIntegrand_apply, matrixBilinearForm_apply, Matrix.neg_mulVec, dotProduct_neg,
    driftForm_apply, massForm_apply, inner_neg_left]
  ring_nf

/-- Pointwise evaluation form of `energyIntegrand_neg`. -/
lemma energyIntegrand_neg_apply :
    energyIntegrand (-A) (-b) (-c) U V = -energyIntegrand A b c U V := by
  simp

/-- The pointwise energy integrand is subtractive in its coefficient triple. -/
@[simp]
lemma energyIntegrand_sub :
    energyIntegrand (A - B) (b - d) (c - e) =
      energyIntegrand A b c - energyIntegrand B d e := by
  apply ContinuousLinearMap.ext
  intro U
  apply ContinuousLinearMap.ext
  intro V
  simp [sub_eq_add_neg]

/-- Pointwise evaluation form of `energyIntegrand_sub`. -/
lemma energyIntegrand_sub_apply :
    energyIntegrand (A - B) (b - d) (c - e) U V =
      energyIntegrand A b c U V - energyIntegrand B d e U V := by
  simp

/-- The pointwise energy integrand is homogeneous in its coefficient triple. -/
@[simp]
lemma energyIntegrand_smul :
    energyIntegrand (r • A) (r • b) (r * c) = r • energyIntegrand A b c := by
  apply ContinuousLinearMap.ext
  intro U
  apply ContinuousLinearMap.ext
  intro V
  simp [energyIntegrand_apply, Matrix.smul_mulVec, dotProduct_smul, driftForm_apply,
    massForm_apply, inner_smul_left, smul_eq_mul]
  ring

/-- Pointwise evaluation form of `energyIntegrand_smul`. -/
lemma energyIntegrand_smul_apply :
    energyIntegrand (r • A) (r • b) (r * c) U V = r * energyIntegrand A b c U V := by
  simp [smul_eq_mul]

/-- The full energy integrand splits into its principal part and lower-order part. -/
lemma energyIntegrand_principal_add_lowerOrder :
    energyIntegrand A b c =
      energyIntegrand A 0 0 + energyIntegrand 0 b c := by
  simpa using
    (energyIntegrand_add A (0 : Matrix n n ℝ) (0 : EuclideanSpace ℝ n) b 0 c)

/-- The full energy integrand splits into its principal, drift, and mass pieces. -/
lemma energyIntegrand_principal_drift_mass :
    energyIntegrand A b c =
      energyIntegrand A 0 0 + energyIntegrand 0 b 0 + energyIntegrand 0 0 c := by
  rw [energyIntegrand_principal_add_lowerOrder]
  have h : energyIntegrand (0 : Matrix n n ℝ) b c =
      energyIntegrand 0 b 0 + energyIntegrand 0 0 c := by
    simpa using
      (energyIntegrand_add (0 : Matrix n n ℝ) (0 : Matrix n n ℝ) b
        (0 : EuclideanSpace ℝ n) 0 c)
  rw [h]
  abel

variable [DecidableEq n]

/-- The full energy integrand is the sum of a shifted Laplacian model with chosen base mass
and the residual perturbation of the coefficient triple. -/
lemma energyIntegrand_eq_one_zero_baseMass_add_perturbation :
    energyIntegrand A b c =
      energyIntegrand (1 : Matrix n n ℝ) 0 m +
        energyIntegrand (A - 1) b (c - m) := by
  calc
    energyIntegrand A b c =
        energyIntegrand ((1 : Matrix n n ℝ) + (A - 1)) (0 + b) (m + (c - m)) := by
      simp [sub_eq_add_neg, add_left_comm, add_comm]
    _ = energyIntegrand (1 : Matrix n n ℝ) 0 m + energyIntegrand (A - 1) b (c - m) :=
      energyIntegrand_add (1 : Matrix n n ℝ) (A - 1) 0 b m (c - m)

/-- Pointwise form of the shifted-Laplacian-plus-residual-perturbation decomposition. -/
lemma energyIntegrand_eq_one_zero_baseMass_add_perturbation_apply :
    energyIntegrand A b c U V =
      energyIntegrand (1 : Matrix n n ℝ) 0 m U V +
        energyIntegrand (A - 1) b (c - m) U V := by
  rw [energyIntegrand_eq_one_zero_baseMass_add_perturbation]
  rfl

/-- The full energy integrand is the sum of a shifted Laplacian model and a perturbation of
the principal and drift coefficients. -/
lemma energyIntegrand_eq_one_zero_mass_add_perturbation :
    energyIntegrand A b c =
      energyIntegrand (1 : Matrix n n ℝ) 0 c +
        energyIntegrand (A - 1) b 0 := by
  simpa using
    (energyIntegrand_eq_one_zero_baseMass_add_perturbation
      (A := A) (b := b) (c := c) (m := c))

end PDE

end TauCeti
