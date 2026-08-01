/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Basic

/-!
# Symmetric pointwise energy integrands

For a divergence-form operator with no drift term, a symmetric principal coefficient
matrix gives a symmetric pointwise jet bilinear form `energyIntegrand A 0 c`.  This file
records that finite-dimensional bookkeeping before the energy form is integrated over a
Sobolev space.

The main use is Lane D of the PDE roadmap: the weak formulation and the Dirichlet spectrum
need the integrated form coming from symmetric coefficients to be a symmetric coercive
bilinear form.  The already-existing `coefficientSymmetricPart` replaces a possibly
nonsymmetric coefficient matrix by `(A + Aᵀ) / 2`; here we prove the corresponding facts for
the full zero-drift jet integrand.

The quantitative diagonal lower bounds are supplied separately by
`TauCeti.Analysis.PDE.EnergyLowerBounds` and its `UniformlyEllipticOn` wrappers.  In the
zero-drift case with positive mass and a principal quadratic lower bound, combine
`energyIntegrand_zero_drift_flip_eq_of_isSymm` or
`energyIntegrand_coefficientSymmetricPart_zero_drift_flip_eq` with
`min_lam_mass_mul_norm_sq_le_energyIntegrand_zero_drift_self` rather than introducing a
separate conjunction API.

## Main declarations

* `TauCeti.PDE.energyIntegrand_zero_drift_transpose_apply`: transposing the principal
  coefficient swaps the two jet arguments.
* `TauCeti.PDE.energyIntegrand_zero_drift_comm_of_isSymm`: a symmetric principal
  coefficient gives a symmetric zero-drift jet form.
* `TauCeti.PDE.energyIntegrand_coefficientSymmetricPart_zero_drift_apply`: the symmetric
  part has zero-drift jet form equal to the average of the original form and its transpose.
* `TauCeti.PDE.energyIntegrand_coefficientSymmetricPart_self`: the diagonal energy density
  is unchanged by replacing the principal coefficient by its symmetric part.
* `TauCeti.PDE.energyIntegrand_zero_drift_comm_on`: a pointwise symmetric coefficient field
  gives symmetric zero-drift jet forms at every point of the domain.
* `TauCeti.PDE.energyIntegrand_one_zero_mass_flip_eq`: bundled symmetry of the shifted
  Laplacian jet form.
-/

public section

namespace TauCeti

namespace PDE

open Matrix

variable {X n : Type*} [Fintype n]

/-- Local classical decidable equality for finite coordinate indices in symmetry proofs. -/
noncomputable local instance symmetricEnergyDecidableEq : DecidableEq n := Classical.decEq n

/-- With zero drift, transposing the principal coefficient swaps the two jet arguments. -/
lemma energyIntegrand_zero_drift_transpose_apply (A : Matrix n n ℝ) (c : ℝ)
    (U V : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand Aᵀ 0 c U V = energyIntegrand A 0 c V U := by
  rw [energyIntegrand_apply, energyIntegrand_apply, matrixBilinearForm_transpose_apply]
  simp [driftForm_apply, massForm_apply, mul_comm, mul_left_comm]

/-- A symmetric principal coefficient gives a symmetric zero-drift jet form. -/
lemma energyIntegrand_zero_drift_comm_of_isSymm {A : Matrix n n ℝ} (hA : A.IsSymm)
    (c : ℝ) (U V : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand A 0 c U V = energyIntegrand A 0 c V U := by
  calc
    energyIntegrand A 0 c U V = energyIntegrand Aᵀ 0 c U V := by rw [hA.eq]
    _ = energyIntegrand A 0 c V U := energyIntegrand_zero_drift_transpose_apply A c U V

/-- Bundled-map form of symmetry for the zero-drift jet integrand.

Downstream energy forms that need the same integrand to be both symmetric and bounded below
pair this with `min_lam_mass_mul_norm_sq_le_energyIntegrand_zero_drift_self`.  For a
nonsymmetric principal coefficient, first pass to `coefficientSymmetricPart` using the uniform
ellipticity API in `TauCeti.Analysis.PDE.Uniform.Ellipticity`, then apply this lemma to the
symmetric coefficient field. -/
@[simp]
lemma energyIntegrand_zero_drift_flip_eq_of_isSymm {A : Matrix n n ℝ} (hA : A.IsSymm) (c : ℝ) :
    (energyIntegrand A 0 c).flip = energyIntegrand A 0 c := by
  apply ContinuousLinearMap.ext
  intro U
  apply ContinuousLinearMap.ext
  intro V
  exact energyIntegrand_zero_drift_comm_of_isSymm hA c V U

/-- The symmetric part's zero-drift jet form is the average of the original form and its
transpose. -/
lemma energyIntegrand_coefficientSymmetricPart_zero_drift_apply (A : Matrix n n ℝ)
    (c : ℝ) (U V : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand (coefficientSymmetricPart A) 0 c U V =
      (energyIntegrand A 0 c U V + energyIntegrand A 0 c V U) / 2 := by
  rw [energyIntegrand_apply, matrixBilinearForm_coefficientSymmetricPart_apply,
    energyIntegrand_apply, energyIntegrand_apply]
  simp [driftForm_apply, massForm_apply, mul_comm, mul_left_comm]
  ring

/-- Replacing the principal coefficient by its symmetric part does not change the diagonal
energy density. -/
lemma energyIntegrand_coefficientSymmetricPart_self (A : Matrix n n ℝ)
    (b : EuclideanSpace ℝ n) (c : ℝ) (U : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand (coefficientSymmetricPart A) b c U U =
      energyIntegrand A b c U U := by
  classical
  rw [energyIntegrand_self, energyIntegrand_self, toQuadraticForm'_coefficientSymmetricPart]

/-- Bundled-map form of symmetry for the symmetric-part zero-drift jet integrand. -/
@[simp]
lemma energyIntegrand_coefficientSymmetricPart_zero_drift_flip_eq (A : Matrix n n ℝ) (c : ℝ) :
    (energyIntegrand (coefficientSymmetricPart A) 0 c).flip =
      energyIntegrand (coefficientSymmetricPart A) 0 c :=
  energyIntegrand_zero_drift_flip_eq_of_isSymm (coefficientSymmetricPart_isSymm A) c

/-- A pointwise symmetric coefficient field gives symmetric zero-drift jet forms at every
point of the domain. -/
lemma energyIntegrand_zero_drift_comm_on {Ω : Set X} {a : X → Matrix n n ℝ}
    (ha : ∀ ⦃x⦄, x ∈ Ω → (a x).IsSymm) {x : X} (hx : x ∈ Ω) (c : X → ℝ)
    (U V : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand (a x) 0 (c x) U V = energyIntegrand (a x) 0 (c x) V U :=
  energyIntegrand_zero_drift_comm_of_isSymm (ha hx) (c x) U V

/-- A pointwise symmetric coefficient field gives a bundled symmetric zero-drift jet form at
each point of the domain. -/
lemma energyIntegrand_zero_drift_flip_eq_on {Ω : Set X} {a : X → Matrix n n ℝ}
    (ha : ∀ ⦃x⦄, x ∈ Ω → (a x).IsSymm) {x : X} (hx : x ∈ Ω) (c : X → ℝ) :
    (energyIntegrand (a x) 0 (c x)).flip = energyIntegrand (a x) 0 (c x) :=
  energyIntegrand_zero_drift_flip_eq_of_isSymm (ha hx) (c x)

/-- Bundled symmetry of the shifted Laplacian jet form. -/
lemma energyIntegrand_one_zero_mass_flip_eq (c : ℝ) :
    (energyIntegrand (1 : Matrix n n ℝ) 0 c).flip =
      energyIntegrand (1 : Matrix n n ℝ) 0 c :=
  energyIntegrand_zero_drift_flip_eq_of_isSymm isSymm_one c

end PDE

end TauCeti
