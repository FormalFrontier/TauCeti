/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import TauCeti.Analysis.PDE.SymmetricEnergy

/-!
# Constant-coefficient energy forms on `L²` jets

Lane D of the PDE roadmap asks for the bounded bilinear energy form used by the weak
formulation of a divergence-form equation. This file performs the functional-analytic bundling
for constant coefficients. A pointwise jet form

`(u, ∇u), (v, ∇v) ↦ (∇v)ᵀ A ∇u + v bᵀ ∇u + c u v`

induces a continuous bilinear form on square-integrable value-gradient jets. The construction
uses Mathlib's `ContinuousLinearMap.lpPairing`, which is the continuous Hölder pairing induced
by a continuous bilinear map.

Variable coefficients will require the corresponding multiplication-operator construction.
The constant-coefficient form here already includes the Dirichlet and shifted-Laplacian models
and has the bounded-bilinear-map shape needed for a later Lax--Milgram application, after
restriction to the intended Hilbert/Sobolev space and a proof of coercivity.

## Main declarations

* `TauCeti.PDE.energyFormLp`: the constant-coefficient energy form on `L²` jets.
* `TauCeti.PDE.energyFormLp_apply`: its characterization as an integral.
* `TauCeti.PDE.energyFormLp_one_zero_zero_apply` and
  `TauCeti.PDE.energyFormLp_one_zero_mass_apply`: the Dirichlet and shifted-Laplacian formulas.
* `TauCeti.PDE.energyFormLp_one_zero_zero_self` and
  `TauCeti.PDE.energyFormLp_one_zero_mass_self`: their diagonal formulas.
* `TauCeti.PDE.energyFormLp_zero_drift_flip_eq_of_isSymm`: bundled symmetry when the principal
  matrix is symmetric and the drift vanishes.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory Matrix
open scoped InnerProductSpace

variable {X n : Type*} [MeasurableSpace X] [Fintype n]

/-- The classical decidable equality used for finite-dimensional matrix computations. -/
noncomputable local instance energyFormLpDecidableEq : DecidableEq n := Classical.decEq n

/-- The constant-coefficient divergence-form energy form on square-integrable
value-gradient jets.

This is the Hölder pairing induced by `energyIntegrand A b c`; in particular it is bundled as
a continuous bilinear map, with no integrability hypotheses required at use sites. -/
noncomputable def energyFormLp (μ : Measure X) (A : Matrix n n ℝ) (b : EuclideanSpace ℝ n) (c : ℝ) :
    Lp (ℝ × EuclideanSpace ℝ n) 2 μ →L[ℝ]
      Lp (ℝ × EuclideanSpace ℝ n) 2 μ →L[ℝ] ℝ :=
  (energyIntegrand A b c).lpPairing μ 2 2

/-- The `L²` energy form is the integral of the pointwise jet energy density. -/
@[simp]
theorem energyFormLp_apply (μ : Measure X) (A : Matrix n n ℝ) (b : EuclideanSpace ℝ n) (c : ℝ)
    (U V : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    energyFormLp μ A b c U V =
      ∫ x, energyIntegrand A b c (U x) (V x) ∂μ := by
  exact ContinuousLinearMap.lpPairing_eq_integral _ _ _

/-- The shifted-Laplacian energy form is the sum of the gradient pairing and the mass
pairing. -/
theorem energyFormLp_one_zero_mass_apply (μ : Measure X) (c : ℝ)
    (U V : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    energyFormLp μ (1 : Matrix n n ℝ) 0 c U V =
      ∫ x, ((V x).2 ⬝ᵥ (U x).2 + c * (U x).1 * (V x).1) ∂μ := by
  rw [energyFormLp_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact energyIntegrand_one_zero_mass_apply c (U x) (V x)

/-- The Dirichlet energy form pairs the gradient components of two `L²` jets. -/
theorem energyFormLp_one_zero_zero_apply (μ : Measure X) (U V : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    energyFormLp μ (1 : Matrix n n ℝ) 0 0 U V =
      ∫ x, (V x).2 ⬝ᵥ (U x).2 ∂μ := by
  rw [energyFormLp_one_zero_mass_apply]
  simp

/-- The diagonal of the shifted-Laplacian `L²` energy form is the integral of the squared
gradient norm plus the mass density. -/
theorem energyFormLp_one_zero_mass_self (μ : Measure X) (c : ℝ)
    (U : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    energyFormLp μ (1 : Matrix n n ℝ) 0 c U U =
      ∫ x, (‖(U x).2‖ ^ 2 + c * (U x).1 ^ 2) ∂μ := by
  rw [energyFormLp_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact energyIntegrand_one_zero_mass_self c (U x)

/-- The diagonal of the Dirichlet `L²` energy form is the integral of the squared gradient
norm. -/
theorem energyFormLp_one_zero_zero_self (μ : Measure X) (U : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    energyFormLp μ (1 : Matrix n n ℝ) 0 0 U U =
      ∫ x, ‖(U x).2‖ ^ 2 ∂μ := by
  rw [energyFormLp_one_zero_mass_self]
  simp

/-- Replacing the principal coefficient by its symmetric part does not change the diagonal
`L²` energy form. -/
theorem energyFormLp_coefficientSymmetricPart_self (μ : Measure X) (A : Matrix n n ℝ)
    (b : EuclideanSpace ℝ n) (c : ℝ) (U : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    energyFormLp μ (coefficientSymmetricPart A) b c U U =
      energyFormLp μ A b c U U := by
  rw [energyFormLp_apply, energyFormLp_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact energyIntegrand_coefficientSymmetricPart_self A b c (U x)

/-- The symmetric-part zero-drift `L²` energy form is the average of the original form and
its transpose. -/
theorem energyFormLp_coefficientSymmetricPart_zero_drift_apply (μ : Measure X)
    (A : Matrix n n ℝ) (c : ℝ) (U V : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    energyFormLp μ (coefficientSymmetricPart A) 0 c U V =
      (energyFormLp μ A 0 c U V + energyFormLp μ A 0 c V U) / 2 := by
  rw [energyFormLp_apply, energyFormLp_apply, energyFormLp_apply]
  have hUV : Integrable (fun x => energyIntegrand A 0 c (U x) (V x)) μ :=
    memLp_one_iff_integrable.mp
      ((energyIntegrand A 0 c).memLp_of_bilin 1 (Lp.memLp U) (Lp.memLp V))
  have hVU : Integrable (fun x => energyIntegrand A 0 c (V x) (U x)) μ :=
    memLp_one_iff_integrable.mp
      ((energyIntegrand A 0 c).memLp_of_bilin 1 (Lp.memLp V) (Lp.memLp U))
  have hpoint :
      (fun x => energyIntegrand (coefficientSymmetricPart A) 0 c (U x) (V x)) =
        fun x => (energyIntegrand A 0 c (U x) (V x) +
          energyIntegrand A 0 c (V x) (U x)) / 2 := by
    funext x
    exact energyIntegrand_coefficientSymmetricPart_zero_drift_apply A c (U x) (V x)
  rw [hpoint]
  rw [integral_div, integral_add hUV hVU]

/-- Transposing the principal coefficient swaps the two arguments of a zero-drift `L²` energy
form. -/
theorem energyFormLp_zero_drift_transpose_apply (μ : Measure X) (A : Matrix n n ℝ) (c : ℝ)
    (U V : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    energyFormLp μ Aᵀ 0 c U V = energyFormLp μ A 0 c V U := by
  rw [energyFormLp_apply, energyFormLp_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact energyIntegrand_zero_drift_transpose_apply A c (U x) (V x)

/-- A symmetric principal coefficient gives a symmetric zero-drift `L²` energy form. -/
theorem energyFormLp_zero_drift_comm_of_isSymm {A : Matrix n n ℝ} (hA : A.IsSymm)
    (μ : Measure X) (c : ℝ) (U V : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    energyFormLp μ A 0 c U V = energyFormLp μ A 0 c V U := by
  rw [energyFormLp_apply, energyFormLp_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact energyIntegrand_zero_drift_comm_of_isSymm hA c (U x) (V x)

/-- A symmetric principal coefficient makes the zero-drift `L²` energy form equal to its
flip. -/
@[simp]
theorem energyFormLp_zero_drift_flip_eq_of_isSymm {A : Matrix n n ℝ} (hA : A.IsSymm)
    (μ : Measure X) (c : ℝ) : (energyFormLp μ A 0 c).flip = energyFormLp μ A 0 c := by
  ext U V
  exact energyFormLp_zero_drift_comm_of_isSymm hA μ c V U

/-- The symmetric-part zero-drift `L²` energy form is symmetric. -/
theorem energyFormLp_coefficientSymmetricPart_zero_drift_comm (μ : Measure X)
    (A : Matrix n n ℝ) (c : ℝ) (U V : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    energyFormLp μ (coefficientSymmetricPart A) 0 c U V =
      energyFormLp μ (coefficientSymmetricPart A) 0 c V U :=
  energyFormLp_zero_drift_comm_of_isSymm (coefficientSymmetricPart_isSymm A) μ c U V

/-- The symmetric-part zero-drift `L²` energy form is equal to its flip. -/
@[simp]
theorem energyFormLp_coefficientSymmetricPart_zero_drift_flip_eq (μ : Measure X)
    (A : Matrix n n ℝ) (c : ℝ) : (energyFormLp μ (coefficientSymmetricPart A) 0 c).flip =
      energyFormLp μ (coefficientSymmetricPart A) 0 c :=
  energyFormLp_zero_drift_flip_eq_of_isSymm (coefficientSymmetricPart_isSymm A) μ c

/-- The shifted-Laplacian `L²` energy form is symmetric. -/
theorem energyFormLp_one_zero_mass_comm (μ : Measure X) (c : ℝ)
    (U V : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    energyFormLp μ (1 : Matrix n n ℝ) 0 c U V =
      energyFormLp μ (1 : Matrix n n ℝ) 0 c V U :=
  energyFormLp_zero_drift_comm_of_isSymm isSymm_one μ c U V

/-- The shifted-Laplacian `L²` energy form is equal to its flip. -/
theorem energyFormLp_one_zero_mass_flip_eq (μ : Measure X) (c : ℝ) :
    (energyFormLp μ (1 : Matrix n n ℝ) 0 c).flip =
      energyFormLp μ (1 : Matrix n n ℝ) 0 c :=
  energyFormLp_zero_drift_flip_eq_of_isSymm isSymm_one μ c

end PDE

end TauCeti

end
