/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.Integrated.EnergyForm

/-!
# Lower bounds for the shifted-Laplacian energy form

The energy-method lane of the PDE roadmap uses the shifted Laplacian `-Δ + m` as the model
coercive operator before adding variable uniformly elliptic coefficients.  The pointwise file
`TauCeti.Analysis.PDE.EnergyLowerBounds` already proves that the jet density
`energyIntegrand 1 0 m U U` controls the jet norm with constant `min 1 m` when `m ≥ 0`.
This file integrates that estimate for raw value-gradient jet fields.

These are still below the weak-derivative Sobolev-space layer: the inputs are arbitrary jet
fields `U : X → ℝ × EuclideanSpace ℝ n`, and the statements carry the Bochner-integrability
hypotheses needed to compare scalar integrals.  Once `H¹`/`W^{1,2}` jets are available, these
lemmas become the concrete coercive lower bounds for the shifted Dirichlet form.

## Main declarations

* `TauCeti.PDE.integral_min_one_mass_mul_norm_sq_le_energyFormIntegral_one_zero_mass_self`:
  a variable nonnegative mass controls the raw jet norm with coefficient `min 1 (m x)`.
* `TauCeti.PDE.integral_min_one_const_mass_mul_norm_sq_le_energyFormIntegral_one_zero_mass_self`:
  the constant-mass specialization.
* `TauCeti.PDE.integral_norm_sq_le_energyFormIntegral_one_zero_mass_self_of_one_le`:
  when the constant mass is at least `1`, the shifted-Laplacian form controls the full jet
  norm with constant `1`.
* `TauCeti.PDE.energyFormIntegral_one_zero_zero_self_nonneg` and
  `TauCeti.PDE.energyFormIntegral_one_zero_mass_self_nonneg`: nonnegativity of the
  Dirichlet and nonnegative shifted-Laplacian diagonal forms.
-/

public section

namespace TauCeti

namespace PDE

open MeasureTheory Matrix

variable {X n : Type*} [MeasurableSpace X] [Fintype n]

/-- Local classical decidable equality for finite coordinate indices in shifted-Laplacian
energy proofs. -/
noncomputable local instance shiftedLaplacianEnergyDecidableEq : DecidableEq n :=
  Classical.decEq n

variable {μ : Measure X} {m : X → ℝ} {U : X → ℝ × EuclideanSpace ℝ n}

/-- Integrated diagonal lower bound for the shifted-Laplacian model with variable
nonnegative mass.

Pointwise, `energyIntegrand 1 0 (m x) (U x) (U x)` is
`‖(U x).2‖² + m x * (U x).1²`, so for `m x ≥ 0` it controls the full product jet norm
with coefficient `min 1 (m x)`. -/
lemma integral_min_one_mass_mul_norm_sq_le_energyFormIntegral_one_zero_mass_self
    (hm : ∀ᵐ x ∂μ, 0 ≤ m x) (hlower : Integrable (fun x => min 1 (m x) * ‖U x‖ ^ 2) μ)
    (henergy : Integrable (fun x => energyIntegrand (1 : Matrix n n ℝ) 0 (m x) (U x) (U x)) μ) :
    ∫ x, (min 1 (m x) * ‖U x‖ ^ 2) ∂μ
      ≤ energyFormIntegral μ (fun _ => (1 : Matrix n n ℝ)) (fun _ => 0) m U U := by
  refine integral_min_lam_mass_mul_norm_sq_le_energyFormIntegral_zero_drift_self
    (μ := μ) (a := fun _ => (1 : Matrix n n ℝ)) (c := m) (U := U) zero_le_one ?_ hm
    hlower henergy
  filter_upwards with x
  intro ξ
  rw [← toQuadraticForm'_eq_dotProduct, toQuadraticForm'_one]
  simp

/-- The shifted-Laplacian diagonal form is nonnegative when the mass is a.e. nonnegative. -/
lemma energyFormIntegral_one_zero_mass_self_nonneg (hm : ∀ᵐ x ∂μ, 0 ≤ m x) :
    0 ≤ energyFormIntegral μ (fun _ => (1 : Matrix n n ℝ)) (fun _ => 0) m U U := by
  refine energyFormIntegral_zero_drift_self_nonneg
    (μ := μ) (a := fun _ => (1 : Matrix n n ℝ)) (c := m) (U := U) ?_ hm
  filter_upwards with x
  intro ξ
  rw [← toQuadraticForm'_eq_dotProduct, toQuadraticForm'_one]
  exact sq_nonneg ‖ξ‖

/-- The Dirichlet model `-Δ` has nonnegative diagonal energy. -/
lemma energyFormIntegral_one_zero_zero_self_nonneg :
    0 ≤ energyFormIntegral μ (fun _ => (1 : Matrix n n ℝ)) (fun _ => 0) (fun _ => 0) U U :=
  energyFormIntegral_one_zero_mass_self_nonneg
    (m := fun _ => (0 : ℝ)) (U := U) (Filter.Eventually.of_forall fun _ => le_rfl)

/-- Constant-mass specialization of the integrated shifted-Laplacian lower bound. -/
lemma integral_min_one_const_mass_mul_norm_sq_le_energyFormIntegral_one_zero_mass_self
    {c : ℝ} (hc : 0 ≤ c) (hlower : Integrable (fun x => min 1 c * ‖U x‖ ^ 2) μ)
    (henergy : Integrable (fun x => energyIntegrand (1 : Matrix n n ℝ) 0 c (U x) (U x)) μ) :
    ∫ x, (min 1 c * ‖U x‖ ^ 2) ∂μ
      ≤ energyFormIntegral μ (fun _ => (1 : Matrix n n ℝ)) (fun _ => 0) (fun _ => c) U U :=
  integral_min_one_mass_mul_norm_sq_le_energyFormIntegral_one_zero_mass_self
    (m := fun _ => c) (U := U) (Filter.Eventually.of_forall fun _ => hc) hlower henergy

/-- Constant nonnegative mass gives a nonnegative shifted-Laplacian diagonal form. -/
lemma energyFormIntegral_one_zero_const_mass_self_nonneg {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ energyFormIntegral μ (fun _ => (1 : Matrix n n ℝ)) (fun _ => 0) (fun _ => c) U U :=
  energyFormIntegral_one_zero_mass_self_nonneg
    (m := fun _ => c) (U := U) (Filter.Eventually.of_forall fun _ => hc)

/-- If the constant mass is at least `1`, the shifted-Laplacian diagonal form controls the
full raw jet `L²` density with constant `1`. -/
lemma integral_norm_sq_le_energyFormIntegral_one_zero_mass_self_of_one_le {c : ℝ} (hc : 1 ≤ c)
    (hlower : Integrable (fun x => ‖U x‖ ^ 2) μ) (henergy : Integrable
      (fun x => energyIntegrand (1 : Matrix n n ℝ) 0 c (U x) (U x)) μ) :
    ∫ x, (‖U x‖ ^ 2) ∂μ
      ≤ energyFormIntegral μ (fun _ => (1 : Matrix n n ℝ)) (fun _ => 0) (fun _ => c) U U := by
  have hmin : min (1 : ℝ) c = 1 := min_eq_left hc
  simpa [hmin] using
    integral_min_one_const_mass_mul_norm_sq_le_energyFormIntegral_one_zero_mass_self
      (U := U) (c := c) (zero_le_one.trans hc) (by simpa [hmin] using hlower) henergy

/-- For constant mass `1`, the shifted-Laplacian diagonal form controls the full raw jet
`L²` density with constant `1`. -/
lemma integral_norm_sq_le_energyFormIntegral_one_zero_one_self
    (hlower : Integrable (fun x => ‖U x‖ ^ 2) μ) (henergy : Integrable
      (fun x => energyIntegrand (1 : Matrix n n ℝ) 0 1 (U x) (U x)) μ) :
    ∫ x, (‖U x‖ ^ 2) ∂μ
      ≤ energyFormIntegral μ (fun _ => (1 : Matrix n n ℝ)) (fun _ => 0) (fun _ => 1) U U :=
  integral_norm_sq_le_energyFormIntegral_one_zero_mass_self_of_one_le
    (U := U) le_rfl hlower henergy

end PDE

end TauCeti
