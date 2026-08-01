/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.Integrated.EnergyForm
public import TauCeti.Analysis.PDE.SymmetricEnergy

/-!
# Symmetry of integrated zero-drift energy forms

Lane D of the PDE roadmap needs symmetric bilinear forms for the energy method and the
Dirichlet spectrum.  `TauCeti.Analysis.PDE.SymmetricEnergy` proves the corresponding
finite-dimensional facts for the pointwise jet integrand.  This file passes those facts
through the Bochner integral for raw jet fields.

The statements remain below the weak-derivative Sobolev-space layer: the inputs are coefficient
fields and raw value-gradient jets `U V : X → ℝ × EuclideanSpace ℝ n`.  Once Lane A supplies
Sobolev jets, these lemmas give the symmetric part of the weak form without unfolding the
integrand.

## Main declarations

* `TauCeti.PDE.energyFormIntegral_zero_drift_transpose_apply`: transposing the principal
  coefficient swaps the two jet fields under the integral.
* `TauCeti.PDE.energyFormIntegral_zero_drift_comm_of_isSymm_ae`: a.e. symmetric principal
  coefficients make the zero-drift integrated form symmetric.
* `TauCeti.PDE.energyFormIntegral_zero_drift_swap_eq_of_isSymm_ae`: bundled symmetry of the
  zero-drift integrated form under a.e. symmetric principal coefficients.
* `TauCeti.PDE.energyFormIntegral_coefficientSymmetricPart_self`: the diagonal integrated
  energy is unchanged by replacing the principal coefficient by its symmetric part.
* `TauCeti.PDE.energyFormIntegral_coefficientSymmetricPart_zero_drift_apply`: the
  symmetric-part zero-drift form is the average of the original form and its transpose, under the
  natural integrability hypotheses.
* `TauCeti.PDE.energyFormIntegral_one_zero_mass_swap_eq`: bundled symmetry of the
  shifted-Laplacian model form.
-/

public section

namespace TauCeti

namespace PDE

open MeasureTheory Matrix

variable {X n : Type*} [MeasurableSpace X] [Fintype n]

/-- Local classical decidable equality for finite coordinate indices in integrated symmetry
proofs. -/
noncomputable local instance integratedSymmetricEnergyDecidableEq : DecidableEq n :=
  Classical.decEq n

variable {μ : Measure X}
variable {a : X → Matrix n n ℝ} {c : X → ℝ}
variable {U V : X → ℝ × EuclideanSpace ℝ n}

/-- With zero drift, transposing the principal coefficient swaps the two jet fields under the
integral. -/
lemma energyFormIntegral_zero_drift_transpose_apply :
    energyFormIntegral μ (fun x => (a x)ᵀ) (fun _ => 0) c U V =
      energyFormIntegral μ a (fun _ => 0) c V U := by
  classical
  rw [energyFormIntegral_def, energyFormIntegral_def]
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall fun x =>
    energyIntegrand_zero_drift_transpose_apply (a x) (c x) (U x) (V x)

/-- A.e. symmetric principal coefficients make the zero-drift integrated energy form
symmetric. -/
lemma energyFormIntegral_zero_drift_comm_of_isSymm_ae (ha : ∀ᵐ x ∂μ, (a x).IsSymm) :
    energyFormIntegral μ a (fun _ => 0) c U V =
      energyFormIntegral μ a (fun _ => 0) c V U := by
  calc
    energyFormIntegral μ a (fun _ => 0) c U V =
        energyFormIntegral μ (fun x => (a x)ᵀ) (fun _ => 0) c U V := by
      refine energyFormIntegral_congr_ae (μ := μ) (a := a) (b := fun _ => 0) (c := c)
        (U := U) (V := V) (a' := fun x => (a x)ᵀ) (b' := fun _ => 0) (c' := c)
        (U' := U) (V' := V) ?_ ?_ ?_ ?_ ?_
      · filter_upwards [ha] with x hx
        exact hx.eq.symm
      · rfl
      · rfl
      · rfl
      · rfl
    _ = energyFormIntegral μ a (fun _ => 0) c V U :=
      energyFormIntegral_zero_drift_transpose_apply

/-- Bundled-map form of symmetry for a zero-drift integrated energy form with a.e. symmetric
principal coefficients. -/
@[simp]
lemma energyFormIntegral_zero_drift_swap_eq_of_isSymm_ae (ha : ∀ᵐ x ∂μ, (a x).IsSymm) :
    Function.swap (energyFormIntegral μ a (fun _ => 0) c) =
      energyFormIntegral μ a (fun _ => 0) c := by
  funext U V
  exact energyFormIntegral_zero_drift_comm_of_isSymm_ae (a := a) (c := c) (U := V) (V := U) ha

/-- Symmetry on a domain when the measure is a.e. supported there and the principal
coefficients are pointwise symmetric on that domain. -/
lemma energyFormIntegral_zero_drift_comm_on {Ω : Set X}
    (hΩ : ∀ᵐ x ∂μ, x ∈ Ω) (ha : ∀ ⦃x⦄, x ∈ Ω → (a x).IsSymm) :
    energyFormIntegral μ a (fun _ => 0) c U V =
      energyFormIntegral μ a (fun _ => 0) c V U :=
  energyFormIntegral_zero_drift_comm_of_isSymm_ae
    (hΩ.mono fun _ hx => ha hx)

/-- Bundled-map symmetry on a domain when the measure is a.e. supported there and the
principal coefficients are pointwise symmetric on that domain. -/
lemma energyFormIntegral_zero_drift_swap_eq_on {Ω : Set X}
    (hΩ : ∀ᵐ x ∂μ, x ∈ Ω) (ha : ∀ ⦃x⦄, x ∈ Ω → (a x).IsSymm) :
    Function.swap (energyFormIntegral μ a (fun _ => 0) c) =
      energyFormIntegral μ a (fun _ => 0) c := by
  funext U V
  exact energyFormIntegral_zero_drift_comm_on
    (a := a) (c := c) (U := V) (V := U) hΩ ha

/-- The symmetric-part zero-drift integrated energy form is symmetric. -/
lemma energyFormIntegral_coefficientSymmetricPart_zero_drift_comm :
    energyFormIntegral μ (fun x => coefficientSymmetricPart (a x)) (fun _ => 0) c U V =
      energyFormIntegral μ (fun x => coefficientSymmetricPart (a x)) (fun _ => 0) c V U :=
  energyFormIntegral_zero_drift_comm_of_isSymm_ae
    (Filter.Eventually.of_forall fun _ => coefficientSymmetricPart_isSymm _)

/-- Bundled-map symmetry for the symmetric-part zero-drift integrated energy form. -/
@[simp]
lemma energyFormIntegral_coefficientSymmetricPart_zero_drift_swap_eq :
    Function.swap
        (energyFormIntegral μ (fun x => coefficientSymmetricPart (a x)) (fun _ => 0) c) =
      energyFormIntegral μ (fun x => coefficientSymmetricPart (a x)) (fun _ => 0) c :=
  energyFormIntegral_zero_drift_swap_eq_of_isSymm_ae
    (Filter.Eventually.of_forall fun _ => coefficientSymmetricPart_isSymm _)

/-- The shifted-Laplacian model integrated form `-Δ + c` is symmetric. -/
lemma energyFormIntegral_one_zero_mass_comm :
    energyFormIntegral μ (fun _ => (1 : Matrix n n ℝ)) (fun _ => 0) c U V =
      energyFormIntegral μ (fun _ => (1 : Matrix n n ℝ)) (fun _ => 0) c V U :=
  energyFormIntegral_zero_drift_comm_of_isSymm_ae
    (Filter.Eventually.of_forall fun _ => isSymm_one)

/-- Bundled symmetry of the shifted-Laplacian model integrated form `-Δ + c`. -/
lemma energyFormIntegral_one_zero_mass_swap_eq :
    Function.swap (energyFormIntegral μ (fun _ => (1 : Matrix n n ℝ)) (fun _ => 0) c) =
      energyFormIntegral μ (fun _ => (1 : Matrix n n ℝ)) (fun _ => 0) c :=
  energyFormIntegral_zero_drift_swap_eq_of_isSymm_ae
    (Filter.Eventually.of_forall fun _ => isSymm_one)

/-- Replacing the principal coefficient by its symmetric part does not change the diagonal
integrated energy.  The drift and mass coefficients are arbitrary, since the diagonal
principal quadratic form is unchanged pointwise. -/
@[simp]
lemma energyFormIntegral_coefficientSymmetricPart_self {b : X → EuclideanSpace ℝ n} :
    energyFormIntegral μ (fun x => coefficientSymmetricPart (a x)) b c U U =
      energyFormIntegral μ a b c U U := by
  classical
  rw [energyFormIntegral_def, energyFormIntegral_def]
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall fun x =>
    energyIntegrand_coefficientSymmetricPart_self (a x) (b x) (c x) (U x)

/-- The symmetric-part zero-drift integrated form is the average of the original zero-drift
form and its transpose, assuming the two original scalar densities are integrable. -/
lemma energyFormIntegral_coefficientSymmetricPart_zero_drift_apply
    (hUV : Integrable (fun x => energyIntegrand (a x) 0 (c x) (U x) (V x)) μ)
    (hVU : Integrable (fun x => energyIntegrand (a x) 0 (c x) (V x) (U x)) μ) :
    energyFormIntegral μ (fun x => coefficientSymmetricPart (a x)) (fun _ => 0) c U V =
      (energyFormIntegral μ a (fun _ => 0) c U V +
        energyFormIntegral μ a (fun _ => 0) c V U) / 2 := by
  classical
  rw [energyFormIntegral_def, energyFormIntegral_def, energyFormIntegral_def]
  have hpoint :
      (fun x => energyIntegrand (coefficientSymmetricPart (a x)) 0 (c x) (U x) (V x)) =
        fun x => (energyIntegrand (a x) 0 (c x) (U x) (V x) +
          energyIntegrand (a x) 0 (c x) (V x) (U x)) / 2 := by
    funext x
    exact energyIntegrand_coefficientSymmetricPart_zero_drift_apply (a x) (c x) (U x) (V x)
  rw [hpoint]
  rw [integral_div, integral_add hUV hVU]

/-- For symmetric principal coefficients, replacing by the symmetric part leaves the integrated
form unchanged. -/
lemma energyFormIntegral_coefficientSymmetricPart_eq_of_isSymm_ae {b : X → EuclideanSpace ℝ n}
    (ha : ∀ᵐ x ∂μ, (a x).IsSymm) :
    energyFormIntegral μ (fun x => coefficientSymmetricPart (a x)) b c U V =
      energyFormIntegral μ a b c U V := by
  classical
  rw [energyFormIntegral_def, energyFormIntegral_def]
  refine integral_congr_ae ?_
  filter_upwards [ha] with x hx
  simp [coefficientSymmetricPart_eq_self_of_isSymm hx]

end PDE

end TauCeti
