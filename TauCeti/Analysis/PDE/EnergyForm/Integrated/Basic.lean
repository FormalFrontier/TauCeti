/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Linearity
public import TauCeti.Analysis.PDE.Ellipticity.Energy
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrated divergence-form energy forms

Lane D of the PDE roadmap asks for the weak energy form

`a(u, v) = ∫ aⁱʲ ∂ᵢu ∂ⱼv + bⁱ ∂ᵢu v + c u v`.

The preceding PDE files build the pointwise jet integrand
`energyIntegrand (a x) (b x) (c x)` and prove the measurability and integrability estimates
needed to integrate it.  This file performs that integration for raw jet fields
`U V : X → ℝ × EuclideanSpace ℝ n`.  It deliberately does not define a Sobolev space or weak
derivative: once Lane A supplies `W^{k,p}(Ω)`, its value-gradient jets can feed this definition.

## Main declarations

* `TauCeti.PDE.energyFormIntegral`: the integrated scalar energy form on two jet fields.
* `TauCeti.PDE.energyFormIntegral_one_zero_zero` and
  `TauCeti.PDE.energyFormIntegral_one_zero_mass`: the `−Δ` and shifted-`−Δ + c` model forms.
* `TauCeti.PDE.energyFormIntegral_add_left`, `TauCeti.PDE.energyFormIntegral_add_right`,
  `TauCeti.PDE.energyFormIntegral_smul_left`, and
  `TauCeti.PDE.energyFormIntegral_smul_right`: bilinearity identities under the usual
  Bochner-integrability hypotheses.
* `TauCeti.PDE.norm_energyFormIntegral_le_of_bounds`: the integrated boundedness estimate
  obtained from the pointwise coefficient bounds.
* `TauCeti.PDE.integral_min_lam_mass_mul_norm_sq_le_energyFormIntegral_zero_drift_self`:
  the zero-drift integrated diagonal lower bound from a principal quadratic lower bound and
  nonnegative mass.
* `TauCeti.PDE.integral_mul_norm_snd_sq_le_energyFormIntegral_zero_drift_self`: the integrated
  zero-drift lower bound for the squared gradient component.
* `TauCeti.PDE.UniformlyEllipticOn.norm_energyFormIntegral_le_on`: the corresponding
  boundedness estimate from uniform ellipticity on an a.e. domain.
-/

public section

namespace TauCeti

namespace PDE

open MeasureTheory Matrix
open scoped InnerProductSpace

variable {X n : Type*} [MeasurableSpace X] [Fintype n]

/-- Local classical decidable equality for finite coordinate indices in integrated energy proofs. -/
noncomputable local instance integratedEnergyFormDecidableEq : DecidableEq n := Classical.decEq n

/-- The scalar energy form obtained by integrating the divergence-form pointwise jet
integrand against a measure.

For a Sobolev function `u`, the intended jet field is `x ↦ (u x, ∇u x)`.  This definition stays
at the raw-jet level because the roadmap's weak-derivative Sobolev spaces are a separate
prerequisite. -/
public noncomputable def energyFormIntegral (μ : Measure X) (a : X → Matrix n n ℝ)
    (b : X → EuclideanSpace ℝ n) (c : X → ℝ) (U V : X → ℝ × EuclideanSpace ℝ n) : ℝ :=
  ∫ x, (energyIntegrand (a x) (b x) (c x) (U x) (V x)) ∂μ

/-- Unfolding rule for the integrated energy form. -/
theorem energyFormIntegral_def (μ : Measure X) (a : X → Matrix n n ℝ)
    (b : X → EuclideanSpace ℝ n) (c : X → ℝ) (U V : X → ℝ × EuclideanSpace ℝ n) :
    energyFormIntegral μ a b c U V =
      ∫ x, (energyIntegrand (a x) (b x) (c x) (U x) (V x)) ∂μ :=
  by simp [energyFormIntegral]

variable (μ : Measure X) (a : X → Matrix n n ℝ)
variable (b : X → EuclideanSpace ℝ n) (c : X → ℝ)
variable (U V W : X → ℝ × EuclideanSpace ℝ n)

/-- The integrated energy form respects almost-everywhere equality of all coefficient and jet
fields. -/
lemma energyFormIntegral_congr_ae {a' : X → Matrix n n ℝ} {b' : X → EuclideanSpace ℝ n}
    {c' : X → ℝ} {U' V' : X → ℝ × EuclideanSpace ℝ n}
    (ha : a =ᵐ[μ] a') (hb : b =ᵐ[μ] b') (hc : c =ᵐ[μ] c') (hU : U =ᵐ[μ] U') (hV : V =ᵐ[μ] V') :
    energyFormIntegral μ a b c U V = energyFormIntegral μ a' b' c' U' V' := by
  rw [energyFormIntegral_def, energyFormIntegral_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ha, hb, hc, hU, hV] with x hax hbx hcx hUx hVx
  simp [hax, hbx, hcx, hUx, hVx]

/-- The integrated energy form vanishes when the left jet field is zero. -/
@[simp]
lemma energyFormIntegral_zero_left :
    energyFormIntegral μ a b c (fun _ => 0) V = 0 := by
  simp [energyFormIntegral_def]

/-- The integrated energy form vanishes when the right jet field is zero. -/
@[simp]
lemma energyFormIntegral_zero_right :
    energyFormIntegral μ a b c U (fun _ => 0) = 0 := by
  simp [energyFormIntegral_def]

/-- The zero coefficient triple gives the zero integrated energy form. -/
@[simp]
lemma energyFormIntegral_zero_coefficients :
    energyFormIntegral μ (fun _ => 0) (fun _ => 0) (fun _ => 0) U V = 0 := by
  simp [energyFormIntegral_def]

-- Pointwise equality of scalar integrands lifts to Bochner integrals (file-local only).
private lemma integral_congr_forall {f g : X → ℝ} (h : ∀ x, f x = g x) :
    ∫ x, f x ∂μ = ∫ x, g x ∂μ :=
  integral_congr_ae (Filter.Eventually.of_forall h)

/-- Negating the left jet field negates the integrated energy form. -/
@[simp]
lemma energyFormIntegral_neg_left :
    energyFormIntegral μ a b c (fun x => -U x) V = -energyFormIntegral μ a b c U V := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x => energyIntegrand (a x) (b x) (c x) (-U x) (V x))
      (g := fun x => -energyIntegrand (a x) (b x) (c x) (U x) (V x))
      (fun x => by simp),
    MeasureTheory.integral_neg]

/-- Negating the right jet field negates the integrated energy form. -/
@[simp]
lemma energyFormIntegral_neg_right :
    energyFormIntegral μ a b c U (fun x => -V x) = -energyFormIntegral μ a b c U V := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x => energyIntegrand (a x) (b x) (c x) (U x) (-V x))
      (g := fun x => -energyIntegrand (a x) (b x) (c x) (U x) (V x))
      (fun x => map_neg (energyIntegrand (a x) (b x) (c x) (U x)) (V x)),
    MeasureTheory.integral_neg]

/-- Negating the coefficient triple negates the integrated energy form. -/
@[simp]
lemma energyFormIntegral_neg_coefficients :
    energyFormIntegral μ (fun x => -a x) (fun x => -b x) (fun x => -c x) U V =
      -energyFormIntegral μ a b c U V := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x => energyIntegrand (-a x) (-b x) (-c x) (U x) (V x))
      (g := fun x => -energyIntegrand (a x) (b x) (c x) (U x) (V x))
      (fun x => by simp),
    MeasureTheory.integral_neg]

/-- Additivity in the left jet field, assuming the two summand energy densities are
integrable. -/
lemma energyFormIntegral_add_left
    (hU : Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ)
    (hW : Integrable (fun x => energyIntegrand (a x) (b x) (c x) (W x) (V x)) μ) :
    energyFormIntegral μ a b c (fun x => U x + W x) V =
      energyFormIntegral μ a b c U V + energyFormIntegral μ a b c W V := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x => energyIntegrand (a x) (b x) (c x) (U x + W x) (V x))
      (g := fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x) +
          energyIntegrand (a x) (b x) (c x) (W x) (V x))
      (fun x => by simp),
    integral_add hU hW]

/-- Additivity in the right jet field, assuming the two summand energy densities are
integrable. -/
lemma energyFormIntegral_add_right
    (hV : Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ)
    (hW : Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (W x)) μ) :
    energyFormIntegral μ a b c U (fun x => V x + W x) =
      energyFormIntegral μ a b c U V + energyFormIntegral μ a b c U W := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x + W x))
      (g := fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x) +
          energyIntegrand (a x) (b x) (c x) (U x) (W x))
      (fun x => map_add (energyIntegrand (a x) (b x) (c x) (U x)) (V x) (W x)),
    integral_add hV hW]

/-- Homogeneity in the left jet field. -/
lemma energyFormIntegral_smul_left (r : ℝ) :
    energyFormIntegral μ a b c (fun x => r • U x) V =
      r * energyFormIntegral μ a b c U V := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x => energyIntegrand (a x) (b x) (c x) (r • U x) (V x))
      (g := fun x => r • energyIntegrand (a x) (b x) (c x) (U x) (V x))
      (fun x => by simp),
    MeasureTheory.integral_smul]
  simp [smul_eq_mul]

/-- Homogeneity in the right jet field. -/
lemma energyFormIntegral_smul_right (r : ℝ) :
    energyFormIntegral μ a b c U (fun x => r • V x) =
      r * energyFormIntegral μ a b c U V := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x => energyIntegrand (a x) (b x) (c x) (U x) (r • V x))
      (g := fun x => r • energyIntegrand (a x) (b x) (c x) (U x) (V x))
      (fun x => by simp),
    MeasureTheory.integral_smul]
  simp [smul_eq_mul]

variable (a' : X → Matrix n n ℝ) (b' : X → EuclideanSpace ℝ n) (c' : X → ℝ)
variable (m : X → ℝ) (r : ℝ)

/-- The integrated energy form is additive in the coefficient triple, under the corresponding
integrability assumptions for the two summand densities. -/
lemma energyFormIntegral_add
    (h : Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ)
    (h' : Integrable (fun x => energyIntegrand (a' x) (b' x) (c' x) (U x) (V x)) μ) :
    energyFormIntegral μ (fun x => a x + a' x) (fun x => b x + b' x) (fun x => c x + c' x)
        U V =
      energyFormIntegral μ a b c U V + energyFormIntegral μ a' b' c' U V := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x => energyIntegrand (a x + a' x) (b x + b' x) (c x + c' x) (U x) (V x))
      (g := fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x) +
          energyIntegrand (a' x) (b' x) (c' x) (U x) (V x))
      (fun x => by simp),
    integral_add h h']

/-- The integrated energy form is subtractive in the coefficient triple, under the
corresponding integrability assumptions for the two densities. -/
lemma energyFormIntegral_sub
    (h : Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ)
    (h' : Integrable (fun x => energyIntegrand (a' x) (b' x) (c' x) (U x) (V x)) μ) :
    energyFormIntegral μ (fun x => a x - a' x) (fun x => b x - b' x) (fun x => c x - c' x)
        U V =
      energyFormIntegral μ a b c U V - energyFormIntegral μ a' b' c' U V := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x => energyIntegrand (a x - a' x) (b x - b' x) (c x - c' x) (U x) (V x))
      (g := fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x) -
          energyIntegrand (a' x) (b' x) (c' x) (U x) (V x))
      (fun x => by simp),
    integral_sub h h']

/-- The integrated energy form is homogeneous in the coefficient triple. -/
lemma energyFormIntegral_smul :
    energyFormIntegral μ (fun x => r • a x) (fun x => r • b x) (fun x => r * c x) U V =
      r * energyFormIntegral μ a b c U V := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x => energyIntegrand (r • a x) (r • b x) (r * c x) (U x) (V x))
      (g := fun x => r • energyIntegrand (a x) (b x) (c x) (U x) (V x))
      (fun x => by simp),
    MeasureTheory.integral_smul]
  simp [smul_eq_mul]

/-- The integrated full energy form splits into its principal and lower-order parts. -/
lemma energyFormIntegral_principal_add_lowerOrder
    (hprincipal : Integrable (fun x => energyIntegrand (a x) 0 0 (U x) (V x)) μ)
    (hlower : Integrable (fun x => energyIntegrand 0 (b x) (c x) (U x) (V x)) μ) :
    energyFormIntegral μ a b c U V =
      energyFormIntegral μ a (fun _ => 0) (fun _ => 0) U V +
        energyFormIntegral μ (fun _ => 0) b c U V := by
  simpa using
    energyFormIntegral_add μ a (fun _ => 0) (fun _ => 0) U V
      (fun _ => 0) b c hprincipal hlower

/-- The integrated full energy form splits into its principal, drift, and mass pieces. -/
lemma energyFormIntegral_principal_drift_mass
    (hprincipal : Integrable (fun x => energyIntegrand (a x) 0 0 (U x) (V x)) μ)
    (hdrift : Integrable (fun x => energyIntegrand 0 (b x) 0 (U x) (V x)) μ)
    (hmass : Integrable (fun x => energyIntegrand 0 0 (c x) (U x) (V x)) μ) :
    energyFormIntegral μ a b c U V =
      energyFormIntegral μ a (fun _ => 0) (fun _ => 0) U V +
        energyFormIntegral μ (fun _ => 0) b (fun _ => 0) U V +
          energyFormIntegral μ (fun _ => 0) (fun _ => 0) c U V := by
  -- Integrability of the combined lower-order density from drift + mass.
  have hlower :
      Integrable (fun x => energyIntegrand 0 (b x) (c x) (U x) (V x)) μ := by
    refine (hdrift.add hmass).congr (Filter.Eventually.of_forall fun x => ?_)
    simp [Pi.add_apply]
  -- Lower-order additivity: drift + mass.
  have hlower_eq :
      energyFormIntegral μ (fun _ => 0) b c U V =
        energyFormIntegral μ (fun _ => 0) b (fun _ => 0) U V +
          energyFormIntegral μ (fun _ => 0) (fun _ => 0) c U V := by
    simpa using
      energyFormIntegral_add μ (fun _ => 0) b (fun _ => 0) U V
        (fun _ => 0) (fun _ => 0) c hdrift hmass
  -- Principal + lower-order, then algebra.
  calc
    energyFormIntegral μ a b c U V =
        energyFormIntegral μ a (fun _ => 0) (fun _ => 0) U V +
          energyFormIntegral μ (fun _ => 0) b c U V :=
      energyFormIntegral_principal_add_lowerOrder μ a b c U V hprincipal hlower
    _ = energyFormIntegral μ a (fun _ => 0) (fun _ => 0) U V +
          (energyFormIntegral μ (fun _ => 0) b (fun _ => 0) U V +
            energyFormIntegral μ (fun _ => 0) (fun _ => 0) c U V) := by
      rw [hlower_eq]
    _ = energyFormIntegral μ a (fun _ => 0) (fun _ => 0) U V +
          energyFormIntegral μ (fun _ => 0) b (fun _ => 0) U V +
            energyFormIntegral μ (fun _ => 0) (fun _ => 0) c U V := by
      rw [add_assoc]

/-- The integrated full energy form is a shifted-Laplacian model plus the residual
coefficient perturbation. -/
lemma energyFormIntegral_eq_one_zero_baseMass_add_perturbation (hmodel : Integrable
      (fun x => energyIntegrand (1 : Matrix n n ℝ) 0 (m x) (U x) (V x)) μ) (hpert : Integrable
      (fun x => energyIntegrand (a x - 1) (b x) (c x - m x) (U x) (V x)) μ) :
    energyFormIntegral μ a b c U V =
      energyFormIntegral μ (fun _ => (1 : Matrix n n ℝ)) (fun _ => 0) m U V +
        energyFormIntegral μ (fun x => a x - 1) b (fun x => c x - m x) U V := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x))
      (g := fun x => energyIntegrand (1 : Matrix n n ℝ) 0 (m x) (U x) (V x) +
          energyIntegrand (a x - 1) (b x) (c x - m x) (U x) (V x))
      (fun x => energyIntegrand_eq_one_zero_baseMass_add_perturbation_apply
        (a x) (b x) (c x) (m x) (U x) (V x)),
    integral_add hmodel hpert]

/-- The integrated full energy form is the shifted-Laplacian form with the same mass plus the
principal-and-drift perturbation. -/
lemma energyFormIntegral_eq_one_zero_mass_add_perturbation (hmodel : Integrable
      (fun x => energyIntegrand (1 : Matrix n n ℝ) 0 (c x) (U x) (V x)) μ) (hpert : Integrable
      (fun x => energyIntegrand (a x - 1) (b x) 0 (U x) (V x)) μ) :
    energyFormIntegral μ a b c U V =
      energyFormIntegral μ (fun _ => (1 : Matrix n n ℝ)) (fun _ => 0) c U V +
        energyFormIntegral μ (fun x => a x - 1) b (fun _ => 0) U V := by
  simpa using
    energyFormIntegral_eq_one_zero_baseMass_add_perturbation μ a b c U V c hmodel
      (by simpa using hpert)

/-- The integrated `−Δ` model form is the integral of the dot product of the two gradient
components of the jet fields. -/
lemma energyFormIntegral_one_zero_zero :
    energyFormIntegral μ (fun _ => (1 : Matrix n n ℝ)) (fun _ => 0) (fun _ => 0) U V =
      ∫ x, ((V x).2 ⬝ᵥ (U x).2) ∂μ := by
  rw [energyFormIntegral_def]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    by simp

/-- The integrated shifted Laplacian model form `−Δ + c` is the sum of the Dirichlet density
and the mass density. -/
lemma energyFormIntegral_one_zero_mass (m : X → ℝ) :
    energyFormIntegral μ (fun _ => (1 : Matrix n n ℝ)) (fun _ => 0) m U V =
      ∫ x, ((V x).2 ⬝ᵥ (U x).2 + m x * (U x).1 * (V x).1) ∂μ := by
  rw [energyFormIntegral_def]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    by simp

/-- The diagonal of the integrated shifted Laplacian model is the integral of
`‖∇u‖² + c u²` at the jet level. -/
lemma energyFormIntegral_one_zero_mass_self (m : X → ℝ) :
    energyFormIntegral μ (fun _ => (1 : Matrix n n ℝ)) (fun _ => 0) m U U =
      ∫ x, (‖(U x).2‖ ^ 2 + m x * (U x).1 ^ 2) ∂μ := by
  rw [energyFormIntegral_def]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    by simpa using energyIntegrand_one_zero_mass_self (m x) (U x)

variable {Lam beta gamma : ℝ}

/-- Integrated boundedness of the raw-jet energy form from a.e. coefficient bounds.

This is the scalar integral version of `norm_energyIntegrand_apply_le_of_bounds`: if the
pointwise jet product `‖U x‖ * ‖V x‖` is integrable, the absolute value of the integrated form
is bounded by `(Λ + β + γ)` times its integral. -/
lemma norm_energyFormIntegral_le_of_bounds (hLam : 0 ≤ Lam)
    (ha : ∀ᵐ x ∂μ, ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma)
    (hUV : Integrable (fun x => (Lam + beta + gamma) * (‖U x‖ * ‖V x‖)) μ) :
    ‖energyFormIntegral μ a b c U V‖ ≤
      ∫ x, ((Lam + beta + gamma) * (‖U x‖ * ‖V x‖)) ∂μ := by
  rw [energyFormIntegral_def]
  refine norm_integral_le_of_norm_le hUV ?_
  filter_upwards [ha, hb, hc] with x hax hbx hcx
  simpa [mul_assoc] using
    norm_energyIntegrand_apply_le_of_bounds hLam hax hbx hcx (U x) (V x)

/-- Integrated Gårding lower bound from a.e. lower ellipticity and a.e. lower-order
coefficient hypotheses. -/
lemma garding_energyFormIntegral_self_of_bounds (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂μ, ∀ ξ : EuclideanSpace ℝ n,
      lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, 0 ≤ c x)
    (hlower : Integrable
      (fun x => lam / 2 * ‖(U x).2‖ ^ 2 - beta ^ 2 / (2 * lam) * (U x).1 ^ 2) μ)
    (henergy : Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (U x)) μ) :
    ∫ x, (lam / 2 * ‖(U x).2‖ ^ 2 - beta ^ 2 / (2 * lam) * (U x).1 ^ 2) ∂μ
      ≤ energyFormIntegral μ a b c U U := by
  rw [energyFormIntegral_def]
  refine integral_mono_ae hlower henergy ?_
  filter_upwards [ha, hb, hc] with x hax hbx hcx
  exact garding_energyIntegrand_self_of_bounds hlam
    (fun ξ => by simpa [toQuadraticForm'_eq_dotProduct] using hax ξ) hbx hcx (U x)

/-- Integrated Gårding lower bound with a mass floor from a.e. lower ellipticity and a.e.
lower-order coefficient hypotheses. -/
lemma garding_energyFormIntegral_self_of_mass_lower_bound_of_bounds (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂μ, ∀ ξ : EuclideanSpace ℝ n,
      lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, mu ≤ c x)
    (hlower : Integrable
      (fun x => lam / 2 * ‖(U x).2‖ ^ 2 +
        (mu - beta ^ 2 / (2 * lam)) * (U x).1 ^ 2) μ)
    (henergy : Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (U x)) μ) :
    ∫ x, (lam / 2 * ‖(U x).2‖ ^ 2 +
        (mu - beta ^ 2 / (2 * lam)) * (U x).1 ^ 2) ∂μ
      ≤ energyFormIntegral μ a b c U U := by
  rw [energyFormIntegral_def]
  refine integral_mono_ae hlower henergy ?_
  filter_upwards [ha, hb, hc] with x hax hbx hcx
  exact garding_energyIntegrand_self_of_mass_lower_bound_of_bounds hlam
    (fun ξ => by simpa [toQuadraticForm'_eq_dotProduct] using hax ξ) hbx hcx (U x)

/-- Integrated zero-drift diagonal lower bound from an a.e. principal quadratic lower bound
and a.e. nonnegative mass coefficient. -/
lemma integral_min_lam_mass_mul_norm_sq_le_energyFormIntegral_zero_drift_self (hlam : 0 ≤ lam)
    (ha : ∀ᵐ x ∂μ, ∀ ξ : EuclideanSpace ℝ n,
      lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (hc : ∀ᵐ x ∂μ, 0 ≤ c x)
    (hlower : Integrable (fun x => min lam (c x) * ‖U x‖ ^ 2) μ)
    (henergy : Integrable (fun x => energyIntegrand (a x) 0 (c x) (U x) (U x)) μ) :
    ∫ x, (min lam (c x) * ‖U x‖ ^ 2) ∂μ
      ≤ energyFormIntegral μ a (fun _ => 0) c U U := by
  rw [energyFormIntegral_def]
  refine integral_mono_ae hlower henergy ?_
  filter_upwards [ha, hc] with x hax hcx
  exact min_lam_mass_mul_norm_sq_le_energyIntegrand_zero_drift_self hlam
    (fun ξ => by simpa [toQuadraticForm'_eq_dotProduct] using hax ξ) hcx (U x)

/-- An integrated zero-drift energy form dominates the integral of the squared gradient
component under an a.e. principal quadratic lower bound and nonnegative mass coefficient. -/
lemma integral_mul_norm_snd_sq_le_energyFormIntegral_zero_drift_self
    (ha : ∀ᵐ x ∂μ, ∀ ξ : EuclideanSpace ℝ n,
      lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (hc : ∀ᵐ x ∂μ, 0 ≤ c x)
    (hlower : Integrable (fun x => lam * ‖(U x).2‖ ^ 2) μ)
    (henergy : Integrable (fun x => energyIntegrand (a x) 0 (c x) (U x) (U x)) μ) :
    ∫ x, lam * ‖(U x).2‖ ^ 2 ∂μ ≤ energyFormIntegral μ a (fun _ => 0) c U U := by
  rw [energyFormIntegral_def]
  refine integral_mono_ae hlower henergy ?_
  filter_upwards [ha, hc] with x hax hcx
  exact mul_norm_snd_sq_le_energyIntegrand_zero_drift_self
    (fun ξ => by simpa [toQuadraticForm'_eq_dotProduct] using hax ξ) hcx (U x)

/-- A zero-drift diagonal integrated energy form is nonnegative when the principal quadratic
form and mass coefficient are a.e. nonnegative. -/
lemma energyFormIntegral_zero_drift_self_nonneg
    (ha : ∀ᵐ x ∂μ, ∀ ξ : EuclideanSpace ℝ n, 0 ≤ ξ ⬝ᵥ (a x *ᵥ ξ)) (hc : ∀ᵐ x ∂μ, 0 ≤ c x) :
    0 ≤ energyFormIntegral μ a (fun _ => 0) c U U := by
  rw [energyFormIntegral_def]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ha, hc] with x hax hcx
  have hpoint :=
    min_lam_mass_mul_norm_sq_le_energyIntegrand_zero_drift_self (lam := 0) (c₀ := c x)
      le_rfl (fun ξ => by simpa [toQuadraticForm'_eq_dotProduct] using hax ξ)
      hcx (U x)
  simpa [min_eq_left hcx] using hpoint

/-- Integrated explicit diagonal lower bound from a.e. lower ellipticity, a.e.
lower-order coefficient hypotheses, and a mass floor that dominates the drift defect. -/
lemma integral_min_diagonal_lower_bound_mul_norm_sq_le_energyFormIntegral_self_of_bounds
    (hlam : 0 < lam) (ha : ∀ᵐ x ∂μ, ∀ ξ : EuclideanSpace ℝ n,
      lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, mu ≤ c x)
    (hmu : beta ^ 2 / (2 * lam) ≤ mu)
    (hlower : Integrable
      (fun x => min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U x‖ ^ 2) μ)
    (henergy : Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (U x)) μ) :
    ∫ x, (min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U x‖ ^ 2) ∂μ
      ≤ energyFormIntegral μ a b c U U := by
  rw [energyFormIntegral_def]
  refine integral_mono_ae hlower henergy ?_
  filter_upwards [ha, hb, hc] with x hax hbx hcx
  exact min_diagonal_lower_bound_mul_norm_sq_le_energyIntegrand_self hlam
    (fun ξ => by simpa [toQuadraticForm'_eq_dotProduct] using hax ξ) hbx hcx hmu (U x)

namespace UniformlyEllipticOn

variable {Ω : Set X} {lam Lam beta gamma mu : ℝ}
variable {a : X → Matrix n n ℝ} {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
variable {U V : X → ℝ × EuclideanSpace ℝ n}

/-- Integrated boundedness of the energy form from uniform ellipticity and a.e. lower-order
coefficient bounds. -/
lemma norm_energyFormIntegral_le_on (h : UniformlyEllipticOn Ω a lam Lam)
    (hΩ : ∀ᵐ x ∂μ, x ∈ Ω) (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma)
    (hUV : Integrable (fun x => (Lam + beta + gamma) * (‖U x‖ * ‖V x‖)) μ) :
    ‖energyFormIntegral μ a b c U V‖ ≤
      ∫ x, ((Lam + beta + gamma) * (‖U x‖ * ‖V x‖)) ∂μ := by
  refine PDE.norm_energyFormIntegral_le_of_bounds (μ := μ) (a := a) (b := b) (c := c)
    (U := U) (V := V) h.upper_nonneg ?_ hb hc hUV
  filter_upwards [hΩ] with x hx
  exact h.upper_bound hx

/-- Integrated Gårding lower bound from uniform ellipticity and a.e. lower-order
coefficient hypotheses. -/
lemma garding_energyFormIntegral_self_on (h : UniformlyEllipticOn Ω a lam Lam)
    (hΩ : ∀ᵐ x ∂μ, x ∈ Ω) (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, 0 ≤ c x)
    (hlower : Integrable (fun x => lam / 2 * ‖(U x).2‖ ^ 2 - beta ^ 2 / (2 * lam) * (U x).1 ^ 2) μ)
    (henergy : Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (U x)) μ) :
    ∫ x, (lam / 2 * ‖(U x).2‖ ^ 2 - beta ^ 2 / (2 * lam) * (U x).1 ^ 2) ∂μ
      ≤ energyFormIntegral μ a b c U U := by
  refine PDE.garding_energyFormIntegral_self_of_bounds (μ := μ) (a := a) (b := b) (c := c)
    (U := U) h.pos ?_ hb hc hlower henergy
  filter_upwards [hΩ] with x hx
  intro ξ
  simpa [toQuadraticForm'_eq_dotProduct] using h.lower_bound hx ξ

/-- Integrated Gårding lower bound with a mass floor from uniform ellipticity and a.e.
coefficient hypotheses. -/
lemma garding_energyFormIntegral_self_of_mass_lower_bound_on
    (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : ∀ᵐ x ∂μ, x ∈ Ω)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, mu ≤ c x) (hlower : Integrable
      (fun x => lam / 2 * ‖(U x).2‖ ^ 2 + (mu - beta ^ 2 / (2 * lam)) * (U x).1 ^ 2) μ)
    (henergy : Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (U x)) μ) :
    ∫ x, (lam / 2 * ‖(U x).2‖ ^ 2 +
        (mu - beta ^ 2 / (2 * lam)) * (U x).1 ^ 2) ∂μ
      ≤ energyFormIntegral μ a b c U U := by
  refine PDE.garding_energyFormIntegral_self_of_mass_lower_bound_of_bounds (μ := μ) (a := a)
    (b := b) (c := c) (U := U) h.pos ?_ hb hc hlower henergy
  filter_upwards [hΩ] with x hx
  intro ξ
  simpa [toQuadraticForm'_eq_dotProduct] using h.lower_bound hx ξ

/-- Integrated explicit diagonal lower bound from uniform ellipticity, a.e.
coefficient hypotheses, and a mass floor that dominates the drift defect. -/
lemma integral_min_diagonal_lower_bound_mul_norm_sq_le_energyFormIntegral_self_on
    (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : ∀ᵐ x ∂μ, x ∈ Ω)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, mu ≤ c x) (hmu : beta ^ 2 / (2 * lam) ≤ mu)
    (hlower : Integrable (fun x => min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U x‖ ^ 2) μ)
    (henergy : Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (U x)) μ) :
    ∫ x, (min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U x‖ ^ 2) ∂μ
      ≤ energyFormIntegral μ a b c U U := by
  refine PDE.integral_min_diagonal_lower_bound_mul_norm_sq_le_energyFormIntegral_self_of_bounds
    (μ := μ) (a := a) (b := b) (c := c) (U := U) h.pos ?_ hb hc hmu hlower henergy
  filter_upwards [hΩ] with x hx
  intro ξ
  simpa [toQuadraticForm'_eq_dotProduct] using h.lower_bound hx ξ

end UniformlyEllipticOn

end PDE

end TauCeti
