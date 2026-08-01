/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Basic

/-!
# Pointwise diagonal lower bounds for divergence-form energy integrands

The file `TauCeti.Analysis.PDE.EnergyForm.Basic` gives the pointwise energy integrand for a
divergence-form operator together with its pointwise Gårding lower bound.  This file refines
that Gårding estimate into an explicit diagonal lower bound
`min (λ/2) (μ − β²/2λ) · ‖U‖² ≤ energyIntegrand A b c U U`, once the zeroth-order mass
coefficient has a lower bound that non-strictly dominates the drift defect `β²/2λ`.

These are pointwise finite-dimensional statements on the jet fibre `ℝ × EuclideanSpace ℝ n`.
They are **not** coercivity of a bilinear form in the sense of `IsCoercive`, and they are not
the hypothesis of Lax--Milgram: `TauCeti.Analysis.InnerProductSpace.LaxMilgram` needs
coercivity of the *integrated* form on a complete inner-product (H¹-type) space, which is
later Lane A/D work.  The genuine consumer of these pointwise bounds is the integrated
inequality `∫ (min (λ/2) (μ − β²/2λ)) · ‖U‖² ≤ energyFormIntegral` in
`TauCeti.Analysis.PDE.Integrated.EnergyForm`, obtained by integrating them; no
finite-dimensional jet fibre is fed into Lax--Milgram.

The lower-bound theorems below take a single principal coefficient `A`, drift coefficient
`b₀`, and mass coefficient `c₀`, together with their pointwise bounds. Callers holding a
field-level `UniformlyEllipticOn Ω a λ Λ` hypothesis should use the pointwise specializations
in `TauCeti.Analysis.PDE.Uniform.EllipticEnergy`, which supply the principal lower bound at a
chosen point `x ∈ Ω`.

Symmetry of the same zero-drift integrand is recorded in
`TauCeti.Analysis.PDE.SymmetricEnergy`.  Consumers that need the hypotheses side by side
should use those symmetry lemmas together with the lower-bound lemmas below, preserving the
separate API boundaries for algebraic symmetry and quantitative lower bounds.

The bookkeeping follows the standard Young-inequality absorption argument used in the
energy method, as in Evans, *Partial Differential Equations*, Chapter 6.

## Main declarations

* `TauCeti.PDE.garding_energyIntegrand_self_of_mass_lower_bound_of_bounds`: pointwise
  Gårding lower bound with a mass floor.
* `TauCeti.PDE.min_diagonal_lower_bound_mul_norm_sq_le_energyIntegrand_self`: explicit
  diagonal estimate from the mass-floor lower bound.
* `TauCeti.PDE.min_lam_mass_mul_norm_sq_le_energyIntegrand_zero_drift_self`: explicit
  zero-drift diagonal lower bound from a principal quadratic lower bound and nonnegative mass.
-/

public section

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {n : Type*} [Fintype n]

/-- Local classical decidable equality for finite coordinate indices in lower-bound proofs. -/
noncomputable local instance energyLowerBoundsDecidableEq : DecidableEq n := Classical.decEq n

variable {lam mu beta : ℝ}

/-- The square of the product sup norm is controlled by the two squared coordinate norms
with the smaller coefficient. -/
private lemma min_mul_prod_norm_sq_le_add (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] (U : E × F) :
    min lam mu * ‖U‖ ^ 2 ≤ lam * ‖U.2‖ ^ 2 + mu * ‖U.1‖ ^ 2 := by
  have hmin_lam : min lam mu ≤ lam := min_le_left _ _
  have hmin_mu : min lam mu ≤ mu := min_le_right _ _
  rw [Prod.norm_def]
  rcases le_total ‖U.1‖ ‖U.2‖ with hle | hle
  · rw [max_eq_right hle]
    calc
      min lam mu * ‖U.2‖ ^ 2 ≤ lam * ‖U.2‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right hmin_lam (sq_nonneg ‖U.2‖)
      _ ≤ lam * ‖U.2‖ ^ 2 + mu * ‖U.1‖ ^ 2 := by
        exact le_add_of_nonneg_right (mul_nonneg hmu (sq_nonneg ‖U.1‖))
  · rw [max_eq_left hle]
    calc
      min lam mu * ‖U.1‖ ^ 2 ≤ mu * ‖U.1‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right hmin_mu (sq_nonneg ‖U.1‖)
      _ ≤ lam * ‖U.2‖ ^ 2 + mu * ‖U.1‖ ^ 2 := by
        exact le_add_of_nonneg_left (mul_nonneg hlam (sq_nonneg ‖U.2‖))

/-- Pointwise lower bound for the energy integrand with bounded drift and a mass lower bound.

If the principal part has quadratic lower bound `λ‖ξ‖²`, the drift satisfies `‖b₀‖ ≤ β`, and
the mass coefficient satisfies `μ ≤ c₀`, then the diagonal of the jet form is bounded below by
`(λ/2)‖∇u‖² + (μ − β²/2λ)|u|²`. -/
lemma garding_energyIntegrand_self_of_mass_lower_bound_of_bounds (hlam : 0 < lam)
    {A : Matrix n n ℝ} {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (U : ℝ × EuclideanSpace ℝ n) :
    lam / 2 * ‖U.2‖ ^ 2 + (mu - beta ^ 2 / (2 * lam)) * U.1 ^ 2
      ≤ energyIntegrand A b₀ c₀ U U := by
  have hdecomp : energyIntegrand A b₀ c₀ U U
      = energyIntegrand A b₀ (c₀ - mu) U U + mu * U.1 ^ 2 := by
    rw [energyIntegrand_self, energyIntegrand_self]; ring
  have hgard := garding_energyIntegrand_self_of_bounds hlam hA hb (sub_nonneg.mpr hc) U
  rw [hdecomp]
  have hrw : lam / 2 * ‖U.2‖ ^ 2 + (mu - beta ^ 2 / (2 * lam)) * U.1 ^ 2
      = lam / 2 * ‖U.2‖ ^ 2 - beta ^ 2 / (2 * lam) * U.1 ^ 2 + mu * U.1 ^ 2 := by ring
  rw [hrw]
  linarith [hgard]

/-- The mass-floor Gårding lower bound implies the explicit diagonal estimate with constant
`min (λ / 2) (μ - β² / (2λ))`, assuming this second coefficient is nonnegative. -/
lemma min_diagonal_lower_bound_mul_norm_sq_le_energyIntegrand_self (hlam : 0 < lam)
    {A : Matrix n n ℝ} {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (hmu : beta ^ 2 / (2 * lam) ≤ mu)
    (U : ℝ × EuclideanSpace ℝ n) :
    min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U‖ ^ 2
      ≤ energyIntegrand A b₀ c₀ U U := by
  have hhalf : 0 < lam / 2 := half_pos hlam
  have hdef : 0 ≤ mu - beta ^ 2 / (2 * lam) := sub_nonneg.mpr hmu
  have hnorm := min_mul_prod_norm_sq_le_add hhalf.le hdef U
  rw [Real.norm_eq_abs, sq_abs] at hnorm
  exact hnorm.trans
    (garding_energyIntegrand_self_of_mass_lower_bound_of_bounds hlam hA hb hc U)

/-- Zero-drift diagonal lower bound from a principal quadratic lower bound and nonnegative
mass coefficient. -/
lemma min_lam_mass_mul_norm_sq_le_energyIntegrand_zero_drift_self {A : Matrix n n ℝ}
    {c₀ : ℝ} (hlam : 0 ≤ lam) (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hc : 0 ≤ c₀) (U : ℝ × EuclideanSpace ℝ n) :
    min lam c₀ * ‖U‖ ^ 2 ≤ energyIntegrand A 0 c₀ U U := by
  have hprod := min_mul_prod_norm_sq_le_add hlam hc U
  have hA' := hA U.2
  rw [energyIntegrand_self]
  simp only [inner_zero_left, zero_mul, add_zero]
  rw [Real.norm_eq_abs, sq_abs] at hprod
  exact hprod.trans (add_le_add hA' le_rfl)

/-- Explicit diagonal lower bound for the shifted Laplacian jet form with nonnegative mass. -/
lemma min_one_mass_mul_norm_sq_le_energyIntegrand_one_zero_mass_self {c : ℝ} (hc : 0 ≤ c)
    (U : ℝ × EuclideanSpace ℝ n) :
    min 1 c * ‖U‖ ^ 2 ≤ energyIntegrand (1 : Matrix n n ℝ) 0 c U U :=
  min_lam_mass_mul_norm_sq_le_energyIntegrand_zero_drift_self zero_le_one
    (by intro ξ; simp) hc U

end PDE

end TauCeti
