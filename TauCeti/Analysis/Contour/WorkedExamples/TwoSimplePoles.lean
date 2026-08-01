/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import TauCeti.Analysis.Contour.Residue.SimplePole

/-!
# A circle integral with two simple poles

This file verifies the two-pole worked example from the contour-integration roadmap.  For two
distinct points `s₁` and `s₂`, the function

`z ↦ A / (z - s₁) + B / (z - s₂)`

has residues `A` and `B` at the respective poles.  When both poles lie inside a circle, its
contour integral is therefore `2πi (A + B)`.  The calculation is stated directly for arbitrary
centres, radii, pole positions, and coefficients, so it also covers a vanishing coefficient
without pretending that the corresponding point remains a pole.

The integral calculation uses Mathlib's `circleIntegral.integral_sub_inv_of_mem_ball`; the
residue calculations use the simple-pole API in
`TauCeti.Analysis.Contour.Residue.SimplePole`.

This is the concrete two-simple-pole acceptance criterion in
`TauCetiRoadmap/ContourIntegration/README.md`, under “Worked examples”.
-/

public section

noncomputable section

open Metric

namespace TauCeti.Contour

/-- The rational function with prescribed principal parts `A / (z - s₁)` and
`B / (z - s₂)`. -/
def twoPrincipalParts (A B s₁ s₂ : ℂ) (z : ℂ) : ℂ :=
  A * (z - s₁)⁻¹ + B * (z - s₂)⁻¹

/-- The value of `twoPrincipalParts` at a point. -/
@[simp]
theorem twoPrincipalParts_apply (A B s₁ s₂ z : ℂ) :
    twoPrincipalParts A B s₁ s₂ z = A * (z - s₁)⁻¹ + B * (z - s₂)⁻¹ :=
  twoPrincipalParts.eq_1 A B s₁ s₂ z

/-- The function-level defining equation for `twoPrincipalParts`. -/
theorem twoPrincipalParts_eq (A B s₁ s₂ : ℂ) :
    twoPrincipalParts A B s₁ s₂ = fun z => A * (z - s₁)⁻¹ + B * (z - s₂)⁻¹ :=
  funext fun z => twoPrincipalParts_apply A B s₁ s₂ z

/-- `twoPrincipalParts` is analytic where each nonzero principal part is away from its designated
point, or where coincident principal parts cancel. -/
theorem analyticAt_twoPrincipalParts {A B s₁ s₂ z : ℂ} (h : ((A = 0 ∨ z ≠ s₁) ∧ (B = 0 ∨ z ≠ s₂)) ∨
      (s₁ = s₂ ∧ A + B = 0)) :
    AnalyticAt ℂ (twoPrincipalParts A B s₁ s₂) z := by
  rcases h with ⟨hz₁, hz₂⟩ | ⟨rfl, hAB⟩
  · rcases hz₁ with rfl | hz₁
    · rcases hz₂ with rfl | hz₂
      · rw [twoPrincipalParts_eq]
        simp only [zero_mul, zero_add]
        exact analyticAt_const
      · rw [twoPrincipalParts_eq]
        simp only [zero_mul, zero_add]
        exact analyticAt_const.mul
          ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 hz₂))
    rcases hz₂ with rfl | hz₂
    · rw [twoPrincipalParts_eq]
      simp only [zero_mul, add_zero]
      exact analyticAt_const.mul
        ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 hz₁))
    exact (analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv
      (sub_ne_zero.2 hz₁))).add (analyticAt_const.mul
        ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 hz₂)))
  rw [twoPrincipalParts_eq]
  have heq : (fun w : ℂ => A * (w - s₁)⁻¹ + B * (w - s₁)⁻¹) = fun _ => 0 := by
    funext w
    rw [← add_mul, hAB, zero_mul]
  rw [heq]
  exact analyticAt_const

/-- The function `twoPrincipalParts` is meromorphic everywhere. -/
theorem meromorphicAt_twoPrincipalParts (A B s₁ s₂ z : ℂ) :
    MeromorphicAt (twoPrincipalParts A B s₁ s₂) z := by
  exact (analyticAt_const.meromorphicAt.mul
    ((analyticAt_id.sub analyticAt_const).meromorphicAt.inv)).add
      (analyticAt_const.meromorphicAt.mul
        ((analyticAt_id.sub analyticAt_const).meromorphicAt.inv))

/-- At the first designated point, the residue of `twoPrincipalParts` is the first coefficient if
the other principal part vanishes or is designated at a distinct point. -/
@[simp]
theorem residue_twoPrincipalParts_left {A B s₁ s₂ : ℂ} (h : B = 0 ∨ s₁ ≠ s₂) :
    residue (twoPrincipalParts A B s₁ s₂) s₁ = A := by
  rcases h with rfl | h
  · simp [twoPrincipalParts_eq]
  rw [twoPrincipalParts_eq]
  have hf₁ : MeromorphicAt (fun z => A * (z - s₁)⁻¹) s₁ :=
    analyticAt_const.meromorphicAt.mul (meromorphicAt_sub_inv s₁)
  have hf₂ : MeromorphicAt (fun z => B * (z - s₂)⁻¹) s₁ :=
    analyticAt_const.meromorphicAt.mul
      ((analyticAt_id.sub analyticAt_const).meromorphicAt.inv)
  have hadd : (fun z => A * (z - s₁)⁻¹ + B * (z - s₂)⁻¹) =
      (fun z => A * (z - s₁)⁻¹) + (fun z => B * (z - s₂)⁻¹) := by
    funext z
    rw [Pi.add_apply]
  rw [hadd, residue_add hf₁ hf₂, residue_const_mul_sub_inv,
    residue_eq_zero_of_analyticAt]
  · simp
  · exact analyticAt_const.mul
      ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 h))

/-- At the second designated point, the residue of `twoPrincipalParts` is the second coefficient if
the other principal part vanishes or is designated at a distinct point. -/
@[simp]
theorem residue_twoPrincipalParts_right {A B s₁ s₂ : ℂ} (h : A = 0 ∨ s₁ ≠ s₂) :
    residue (twoPrincipalParts A B s₁ s₂) s₂ = B := by
  rcases h with rfl | h
  · simp [twoPrincipalParts_eq]
  rw [twoPrincipalParts_eq]
  have hf₁ : MeromorphicAt (fun z => A * (z - s₁)⁻¹) s₂ :=
    analyticAt_const.meromorphicAt.mul
      ((analyticAt_id.sub analyticAt_const).meromorphicAt.inv)
  have hf₂ : MeromorphicAt (fun z => B * (z - s₂)⁻¹) s₂ :=
    analyticAt_const.meromorphicAt.mul (meromorphicAt_sub_inv s₂)
  have hadd : (fun z => A * (z - s₁)⁻¹ + B * (z - s₂)⁻¹) =
      (fun z => A * (z - s₁)⁻¹) + (fun z => B * (z - s₂)⁻¹) := by
    funext z
    rw [Pi.add_apply]
  rw [hadd, residue_add hf₁ hf₂, residue_const_mul_sub_inv,
    residue_eq_zero_of_analyticAt, zero_add]
  exact analyticAt_const.mul
    ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 h.symm))

/-- A reciprocal simple pole strictly inside a circle is circle integrable. -/
private theorem circleIntegrable_const_mul_sub_inv {A c s : ℂ} {R : ℝ} (hs : s ∈ ball c R) :
    CircleIntegrable (fun z => A * (z - s)⁻¹) c R := by
  have hR : 0 < R := pos_of_mem_ball hs
  apply CircleIntegrable.const_fun_smul (a := A)
  rw [circleIntegrable_sub_inv_iff]
  right
  rw [abs_of_pos hR]
  exact fun hsp => (ne_of_lt (mem_ball.1 hs)) (mem_sphere.1 hsp)

/-- **Two-pole circle integral.** If the designated point of each nonzero principal part lies
strictly inside the circle `C(c, R)`, then the integral of `A / (z - s₁) + B / (z - s₂)` around
that circle is `2πi (A + B)`.  Together with
`residue_twoPrincipalParts_left` and `residue_twoPrincipalParts_right`, this is the roadmap's worked
example of the classical residue theorem with two simple poles. -/
theorem circleIntegral_twoPrincipalParts {A B c s₁ s₂ : ℂ} {R : ℝ}
    (hs₁ : A = 0 ∨ s₁ ∈ ball c R) (hs₂ : B = 0 ∨ s₂ ∈ ball c R) :
    circleIntegral (twoPrincipalParts A B s₁ s₂) c R =
      2 * (Real.pi : ℂ) * Complex.I * (A + B) := by
  rcases hs₁ with rfl | hs₁
  · rcases hs₂ with rfl | hs₂
    · rw [twoPrincipalParts_eq]
      simp only [zero_mul, zero_add]
      simp [circleIntegral]
    · rw [twoPrincipalParts_eq]
      simp only [zero_mul, zero_add, circleIntegral.integral_const_mul,
        circleIntegral.integral_sub_inv_of_mem_ball hs₂]
      ring
  rcases hs₂ with rfl | hs₂
  · rw [twoPrincipalParts_eq]
    simp only [zero_mul, add_zero, circleIntegral.integral_const_mul,
      circleIntegral.integral_sub_inv_of_mem_ball hs₁]
    ring
  rw [twoPrincipalParts_eq, circleIntegral.integral_add
    (circleIntegrable_const_mul_sub_inv hs₁) (circleIntegrable_const_mul_sub_inv hs₂),
    circleIntegral.integral_const_mul, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_inv_of_mem_ball hs₁,
    circleIntegral.integral_sub_inv_of_mem_ball hs₂]
  ring

/-- The two-pole calculation in residue-theorem form: for distinct designated points, with the
point of each nonzero principal part inside the circle, the integral is `2πi` times the sum of the
two residues. -/
theorem circleIntegral_twoPrincipalParts_eq_residue_sum {A B c s₁ s₂ : ℂ} {R : ℝ}
    (hs : s₁ ≠ s₂) (hs₁ : A = 0 ∨ s₁ ∈ ball c R) (hs₂ : B = 0 ∨ s₂ ∈ ball c R) :
    circleIntegral (twoPrincipalParts A B s₁ s₂) c R =
      2 * (Real.pi : ℂ) * Complex.I *
        (residue (twoPrincipalParts A B s₁ s₂) s₁ +
          residue (twoPrincipalParts A B s₁ s₂) s₂) := by
  rw [circleIntegral_twoPrincipalParts hs₁ hs₂, residue_twoPrincipalParts_left (Or.inr hs),
    residue_twoPrincipalParts_right (Or.inr hs)]

end TauCeti.Contour

end
