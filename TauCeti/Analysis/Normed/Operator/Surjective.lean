/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Surjective continuous linear maps onto a finite-dimensional space

Surjectivity onto a finite-dimensional space is stable under small perturbations in the operator
norm: the surjective maps form an open subset of the space of continuous linear maps. The source
is an arbitrary normed space over a complete nontrivially normed field.

Mathlib records the companion fact that a surjective continuous linear map between Banach spaces
is an open map, in `ContinuousLinearMap.isOpenMap`; the openness proved here is openness of the
locus of such maps inside `E →L[𝕜] F`, not of any one of them.

## Main results

* `TauCeti.isOpen_setOf_surjective`: surjectivity onto a finite-dimensional space is an open
  condition on continuous linear maps.
-/

public section

open Function

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Surjectivity onto a finite-dimensional space is an open condition on continuous linear maps.

A surjection `A` onto a finite-dimensional space admits a continuous linear right inverse `R`, and
then `B ∘ R` is within distance `‖B - A‖ * ‖R‖` of the identity, hence injective and so, the
target being finite-dimensional, surjective as soon as `B` is close enough to `A`. -/
theorem isOpen_setOf_surjective : IsOpen {A : E →L[𝕜] F | Surjective A} := by
  rw [Metric.isOpen_iff]
  rintro A (hA : Surjective A)
  obtain ⟨R, hAR⟩ := A.exists_rightInverse_of_surjective (A.range_eq_top_of_surjective hA)
  have hAR : ∀ y, A (R y) = y := fun y ↦ by
    have := congrArg (fun g : F →L[𝕜] F ↦ g y) hAR
    simpa using this
  refine ⟨(‖R‖ + 1)⁻¹, by positivity, fun B hB ↦ ?_⟩
  have hBA : ‖B - A‖ < (‖R‖ + 1)⁻¹ := by
    rwa [Metric.mem_ball, dist_eq_norm] at hB
  have hlt : ‖B - A‖ * ‖R‖ < 1 := by
    have h₁ : ‖B - A‖ * ‖R‖ ≤ (‖R‖ + 1)⁻¹ * ‖R‖ :=
      mul_le_mul_of_nonneg_right hBA.le (norm_nonneg R)
    have h₂ : (‖R‖ + 1)⁻¹ * ‖R‖ < 1 := by
      rw [inv_mul_eq_div, div_lt_one (by positivity)]
      linarith
    linarith
  have key : ∀ y : F, ‖B (R y) - y‖ ≤ ‖B - A‖ * ‖R‖ * ‖y‖ := by
    intro y
    have hsub : B (R y) - y = (B - A) (R y) := by simp [hAR]
    rw [hsub]
    calc ‖(B - A) (R y)‖ ≤ ‖B - A‖ * ‖R y‖ := (B - A).le_opNorm _
      _ ≤ ‖B - A‖ * (‖R‖ * ‖y‖) := by gcongr; exact R.le_opNorm y
      _ = ‖B - A‖ * ‖R‖ * ‖y‖ := by ring
  have hinj : Injective ((B.comp R : F →L[𝕜] F) : F →ₗ[𝕜] F) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    by_contra hy0
    have h1 : ‖y‖ ≤ ‖B - A‖ * ‖R‖ * ‖y‖ := by
      have hy' : B (R y) = 0 := hy
      have := key y
      rw [hy', zero_sub, norm_neg] at this
      exact this
    have h2 : 0 < ‖y‖ := norm_pos_iff.2 hy0
    nlinarith
  intro w
  obtain ⟨y, hy⟩ := LinearMap.injective_iff_surjective.1 hinj w
  exact ⟨R y, by simpa using hy⟩

end TauCeti

end
