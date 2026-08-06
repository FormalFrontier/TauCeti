/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Differentiating inverse continuous linear maps

This file packages the derivative of an inverse family of continuous linear maps at the identity,
including its action on a varying vector. The result is the analytic input for differentiating a
vector-field pullback along a flow.

This supplies a prerequisite for Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main result

* `HasDerivAt.clm_inverse_apply`: differentiates `(A t)⁻¹ (w t)` when `A 0 = id`.
* `HasDerivAt.clm_inverse_apply_comp`: differentiates `(A t)⁻¹ (W (z t))` by the chain rule.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The infinitesimal adjoint".
-/

public section

noncomputable section

open ContinuousLinearMap
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : ℝ → E →L[ℝ] E} {A' : E →L[ℝ] E} {w : ℝ → E} {w' : E}

/-- If a differentiable family of invertible continuous linear maps is the identity at zero, and
its inverse family is differentiable there, then the derivative of the inverse acting on a
differentiable vector curve is `w' - A' (w 0)`. -/
theorem HasDerivAt.clm_inverse_apply (hA : HasDerivAt A A' 0)
    (hA0 : A 0 = ContinuousLinearMap.id ℝ E)
    (hInvDiff : DifferentiableAt ℝ (fun t => (A t).inverse) 0)
    (hAInv : ∀ᶠ t in 𝓝 0, (A t).IsInvertible) (hw : HasDerivAt w w' 0) :
    HasDerivAt (fun t => (A t).inverse (w t)) (w' - A' (w 0)) 0 := by
  let B' : E →L[ℝ] E := _root_.deriv (fun t => (A t).inverse) 0
  have hInvRaw : HasDerivAt (fun t => (A t).inverse) B' 0 := hInvDiff.hasDerivAt
  have hInv : HasDerivAt (fun t => (A t).inverse) (-A') 0 := by
    have hB'eq : B' = -A' := by
      apply ContinuousLinearMap.ext
      intro v
      have hconst : HasDerivAt (fun _ : ℝ => v) 0 0 := hasDerivAt_const 0 v
      have hBv := hInvRaw.clm_apply hconst
      have hABv := hA.clm_apply hBv
      have heq : (fun t => A t ((A t).inverse v)) =ᶠ[𝓝 0] fun _ => v := by
        filter_upwards [hAInv] with t ht
        exact ht.self_apply_inverse v
      have hzero : HasDerivAt (fun t => A t ((A t).inverse v)) 0 0 := by
        exact hconst.congr_of_eventuallyEq heq
      have hderivZero := hABv.unique hzero
      simp only [hA0, ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_apply,
        map_zero, add_zero] at hderivZero
      exact eq_neg_of_add_eq_zero_right hderivZero
    rw [hB'eq] at hInvRaw
    exact hInvRaw
  simpa [hA0, sub_eq_add_neg, add_comm] using hInv.clm_apply hw

/-- Chain-rule form of `HasDerivAt.clm_inverse_apply`, for the inverse family acting on a vector
field evaluated along a curve. -/
theorem HasDerivAt.clm_inverse_apply_comp {z : ℝ → E} {z' : E} {W : E → E}
    {W' : E →L[ℝ] E} (hA : HasDerivAt A A' 0)
    (hA0 : A 0 = ContinuousLinearMap.id ℝ E)
    (hInvDiff : DifferentiableAt ℝ (fun t => (A t).inverse) 0)
    (hAInv : ∀ᶠ t in 𝓝 0, (A t).IsInvertible) (hz : HasDerivAt z z' 0)
    (hW : HasFDerivAt W W' (z 0)) :
    HasDerivAt (fun t => (A t).inverse (W (z t)))
      (W' z' - A' (W (z 0))) 0 := by
  exact hA.clm_inverse_apply hA0 hInvDiff hAInv (hW.comp_hasDerivAt 0 hz)
