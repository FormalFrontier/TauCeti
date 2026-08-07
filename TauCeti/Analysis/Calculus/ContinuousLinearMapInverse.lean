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

* `HasDerivAt.clm_inverse_apply`: differentiates `(A t)⁻¹ (w t)`.

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

/-- The derivative of an inverse family of continuous linear maps acting on a differentiable
vector curve. -/
theorem HasDerivAt.clm_inverse_apply (hA : HasDerivAt A A' 0)
    (hA0Inv : (A 0).IsInvertible)
    (hInvDiff : DifferentiableAt ℝ (fun t => (A t).inverse) 0)
    (hAInv : ∀ᶠ t in 𝓝 0, (A t).IsInvertible) (hw : HasDerivAt w w' 0) :
    HasDerivAt (fun t => (A t).inverse (w t))
      ((A 0).inverse w' - (A 0).inverse (A' ((A 0).inverse (w 0)))) 0 := by
  let B' : E →L[ℝ] E := _root_.deriv (fun t => (A t).inverse) 0
  have hInvRaw : HasDerivAt (fun t => (A t).inverse) B' 0 := hInvDiff.hasDerivAt
  have hInv : HasDerivAt (fun t => (A t).inverse)
      (-((A 0).inverse.comp (A'.comp (A 0).inverse))) 0 := by
    have hB'eq : B' = -((A 0).inverse.comp (A'.comp (A 0).inverse)) := by
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
      simp only [map_zero, add_zero] at hderivZero
      apply hA0Inv.injective
      change (A 0) (B' v) = (A 0) (-((A 0).inverse (A' ((A 0).inverse v))))
      rw [map_neg, hA0Inv.self_apply_inverse]
      exact eq_neg_of_add_eq_zero_right hderivZero
    rw [hB'eq] at hInvRaw
    exact hInvRaw
  simpa [sub_eq_add_neg, add_comm] using hInv.clm_apply hw
