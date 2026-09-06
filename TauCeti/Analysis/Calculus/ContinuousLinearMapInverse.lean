/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Inverting and differentiating continuous linear maps

This file collects two kinds of facts about inverting continuous linear maps. The first is a
perturbation criterion: a map differing from a continuous linear equivalence `L` by less than
`‖L⁻¹‖⁻¹` in operator norm is again invertible, by a Neumann series. The second packages the
derivative of a differentiable inverse family of continuous linear maps at an invertible base
point, including its action on a varying vector; that is the analytic input for differentiating a
vector-field pullback along a parametric family.

This supplies a prerequisite for Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main results

* `ContinuousLinearMap.isInvertible_of_norm_sub_lt` and
  `ContinuousLinearMap.isInvertible_of_norm_sub_le_half`: a continuous linear map closer to an
  invertible one than the reciprocal norm of its inverse — or than half of it — is itself
  invertible.
* `HasDerivAt.clm_inverse`: differentiates `(A t)⁻¹`.
* `HasDerivAt.clm_inverse_apply`: differentiates `(A t)⁻¹ (w t)`.
* `DifferentiableAt.clm_inverse_of_completeSpace`: the inverse of a differentiable family between
  Banach spaces is differentiable at an invertible base point.
* `HasDerivAt.clm_inverse_of_completeSpace`: the Banach-space specialization for an inverse family.
* `HasDerivAt.clm_inverse_apply_of_completeSpace`: the Banach-space specialization acting on a
  vector curve.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The infinitesimal adjoint".
-/

public section

noncomputable section

open ContinuousLinearMap
open scoped Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section Perturbation

/-- A continuous linear map that differs from a continuous linear equivalence `L` by less than
`‖L⁻¹‖⁻¹` in operator norm is itself invertible: `L⁻¹A` is close enough to `1` to be a unit of the
Banach algebra of endomorphisms of `E`. -/
theorem ContinuousLinearMap.isInvertible_of_norm_sub_lt [CompleteSpace E]
    (L : E ≃L[𝕜] F) {A : E →L[𝕜] F}
    (h : ‖A - (L : E →L[𝕜] F)‖₊ < ‖(L.symm : F →L[𝕜] E)‖₊⁻¹) : A.IsInvertible := by
  have hsymm : ‖(L.symm : F →L[𝕜] E)‖₊ ≠ 0 := by
    rintro h0
    rw [h0, inv_zero] at h
    simp at h
  have hpos : 0 < ‖(L.symm : F →L[𝕜] E)‖ := by
    simpa using pos_iff_ne_zero.2 hsymm
  have hreal : ‖A - (L : E →L[𝕜] F)‖ < ‖(L.symm : F →L[𝕜] E)‖⁻¹ := by
    rw [← NNReal.coe_lt_coe] at h
    simpa using h
  have hnorm : ‖(L.symm : F →L[𝕜] E).comp A - 1‖ < 1 :=
    calc
      ‖(L.symm : F →L[𝕜] E).comp A - 1‖ =
          ‖(L.symm : F →L[𝕜] E).comp (A - (L : E →L[𝕜] F))‖ := by
        congr 1
        ext x
        simp
      _ ≤ ‖(L.symm : F →L[𝕜] E)‖ * ‖A - (L : E →L[𝕜] F)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ < ‖(L.symm : F →L[𝕜] E)‖ * ‖(L.symm : F →L[𝕜] E)‖⁻¹ :=
          mul_lt_mul_of_pos_left hreal hpos
      _ = 1 := mul_inv_cancel₀ hpos.ne'
  let _ : Nontrivial E := not_subsingleton_iff_nontrivial.mp (by
    intro hE
    let _ := hE
    exact hpos.ne' (norm_of_subsingleton _))
  let u : (E →L[𝕜] E)ˣ := Units.ofNearby 1 ((L.symm : F →L[𝕜] E).comp A) (by simpa using hnorm)
  refine ⟨(ContinuousLinearEquiv.unitsEquiv 𝕜 E u).trans L, ?_⟩
  ext x
  simp [u, ContinuousLinearEquiv.unitsEquiv_apply]

/-- A continuous linear map within `‖L⁻¹‖⁻¹ / 2` of a continuous linear equivalence `L` is
invertible. This is the shape in which Mathlib's inverse function theorem supplies the estimate. -/
theorem ContinuousLinearMap.isInvertible_of_norm_sub_le_half [CompleteSpace E]
    (L : E ≃L[𝕜] F) {A : E →L[𝕜] F}
    (h : ‖A - (L : E →L[𝕜] F)‖₊ ≤ ‖(L.symm : F →L[𝕜] E)‖₊⁻¹ / 2) : A.IsInvertible := by
  rcases eq_or_ne (‖(L.symm : F →L[𝕜] E)‖₊)⁻¹ 0 with h0 | h0
  · rw [h0, zero_div, le_zero_iff, nnnorm_eq_zero, sub_eq_zero] at h
    exact h ▸ ContinuousLinearMap.isInvertible_equiv
  · exact ContinuousLinearMap.isInvertible_of_norm_sub_lt L (h.trans_lt (NNReal.half_lt_self h0))

end Perturbation

variable {t₀ : 𝕜} {A : 𝕜 → E →L[𝕜] F} {A' : E →L[𝕜] F} {w : 𝕜 → F} {w' : F}

/-- **Invertibility persists where the inverse family is continuous.** If `A t₀` is invertible and
`t ↦ (A t).inverse` is continuous at `t₀`, then `A t` is invertible for every `t` near `t₀`. -/
private theorem eventually_isInvertible_of_isInvertible_of_continuousAt_inverse
    (hA0Inv : (A t₀).IsInvertible) (hcont : ContinuousAt (fun t => (A t).inverse) t₀) :
    ∀ᶠ t in 𝓝 t₀, (A t).IsInvertible := by
  -- The continuity argument below needs the inverse at `t₀` to be nonzero, which fails exactly
  -- when `E` is a subsingleton; in that case all maps involved are zero and invertibility is
  -- instead immediate from the induced subsingleton structures.
  by_cases hE : Subsingleton E
  · rcases hA0Inv with ⟨e, _⟩
    let _ : Subsingleton E := hE
    let _ : Subsingleton F := e.toEquiv.symm.subsingleton
    exact Filter.Eventually.of_forall fun t => by
      -- Between subsingleton spaces every continuous linear map is the zero map.
      have hAt_zero : A t = 0 := Subsingleton.elim _ _
      rw [hAt_zero, isInvertible_zero_iff]
      exact ⟨inferInstance, inferInstance⟩
  · have hInv0Inv : ((A t₀).inverse).IsInvertible := hA0Inv.inverse
    have hInv0 : (A t₀).inverse ≠ 0 := by
      intro hzero
      rw [hzero, isInvertible_zero_iff] at hInv0Inv
      exact hE hInv0Inv.2
    filter_upwards [hcont.eventually_ne hInv0] with t ht
    by_contra hAt
    -- A non-invertible map has zero `inverse`, contradicting continuity near the nonzero inverse
    -- at the base point.
    exact ht (inverse_of_not_isInvertible hAt)

/-- The derivative of an inverse family of continuous linear maps, assuming the family is
invertible at the base point and the inverse family is differentiable there. -/
theorem HasDerivAt.clm_inverse (hA : HasDerivAt A A' t₀)
    (hA0Inv : (A t₀).IsInvertible)
    (hInvDiff : DifferentiableAt 𝕜 (fun t => (A t).inverse) t₀) :
    HasDerivAt (fun t => (A t).inverse)
      (-((A t₀).inverse.comp (A'.comp (A t₀).inverse))) t₀ := by
  have hAInv : ∀ᶠ t in 𝓝 t₀, (A t).IsInvertible :=
    eventually_isInvertible_of_isInvertible_of_continuousAt_inverse hA0Inv hInvDiff.continuousAt
  let B' : F →L[𝕜] E := _root_.deriv (fun t => (A t).inverse) t₀
  have hInvRaw : HasDerivAt (fun t => (A t).inverse) B' t₀ := hInvDiff.hasDerivAt
  have hB'eq : B' = -((A t₀).inverse.comp (A'.comp (A t₀).inverse)) := by
    apply ContinuousLinearMap.ext
    intro v
    have hconst : HasDerivAt (fun _ : 𝕜 => v) 0 t₀ := hasDerivAt_const t₀ v
    have hBv := hInvRaw.clm_apply hconst
    have hABv := hA.clm_apply hBv
    have heq : (fun t => A t ((A t).inverse v)) =ᶠ[𝓝 t₀] fun _ => v := by
      filter_upwards [hAInv] with t ht
      exact ht.self_apply_inverse v
    have hzero : HasDerivAt (fun t => A t ((A t).inverse v)) 0 t₀ := by
      exact hconst.congr_of_eventuallyEq heq
    have hderivZero := hABv.unique hzero
    simp only [map_zero, add_zero] at hderivZero
    apply hA0Inv.injective
    simp only [neg_apply, ContinuousLinearMap.comp_apply]
    rw [map_neg, hA0Inv.self_apply_inverse]
    exact eq_neg_of_add_eq_zero_right hderivZero
  rw [hB'eq] at hInvRaw
  exact hInvRaw

/-- The derivative of an inverse family of continuous linear maps acting on a differentiable
vector curve, assuming the family is invertible at the base point and the inverse family is
differentiable there. -/
theorem HasDerivAt.clm_inverse_apply (hA : HasDerivAt A A' t₀)
    (hA0Inv : (A t₀).IsInvertible)
    (hInvDiff : DifferentiableAt 𝕜 (fun t => (A t).inverse) t₀)
    (hw : HasDerivAt w w' t₀) :
    HasDerivAt (fun t => (A t).inverse (w t))
      ((A t₀).inverse w' - (A t₀).inverse (A' ((A t₀).inverse (w t₀)))) t₀ := by
  simpa only [neg_apply, ContinuousLinearMap.comp_apply, sub_eq_neg_add] using
    (hA.clm_inverse hA0Inv hInvDiff).clm_apply hw

/-- In a Banach space, the inverse of a differentiable family is differentiable at an invertible
base point. -/
theorem DifferentiableAt.clm_inverse_of_completeSpace [CompleteSpace E]
    (hA : DifferentiableAt 𝕜 A t₀) (hA0Inv : (A t₀).IsInvertible) :
    DifferentiableAt 𝕜 (fun t => (A t).inverse) t₀ :=
  (hA0Inv.contDiffAt_map_inverse (n := 1)).differentiableAt one_ne_zero |>.comp t₀ hA

/-- The derivative of an inverse family of continuous linear maps between Banach spaces. -/
theorem HasDerivAt.clm_inverse_of_completeSpace [CompleteSpace E]
    (hA : HasDerivAt A A' t₀) (hA0Inv : (A t₀).IsInvertible) :
    HasDerivAt (fun t => (A t).inverse)
      (-((A t₀).inverse.comp (A'.comp (A t₀).inverse))) t₀ := by
  apply hA.clm_inverse hA0Inv
  exact DifferentiableAt.clm_inverse_of_completeSpace hA.differentiableAt hA0Inv

/-- The derivative of an inverse family of continuous linear maps between Banach spaces, acting
on a differentiable vector curve. -/
theorem HasDerivAt.clm_inverse_apply_of_completeSpace [CompleteSpace E]
    (hA : HasDerivAt A A' t₀) (hA0Inv : (A t₀).IsInvertible) (hw : HasDerivAt w w' t₀) :
    HasDerivAt (fun t => (A t).inverse (w t))
      ((A t₀).inverse w' - (A t₀).inverse (A' ((A t₀).inverse (w t₀)))) t₀ := by
  exact hA.clm_inverse_apply hA0Inv
    (DifferentiableAt.clm_inverse_of_completeSpace hA.differentiableAt hA0Inv) hw
