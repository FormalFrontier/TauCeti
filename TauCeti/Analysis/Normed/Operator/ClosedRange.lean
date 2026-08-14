/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.Complement

/-!
# The a priori estimate of a closed-range operator

A continuous linear map `T : E →L[𝕜] F` between Banach spaces with closed range fails to be
bounded below only in the direction of its kernel. When that kernel is complemented, this file
makes the failure quantitative, in the classical form

`‖x‖ ≤ C * ‖T x‖ + ‖P x‖`,

where `P` is a continuous projection of `E` onto `ker T`. When the kernel is in addition
finite-dimensional the estimate turns an operator bound into a compactness statement: the
correction term ranges over a finite-dimensional — hence locally compact — direction.

The proof is one application of the open mapping theorem, in the packaged form
`ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range`: on a topological complement
`X₁` of the kernel, `T` is injective with closed range, so it is bounded below there. Mathlib's
file carries a `TODO` asking for exactly this generalisation once Fredholm operators are available.

## Main declarations

* `ContinuousLinearMap.exists_norm_le_mul_norm_of_isTopCompl`: a closed-range operator is bounded
  below on any topological complement of its kernel.
* `ContinuousLinearMap.exists_norm_le_mul_norm_add_norm_projectionL`: the a priori estimate
  against the projection onto the kernel determined by a chosen complement.
* `ContinuousLinearMap.exists_projection_norm_le_mul_norm_add_norm`: the same estimate with the
  complement discharged, so that the only data left is a continuous projection with range the
  kernel.

Nothing here is Fredholm theory — only a closed range and a complemented kernel are used — but the
Fredholm reading is the intended one: `TauCeti.Analysis.Fredholm.Estimate` specialises the last
estimate to a Fredholm operator, and `TauCeti.Analysis.Fredholm.Proper` uses it to prove that a map
with Fredholm derivative is proper near a point (Smale, *An infinite dimensional version of Sard's
theorem*, Amer. J. Math. 87 (1965)), as Lane F0 of the analytic Heegaard Floer roadmap asks.
-/

public section

namespace TauCeti

open Submodule

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {T : E →L[𝕜] F} {X₁ : Submodule 𝕜 E}
variable [CompleteSpace E] [CompleteSpace F]

/-- **A closed-range operator is bounded below off its kernel.** On any topological complement
`X₁` of `ker T` there is a constant `C > 0` with `‖x‖ ≤ C * ‖T x‖` for every `x ∈ X₁`.

This is `ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range` applied to the
restriction of `T` to `X₁`, which is injective because `X₁` meets the kernel trivially, and has
closed range because that range is the range of `T`. -/
theorem _root_.ContinuousLinearMap.exists_norm_le_mul_norm_of_isTopCompl (T : E →L[𝕜] F)
    (hclosed : IsClosed (T.range : Set F)) (h : IsTopCompl (T.ker) X₁) :
    ∃ C > 0, ∀ x ∈ X₁, ‖x‖ ≤ C * ‖T x‖ := by
  have : CompleteSpace X₁ := h.isClosed'.completeSpace_coe
  have hinj : Function.Injective (T ∘L X₁.subtypeL) := by
    intro x y hxy
    have hxy' : T (x : E) = T (y : E) := by simpa using hxy
    have hmem : (x : E) - (y : E) ∈ T.ker ⊓ X₁ := by
      refine ⟨LinearMap.mem_ker.2 ?_, X₁.sub_mem x.2 y.2⟩
      simp [map_sub, hxy']
    rw [h.isCompl.inf_eq_bot] at hmem
    exact Subtype.ext (sub_eq_zero.1 hmem)
  have hrange : Set.range (T ∘L X₁.subtypeL) = (T.range : Set F) := by
    have himage : Set.range (T ∘L X₁.subtypeL) = T '' (X₁ : Set E) := by
      ext y
      exact ⟨by rintro ⟨x, rfl⟩; exact ⟨x, x.2, rfl⟩, by rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩⟩
    have hmap : Submodule.map (T : E →ₗ[𝕜] F) X₁ = T.range :=
      Submodule.map_eq_range_iff.2 h.isCompl.symm.codisjoint
    rw [himage]
    simpa using congrArg (SetLike.coe) hmap
  obtain ⟨K, hK⟩ :=
    (T ∘L X₁.subtypeL).antilipschitz_of_injective_of_isClosed_range hinj (hrange ▸ hclosed)
  refine ⟨K + 1, by positivity, fun x hx => ?_⟩
  have hx' := hK.le_mul_dist (⟨x, hx⟩ : X₁) 0
  simp only [ContinuousLinearMap.comp_apply, coe_subtypeL, coe_subtype, map_zero,
    dist_eq_norm, sub_zero] at hx'
  have hK0 : (0 : ℝ) ≤ K := K.coe_nonneg
  calc ‖x‖ ≤ (K : ℝ) * ‖T x‖ := hx'
    _ ≤ ((K : ℝ) + 1) * ‖T x‖ := by nlinarith [norm_nonneg (T x)]

/-- **The a priori estimate of a closed-range operator**, stated against the projection onto the
kernel along a chosen topological complement: there is a `C > 0` with
`‖x‖ ≤ C * ‖T x‖ + ‖P x‖` for all `x`, where `P` is that projection. -/
theorem _root_.ContinuousLinearMap.exists_norm_le_mul_norm_add_norm_projectionL
    (T : E →L[𝕜] F) (hclosed : IsClosed (T.range : Set F)) (h : IsTopCompl (T.ker) X₁) :
    ∃ C > 0, ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖(T.ker).projectionL X₁ h x‖ := by
  obtain ⟨C, hC, hbound⟩ := T.exists_norm_le_mul_norm_of_isTopCompl hclosed h
  refine ⟨C, hC, fun x => ?_⟩
  have hsum : (T.ker).projectionL X₁ h x + X₁.projectionL (T.ker) h.symm x = x :=
    projectionL_add_projectionL_eq_self h x
  have hq := hbound (X₁.projectionL (T.ker) h.symm x) (projectionL_apply_mem h.symm x)
  -- `T` sees only the component of `x` in the complement, the other one lying in `ker T`
  have hker : T ((T.ker).projectionL X₁ h x) = 0 :=
    LinearMap.mem_ker.1 (projectionL_apply_mem h x)
  have hTx : T (X₁.projectionL (T.ker) h.symm x) = T x := by
    conv_rhs => rw [← hsum]
    rw [map_add, hker, zero_add]
  rw [hTx] at hq
  calc ‖x‖ = ‖(T.ker).projectionL X₁ h x + X₁.projectionL (T.ker) h.symm x‖ := by rw [hsum]
    _ ≤ ‖(T.ker).projectionL X₁ h x‖ + ‖X₁.projectionL (T.ker) h.symm x‖ := norm_add_le _ _
    _ ≤ ‖(T.ker).projectionL X₁ h x‖ + C * ‖T x‖ := by gcongr
    _ = C * ‖T x‖ + ‖(T.ker).projectionL X₁ h x‖ := by ring

/-- **The a priori estimate of a closed-range operator with complemented kernel**, with the
complement discharged: there is a continuous projection `P` of `E` onto `ker T` and a constant
`C > 0` with
`‖x‖ ≤ C * ‖T x‖ + ‖P x‖`.

When `ker T` is finite-dimensional, the correction term `‖P x‖` ranges over a finite-dimensional
space; in particular, this says that a Fredholm operator is bounded below "up to a compact
error". -/
theorem _root_.ContinuousLinearMap.exists_projection_norm_le_mul_norm_add_norm (T : E →L[𝕜] F)
    (hclosed : IsClosed (T.range : Set F)) (hcompl : T.ker.ClosedComplemented) :
    ∃ (P : E →L[𝕜] E) (C : ℝ), 0 < C ∧ IsIdempotentElem P ∧ P.range = T.ker ∧
      ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖P x‖ := by
  obtain ⟨X₁, h⟩ := hcompl.exists_isTopCompl
  obtain ⟨C, hC, hbound⟩ := T.exists_norm_le_mul_norm_add_norm_projectionL hclosed h
  exact ⟨(T.ker).projectionL X₁ h, C, hC, isIdempotentElem_projectionL h,
    range_projectionL h, hbound⟩

end TauCeti
