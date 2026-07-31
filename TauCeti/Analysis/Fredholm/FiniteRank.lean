/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Fredholm.Comp
public import TauCeti.Analysis.Fredholm.Criteria

/-!
# Finite-rank perturbations of Fredholm operators

Mathlib's `ContinuousLinearMap.IsFredholm` API characterizes Fredholm operators by the existence
of a continuous quasi-inverse. This file uses that characterization directly to prove that
finite-rank perturbations over a complete nontrivially normed field preserve Fredholmness. The
index statement then follows by restricting both operators to the kernel of the perturbation.

## Main declarations

* `ContinuousLinearMap.IsFredholm.add_of_finiteDimensional_range`: over a complete nontrivially
  normed field, adding an operator with finite-dimensional range preserves Fredholmness.
* `TauCeti.ContinuousLinearMap.index_add_of_finiteDimensional_range`: over a complete nontrivially
  normed field, adding an operator with finite-dimensional range preserves the Fredholm index.
-/

public section

namespace TauCeti

open Module

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {T K : E →L[𝕜] F}

/-- Over a complete nontrivially normed field, perturbing a Fredholm operator by an operator of
finite rank leaves it Fredholm. -/
theorem _root_.ContinuousLinearMap.IsFredholm.add_of_finiteDimensional_range
    (hT : ContinuousLinearMap.IsFredholm T)
    (hK : FiniteDimensional 𝕜 (LinearMap.range (K : E →ₗ[𝕜] F))) :
    ContinuousLinearMap.IsFredholm (T + K) := by
  open scoped LinearMap.FiniteRangeSetoid in
    obtain ⟨S, hS⟩ := hT.exists_isQuasiInverse
    refine ContinuousLinearMap.IsFredholm.of_isQuasiInverse (v := S) ?_
    apply hS.congr (Setoid.refl _)
    rw [LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange]
    -- Unfold the finite-range setoid goal to the range of the perturbation `K`.
    change
      (((T + K : E →L[𝕜] F) : E →ₗ[𝕜] F) - (T : E →ₗ[𝕜] F)).range.FG
    simpa only [ContinuousLinearMap.toLinearMap_add, add_sub_cancel_left]
      using (Submodule.fg_iff_finiteDimensional _).mpr hK

namespace ContinuousLinearMap

/-- Over a complete nontrivially normed field, perturbing a Fredholm operator by an operator of
finite rank leaves its index unchanged: both operators restrict to the same map on the closed,
finite-codimensional subspace `ker K`, and additivity of the index cancels the index shift of that
restriction. -/
theorem index_add_of_finiteDimensional_range (hT : ContinuousLinearMap.IsFredholm T)
    (hK : FiniteDimensional 𝕜 (LinearMap.range (K : E →ₗ[𝕜] F))) :
    index (T + K) = index T := by
  haveI := hK
  set ι := (LinearMap.ker (K : E →ₗ[𝕜] F)).subtypeL with hι
  have hιF : ContinuousLinearMap.IsFredholm ι := isFredholm_ker_subtypeL hK
  have hcomp : (T + K).comp ι = T.comp ι := by
    ext x
    have hx : K (x : E) = 0 := LinearMap.mem_ker.mp x.2
    simp [hι, hx]
  have h₁ := index_comp (T + K) ι (hT.add_of_finiteDimensional_range hK) hιF
  have h₂ := index_comp T ι hT hιF
  rw [hcomp, h₂] at h₁
  omega

end ContinuousLinearMap

end TauCeti

end
