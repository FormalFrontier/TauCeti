/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Comp
public import TauCeti.Analysis.Fredholm.Criteria

/-!
# The index under finite-rank perturbations of Fredholm operators

That a finite-rank perturbation of a Fredholm operator is again Fredholm is Mathlib's
`ContinuousLinearMap.IsFredholm.add_hasFiniteRange`. This file records the corresponding index
statement, which follows by restricting both operators to the kernel of the perturbation.

Finiteness of the rank is spelled with Mathlib's `LinearMap.HasFiniteRange`, matching the
hypothesis of `ContinuousLinearMap.IsFredholm.add_hasFiniteRange`.

## Main declarations

* `TauCeti.ContinuousLinearMap.index_add_of_hasFiniteRange`: over a complete nontrivially normed
  field, adding an operator of finite rank preserves the Fredholm index.
-/

public section

namespace TauCeti

open Module

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {T K : E →L[𝕜] F}

namespace ContinuousLinearMap

/-- Over a complete nontrivially normed field, perturbing a Fredholm operator by an operator of
finite rank leaves its index unchanged: both operators restrict to the same map on the closed,
finite-codimensional subspace `ker K`, and additivity of the index cancels the index shift of that
restriction. -/
theorem index_add_of_hasFiniteRange (hT : ContinuousLinearMap.IsFredholm T)
    (hK : LinearMap.HasFiniteRange (K : E →ₗ[𝕜] F)) :
    index (T + K) = index T := by
  set ι := (LinearMap.ker (K : E →ₗ[𝕜] F)).subtypeL with hι
  have hιF : ContinuousLinearMap.IsFredholm ι := isFredholm_ker_subtypeL hK
  have hcomp : (T + K).comp ι = T.comp ι := by
    ext x
    have hx : K (x : E) = 0 := LinearMap.mem_ker.mp x.2
    simp [hι, hx]
  have h₁ := index_comp (T + K) ι (hT.add_hasFiniteRange hK) hιF
  have h₂ := index_comp T ι hT hιF
  rw [hcomp, h₂] at h₁
  omega

end ContinuousLinearMap

end TauCeti

end
