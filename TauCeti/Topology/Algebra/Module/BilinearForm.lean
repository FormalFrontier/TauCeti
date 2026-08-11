/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Nondegeneracy of the bilinear form of a continuous linear map into the dual

A continuous linear map `L : E →L[𝕜] E →L[𝕜] 𝕜` carries a bilinear form
`ContinuousLinearMap.toBilinForm L`, and that form is left-separating exactly when `L` is
injective: both say that no nonzero vector is annihilated by `L`. Reading nondegeneracy of the
form off injectivity of the map is the step that connects the two ways a Hessian is presented —
as a map into the dual space and as a bilinear form — and it has nothing to do with the analysis
that produces the Hessian, so it is recorded here, next to `ContinuousLinearMap.toBilinForm`
itself, rather than with any of its users.

## Main results

* `TauCeti.ContinuousLinearMap.separatingLeft_toBilinForm_iff_injective`: the bilinear form of a
  continuous linear map into the dual is left-separating if and only if the map is injective.
-/

public section

namespace TauCeti

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-- The bilinear form of a continuous linear map into the dual space is left-separating exactly
when the map is injective. -/
theorem separatingLeft_toBilinForm_iff_injective (L : E →L[𝕜] E →L[𝕜] 𝕜) :
    L.toBilinForm.SeparatingLeft ↔ Function.Injective L := by
  rw [LinearMap.separatingLeft_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  exact ⟨fun h v w hvw ↦ h (LinearMap.ext fun u ↦ by simp [hvw]),
    fun h v w hvw ↦ h (ContinuousLinearMap.ext fun u ↦ by simpa using LinearMap.congr_fun hvw u)⟩

end ContinuousLinearMap

end TauCeti

end
