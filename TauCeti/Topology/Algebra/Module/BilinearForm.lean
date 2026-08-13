/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dual.Lemmas
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
* `TauCeti.ContinuousLinearMap.isInvertible_of_injective`: in finite dimensions an injective map
  into the dual is already invertible, the dual having the same dimension as the space.
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

/-- In finite dimensions an injective continuous linear map into the dual is invertible: injectivity
makes it a linear equivalence onto its range, and the dual has the same finite dimension as the
space, so that range is everything. -/
theorem isInvertible_of_injective {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] {L : E →L[𝕜] E →L[𝕜] 𝕜}
    (hinj : Function.Injective L) : L.IsInvertible := by
  have hrank : Module.finrank 𝕜 E = Module.finrank 𝕜 (E →L[𝕜] 𝕜) := by
    rw [← LinearEquiv.finrank_eq
      (LinearMap.toContinuousLinearMap : (E →ₗ[𝕜] 𝕜) ≃ₗ[𝕜] E →L[𝕜] 𝕜)]
    exact Subspace.dual_finrank_eq.symm
  exact ⟨((L : E →ₗ[𝕜] E →L[𝕜] 𝕜).linearEquivOfInjective hinj hrank).toContinuousLinearEquiv,
    by ext v; simp⟩

end ContinuousLinearMap

end TauCeti

end
