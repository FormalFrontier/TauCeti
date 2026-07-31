/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Fredholm.Basic

/-!
# The zero Fredholm operator

This file characterizes when the zero continuous linear map is Fredholm. Its kernel is the whole
domain and its cokernel is the whole codomain, so it is Fredholm exactly when both spaces are
finite dimensional. In that case its index is `dim E - dim F`.

The result is the boundary case for finite-dimensional reductions in the Fredholm substrate of the
analytic Heegaard Floer roadmap: after an infinite-dimensional invertible block is split off, a
remaining zero block records precisely the finite-dimensional kernel and cokernel.

## Main declarations

* `TauCeti.isFredholm_zero_iff`: the zero operator is Fredholm exactly when its domain and
  codomain are finite dimensional.
* `TauCeti.ContinuousLinearMap.index_zero`: the index of the zero operator is the difference of
  the dimensions of its domain and codomain.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix
A.1.
-/

public section

namespace TauCeti

open Module

variable {𝕜 E F : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

private lemma finiteDimensional_domain_of_isFredholm_zero
    (hT : ContinuousLinearMap.IsFredholm (0 : E →L[𝕜] F)) : FiniteDimensional 𝕜 E := by
  letI := hT.finite_ker
  exact
    ((LinearEquiv.ofEq (LinearMap.ker (0 : E →ₗ[𝕜] F)) (⊤ : Submodule 𝕜 E)
        LinearMap.ker_zero) ≪≫ₗ
      (Submodule.topEquiv : (⊤ : Submodule 𝕜 E) ≃ₗ[𝕜] E)).finiteDimensional

private lemma finiteDimensional_codomain_of_isFredholm_zero
    (hT : ContinuousLinearMap.IsFredholm (0 : E →L[𝕜] F)) : FiniteDimensional 𝕜 F := by
  letI := hT.finite_coker
  exact
    (LinearMap.range (0 : E →ₗ[𝕜] F)).quotEquivOfEqBot LinearMap.range_zero
      |>.finiteDimensional

/-- The zero continuous linear map is Fredholm exactly when its domain and codomain are both
finite dimensional. -/
@[simp]
lemma isFredholm_zero_iff :
    ContinuousLinearMap.IsFredholm (0 : E →L[𝕜] F) ↔
      Nonempty (FiniteDimensional 𝕜 E) ∧ Nonempty (FiniteDimensional 𝕜 F) := by
  constructor
  · intro h
    exact ⟨⟨finiteDimensional_domain_of_isFredholm_zero h⟩,
      ⟨finiteDimensional_codomain_of_isFredholm_zero h⟩⟩
  · rintro ⟨⟨hE⟩, ⟨hF⟩⟩
    letI := hE
    letI := hF
    exact
      { isStrictMap := by
          have hclosed : IsClosedMap (0 : E →L[𝕜] F) := fun s hs ↦ by
            simpa using (Set.Subsingleton.isClosed (by
              rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
              rfl))
          exact hclosed.isStrictMap (by fun_prop)
        isClosed_range := by simp
        finite_ker := inferInstance
        finite_coker := inferInstance
        closedComplemented_ker := by
          rw [ContinuousLinearMap.toLinearMap_zero, LinearMap.ker_zero]
          exact Submodule.closedComplemented_top }

namespace ContinuousLinearMap

/-- The index of the zero continuous linear map is the dimension of its domain minus the
dimension of its codomain. -/
@[simp]
lemma index_zero :
    index (0 : E →L[𝕜] F) = (finrank 𝕜 E : ℤ) - finrank 𝕜 F := by
  rw [index_eq_finrank_sub]
  simpa only [ContinuousLinearMap.toLinearMap_zero, LinearMap.index_eq_finrank_sub] using
    (LinearMap.index_zero (R := 𝕜) (M := E) (N := F))

end ContinuousLinearMap

end TauCeti

end
