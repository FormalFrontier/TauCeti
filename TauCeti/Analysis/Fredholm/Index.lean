/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.LinearMap.Index
public import TauCeti.Analysis.Fredholm.Basic

/-!
# The Fredholm index

The Fredholm index of a continuous linear map is the integer `dim ker T − dim coker T`. Mathlib
already develops the purely algebraic `LinearMap.index`; this file transfers its elementary API to
continuous linear maps. For a non-Fredholm map the value is junk, following Mathlib's convention.

## Main declarations

* `TauCeti.ContinuousLinearMap.index`: the index of a continuous linear map.
* `TauCeti.ContinuousLinearMap.index_eq_finrank_sub`: the defining dimension formula.
* `TauCeti.ContinuousLinearMap.index_id` and `index_continuousLinearEquiv_eq_zero`: identities and
  continuous linear equivalences have index zero.
* `TauCeti.ContinuousLinearMap.index_smul` and `index_neg`: nonzero rescaling preserves the index.
* `TauCeti.ContinuousLinearMap.index_equiv_comp` and `index_comp_equiv`: composition with a
  continuous linear equivalence preserves the index.

The sign convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Appendix A.1.
-/

public section

namespace TauCeti

open Module

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace ContinuousLinearMap

/-- The **index** of a continuous linear map, `dim ker T − dim coker T`, defined as the index of
the underlying linear map. -/
noncomputable def index (T : E →L[𝕜] F) : ℤ := (T : E →ₗ[𝕜] F).index

/-- The index as the algebraic index of the underlying linear map. -/
private lemma index_def (T : E →L[𝕜] F) : index T = (T : E →ₗ[𝕜] F).index := rfl

/-- The index is `dim ker T − dim coker T`. -/
lemma index_eq_finrank_sub (T : E →L[𝕜] F) :
    index T = (finrank 𝕜 (LinearMap.ker (T : E →ₗ[𝕜] F)) : ℤ) -
      finrank 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) := by
  rw [index_def]
  exact LinearMap.index_eq_finrank_sub

/-- The identity operator has index `0`. -/
@[simp] lemma index_id : index (ContinuousLinearMap.id 𝕜 E) = 0 := by
  rw [index_def, ContinuousLinearMap.coe_id, LinearMap.index_id]

/-- A continuous linear equivalence has index `0`. -/
@[simp] lemma index_continuousLinearEquiv_eq_zero (e : E ≃L[𝕜] F) :
    index (e : E →L[𝕜] F) = 0 := by
  rw [index_def]
  exact LinearEquiv.index_eq_zero

/-- Between finite-dimensional spaces the index is `dim E − dim F`, for any operator. -/
lemma index_eq_of_finiteDimensional [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (T : E →L[𝕜] F) : index T = (finrank 𝕜 E : ℤ) - finrank 𝕜 F := by
  rw [index_def, LinearMap.index_eq_of_finiteDimensional]

/-- The index is unchanged by a nonzero scalar multiple. -/
lemma index_smul (T : E →L[𝕜] F) {c : 𝕜} (hc : c ≠ 0) : index (c • T) = index T := by
  rw [index_def, index_def, ContinuousLinearMap.toLinearMap_smul, LinearMap.index_smul _ hc]

/-- The index is unchanged by negation. -/
@[simp] lemma index_neg (T : E →L[𝕜] F) : index (-T) = index T := by
  rw [index_def, index_def, ContinuousLinearMap.toLinearMap_neg, LinearMap.index_neg]

variable {T : E →L[𝕜] F}

/-- Postcomposing with a continuous linear equivalence leaves the index unchanged. -/
@[simp] lemma index_equiv_comp (e : F ≃L[𝕜] G) :
    index ((e : F →L[𝕜] G).comp T) = index T := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub]
  congr 1
  · congr 1
    rw [show (((e : F →L[𝕜] G).comp T : E →L[𝕜] G) : E →ₗ[𝕜] G) =
      (e.toLinearEquiv : F →ₗ[𝕜] G).comp (T : E →ₗ[𝕜] F) by ext; simp]
    rw [LinearMap.ker_comp_of_ker_eq_bot _
      (LinearMap.ker_eq_bot.2 e.toLinearEquiv.injective)]
  · congr 1
    rw [show (((e : F →L[𝕜] G).comp T : E →L[𝕜] G) : E →ₗ[𝕜] G) =
      (e.toLinearEquiv : F →ₗ[𝕜] G).comp (T : E →ₗ[𝕜] F) by ext; simp]
    rw [LinearMap.range_comp]
    exact (LinearEquiv.finrank_eq
      (Submodule.Quotient.equiv _ _ e.toLinearEquiv rfl)).symm

/-- Precomposing with a continuous linear equivalence leaves the index unchanged. -/
@[simp] lemma index_comp_equiv (e : G ≃L[𝕜] E) :
    index (T.comp (e : G →L[𝕜] E)) = index T := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub]
  congr 1
  · congr 1
    rw [show ((T.comp (e : G →L[𝕜] E) : G →L[𝕜] F) : G →ₗ[𝕜] F) =
      (T : E →ₗ[𝕜] F).comp (e.toLinearEquiv : G →ₗ[𝕜] E) by ext; simp]
    rw [LinearMap.ker_comp, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  · congr 1
    rw [show ((T.comp (e : G →L[𝕜] E) : G →L[𝕜] F) : G →ₗ[𝕜] F) =
      (T : E →ₗ[𝕜] F).comp (e.toLinearEquiv : G →ₗ[𝕜] E) by ext; simp]
    rw [LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.2 e.toLinearEquiv.surjective)]

end ContinuousLinearMap

end TauCeti
