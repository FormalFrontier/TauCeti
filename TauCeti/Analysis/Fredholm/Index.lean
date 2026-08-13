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
continuous linear maps. The value is junk when the kernel or cokernel is infinite-dimensional,
following Mathlib's convention for `LinearMap.index`.

## Main declarations

* `TauCeti.ContinuousLinearMap.index`: the index of a continuous linear map.
* `TauCeti.ContinuousLinearMap.index_eq_finrank_sub`: the defining dimension formula.
* `TauCeti.ContinuousLinearMap.index_eq_of_finiteDimensional`: between finite-dimensional spaces,
  the index is the dimension of the domain minus the dimension of the codomain.
* `TauCeti.ContinuousLinearMap.index_id`, `index_continuousLinearEquiv_eq_zero`, and
  `index_eq_zero_of_bijective`: identities, continuous linear equivalences, and bijective maps have
  index zero.
* `TauCeti.ContinuousLinearMap.index_smul` and `index_neg`: nonzero rescaling and negation preserve
  the index.
* `TauCeti.ContinuousLinearMap.index_equiv_comp` and `index_comp_equiv`: composition with a
  continuous linear equivalence preserves the index.
* `LinearMap.index_equiv_comp` and `LinearMap.index_comp_equiv`: the corresponding algebraic
  statements for arbitrary modules.

The sign convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Appendix A.1.
-/

public section

namespace LinearMap

variable {𝕜 E F G : Type*} [DivisionRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F]
variable [AddCommGroup G] [Module 𝕜 G]

/-- Postcomposition with a linear equivalence leaves the index unchanged. -/
@[simp]
lemma index_equiv_comp (T : E →ₗ[𝕜] F) (e : F ≃ₗ[𝕜] G) :
    ((e : F →ₗ[𝕜] G).comp T).index = T.index := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub]
  congr 1
  · rw [ker_equiv_comp]
  · rw [range_equiv_comp]
    exact_mod_cast (LinearEquiv.finrank_eq (TauCeti.quotientEquivMap e T.range)).symm

/-- Precomposition with a linear equivalence leaves the index unchanged. -/
@[simp]
lemma index_comp_equiv (T : E →ₗ[𝕜] F) (e : G ≃ₗ[𝕜] E) :
    (T.comp (e : G →ₗ[𝕜] E)).index = T.index := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub]
  congr 1
  · rw [ker_comp_equiv, LinearEquiv.finrank_map_eq]
  · rw [range_comp_equiv]

end LinearMap

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
lemma index_def (T : E →L[𝕜] F) : index T = (T : E →ₗ[𝕜] F).index := (rfl)

/-- The index is `dim ker T − dim coker T`. -/
lemma index_eq_finrank_sub (T : E →L[𝕜] F) :
    index T = (finrank 𝕜 (LinearMap.ker (T : E →ₗ[𝕜] F)) : ℤ) -
      finrank 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) := by
  rw [index_def]
  exact LinearMap.index_eq_finrank_sub

/-- A bijective continuous linear map has index zero. -/
lemma index_eq_zero_of_bijective (T : E →L[𝕜] F) (hT : Function.Bijective T) : index T = 0 := by
  rw [index_def]
  exact LinearEquiv.index_eq_zero (e := LinearEquiv.ofBijective (T : E →ₗ[𝕜] F) hT)

/-- The identity operator has index `0`. -/
@[simp] lemma index_id : index (ContinuousLinearMap.id 𝕜 E) = 0 :=
  index_eq_zero_of_bijective _ Function.bijective_id

/-- A continuous linear equivalence has index `0`. -/
@[simp] lemma index_continuousLinearEquiv_eq_zero (e : E ≃L[𝕜] F) :
    index (e : E →L[𝕜] F) = 0 :=
  index_eq_zero_of_bijective _ e.bijective

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
  rw [index_def, index_def, coe_equiv_comp, LinearMap.index_equiv_comp]

/-- Precomposing with a continuous linear equivalence leaves the index unchanged. -/
@[simp] lemma index_comp_equiv (e : G ≃L[𝕜] E) :
    index (T.comp (e : G →L[𝕜] E)) = index T := by
  rw [index_def, index_def, coe_comp_equiv, LinearMap.index_comp_equiv]

end ContinuousLinearMap

end TauCeti
