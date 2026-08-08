/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.Algebra.Module.LinearMap.Index

/-!
# Fredholm operators

This file connects Mathlib's analytic notion of a **Fredholm operator** to the nonlinear-analysis
substrate of the analytic Heegaard Floer roadmap (Lane F0, "Fredholm operators and index theory").
All Fredholm hypotheses use `ContinuousLinearMap.IsFredholm` directly. That predicate asks for a
strict map with closed range, finite-dimensional kernel and cokernel, and a topologically
complemented kernel. Between Banach spaces over an `IsRCLikeNormedField` the strictness,
closed-range and complemented-kernel conditions are automatic, so the predicate is *equivalent*
there to finite dimensionality of the kernel and cokernel alone; that equivalence is proved and
exposed as `TauCeti.isFredholm_iff_finite_ker_coker` in `TauCeti.Analysis.Fredholm.ClosedRange`.
Outside that setting `ContinuousLinearMap.IsFredholm` is genuinely stronger, and it is the notion
intended throughout.

The **index** of such an operator is the integer `dim ker T − dim coker T`. Mathlib already builds
the purely algebraic index of a linear map, `LinearMap.index`, together with its behaviour under
negation and nonzero scaling; this file reuses that development at the level of continuous linear
maps rather than restating it.

## Main declarations

* `TauCeti.ContinuousLinearMap.index`: the Fredholm index `dim ker T − dim coker T`, defined via
  `LinearMap.index`.
* `TauCeti.ContinuousLinearMap.index_eq_finrank_sub`: the index as `dim ker T − dim coker T`.
* `TauCeti.isFredholm_id` and `TauCeti.ContinuousLinearMap.index_id`: the identity is Fredholm of
  index `0`.
* `ContinuousLinearMap.IsFredholm.of_continuousLinearEquiv` and
  `TauCeti.ContinuousLinearMap.index_continuousLinearEquiv_eq_zero`: a continuous linear
  equivalence is Fredholm of index `0`.
* `TauCeti.isFredholm_of_finiteDimensional` and
  `TauCeti.ContinuousLinearMap.index_eq_of_finiteDimensional`: every operator between
  finite-dimensional spaces is Fredholm, with index `dim E − dim F`.
* `ContinuousLinearMap.IsFredholm.neg`, `ContinuousLinearMap.IsFredholm.smul`: Fredholmness is
  preserved by negation and by nonzero scalar multiples, with the index unchanged.
* `ContinuousLinearMap.IsFredholm.comp_equiv` and
  `ContinuousLinearMap.IsFredholm.equiv_comp`: composing with a continuous linear equivalence on
  either side preserves Fredholmness and the index.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix
A.1, where the index is `dim ker D − dim coker D`.
-/

public section

namespace TauCeti

open Module

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The underlying linear map of a continuous linear equivalence, written with the
linear-equivalence coercion so that submodule lemmas apply. -/
private lemma coe_continuousLinearEquiv (e : E ≃L[𝕜] F) :
    ((e : E →L[𝕜] F) : E →ₗ[𝕜] F) = (e.toLinearEquiv : E →ₗ[𝕜] F) := by
  ext x; simp

/-- A continuous linear equivalence is a Fredholm operator.

This is proved directly from the structure fields because Mathlib's quasi-inverse
characterization currently assumes that the scalar field is complete, whereas this result does
not need that assumption. -/
lemma _root_.ContinuousLinearMap.IsFredholm.of_continuousLinearEquiv (e : E ≃L[𝕜] F) :
    ContinuousLinearMap.IsFredholm (e : E →L[𝕜] F) where
  isStrictMap := e.isHomeomorph.isStrictMap
  isClosed_range := by
    rw [coe_continuousLinearEquiv, LinearEquiv.range]
    simp
  finite_ker := by
    rw [coe_continuousLinearEquiv, LinearEquiv.ker]
    infer_instance
  finite_coker := by
    rw [coe_continuousLinearEquiv, LinearEquiv.range]
    infer_instance
  closedComplemented_ker := by
    rw [coe_continuousLinearEquiv, LinearEquiv.ker]
    exact Submodule.closedComplemented_bot

/-- The identity operator is Fredholm: its kernel is trivial and its range is everything. -/
lemma isFredholm_id : ContinuousLinearMap.IsFredholm (ContinuousLinearMap.id 𝕜 E) := by
  simpa using ContinuousLinearMap.IsFredholm.of_continuousLinearEquiv (.refl 𝕜 E)

section FiniteDimensional

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- Every continuous linear map between finite-dimensional spaces is Fredholm. -/
lemma isFredholm_of_finiteDimensional (T : E →L[𝕜] F) : ContinuousLinearMap.IsFredholm T where
  isStrictMap := T.isStrictMap_of_finiteDimensional
  isClosed_range := (LinearMap.range (T : E →ₗ[𝕜] F)).closed_of_finiteDimensional
  finite_ker := inferInstance
  finite_coker := inferInstance
  closedComplemented_ker :=
    Submodule.ClosedComplemented.of_finiteDimensional_of_le
      Submodule.closedComplemented_top le_top

end FiniteDimensional

/-- A nonzero scalar multiple of a Fredholm operator is Fredholm. -/
lemma _root_.ContinuousLinearMap.IsFredholm.smul {T : E →L[𝕜] F}
    (hT : ContinuousLinearMap.IsFredholm T) {c : 𝕜} (hc : c ≠ 0) :
    ContinuousLinearMap.IsFredholm (c • T) where
  isStrictMap := by
    -- `IsStrictMap` is phrased for functions; unfold the bundled scalar action to match it.
    change Topology.IsStrictMap (fun x ↦ c • T x)
    exact (Homeomorph.smulOfNeZero c hc).comp_isStrictMap_iff.mpr hT.isStrictMap
  isClosed_range := by
    rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.range_smul _ _ hc]
    exact hT.isClosed_range
  finite_ker := by
    rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.ker_smul _ _ hc]
    exact hT.finite_ker
  finite_coker := by
    rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.range_smul _ _ hc]
    exact hT.finite_coker
  closedComplemented_ker := by
    rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.ker_smul _ _ hc]
    exact hT.closedComplemented_ker

/-- The negation of a Fredholm operator is Fredholm. -/
lemma _root_.ContinuousLinearMap.IsFredholm.neg {T : E →L[𝕜] F}
    (hT : ContinuousLinearMap.IsFredholm T) : ContinuousLinearMap.IsFredholm (-T) := by
  simpa using hT.smul (c := -1) (by norm_num)

section CompEquiv

variable {T : E →L[𝕜] F}

/-- The underlying linear map of `e.comp T`, for a continuous linear equivalence `e`, written with
the linear-equivalence coercion so that submodule and quotient lemmas apply. -/
private lemma coe_equiv_comp (e : F ≃L[𝕜] G) : (((e : F →L[𝕜] G).comp T : E →L[𝕜] G) : E →ₗ[𝕜] G) =
      (e.toLinearEquiv : F →ₗ[𝕜] G).comp (T : E →ₗ[𝕜] F) := by
  ext x; simp

/-- The underlying linear map of `T.comp e`, for a continuous linear equivalence `e`. -/
private lemma coe_comp_equiv (e : G ≃L[𝕜] E) : ((T.comp (e : G →L[𝕜] E) : G →L[𝕜] F) : G →ₗ[𝕜] F) =
      (T : E →ₗ[𝕜] F).comp (e.toLinearEquiv : G →ₗ[𝕜] E) := by
  ext x; simp

/-- A linear equivalence `e : F ≃ₗ G` sends the cokernel by a submodule `p` to the cokernel by
its image `p.map e`, linearly equivalently. Transports the cokernel along a postcomposed
equivalence in both `equiv_comp` and `index_equiv_comp`. -/
private noncomputable def quotientEquivMap (e : F ≃ₗ[𝕜] G) (p : Submodule 𝕜 F) :
    (F ⧸ p) ≃ₗ[𝕜] G ⧸ p.map (e : F →ₗ[𝕜] G) :=
  Submodule.Quotient.equiv p (p.map (e : F →ₗ[𝕜] G)) e rfl

/-- A continuous linear equivalence carries a complemented submodule to a complemented
submodule. -/
private lemma closedComplemented_map_continuousLinearEquiv (e : E ≃L[𝕜] F)
    (p : Submodule 𝕜 E) (hp : p.ClosedComplemented) :
    (p.map (e : E →ₗ[𝕜] F)).ClosedComplemented := by
  obtain ⟨P, hP⟩ := hp
  let ep := e.submoduleMap p
  refine ⟨ep.toContinuousLinearMap.comp (P.comp (e.symm : F →L[𝕜] E)), ?_⟩
  intro y
  have h := congrArg ep (hP (ep.symm y))
  simpa only [ep, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.submoduleMap_apply,
    ContinuousLinearEquiv.submoduleMap_symm_apply,
    ep.apply_symm_apply] using h

/-- The kernel of `T.comp e`, for a continuous linear equivalence `e : G ≃L[𝕜] E`, is the image
of `ker T` under `e⁻¹`. Transports the kernel along a precomposed equivalence in both
`comp_equiv` and `index_comp_equiv`. -/
private lemma ker_comp_equiv (e : G ≃L[𝕜] E) :
    LinearMap.ker ((T.comp (e : G →L[𝕜] E) : G →L[𝕜] F) : G →ₗ[𝕜] F) =
      (LinearMap.ker (T : E →ₗ[𝕜] F)).map (e.toLinearEquiv.symm : E →ₗ[𝕜] G) := by
  rw [coe_comp_equiv, LinearMap.ker_comp, Submodule.comap_equiv_eq_map_symm]

/-- The kernel of `e.comp T`, for a continuous linear equivalence `e : F ≃L[𝕜] G`, is `ker T`
unchanged, `e` being injective. Shared by `equiv_comp` and `index_equiv_comp`. -/
private lemma ker_equiv_comp (e : F ≃L[𝕜] G) :
    LinearMap.ker (((e : F →L[𝕜] G).comp T : E →L[𝕜] G) : E →ₗ[𝕜] G) =
      LinearMap.ker (T : E →ₗ[𝕜] F) := by
  rw [coe_equiv_comp, LinearMap.ker_comp_of_ker_eq_bot _
    (LinearMap.ker_eq_bot.2 e.toLinearEquiv.injective)]

/-- The range of `T.comp e`, for a continuous linear equivalence `e : G ≃L[𝕜] E`, is `range T`
unchanged, `e` being surjective. Shared by `comp_equiv` and `index_comp_equiv`. -/
private lemma range_comp_equiv (e : G ≃L[𝕜] E) :
    LinearMap.range ((T.comp (e : G →L[𝕜] E) : G →L[𝕜] F) : G →ₗ[𝕜] F) =
      LinearMap.range (T : E →ₗ[𝕜] F) := by
  rw [coe_comp_equiv, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.2 e.toLinearEquiv.surjective)]

/-- Postcomposing a Fredholm operator with a continuous linear equivalence yields a Fredholm
operator.

The structure fields are transported directly to avoid the complete-scalar-field assumption on
Mathlib's quasi-inverse characterization. -/
lemma _root_.ContinuousLinearMap.IsFredholm.equiv_comp
    (hT : ContinuousLinearMap.IsFredholm T) (e : F ≃L[𝕜] G) :
    ContinuousLinearMap.IsFredholm ((e : F →L[𝕜] G).comp T) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Expose function composition so the homeomorphism strictness lemma applies.
    change Topology.IsStrictMap (fun x ↦ e (T x))
    exact e.toHomeomorph.comp_isStrictMap_iff.mpr hT.isStrictMap
  · rw [coe_equiv_comp, LinearMap.range_comp]
    simpa [Submodule.map_coe] using e.isClosed_image.2 hT.isClosed_range
  · rw [ker_equiv_comp]
    exact hT.finite_ker
  · rw [coe_equiv_comp, LinearMap.range_comp]
    have := hT.finite_coker
    exact (quotientEquivMap e.toLinearEquiv _).finiteDimensional
  · rw [ker_equiv_comp]
    exact hT.closedComplemented_ker

/-- Precomposing a Fredholm operator with a continuous linear equivalence yields a Fredholm
operator.

The structure fields are transported directly to avoid the complete-scalar-field assumption on
Mathlib's quasi-inverse characterization. -/
lemma _root_.ContinuousLinearMap.IsFredholm.comp_equiv (hT : ContinuousLinearMap.IsFredholm T)
    (e : G ≃L[𝕜] E) :
    ContinuousLinearMap.IsFredholm (T.comp (e : G →L[𝕜] E)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Expose function composition so the homeomorphism strictness lemma applies.
    change Topology.IsStrictMap (fun x ↦ T (e x))
    exact e.toHomeomorph.isStrictMap_comp_iff.mpr hT.isStrictMap
  · rw [range_comp_equiv]
    exact hT.isClosed_range
  · rw [ker_comp_equiv]
    have := hT.finite_ker
    exact (e.symm.submoduleMap _).finiteDimensional
  · rw [range_comp_equiv]
    exact hT.finite_coker
  · rw [ker_comp_equiv]
    exact closedComplemented_map_continuousLinearEquiv e.symm _ hT.closedComplemented_ker

end CompEquiv

namespace ContinuousLinearMap

/-- The **index** of a continuous linear map, `dim ker T − dim coker T`, defined as the index of
the underlying linear map. For non-Fredholm operators the value is junk, matching the convention of
`LinearMap.index`. -/
noncomputable def index (T : E →L[𝕜] F) : ℤ := (T : E →ₗ[𝕜] F).index

/-- The Fredholm index unfolds to the algebraic `LinearMap.index` of the underlying linear map.
Internal bridge to the reused Mathlib API; the public characteristic equation is
`index_eq_finrank_sub`. -/
private lemma index_def (T : E →L[𝕜] F) : index T = (T : E →ₗ[𝕜] F).index := rfl

/-- The index is `dim ker T − dim coker T`. -/
lemma index_eq_finrank_sub (T : E →L[𝕜] F) :
    index T = (finrank 𝕜 (LinearMap.ker (T : E →ₗ[𝕜] F)) : ℤ) -
      finrank 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) := by
  rw [index_def]; exact LinearMap.index_eq_finrank_sub

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
    rw [ker_equiv_comp]
  · congr 1
    rw [coe_equiv_comp, LinearMap.range_comp]
    exact (LinearEquiv.finrank_eq (quotientEquivMap e.toLinearEquiv _)).symm

/-- Precomposing with a continuous linear equivalence leaves the index unchanged. -/
@[simp] lemma index_comp_equiv (e : G ≃L[𝕜] E) :
    index (T.comp (e : G →L[𝕜] E)) = index T := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub]
  congr 1
  · congr 1
    rw [ker_comp_equiv, LinearEquiv.finrank_map_eq]
  · congr 1
    rw [range_comp_equiv]

end ContinuousLinearMap

end TauCeti
