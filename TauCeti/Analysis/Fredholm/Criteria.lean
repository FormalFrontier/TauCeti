/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Fredholm.ClosedRange

/-!
# Injective and surjective criteria for Fredholm operators

This file gives streamlined Fredholm criteria when an operator is already known to be injective
or surjective. Between Banach spaces over an `IsRCLikeNormedField`, a surjective continuous linear
map is Fredholm exactly when its kernel is finite dimensional. Between Banach spaces over any
nontrivially normed field, an injective continuous linear map with closed range is Fredholm exactly
when its cokernel is finite dimensional. Specialising both sides gives the bijective corollaries:
a bijective continuous linear map between Banach spaces is Fredholm of index zero.

These criteria are the elementary endpoints of the finite-dimensional reductions used throughout
Fredholm theory. As an application of the injective closed-range criterion, the inclusion of the
kernel of an operator of finite rank is Fredholm.

## Main declarations

* `TauCeti.isFredholm_iff_finite_ker_of_surjective`: the surjective criterion.
* `TauCeti.isFredholm_iff_finite_coker_of_injective`: the injective closed-range
  criterion.
* `TauCeti.isFredholm_ker_subtypeL`: the inclusion of the kernel of an operator of finite rank is
  Fredholm.
* `TauCeti.ContinuousLinearMap.index_of_surjective` and
  `TauCeti.ContinuousLinearMap.index_of_injective`: the index in the two one-sided cases.
* `ContinuousLinearMap.IsFredholm.of_bijective` and
  `TauCeti.ContinuousLinearMap.index_eq_zero_of_bijective`: the bijective corollaries.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix
A.1.
-/

public section

namespace TauCeti

open Module

variable {K E F : Type*}
variable [NontriviallyNormedField K] [IsRCLikeNormedField K]
variable [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F]

variable {T : E →L[K] F}

/-- A surjective continuous linear map between Banach spaces over an `IsRCLikeNormedField` with
finite-dimensional kernel is Fredholm. -/
lemma _root_.ContinuousLinearMap.IsFredholm.of_surjective (hT : Function.Surjective T)
    [FiniteDimensional K (LinearMap.ker (T : E →ₗ[K] F))] :
    ContinuousLinearMap.IsFredholm T := by
  letI := IsRCLikeNormedField.rclike K
  apply ContinuousLinearMap.IsFredholm.of_finite_ker_coker T inferInstance
  rw [LinearMap.range_eq_top.mpr hT]
  infer_instance

/-- For a surjective continuous linear map between Banach spaces over an `IsRCLikeNormedField`,
Fredholmness is equivalent to finite-dimensionality of the kernel. -/
lemma isFredholm_iff_finite_ker_of_surjective (hT : Function.Surjective T) :
    ContinuousLinearMap.IsFredholm T ↔ FiniteDimensional K (LinearMap.ker (T : E →ₗ[K] F)) := by
  constructor
  · exact ContinuousLinearMap.IsFredholm.finite_ker
  · intro hker
    letI := hker
    exact ContinuousLinearMap.IsFredholm.of_surjective hT

omit [IsRCLikeNormedField K] in
/-- An injective continuous linear map between Banach spaces with closed range and
finite-dimensional cokernel is Fredholm. -/
lemma _root_.ContinuousLinearMap.IsFredholm.of_injective (hT : Function.Injective T)
    (hclosed : IsClosed (LinearMap.range (T : E →ₗ[K] F) : Set F))
    [FiniteDimensional K (F ⧸ LinearMap.range (T : E →ₗ[K] F))] :
    ContinuousLinearMap.IsFredholm T where
  isStrictMap := by
    letI : CompleteSpace T.range := hclosed.completeSpace_coe
    rw [Topology.isStrictMap_iff_isQuotientMap_rangeFactorization]
    exact T.rangeRestrict.isQuotientMap Set.rangeFactorization_surjective
  isClosed_range := hclosed
  finite_ker := by
    rw [LinearMap.ker_eq_bot.mpr hT]
    infer_instance
  finite_coker := inferInstance
  closedComplemented_ker := by
    rw [LinearMap.ker_eq_bot.mpr hT]
    exact Submodule.closedComplemented_bot

omit [IsRCLikeNormedField K] in
/-- For an injective continuous linear map between Banach spaces with closed range, Fredholmness is
equivalent to finite-dimensionality of the cokernel. -/
lemma isFredholm_iff_finite_coker_of_injective (hT : Function.Injective T)
    (hclosed : IsClosed (LinearMap.range (T : E →ₗ[K] F) : Set F)) :
    ContinuousLinearMap.IsFredholm T ↔
      FiniteDimensional K (F ⧸ LinearMap.range (T : E →ₗ[K] F)) := by
  constructor
  · exact ContinuousLinearMap.IsFredholm.finite_coker
  · intro hcoker
    letI := hcoker
    exact ContinuousLinearMap.IsFredholm.of_injective hT hclosed

omit [IsRCLikeNormedField K] [CompleteSpace E] [CompleteSpace F] in
/-- The inclusion of the kernel of an operator of finite rank is Fredholm: the kernel is closed
and, by the first isomorphism theorem, of finite codimension. -/
lemma isFredholm_ker_subtypeL (hT : FiniteDimensional K (LinearMap.range (T : E →ₗ[K] F))) :
    ContinuousLinearMap.IsFredholm (LinearMap.ker (T : E →ₗ[K] F)).subtypeL := by
  letI := hT
  letI : FiniteDimensional K (E ⧸ LinearMap.range
      ((LinearMap.ker (T : E →ₗ[K] F)).subtypeL : LinearMap.ker (T : E →ₗ[K] F) →ₗ[K] E)) := by
    rw [Submodule.toLinearMap_subtypeL, Submodule.range_subtype]
    exact (T : E →ₗ[K] F).quotKerEquivRange.symm.finiteDimensional
  refine
    { isStrictMap := (Submodule.isEmbedding_subtypeL _).isStrictMap
      isClosed_range := ?_
      finite_ker := ?_
      finite_coker := inferInstance
      closedComplemented_ker := ?_ }
  · rw [Submodule.toLinearMap_subtypeL, Submodule.range_subtype]
    exact T.isClosed_ker
  · rw [Submodule.toLinearMap_subtypeL, Submodule.ker_subtype]
    infer_instance
  · rw [Submodule.toLinearMap_subtypeL, Submodule.ker_subtype]
    exact Submodule.closedComplemented_bot

namespace ContinuousLinearMap

omit [IsRCLikeNormedField K] [CompleteSpace E] [CompleteSpace F] in
/-- A surjective continuous linear map has index the dimension of its kernel. -/
lemma index_of_surjective (T : E →L[K] F) (hT : Function.Surjective T) :
    index T = (finrank K (LinearMap.ker (T : E →ₗ[K] F)) : ℤ) := by
  rw [index_eq_finrank_sub, ← LinearMap.index_eq_finrank_sub, LinearMap.index_of_surjective hT]

omit [IsRCLikeNormedField K] [CompleteSpace E] [CompleteSpace F] in
/-- An injective continuous linear map has index the negative of the dimension of its cokernel. -/
lemma index_of_injective (T : E →L[K] F) (hT : Function.Injective T) :
    index T = -(finrank K (F ⧸ LinearMap.range (T : E →ₗ[K] F)) : ℤ) := by
  rw [index_eq_finrank_sub, ← LinearMap.index_eq_finrank_sub, LinearMap.index_of_injective hT]

omit [IsRCLikeNormedField K] [CompleteSpace E] [CompleteSpace F] in
/-- A bijective continuous linear map has Fredholm index zero. This formulation applies directly
when bijectivity is known before a continuous inverse has been bundled. -/
lemma index_eq_zero_of_bijective (T : E →L[K] F) (hT : Function.Bijective T) : index T = 0 := by
  rw [index_eq_finrank_sub, ← LinearMap.index_eq_finrank_sub]
  exact LinearEquiv.index_eq_zero (e := LinearEquiv.ofBijective (T : E →ₗ[K] F) hT)

end ContinuousLinearMap

omit [IsRCLikeNormedField K] in
/-- A bijective continuous linear map between Banach spaces is Fredholm. This formulation does not
require bundling its inverse as a continuous linear equivalence. Codomain completeness is used by
Mathlib's bounded-inverse construction `ContinuousLinearEquiv.ofBijective`. -/
lemma _root_.ContinuousLinearMap.IsFredholm.of_bijective (hT : Function.Bijective T) :
    ContinuousLinearMap.IsFredholm T := by
  exact ContinuousLinearMap.IsFredholm.of_continuousLinearEquiv
    (ContinuousLinearEquiv.ofBijective T
      (LinearMap.ker_eq_bot.mpr hT.injective)
      (LinearMap.range_eq_top.mpr hT.surjective))

end TauCeti
