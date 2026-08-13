/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Fredholm.ClosedRange
public import TauCeti.Analysis.Fredholm.Index

/-!
# Injective and surjective criteria for Fredholm operators

This file gives streamlined Fredholm criteria when an operator is already known to be injective
or surjective. Between Banach spaces over an `IsRCLikeNormedField`, a surjective continuous linear
map is Fredholm exactly when its kernel is finite dimensional. Between Banach spaces over any
nontrivially normed field, an injective continuous linear map with closed range is Fredholm exactly
when its cokernel is finite dimensional. Specialising both sides gives the bijective corollary:
a bijective continuous linear map between Banach spaces is Fredholm.

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
* `TauCeti.ContinuousLinearMap.finrank_ker_eq_iff_index_eq`: for a surjective operator, index `n`
  and kernel dimension `n` are the same statement.
* `TauCeti.ContinuousLinearMap.bijective_of_surjective_of_index_eq_zero`: a surjective operator of
  index zero with finite-dimensional kernel is bijective.
* `ContinuousLinearMap.IsFredholm.of_bijective`: a bijective continuous linear map between Banach
  spaces is Fredholm.

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
  let := IsRCLikeNormedField.rclike K
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
    let := hker
    exact ContinuousLinearMap.IsFredholm.of_surjective hT

omit [IsRCLikeNormedField K] in
/-- An injective continuous linear map between Banach spaces with closed range and
finite-dimensional cokernel is Fredholm. -/
lemma _root_.ContinuousLinearMap.IsFredholm.of_injective (hT : Function.Injective T)
    (hclosed : IsClosed (LinearMap.range (T : E →ₗ[K] F) : Set F))
    [FiniteDimensional K (F ⧸ LinearMap.range (T : E →ₗ[K] F))] :
    ContinuousLinearMap.IsFredholm T where
  isStrictMap := by
    let : CompleteSpace T.range := hclosed.completeSpace_coe
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
    let := hcoker
    exact ContinuousLinearMap.IsFredholm.of_injective hT hclosed

omit [IsRCLikeNormedField K] [CompleteSpace E] [CompleteSpace F] in
/-- The inclusion of the kernel of an operator of finite rank is Fredholm: the kernel is closed
and, by the first isomorphism theorem, of finite codimension. -/
lemma isFredholm_ker_subtypeL (hT : LinearMap.HasFiniteRange (T : E →ₗ[K] F)) :
    ContinuousLinearMap.IsFredholm (LinearMap.ker (T : E →ₗ[K] F)).subtypeL := by
  let : FiniteDimensional K (LinearMap.range (T : E →ₗ[K] F)) :=
    (Submodule.fg_iff_finiteDimensional _).mp hT.fg_range
  let : FiniteDimensional K (E ⧸ LinearMap.range
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
  rw [index_def, LinearMap.index_of_surjective hT]

omit [IsRCLikeNormedField K] [CompleteSpace E] [CompleteSpace F] in
/-- For a surjective continuous linear map, having index `n` and having a kernel of dimension `n`
are the same statement. This is `TauCeti.ContinuousLinearMap.index_of_surjective` with the cast to
`ℤ` discharged. -/
lemma finrank_ker_eq_iff_index_eq {n : ℕ} (T : E →L[K] F) (hT : Function.Surjective T) :
    finrank K (LinearMap.ker (T : E →ₗ[K] F)) = n ↔ index T = n := by
  rw [index_of_surjective T hT, Nat.cast_inj]

omit [IsRCLikeNormedField K] [CompleteSpace E] [CompleteSpace F] in
/-- A surjective operator of index zero with finite-dimensional kernel is bijective: its index is
the dimension of that kernel, so a vanishing index makes the kernel trivial. Only finiteness of the
kernel is used, not the full Fredholm property, which for a surjective operator is anyway
equivalent to it by `TauCeti.isFredholm_iff_finite_ker_of_surjective`. This is the converse of
`TauCeti.ContinuousLinearMap.index_eq_zero_of_bijective` for a surjective operator. -/
lemma bijective_of_surjective_of_index_eq_zero (T : E →L[K] F)
    (hfin : FiniteDimensional K (LinearMap.ker (T : E →ₗ[K] F))) (hT : Function.Surjective T)
    (hindex : index T = 0) : Function.Bijective T := by
  have := hfin
  have hker : LinearMap.ker (T : E →ₗ[K] F) = ⊥ :=
    Submodule.finrank_eq_zero.1 ((finrank_ker_eq_iff_index_eq T hT).2 (by exact_mod_cast hindex))
  exact ⟨LinearMap.ker_eq_bot.1 hker, hT⟩

omit [IsRCLikeNormedField K] [CompleteSpace E] [CompleteSpace F] in
/-- An injective continuous linear map has index the negative of the dimension of its cokernel. -/
lemma index_of_injective (T : E →L[K] F) (hT : Function.Injective T) :
    index T = -(finrank K (F ⧸ LinearMap.range (T : E →ₗ[K] F)) : ℤ) := by
  rw [index_def, LinearMap.index_of_injective hT]

end ContinuousLinearMap

omit [IsRCLikeNormedField K] in
/-- A bijective continuous linear map between Banach spaces is Fredholm. This formulation does not
require bundling its inverse as a continuous linear equivalence. Codomain completeness is used by
Mathlib's bounded-inverse construction `ContinuousLinearEquiv.ofBijective`. -/
lemma _root_.ContinuousLinearMap.IsFredholm.of_bijective (hT : Function.Bijective T) :
    ContinuousLinearMap.IsFredholm T := by
  have := ContinuousLinearEquiv.isFredholm
    (ContinuousLinearEquiv.ofBijective T
      (LinearMap.ker_eq_bot.mpr hT.injective)
      (LinearMap.range_eq_top.mpr hT.surjective))
  rwa [ContinuousLinearEquiv.coe_ofBijective] at this

end TauCeti
