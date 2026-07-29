/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Fredholm.Basic

/-!
# Injective and surjective criteria for Fredholm operators

This file gives streamlined Fredholm criteria when an operator is already known to be injective
or surjective. A surjective continuous linear map is Fredholm exactly when its kernel is finite
dimensional. Dually, an injective continuous linear map with closed range is Fredholm exactly when
its cokernel is finite dimensional. Specialising both sides gives the bijective corollaries: a
bijective continuous linear map is Fredholm of index zero.

These criteria are the elementary endpoints of the finite-dimensional reductions used throughout
Fredholm theory. As an application of the injective closed-range criterion, the inclusion of the
kernel of an operator of finite rank is Fredholm.

## Main declarations

* `TauCeti.isFredholm_iff_finiteDimensional_ker_of_surjective`: the surjective criterion.
* `TauCeti.isFredholm_iff_finiteDimensional_coker_of_injective`: the injective closed-range
  criterion.
* `TauCeti.isFredholm_ker_subtypeL`: the inclusion of the kernel of an operator of finite rank is
  Fredholm.
* `TauCeti.ContinuousLinearMap.index_of_surjective` and
  `TauCeti.ContinuousLinearMap.index_of_injective`: the index in the two one-sided cases.
* `TauCeti.IsFredholm.of_bijective` and
  `TauCeti.ContinuousLinearMap.index_eq_zero_of_bijective`: the bijective corollaries.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix
A.1.
-/

public section

namespace TauCeti

open Module

variable {K E F : Type*}
variable [NontriviallyNormedField K]
variable [NormedAddCommGroup E] [NormedSpace K E]
variable [NormedAddCommGroup F] [NormedSpace K F]

variable {T : E →L[K] F}

/-- A surjective continuous linear map with finite-dimensional kernel is Fredholm. -/
lemma IsFredholm.of_surjective (hT : Function.Surjective T)
    [FiniteDimensional K (LinearMap.ker (T : E →ₗ[K] F))] : IsFredholm T where
  finiteDimensional_ker := inferInstance
  isClosed_range := by
    rw [LinearMap.range_eq_top.mpr hT]
    exact isClosed_univ
  finiteDimensional_coker := by
    rw [LinearMap.range_eq_top.mpr hT]
    infer_instance

/-- For a surjective continuous linear map, Fredholmness is equivalent to finite-dimensionality of
the kernel. -/
lemma isFredholm_iff_finiteDimensional_ker_of_surjective (hT : Function.Surjective T) :
    IsFredholm T ↔ FiniteDimensional K (LinearMap.ker (T : E →ₗ[K] F)) := by
  constructor
  · exact IsFredholm.finiteDimensional_ker
  · intro hker
    letI := hker
    exact IsFredholm.of_surjective hT

/-- An injective continuous linear map with closed range and finite-dimensional cokernel is
Fredholm. -/
lemma IsFredholm.of_injective (hT : Function.Injective T)
    (hclosed : IsClosed (LinearMap.range (T : E →ₗ[K] F) : Set F))
    [FiniteDimensional K (F ⧸ LinearMap.range (T : E →ₗ[K] F))] : IsFredholm T where
  finiteDimensional_ker := by
    rw [LinearMap.ker_eq_bot.mpr hT]
    infer_instance
  isClosed_range := hclosed
  finiteDimensional_coker := inferInstance

/-- For an injective continuous linear map with closed range, Fredholmness is equivalent to
finite-dimensionality of the cokernel. -/
lemma isFredholm_iff_finiteDimensional_coker_of_injective (hT : Function.Injective T)
    (hclosed : IsClosed (LinearMap.range (T : E →ₗ[K] F) : Set F)) :
    IsFredholm T ↔ FiniteDimensional K (F ⧸ LinearMap.range (T : E →ₗ[K] F)) := by
  constructor
  · exact IsFredholm.finiteDimensional_coker
  · intro hcoker
    letI := hcoker
    exact IsFredholm.of_injective hT hclosed

/-- The inclusion of the kernel of an operator of finite rank is Fredholm: the kernel is closed
and, by the first isomorphism theorem, of finite codimension. -/
lemma isFredholm_ker_subtypeL (hT : FiniteDimensional K (LinearMap.range (T : E →ₗ[K] F))) :
    IsFredholm (LinearMap.ker (T : E →ₗ[K] F)).subtypeL := by
  letI := hT
  letI : FiniteDimensional K (E ⧸ LinearMap.range
      ((LinearMap.ker (T : E →ₗ[K] F)).subtypeL : LinearMap.ker (T : E →ₗ[K] F) →ₗ[K] E)) := by
    rw [Submodule.toLinearMap_subtypeL, Submodule.range_subtype]
    exact (T : E →ₗ[K] F).quotKerEquivRange.symm.finiteDimensional
  refine IsFredholm.of_injective (Submodule.injective_subtype _) ?_
  rw [Submodule.toLinearMap_subtypeL, Submodule.range_subtype]
  exact T.isClosed_ker

namespace ContinuousLinearMap

/-- A surjective continuous linear map has index the dimension of its kernel. -/
lemma index_of_surjective (T : E →L[K] F) (hT : Function.Surjective T) :
    index T = (finrank K (LinearMap.ker (T : E →ₗ[K] F)) : ℤ) := by
  rw [index_eq_finrank_sub, ← LinearMap.index_eq_finrank_sub, LinearMap.index_of_surjective hT]

/-- An injective continuous linear map has index the negative of the dimension of its cokernel. -/
lemma index_of_injective (T : E →L[K] F) (hT : Function.Injective T) :
    index T = -(finrank K (F ⧸ LinearMap.range (T : E →ₗ[K] F)) : ℤ) := by
  rw [index_eq_finrank_sub, ← LinearMap.index_eq_finrank_sub, LinearMap.index_of_injective hT]

/-- A bijective continuous linear map has Fredholm index zero. This formulation applies directly
when bijectivity is known before a continuous inverse has been bundled. -/
lemma index_eq_zero_of_bijective (T : E →L[K] F) (hT : Function.Bijective T) : index T = 0 := by
  rw [index_eq_finrank_sub, ← LinearMap.index_eq_finrank_sub]
  exact LinearEquiv.index_eq_zero (e := LinearEquiv.ofBijective (T : E →ₗ[K] F) hT)

end ContinuousLinearMap

/-- A bijective continuous linear map is Fredholm. This formulation does not require bundling its
inverse as a continuous linear equivalence. -/
lemma IsFredholm.of_bijective (hT : Function.Bijective T) : IsFredholm T := by
  letI : FiniteDimensional K (LinearMap.ker (T : E →ₗ[K] F)) := by
    rw [LinearMap.ker_eq_bot.mpr hT.injective]
    infer_instance
  exact IsFredholm.of_surjective hT.surjective

end TauCeti
