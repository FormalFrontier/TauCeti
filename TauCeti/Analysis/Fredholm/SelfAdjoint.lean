/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Fredholm.Adjoint

/-!
# Self-adjoint Fredholm operators

This file proves that a self-adjoint Fredholm operator on a Hilbert space has index zero. More
generally, the same conclusion holds whenever an operator and its adjoint have the same kernel.
The closed range of a Fredholm operator has orthogonal complement equal to the kernel of its
adjoint. Orthogonal decomposition therefore identifies the cokernel with that kernel; under the
kernel-equality hypothesis, it identifies the cokernel with the original kernel.

## Main declarations

* `TauCeti.IsFredholm.cokerEquivKerOfKerAdjointEq`: identify the cokernel with the kernel when
  the operator and its adjoint have equal kernels.
* `TauCeti.ContinuousLinearMap.index_eq_zero_of_ker_adjoint_eq`: the corresponding index-zero
  criterion.
* `TauCeti.ContinuousLinearMap.index_eq_zero_of_isSelfAdjoint`: a self-adjoint Fredholm operator
  has index zero.
* `TauCeti.ContinuousLinearMap.index_eq_zero_of_isSymmetric`: the same result in terms of
  symmetry of the underlying linear map.

This is the elementary self-adjoint index computation in the Fredholm package needed by the
nonlinear-analysis substrate of the analytic Heegaard Floer roadmap. The convention and argument
follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix A.1.
-/

public section

namespace TauCeti

open Module

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The cokernel of a Fredholm operator is linearly equivalent to its kernel if the operator and
its adjoint have the same kernel. -/
noncomputable def IsFredholm.cokerEquivKerOfKerAdjointEq {T : E →L[𝕜] E}
    (hT : IsFredholm T)
    (hker : (ContinuousLinearMap.adjoint T).ker = T.ker) :
    (E ⧸ LinearMap.range (T : E →ₗ[𝕜] E)) ≃ₗ[𝕜]
      LinearMap.ker (T : E →ₗ[𝕜] E) :=
  (TauCeti.ContinuousLinearMap.cokerEquivKerAdjoint T hT.isClosed_range).trans
    (LinearEquiv.ofEq _ _ hker)

/-- The cokernel of a self-adjoint Fredholm operator is linearly equivalent to its kernel. -/
noncomputable def IsFredholm.cokerEquivKer {T : E →L[𝕜] E} (hT : IsFredholm T)
    (hself : IsSelfAdjoint T) :
    (E ⧸ LinearMap.range (T : E →ₗ[𝕜] E)) ≃ₗ[𝕜]
      LinearMap.ker (T : E →ₗ[𝕜] E) :=
  hT.cokerEquivKerOfKerAdjointEq <| by rw [hself.adjoint_eq]

namespace ContinuousLinearMap

/-- A Fredholm operator has index zero if it and its adjoint have the same kernel. -/
theorem index_eq_zero_of_ker_adjoint_eq {T : E →L[𝕜] E} (hT : IsFredholm T)
    (hker : (ContinuousLinearMap.adjoint T).ker = T.ker) :
    index T = 0 := by
  rw [index_eq_finrank_sub,
    ← LinearEquiv.finrank_eq (hT.cokerEquivKerOfKerAdjointEq hker)]
  omega

/-- A self-adjoint Fredholm operator on a Hilbert space has Fredholm index zero. -/
@[simp]
theorem index_eq_zero_of_isSelfAdjoint {T : E →L[𝕜] E} (hT : IsFredholm T)
    (hself : IsSelfAdjoint T) : index T = 0 :=
  index_eq_zero_of_ker_adjoint_eq hT <| by rw [hself.adjoint_eq]

/-- A symmetric Fredholm operator on a Hilbert space has Fredholm index zero. -/
@[simp]
theorem index_eq_zero_of_isSymmetric {T : E →L[𝕜] E} (hT : IsFredholm T)
    (hsymm : T.IsSymmetric) : index T = 0 :=
  index_eq_zero_of_isSelfAdjoint hT
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hsymm)

end ContinuousLinearMap

end TauCeti
