/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Fredholm.Basic
import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Normed.Module.Complemented

/-!
# Splittings for Fredholm operators

This file proves the kernel and range splitting statements for a Fredholm operator between
Banach spaces. Over `IsRCLikeNormedField` scalars, the finite-dimensional kernel has a closed
complement by Hahn--Banach. The closed range has a closed complement because its quotient, the
cokernel, is finite-dimensional. The operator restricts to a continuous linear equivalence from
the chosen kernel complement onto its range.

These are the splittings used in the local normal form of a Fredholm map and in finite-dimensional
reduction. The complements are deliberately noncanonical; their defining properties, rather than
their chosen values, form the public API.

## Main declarations

* `TauCeti.IsFredholm.closedComplemented_ker`: the kernel of a Fredholm operator is
  topologically complemented.
* `TauCeti.IsFredholm.closedComplemented_range`: the range of a Fredholm operator is
  topologically complemented.
* `TauCeti.IsFredholm.kerComplement` and `TauCeti.IsFredholm.cokerComplement`: chosen closed
  complements to the kernel and range.
* `TauCeti.IsFredholm.kerComplementEquivRange`: the restriction of the operator is a continuous
  linear equivalence from the kernel complement to the range.
* `TauCeti.IsFredholm.cokerEquivComplement`: the cokernel is continuously linearly equivalent to
  its chosen complement.

The argument follows the kernel/cokernel splitting in McDuff--Salamon,
*J-holomorphic Curves and Symplectic Topology*, Appendix A.1. The existence of a complement to a
finite-dimensional subspace is Mathlib's Hahn--Banach theorem
`Submodule.ClosedComplemented.of_finiteDimensional`.
-/

public section

namespace TauCeti

open Module

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

namespace IsFredholm

variable {T : E →L[𝕜] F} (hT : _root_.TauCeti.IsFredholm T)

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The kernel of a Fredholm operator is topologically complemented. -/
theorem closedComplemented_ker (hT : _root_.TauCeti.IsFredholm T) :
    (LinearMap.ker (T : E →ₗ[𝕜] F)).ClosedComplemented := by
  letI := _root_.TauCeti.IsFredholm.finiteDimensional_ker hT
  exact Submodule.ClosedComplemented.of_finiteDimensional _

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The range of a Fredholm operator is topologically complemented. -/
theorem closedComplemented_range (hT : _root_.TauCeti.IsFredholm T) :
    (LinearMap.range (T : E →ₗ[𝕜] F)).ClosedComplemented := by
  letI := _root_.TauCeti.IsFredholm.finiteDimensional_coker hT
  exact Submodule.ClosedComplemented.of_finiteDimensional_quotient
    (_root_.TauCeti.IsFredholm.isClosed_range hT)

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- A chosen closed complement to the kernel of a Fredholm operator. -/
noncomputable def kerComplement : Submodule 𝕜 E :=
  hT.closedComplemented_ker.complement

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- A chosen finite-dimensional complement to the range of a Fredholm operator. It represents
the cokernel inside the codomain. -/
noncomputable def cokerComplement : Submodule 𝕜 F :=
  hT.closedComplemented_range.complement

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The kernel and its chosen complement are topological complements. -/
theorem isTopCompl_ker_kerComplement :
    Submodule.IsTopCompl (LinearMap.ker (T : E →ₗ[𝕜] F)) hT.kerComplement :=
  hT.closedComplemented_ker.isTopCompl_complement

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The range and its chosen complement are topological complements. -/
theorem isTopCompl_range_cokerComplement :
    Submodule.IsTopCompl (LinearMap.range (T : E →ₗ[𝕜] F)) hT.cokerComplement :=
  hT.closedComplemented_range.isTopCompl_complement

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The chosen complement to the kernel is closed. -/
theorem isClosed_kerComplement : IsClosed (hT.kerComplement : Set E) :=
  hT.closedComplemented_ker.isClosed_complement

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The chosen complement to the range is closed. -/
theorem isClosed_cokerComplement : IsClosed (hT.cokerComplement : Set F) :=
  hT.closedComplemented_range.isClosed_complement

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The codomain is continuously linearly equivalent to the product of the range and a chosen
cokernel representative. -/
noncomputable def rangeProdCokerComplementEquiv :
    (LinearMap.range (T : E →ₗ[𝕜] F) × hT.cokerComplement) ≃L[𝕜] F :=
  Submodule.prodEquivOfIsTopCompl _ _ hT.isTopCompl_range_cokerComplement

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
@[simp]
theorem rangeProdCokerComplementEquiv_apply
    (x : LinearMap.range (T : E →ₗ[𝕜] F) × hT.cokerComplement) :
    hT.rangeProdCokerComplementEquiv x = (x.1 : F) + x.2 :=
  Submodule.prodEquivOfIsTopCompl_apply hT.isTopCompl_range_cokerComplement x

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
@[simp]
theorem rangeProdCokerComplementEquiv_symm_apply (x : F) :
    hT.rangeProdCokerComplementEquiv.symm x =
      ((LinearMap.range (T : E →ₗ[𝕜] F)).projectionOntoL hT.cokerComplement
        hT.isTopCompl_range_cokerComplement x,
      hT.cokerComplement.projectionOntoL (LinearMap.range (T : E →ₗ[𝕜] F))
        hT.isTopCompl_range_cokerComplement.symm x) :=
  Submodule.prodEquivOfIsTopCompl_symm_apply hT.isTopCompl_range_cokerComplement x

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The domain is continuously linearly equivalent to the product of the kernel and a chosen
kernel complement. -/
noncomputable def kerProdComplementEquiv :
    (LinearMap.ker (T : E →ₗ[𝕜] F) × hT.kerComplement) ≃L[𝕜] E :=
  Submodule.prodEquivOfIsTopCompl _ _ hT.isTopCompl_ker_kerComplement

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
@[simp]
theorem kerProdComplementEquiv_apply
    (x : LinearMap.ker (T : E →ₗ[𝕜] F) × hT.kerComplement) :
    hT.kerProdComplementEquiv x = (x.1 : E) + x.2 :=
  Submodule.prodEquivOfIsTopCompl_apply hT.isTopCompl_ker_kerComplement x

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
@[simp]
theorem kerProdComplementEquiv_symm_apply (x : E) :
    hT.kerProdComplementEquiv.symm x =
      ((LinearMap.ker (T : E →ₗ[𝕜] F)).projectionOntoL hT.kerComplement
        hT.isTopCompl_ker_kerComplement x,
      hT.kerComplement.projectionOntoL (LinearMap.ker (T : E →ₗ[𝕜] F))
        hT.isTopCompl_ker_kerComplement.symm x) :=
  Submodule.prodEquivOfIsTopCompl_symm_apply hT.isTopCompl_ker_kerComplement x

/-- A Fredholm operator restricts to a continuous linear equivalence from its chosen kernel
complement onto its range. -/
noncomputable def kerComplementEquivRange :
    hT.kerComplement ≃L[𝕜] LinearMap.range (T : E →ₗ[𝕜] F) := by
  letI : CompleteSpace hT.kerComplement := hT.isClosed_kerComplement.completeSpace_coe
  -- `toContinuousLinearEquivOfContinuous` requires both sides to be complete.
  letI : CompleteSpace (LinearMap.range (T : E →ₗ[𝕜] F)) :=
    (_root_.TauCeti.IsFredholm.isClosed_range hT).completeSpace_coe
  exact (LinearMap.kerComplementEquivRange (T : E →ₗ[𝕜] F)
    hT.isTopCompl_ker_kerComplement.isCompl.symm).toContinuousLinearEquivOfContinuous
      ((T.continuous.comp continuous_subtype_val).subtype_mk _)

omit [CompleteSpace 𝕜] in
@[simp]
theorem kerComplementEquivRange_apply (x : hT.kerComplement) :
    (hT.kerComplementEquivRange x : F) = T x := by
  letI : CompleteSpace hT.kerComplement := hT.isClosed_kerComplement.completeSpace_coe
  letI : CompleteSpace (LinearMap.range (T : E →ₗ[𝕜] F)) :=
    (_root_.TauCeti.IsFredholm.isClosed_range hT).completeSpace_coe
  rw [kerComplementEquivRange, LinearEquiv.coeFn_toContinuousLinearEquivOfContinuous]
  exact LinearMap.kerComplementEquivRange_apply_coe _ _ x

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The cokernel of a Fredholm operator is continuously linearly equivalent to its chosen
complement in the codomain. -/
noncomputable def cokerEquivComplement :
    (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) ≃L[𝕜] hT.cokerComplement :=
  Submodule.quotientEquivOfIsTopCompl _ _ hT.isTopCompl_range_cokerComplement

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
@[simp]
theorem cokerEquivComplement_symm_apply (x : hT.cokerComplement) :
    hT.cokerEquivComplement.symm x = (LinearMap.range (T : E →ₗ[𝕜] F)).mkQ x :=
  Submodule.quotientEquivOfIsTopCompl_symm_apply hT.isTopCompl_range_cokerComplement x

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
@[simp]
theorem cokerEquivComplement_apply_mk (x : F) :
    hT.cokerEquivComplement (Submodule.Quotient.mk x) =
      hT.cokerComplement.projectionOnto (LinearMap.range (T : E →ₗ[𝕜] F))
        hT.isTopCompl_range_cokerComplement.isCompl.symm x :=
  Submodule.quotientEquivOfIsTopCompl_apply_mk hT.isTopCompl_range_cokerComplement x

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
noncomputable instance finiteDimensional_cokerComplement :
    FiniteDimensional 𝕜 hT.cokerComplement := by
  letI := _root_.TauCeti.IsFredholm.finiteDimensional_coker hT
  exact hT.cokerEquivComplement.toLinearEquiv.finiteDimensional

end IsFredholm

end TauCeti

end
