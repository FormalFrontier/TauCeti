/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Fredholm.ClosedRange
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Adjoints of Fredholm operators

This file proves the closed-range theorem for adjoints on Hilbert spaces and applies it to
Fredholm operators. If a continuous linear map has closed range, then its adjoint has range
equal to the orthogonal complement of the original kernel. Consequently, taking adjoints
preserves Fredholm operators and negates their index.

The proof restricts an operator with closed range to a continuous linear equivalence from the
orthogonal complement of its kernel onto its range. The adjoint of this equivalence is
surjective, which removes the closure from Mathlib's general identity
`T.orthogonal_ker : T.kerᗮ = T†.range.topologicalClosure`.

## Main declarations

* `TauCeti.ContinuousLinearMap.orthogonalKerEquivRange`: the restriction of a closed-range
  operator to the orthogonal complement of its kernel.
* `TauCeti.ContinuousLinearMap.range_adjoint_eq_orthogonal_ker_of_isClosed_range`: the
  closed-range theorem for adjoints.
* `TauCeti.ContinuousLinearMap.isClosed_range_adjoint_iff`: an operator has closed range if and
  only if its adjoint does.
* `TauCeti.IsFredholm.adjoint`: the adjoint of a Fredholm operator is Fredholm.
* `TauCeti.ContinuousLinearMap.index_adjoint`: taking the adjoint negates the Fredholm index.

The argument and index convention follow McDuff--Salamon,
*J-holomorphic Curves and Symplectic Topology*, Appendix A.1.
-/

public section

namespace TauCeti

open Module
open scoped InnerProduct

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F]

namespace ContinuousLinearMap

section Restriction

variable [NormedSpace 𝕜 F] [CompleteSpace F]

/-- The restriction of a closed-range operator to the orthogonal complement of its kernel is a
continuous linear equivalence onto its range. -/
noncomputable def orthogonalKerEquivRange (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) :
    (LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ ≃L[𝕜]
      LinearMap.range (T : E →ₗ[𝕜] F) := by
  let K := LinearMap.ker (T : E →ₗ[𝕜] F)
  let R := LinearMap.range (T : E →ₗ[𝕜] F)
  letI : CompleteSpace Kᗮ := K.isClosed_orthogonal.completeSpace_coe
  letI : CompleteSpace R := hT.completeSpace_coe
  exact (LinearMap.kerComplementEquivRange (T : E →ₗ[𝕜] F)
    K.isCompl_orthogonal.symm).toContinuousLinearEquivOfContinuous
      ((T.continuous.comp continuous_subtype_val).subtype_mk _)

/-- The closed-range restriction equivalence acts by the original operator. -/
@[simp]
theorem orthogonalKerEquivRange_apply (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F))
    (x : (LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ) :
    (orthogonalKerEquivRange T hT x :
      F) = T x := by
  letI : CompleteSpace (LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ :=
    (LinearMap.ker (T : E →ₗ[𝕜] F)).isClosed_orthogonal.completeSpace_coe
  letI : CompleteSpace (LinearMap.range (T : E →ₗ[𝕜] F)) :=
    hT.completeSpace_coe
  rw [orthogonalKerEquivRange, LinearEquiv.coeFn_toContinuousLinearEquivOfContinuous]
  exact LinearMap.kerComplementEquivRange_apply_coe _ _ x

/-- Applying a closed-range operator to the inverse of its orthogonal-kernel restriction
recovers the given range element. -/
@[simp]
theorem orthogonalKerEquivRange_symm_apply (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F))
    (y : LinearMap.range (T : E →ₗ[𝕜] F)) :
    T ((orthogonalKerEquivRange T hT).symm y) = (y : F) :=
  (orthogonalKerEquivRange_apply T hT _).symm.trans <|
    congr_arg Subtype.val ((orthogonalKerEquivRange T hT).apply_symm_apply y)

end Restriction

end ContinuousLinearMap

section HilbertCodomain

variable [InnerProductSpace 𝕜 F] [CompleteSpace F]

namespace ContinuousLinearMap

/-- The adjoint of a continuous linear equivalence is bijective. -/
private theorem adjoint_bijective (e : E ≃L[𝕜] F) :
    Function.Bijective ((e : E →L[𝕜] F)†) := by
  let A : F →L[𝕜] E := ((e : E →L[𝕜] F)†)
  let B : E →L[𝕜] F := ((e.symm : F →L[𝕜] E)†)
  have hBA : B.comp A = ContinuousLinearMap.id 𝕜 F := by
    rw [← ContinuousLinearMap.adjoint_comp]
    ext x
    simp
  have hAB : A.comp B = ContinuousLinearMap.id 𝕜 E := by
    rw [← ContinuousLinearMap.adjoint_comp]
    ext x
    simp
  -- Fold the displayed adjoint back to the local name used for the inverse identities.
  change Function.Bijective A
  constructor
  · intro x y hxy
    apply_fun B at hxy
    simpa only [← ContinuousLinearMap.comp_apply, hBA, ContinuousLinearMap.id_apply] using hxy
  · intro x
    refine ⟨B x, ?_⟩
    simp only [← ContinuousLinearMap.comp_apply, hAB, ContinuousLinearMap.id_apply]

/-- A continuous linear map with closed range has adjoint range equal to the orthogonal
complement of its kernel. -/
theorem range_adjoint_eq_orthogonal_ker_of_isClosed_range (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) :
    LinearMap.range (T† : F →ₗ[𝕜] E) =
      (LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ := by
  let K := LinearMap.ker (T : E →ₗ[𝕜] F)
  let R := LinearMap.range (T : E →ₗ[𝕜] F)
  let e : Kᗮ ≃L[𝕜] R := orthogonalKerEquivRange T hT
  have he_apply (x : Kᗮ) : (e x : F) = T (x : E) := by
    simpa only [e] using orthogonalKerEquivRange_apply T hT x
  have hadj_mem (y : F) : (T†) y ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    intro x hx
    have hx0 : T x = 0 := LinearMap.mem_ker.mp (by simpa [K] using hx)
    rw [T.adjoint_inner_right, hx0]
    simp
  let B : R →L[𝕜] Kᗮ :=
    ((T†).domRestrict R).codRestrict Kᗮ fun y => hadj_mem y
  have hB : B = ((e : Kᗮ →L[𝕜] R)†) := by
    apply ContinuousLinearMap.ext
    intro y
    refine ext_inner_left 𝕜 fun x => ?_
    calc
      inner 𝕜 x (B y) = inner 𝕜 (x : E) ((T†) (y : F)) := by
        rw [Submodule.coe_inner]
        simp only [B, ContinuousLinearMap.coe_codRestrict_apply,
          ContinuousLinearMap.domRestrict_apply]
      _ = inner 𝕜 (T (x : E)) (y : F) := T.adjoint_inner_right x y
      _ = inner 𝕜 ((e x : R) : F) (y : F) := by
        rw [he_apply]
      _ = inner 𝕜 (e x) y := (Submodule.coe_inner R (e x) y).symm
      _ = inner 𝕜 x (((e : Kᗮ →L[𝕜] R)†) y) :=
        (ContinuousLinearMap.adjoint_inner_right (e : Kᗮ →L[𝕜] R) x y).symm
  have hB_surjective : Function.Surjective B := by
    rw [hB]
    exact (adjoint_bijective e).2
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    exact hadj_mem y
  · intro x hx
    obtain ⟨y, hy⟩ := hB_surjective ⟨x, hx⟩
    refine ⟨(y : F), ?_⟩
    exact congr_arg Subtype.val hy

/-- If a continuous linear map between Hilbert spaces has closed range, then so does its
adjoint. -/
theorem isClosed_range_adjoint_of_isClosed_range (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) :
    IsClosed (LinearMap.range (T† : F →ₗ[𝕜] E) : Set E) := by
  rw [range_adjoint_eq_orthogonal_ker_of_isClosed_range T hT]
  exact (LinearMap.ker (T : E →ₗ[𝕜] F)).isClosed_orthogonal

/-- A continuous linear map between Hilbert spaces has closed range if and only if its adjoint
does. -/
@[simp]
theorem isClosed_range_adjoint_iff (T : E →L[𝕜] F) :
    IsClosed (LinearMap.range (T† : F →ₗ[𝕜] E) : Set E) ↔
      IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F) := by
  constructor
  · intro hT
    simpa using isClosed_range_adjoint_of_isClosed_range (T†) hT
  · exact isClosed_range_adjoint_of_isClosed_range T

end ContinuousLinearMap

namespace ContinuousLinearMap

/-- The cokernel of a closed-range operator is continuously linearly equivalent to the kernel of
its adjoint. -/
noncomputable def cokerEquivKerAdjoint (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) :
    (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) ≃L[𝕜]
      LinearMap.ker (T† : F →ₗ[𝕜] E) := by
  let range := LinearMap.range (T : E →ₗ[𝕜] F)
  letI : CompleteSpace range := hT.completeSpace_coe
  exact range.quotientEquivOrthogonal.toContinuousLinearEquiv.trans
    (LinearIsometryEquiv.ofEq _ _ T.orthogonal_range).toContinuousLinearEquiv

/-- On quotient representatives, the cokernel--adjoint-kernel equivalence is orthogonal
projection onto the orthogonal complement of the range. -/
@[simp]
theorem coe_cokerEquivKerAdjoint_apply_mk (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) (y : F) :
    (cokerEquivKerAdjoint T hT (Submodule.Quotient.mk y) : F) =
      ((LinearMap.range (T : E →ₗ[𝕜] F))ᗮ.orthogonalProjectionOnto y : F) := by
  simp [cokerEquivKerAdjoint,
    Submodule.orthogonalProjectionOnto_apply_eq_projectionOnto]

/-- The inverse cokernel--adjoint-kernel equivalence sends a kernel vector to its quotient
class. -/
@[simp]
theorem cokerEquivKerAdjoint_symm_apply (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F))
    (y : LinearMap.ker (T† : F →ₗ[𝕜] E)) :
    (cokerEquivKerAdjoint T hT).symm y = Submodule.Quotient.mk (y : F) := by
  let range := LinearMap.range (T : E →ₗ[𝕜] F)
  letI : CompleteSpace range := hT.completeSpace_coe
  simp [cokerEquivKerAdjoint]

/-- The cokernel of the adjoint of a closed-range operator is continuously linearly equivalent to
the original kernel. -/
noncomputable def cokerAdjointEquivKer (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) :
    (E ⧸ LinearMap.range (T† : F →ₗ[𝕜] E)) ≃L[𝕜]
      LinearMap.ker (T : E →ₗ[𝕜] F) :=
  (cokerEquivKerAdjoint (T†) (isClosed_range_adjoint_of_isClosed_range T hT)).trans
    (LinearIsometryEquiv.ofEq _ _ <| by simp).toContinuousLinearEquiv

/-- On quotient representatives, the adjoint-cokernel--kernel equivalence is orthogonal
projection onto the orthogonal complement of the adjoint range. -/
@[simp]
theorem coe_cokerAdjointEquivKer_apply_mk (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) (x : E) :
    (cokerAdjointEquivKer T hT (Submodule.Quotient.mk x) : E) =
      ((LinearMap.range (T† : F →ₗ[𝕜] E))ᗮ.orthogonalProjectionOnto x : E) := by
  simp [cokerAdjointEquivKer, coe_cokerEquivKerAdjoint_apply_mk]

/-- The inverse adjoint-cokernel--kernel equivalence sends a kernel vector to its quotient
class. -/
@[simp]
theorem cokerAdjointEquivKer_symm_apply (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F))
    (x : LinearMap.ker (T : E →ₗ[𝕜] F)) :
    (cokerAdjointEquivKer T hT).symm x = Submodule.Quotient.mk (x : E) := by
  simp [cokerAdjointEquivKer]

end ContinuousLinearMap

/-- The adjoint of a Fredholm operator between Hilbert spaces is Fredholm. -/
theorem IsFredholm.adjoint {T : E →L[𝕜] F} (hT : IsFredholm T) :
    IsFredholm (T†) := by
  letI := hT.finiteDimensional_ker
  letI := hT.finiteDimensional_coker
  refine ⟨?_, ?_, ?_⟩
  · exact (ContinuousLinearMap.cokerEquivKerAdjoint T
      hT.isClosed_range).toLinearEquiv.finiteDimensional
  · exact ContinuousLinearMap.isClosed_range_adjoint_of_isClosed_range T hT.isClosed_range
  · exact (ContinuousLinearMap.cokerAdjointEquivKer T
      hT.isClosed_range).symm.toLinearEquiv.finiteDimensional

/-- A continuous linear map between Hilbert spaces is Fredholm if and only if its adjoint is
Fredholm. -/
@[simp]
theorem isFredholm_adjoint_iff (T : E →L[𝕜] F) :
    IsFredholm (T†) ↔ IsFredholm T := by
  constructor
  · intro hT
    simpa using hT.adjoint
  · exact IsFredholm.adjoint

namespace ContinuousLinearMap

/-- Taking the adjoint of a Fredholm operator negates its index. -/
@[simp]
theorem index_adjoint (T : E →L[𝕜] F) (hT : IsFredholm T) :
    index (T†) = -index T := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub,
    ← LinearEquiv.finrank_eq (cokerEquivKerAdjoint T hT.isClosed_range).toLinearEquiv,
    LinearEquiv.finrank_eq (cokerAdjointEquivKer T hT.isClosed_range).toLinearEquiv]
  omega

end ContinuousLinearMap

end HilbertCodomain

end TauCeti

end
