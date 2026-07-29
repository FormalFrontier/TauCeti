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
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

namespace ContinuousLinearMap

/-- The restriction of a closed-range operator to the orthogonal complement of its kernel is a
continuous linear equivalence onto its range. -/
noncomputable def orthogonalKerEquivRange (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) :
    (LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ ≃L[𝕜]
      LinearMap.range (T : E →ₗ[𝕜] F) := by
  let K := LinearMap.ker (T : E →ₗ[𝕜] F)
  let R := LinearMap.range (T : E →ₗ[𝕜] F)
  let A : Kᗮ →L[𝕜] R :=
    (T.domRestrict Kᗮ).codRestrict R fun x => ⟨x, rfl⟩
  have hA_injective : Function.Injective A := by
    intro x y hxy
    apply Subtype.ext
    have hker : (x : E) - y ∈ K := by
      rw [LinearMap.mem_ker]
      simpa [A, K, sub_eq_zero] using congr_arg Subtype.val hxy
    have horth : (x : E) - y ∈ Kᗮ := Submodule.sub_mem _ x.2 y.2
    exact sub_eq_zero.mp <|
      inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hker horth)
  have hA_surjective : Function.Surjective A := by
    intro y
    obtain ⟨z, hz⟩ := y.2
    obtain ⟨k, hk, x, hx, hkx⟩ := K.exists_add_mem_mem_orthogonal z
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    -- Expose the ambient equality hidden by the range subtype.
    change T x = y
    rw [← hz, hkx, map_add]
    simp [LinearMap.mem_ker.mp hk]
  let e := LinearEquiv.ofBijective A.toLinearMap ⟨hA_injective, hA_surjective⟩
  exact e.toContinuousLinearEquivOfContinuous A.continuous

/-- The closed-range restriction equivalence acts by the original operator. -/
@[simp]
theorem orthogonalKerEquivRange_apply (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F))
    (x : (LinearMap.ker (T : E →ₗ[𝕜] F))ᗮ) :
    (orthogonalKerEquivRange T hT x :
      F) = T x := by
  simp [orthogonalKerEquivRange]

/-- Applying a closed-range operator to the inverse of its orthogonal-kernel restriction
recovers the given range element. -/
@[simp]
theorem orthogonalKerEquivRange_symm_apply (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F))
    (y : LinearMap.range (T : E →ₗ[𝕜] F)) :
    T ((orthogonalKerEquivRange T hT).symm y) = (y : F) :=
  (orthogonalKerEquivRange_apply T hT _).symm.trans <|
    congr_arg Subtype.val ((orthogonalKerEquivRange T hT).apply_symm_apply y)

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
    -- Pass from the inherited inner product on the subspace to the ambient one.
    change inner 𝕜 (x : E) ((T†) (y : F)) =
      inner 𝕜 (x : Kᗮ) (((e : Kᗮ →L[𝕜] R)†) y)
    rw [T.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
    dsimp only [e]
    -- Make both inherited range inner products ambient before using the restriction API.
    change inner 𝕜 (T (x : E)) (y : F) =
      inner 𝕜 ((orthogonalKerEquivRange T hT x :
        LinearMap.range (T : E →ₗ[𝕜] F)) : F) (y : F)
    rw [orthogonalKerEquivRange_apply]
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

/-- The cokernel of a Fredholm operator is linearly equivalent to the kernel of its adjoint. -/
noncomputable def IsFredholm.cokerEquivKerAdjoint {T : E →L[𝕜] F}
    (hT : IsFredholm T) :
    (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) ≃ₗ[𝕜]
      LinearMap.ker (T† : F →ₗ[𝕜] E) := by
  let range := LinearMap.range (T : E →ₗ[𝕜] F)
  letI : CompleteSpace range := hT.isClosed_range.completeSpace_coe
  exact range.quotientEquivOrthogonal.toLinearEquiv.trans
    (LinearEquiv.ofEq _ _ T.orthogonal_range)

/-- The cokernel of the adjoint of a Fredholm operator is linearly equivalent to the original
kernel. -/
noncomputable def IsFredholm.cokerAdjointEquivKer {T : E →L[𝕜] F}
    (hT : IsFredholm T) :
    (E ⧸ LinearMap.range (T† : F →ₗ[𝕜] E)) ≃ₗ[𝕜]
      LinearMap.ker (T : E →ₗ[𝕜] F) := by
  rw [ContinuousLinearMap.range_adjoint_eq_orthogonal_ker_of_isClosed_range T
    hT.isClosed_range]
  let K := LinearMap.ker (T : E →ₗ[𝕜] F)
  exact (Kᗮ).quotientEquivOrthogonal.toLinearEquiv.trans
    (LinearEquiv.ofEq _ _ <| by
      rw [K.orthogonal_orthogonal_eq_closure,
        T.isClosed_ker.submodule_topologicalClosure_eq])

/-- The adjoint of a Fredholm operator between Hilbert spaces is Fredholm. -/
theorem IsFredholm.adjoint {T : E →L[𝕜] F} (hT : IsFredholm T) :
    IsFredholm (T†) := by
  letI := hT.finiteDimensional_ker
  letI := hT.finiteDimensional_coker
  refine ⟨?_, ?_, ?_⟩
  · exact hT.cokerEquivKerAdjoint.finiteDimensional
  · exact ContinuousLinearMap.isClosed_range_adjoint_of_isClosed_range T hT.isClosed_range
  · exact hT.cokerAdjointEquivKer.symm.finiteDimensional

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
    ← LinearEquiv.finrank_eq hT.cokerEquivKerAdjoint,
    LinearEquiv.finrank_eq hT.cokerAdjointEquivKer]
  omega

end ContinuousLinearMap

end TauCeti

end
