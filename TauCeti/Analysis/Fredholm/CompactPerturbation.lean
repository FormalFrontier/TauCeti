/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.ClosedRange
public import TauCeti.Analysis.Fredholm.ContinuousFamily
public import TauCeti.Analysis.Normed.Operator.Compact.RieszTheory

/-!
# Compact perturbations of Fredholm operators

A compact perturbation of a Fredholm operator between Banach spaces is Fredholm, with the same
index. This is the last of the three classical stability statements for the Fredholm index --
after finite-rank perturbations (`TauCeti.Analysis.Fredholm.FiniteRank`) and small perturbations
(`TauCeti.Analysis.Fredholm.SmallPerturbation`) -- and completes the linear half of Lane F0 of the
analytic Heegaard Floer roadmap.

The starting point is the Riesz--Schauder theory of
`TauCeti.Analysis.Normed.Operator.Compact.RieszTheory`: for a compact operator `K` the kernel of
`1 - K` is finite dimensional and its cokernel is finite dimensional, so `1 - K` is Fredholm.

For a general Fredholm `T` and compact `C`, take a continuous quasi-inverse `S` of `T`, so that
`S ∘ T` and `T ∘ S` differ from the identity by operators of finite rank. Then
`S ∘ (T + C) = (1 + S ∘ C) + (S ∘ T - 1)` is a finite-rank perturbation of a compact perturbation
of the identity, hence Fredholm, and likewise for `(T + C) ∘ S`. The kernel of `T + C` sits inside
the kernel of `S ∘ (T + C)` and the range of `T + C` contains the range of `(T + C) ∘ S`, so both
defect spaces of `T + C` are finite dimensional.

The index statement is then a connectedness argument rather than a new computation: the family
`c ↦ T + c • C` is a continuous family of Fredholm operators over the preconnected parameter space
`𝕜`, so the local constancy of the index proved in `TauCeti.Analysis.Fredholm.ContinuousFamily`
forces the values at `c = 0` and `c = 1` to agree.

## Main declarations

* `TauCeti.isFredholm_one_sub` and `TauCeti.isFredholm_one_add`: `1 - K` and `1 + K` are Fredholm
  for `K` compact.
* `ContinuousLinearMap.IsFredholm.add_of_isCompactOperator`: a compact perturbation of a Fredholm
  operator is Fredholm.
* `TauCeti.ContinuousLinearMap.index_add_of_isCompactOperator`: a compact perturbation leaves the
  index unchanged.
* `TauCeti.ContinuousLinearMap.index_one_sub_eq_zero` and
  `TauCeti.ContinuousLinearMap.index_one_add_eq_zero`: `1 - K` and `1 + K` have index `0` for `K`
  compact.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix
A.1; the compact-perturbation statement is Atkinson's theorem together with the Riesz--Schauder
theory, see Conway, *A Course in Functional Analysis*, Chapter XI.
-/

public section

namespace TauCeti

open Module

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **Riesz--Schauder**: a compact perturbation of the identity is a Fredholm operator. -/
theorem isFredholm_one_sub {K : E →L[𝕜] E} (hK : IsCompactOperator K) :
    ContinuousLinearMap.IsFredholm (1 - K : E →L[𝕜] E) :=
  ContinuousLinearMap.IsFredholm.of_finite_ker_coker _
    (IsCompactOperator.finiteDimensional_ker_one_sub hK)
    (IsCompactOperator.finiteDimensional_quotient_range_one_sub hK)

/-- **Riesz--Schauder**, in the form in which compact perturbations of the identity arise below. -/
theorem isFredholm_one_add {K : E →L[𝕜] E} (hK : IsCompactOperator K) :
    ContinuousLinearMap.IsFredholm (1 + K : E →L[𝕜] E) := by
  have hneg : IsCompactOperator (-K : E →L[𝕜] E) := by
    simpa only [FunLike.coe_neg] using hK.neg
  have hrw : (1 + K : E →L[𝕜] E) = 1 - (-K) := by abel
  rw [hrw]
  exact isFredholm_one_sub hneg

variable {T C : E →L[𝕜] F}

/-- A compact perturbation of a Fredholm operator between Banach spaces is Fredholm.

The proof is Atkinson's argument: a quasi-inverse `S` of `T` turns `T + C` into a compact
perturbation of the identity on both sides, up to finite rank, and the two defect spaces of
`T + C` are then squeezed between those of `S ∘ (T + C)` and `(T + C) ∘ S`. -/
theorem _root_.ContinuousLinearMap.IsFredholm.add_of_isCompactOperator
    (hT : ContinuousLinearMap.IsFredholm T) (hC : IsCompactOperator C) :
    ContinuousLinearMap.IsFredholm (T + C) := by
  obtain ⟨S, hS⟩ := hT.exists_isQuasiInverse
  -- `S ∘ T` and `T ∘ S` differ from the identity by an operator of finite rank.
  have hleft : LinearMap.HasFiniteRange ((S.comp T - 1 : E →L[𝕜] E) : E →ₗ[𝕜] E) := by
    simpa only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_comp,
      ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id] using
      LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mp hS.1
  have hright : LinearMap.HasFiniteRange ((T.comp S - 1 : F →L[𝕜] F) : F →ₗ[𝕜] F) := by
    simpa only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_comp,
      ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id] using
      LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mp hS.2
  have hcomp₁ : ContinuousLinearMap.IsFredholm (S.comp (T + C)) := by
    have hrw : S.comp (T + C) = (1 + S.comp C) + (S.comp T - 1) := by
      rw [ContinuousLinearMap.comp_add]
      abel
    rw [hrw]
    exact (isFredholm_one_add (hC.clm_comp S :)).add_hasFiniteRange hleft
  have hcomp₂ : ContinuousLinearMap.IsFredholm ((T + C).comp S) := by
    have hrw : (T + C).comp S = (1 + C.comp S) + (T.comp S - 1) := by
      rw [ContinuousLinearMap.add_comp]
      abel
    rw [hrw]
    exact (isFredholm_one_add (hC.comp_clm S :)).add_hasFiniteRange hright
  refine ContinuousLinearMap.IsFredholm.of_finite_ker_coker _ ?_ ?_
  · -- The kernel of `T + C` sits inside that of `S ∘ (T + C)`.
    have hker : LinearMap.ker ((T + C : E →L[𝕜] F) : E →ₗ[𝕜] F)
        ≤ LinearMap.ker ((S.comp (T + C) : E →L[𝕜] E) : E →ₗ[𝕜] E) := by
      intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      simpa only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, map_zero] using
        congrArg S hx
    have := ((isFredholm_iff_finite_ker_coker _).mp hcomp₁).1
    exact Submodule.finiteDimensional_of_le hker
  · -- The range of `T + C` contains that of `(T + C) ∘ S`.
    have hrange : LinearMap.range (((T + C).comp S : F →L[𝕜] F) : F →ₗ[𝕜] F)
        ≤ LinearMap.range ((T + C : E →L[𝕜] F) : E →ₗ[𝕜] F) := by
      rintro y ⟨z, rfl⟩
      exact ⟨S z, rfl⟩
    have := ((isFredholm_iff_finite_ker_coker _).mp hcomp₂).2
    exact FiniteDimensional.of_surjective (Submodule.factor hrange)
      (Submodule.factor_surjective hrange)

namespace ContinuousLinearMap

/-- A compact perturbation leaves the Fredholm index unchanged.

The scalar family `c ↦ T + c • C` is a continuous family of Fredholm operators over the
preconnected parameter space `𝕜`, so its index is constant; comparing `c = 0` with `c = 1` gives
the claim. -/
theorem index_add_of_isCompactOperator (hT : ContinuousLinearMap.IsFredholm T)
    (hC : IsCompactOperator C) : index (T + C) = index T := by
  let _i := IsRCLikeNormedField.rclike 𝕜
  have hpre : PreconnectedSpace 𝕜 :=
    ⟨(convex_univ : Convex ℝ (Set.univ : Set 𝕜)).isPreconnected⟩
  have hcont : Continuous fun c : 𝕜 => T + c • C := by fun_prop
  have hfred : ∀ c : 𝕜, ContinuousLinearMap.IsFredholm (T + c • C) := fun c =>
    hT.add_of_isCompactOperator (by simpa using hC.smul c)
  simpa using Continuous.index_eq_of_preconnectedSpace hcont hfred 1 0

/-- A compact perturbation of the identity has index `0`. -/
@[simp]
theorem index_one_sub_eq_zero {K : E →L[𝕜] E} (hK : IsCompactOperator K) :
    index (1 - K : E →L[𝕜] E) = 0 := by
  have hneg : IsCompactOperator (-K : E →L[𝕜] E) := by
    simpa only [FunLike.coe_neg] using hK.neg
  have hrw : (1 - K : E →L[𝕜] E) = ContinuousLinearMap.id 𝕜 E + (-K) := by
    ext x
    simp [sub_eq_add_neg]
  rw [hrw, index_add_of_isCompactOperator .id hneg, index_id]

/-- A compact perturbation of the identity has index `0`, in additive form. -/
@[simp]
theorem index_one_add_eq_zero {K : E →L[𝕜] E} (hK : IsCompactOperator K) :
    index (1 + K : E →L[𝕜] E) = 0 := by
  have hrw : (1 + K : E →L[𝕜] E) = ContinuousLinearMap.id 𝕜 E + K := rfl
  rw [hrw, index_add_of_isCompactOperator .id hK, index_id]

end ContinuousLinearMap

end TauCeti

end
