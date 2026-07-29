/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Fredholm.Comp
public import TauCeti.Analysis.Fredholm.Criteria
public import TauCeti.Analysis.Fredholm.Splitting

/-!
# Parametrices, Atkinson's theorem, and finite-rank perturbations

This file builds the **parametrix** of a Fredholm operator: an operator `S : F →L[𝕜] E` inverting
`T : E →L[𝕜] F` up to finite-rank error terms,

`S ∘ T = 1 - P`,   `T ∘ S = 1 - Q`,

with `P` the projection onto `ker T` and `Q` the projection onto the chosen cokernel
representative. Conversely, an operator admitting such one-sided inverses is Fredholm. Together
these give **Atkinson's theorem**: between Banach spaces, a continuous linear map is Fredholm
exactly when it is invertible modulo finite-rank operators.

The intended payoff, and the last of the three stability statements that Lane F0 of the analytic
Heegaard Floer roadmap asks for alongside small perturbations and the kernel/cokernel splitting,
is perturbation stability: if `T` is Fredholm and `K` has finite-dimensional range, then `T + K`
is Fredholm with the *same index*. Fredholmness follows from Atkinson's criterion, because a
parametrix for `T` is still a parametrix for `T + K` after absorbing `S ∘ K` and `K ∘ S` into the
error terms. The index statement is a restriction argument rather than a homotopy: `T` and `T + K`
agree on the closed, finite-codimensional subspace `ker K`, so composing both with its inclusion
— itself Fredholm, by `TauCeti.isFredholm_ker_subtypeL` — and cancelling that common index shift
through additivity of the index gives `index (T + K) = index T`.

## Main declarations

* `TauCeti.IsFredholm.parametrix`: the parametrix of a Fredholm operator.
* `TauCeti.IsFredholm.parametrix_comp_self` and `TauCeti.IsFredholm.self_comp_parametrix`: the two
  parametrix identities, with their finite-rank error terms
  `TauCeti.IsFredholm.kerProjection` and `TauCeti.IsFredholm.cokerProjection`.
* `TauCeti.IsFredholm.ker_kerProjection`, `TauCeti.IsFredholm.range_kerProjection` and their
  cokernel counterparts, together with the action of the two error terms on the complementary
  subspaces they project onto and along, and their idempotence.
* `TauCeti.IsFredholm.self_comp_parametrix_comp_self` and
  `TauCeti.IsFredholm.parametrix_comp_self_comp_parametrix`: a parametrix is a generalized inverse,
  `T ∘ S ∘ T = T` and `S ∘ T ∘ S = S`.
* `TauCeti.IsFredholm.exists_parametrix`: the existential form of the two identities.
* `TauCeti.IsFredholm.of_parametrix`: **Atkinson's criterion**, that an operator invertible on both
  sides modulo finite-rank errors is Fredholm.
* `TauCeti.isFredholm_iff_exists_parametrix`: **Atkinson's theorem** as an equivalence.
* `TauCeti.IsFredholm.isFredholm_parametrix` and
  `TauCeti.ContinuousLinearMap.index_parametrix`: a parametrix is itself Fredholm, of the opposite
  index.
* `TauCeti.IsFredholm.add_of_finiteDimensional_range` and
  `TauCeti.ContinuousLinearMap.index_add_of_finiteDimensional_range`: Fredholmness and the index
  are stable under perturbation by an operator of finite rank.

The parametrix construction and the index conventions follow McDuff--Salamon, *J-holomorphic
Curves and Symplectic Topology*, Appendix A.1; Atkinson's theorem in the finite-rank form proved
here is the elementary half of the classical statement modulo compact operators (Atkinson, 1951).
The splittings it is built from are those of `TauCeti.Analysis.Fredholm.Splitting`, and the
projections and topological complements are Mathlib's `Submodule.projectionL` and
`Submodule.IsTopCompl`; no implementation is vendored.
-/

public section

namespace TauCeti

open Module

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-! ### Atkinson's criterion

An operator that is invertible on one side modulo a finite-rank error has a finite-dimensional
kernel; on the other side, a finite-dimensional cokernel. Neither statement needs completeness or
the scalar field to be `ℝ` or `ℂ`; assembling them into the Fredholm predicate does, through
`TauCeti.IsFredholm.of_finiteDimensional_ker_coker`. -/

variable {T : E →L[𝕜] F} {S : F →L[𝕜] E}

omit [IsRCLikeNormedField 𝕜] [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- A left inverse modulo a finite-rank error forces a finite-dimensional kernel: on `ker T` the
identity agrees with the error term, so `ker T` sits inside its range. -/
theorem finiteDimensional_ker_of_comp_eq_id_sub {P : E →L[𝕜] E}
    (hP : FiniteDimensional 𝕜 (LinearMap.range (P : E →ₗ[𝕜] E)))
    (h : S.comp T = ContinuousLinearMap.id 𝕜 E - P) :
    FiniteDimensional 𝕜 (LinearMap.ker (T : E →ₗ[𝕜] F)) := by
  haveI := hP
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (P : E →ₗ[𝕜] E)) ?_
  intro x hx
  have hTx : T x = 0 := by simpa using hx
  have hx' : (0 : E) = x - P x := by
    have := ContinuousLinearMap.ext_iff.mp h x
    simpa [hTx] using this
  exact ⟨x, by simpa using (sub_eq_zero.mp hx'.symm).symm⟩

omit [IsRCLikeNormedField 𝕜] [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- A right inverse modulo a finite-rank error forces a finite-dimensional cokernel: every vector
differs from its error term by an element of `range T`, so the finite-dimensional `range Q`
already surjects onto `F ⧸ range T`. -/
theorem finiteDimensional_coker_of_comp_eq_id_sub {Q : F →L[𝕜] F}
    (hQ : FiniteDimensional 𝕜 (LinearMap.range (Q : F →ₗ[𝕜] F)))
    (h : T.comp S = ContinuousLinearMap.id 𝕜 F - Q) :
    FiniteDimensional 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) := by
  haveI := hQ
  have key : ∀ y : F, y - Q y ∈ LinearMap.range (T : E →ₗ[𝕜] F) := by
    intro y
    refine ⟨S y, ?_⟩
    have := ContinuousLinearMap.ext_iff.mp h y
    simpa using this
  refine Module.Finite.of_surjective
    ((LinearMap.range (T : E →ₗ[𝕜] F)).mkQ.comp
      (LinearMap.range (Q : F →ₗ[𝕜] F)).subtype) ?_
  intro z
  obtain ⟨y, rfl⟩ := (LinearMap.range (T : E →ₗ[𝕜] F)).mkQ_surjective z
  refine ⟨⟨Q y, LinearMap.mem_range_self _ y⟩, ?_⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq]
  simpa using neg_mem (key y)

omit [IsRCLikeNormedField 𝕜] in
/-- **Atkinson's criterion.** An operator between Banach spaces that has a left inverse modulo a
finite-rank error and a right inverse modulo a finite-rank error is Fredholm. The two one-sided
inverses need not agree. -/
theorem IsFredholm.of_parametrix {S₁ S₂ : F →L[𝕜] E} {P : E →L[𝕜] E} {Q : F →L[𝕜] F}
    (hP : FiniteDimensional 𝕜 (LinearMap.range (P : E →ₗ[𝕜] E)))
    (hQ : FiniteDimensional 𝕜 (LinearMap.range (Q : F →ₗ[𝕜] F)))
    (h₁ : S₁.comp T = ContinuousLinearMap.id 𝕜 E - P)
    (h₂ : T.comp S₂ = ContinuousLinearMap.id 𝕜 F - Q) :
    IsFredholm T :=
  .of_finiteDimensional_ker_coker T (finiteDimensional_ker_of_comp_eq_id_sub hP h₁)
    (finiteDimensional_coker_of_comp_eq_id_sub hQ h₂)

/-! ### The parametrix of a Fredholm operator -/

namespace IsFredholm

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The projection of the domain onto `ker T` along the chosen kernel complement
`TauCeti.IsFredholm.kerComplement`. It is the finite-rank error term of
`TauCeti.IsFredholm.parametrix_comp_self`, named because the unfolded projection is unreadable at
the point of use. -/
noncomputable def kerProjection (hT : _root_.TauCeti.IsFredholm T) : E →L[𝕜] E :=
  (LinearMap.ker (T : E →ₗ[𝕜] F)).projectionL hT.kerComplement
    hT.isTopCompl_ker_kerComplement

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The projection of the codomain onto the chosen cokernel representative
`TauCeti.IsFredholm.cokerComplement` along `range T`. It is the finite-rank error term of
`TauCeti.IsFredholm.self_comp_parametrix`. -/
noncomputable def cokerProjection (hT : _root_.TauCeti.IsFredholm T) : F →L[𝕜] F :=
  hT.cokerComplement.projectionL (LinearMap.range (T : E →ₗ[𝕜] F))
    hT.isTopCompl_range_cokerComplement.symm

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The kernel of the first error term is the chosen kernel complement: it is the subspace
`TauCeti.IsFredholm.kerProjection` projects along. -/
theorem ker_kerProjection (hT : _root_.TauCeti.IsFredholm T) :
    LinearMap.ker (hT.kerProjection : E →ₗ[𝕜] E) = hT.kerComplement :=
  Submodule.ker_projectionL hT.isTopCompl_ker_kerComplement

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The kernel of the second error term is `range T`: it is the subspace
`TauCeti.IsFredholm.cokerProjection` projects along. -/
theorem ker_cokerProjection (hT : _root_.TauCeti.IsFredholm T) :
    LinearMap.ker (hT.cokerProjection : F →ₗ[𝕜] F) = LinearMap.range (T : E →ₗ[𝕜] F) :=
  Submodule.ker_projectionL hT.isTopCompl_range_cokerComplement.symm

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The first error term is the identity on `ker T`. -/
theorem kerProjection_apply_of_mem_ker (hT : _root_.TauCeti.IsFredholm T) {x : E}
    (hx : x ∈ LinearMap.ker (T : E →ₗ[𝕜] F)) : hT.kerProjection x = x :=
  Submodule.projectionL_apply_left hT.isTopCompl_ker_kerComplement ⟨x, hx⟩

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The first error term vanishes on the chosen kernel complement. -/
theorem kerProjection_apply_eq_zero_of_mem_kerComplement (hT : _root_.TauCeti.IsFredholm T)
    {x : E} (hx : x ∈ hT.kerComplement) : hT.kerProjection x = 0 :=
  Submodule.projectionL_apply_eq_zero_of_mem_right _ hx

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The first error term takes values in `ker T`. -/
theorem kerProjection_apply_mem_ker (hT : _root_.TauCeti.IsFredholm T) (x : E) :
    hT.kerProjection x ∈ LinearMap.ker (T : E →ₗ[𝕜] F) :=
  Submodule.projectionL_apply_mem _ x

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- `T` annihilates the first error term, which projects onto `ker T`. -/
@[simp]
theorem apply_kerProjection (hT : _root_.TauCeti.IsFredholm T) (x : E) :
    T (hT.kerProjection x) = 0 :=
  LinearMap.mem_ker.mp (hT.kerProjection_apply_mem_ker x)

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The second error term is the identity on the chosen cokernel representative. -/
theorem cokerProjection_apply_of_mem_cokerComplement (hT : _root_.TauCeti.IsFredholm T) {y : F}
    (hy : y ∈ hT.cokerComplement) : hT.cokerProjection y = y :=
  Submodule.projectionL_apply_left hT.isTopCompl_range_cokerComplement.symm ⟨y, hy⟩

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The second error term vanishes on `range T`. -/
theorem cokerProjection_apply_eq_zero_of_mem_range (hT : _root_.TauCeti.IsFredholm T) {y : F}
    (hy : y ∈ LinearMap.range (T : E →ₗ[𝕜] F)) : hT.cokerProjection y = 0 :=
  Submodule.projectionL_apply_eq_zero_of_mem_right _ hy

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The second error term annihilates every value of `T`. -/
@[simp]
theorem cokerProjection_apply_apply (hT : _root_.TauCeti.IsFredholm T) (x : E) :
    hT.cokerProjection (T x) = 0 :=
  hT.cokerProjection_apply_eq_zero_of_mem_range ⟨x, rfl⟩

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The first error term is idempotent: it is a projection. -/
@[simp]
theorem isIdempotentElem_kerProjection (hT : _root_.TauCeti.IsFredholm T) :
    IsIdempotentElem hT.kerProjection :=
  Submodule.isIdempotentElem_projectionL _

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The second error term is idempotent: it is a projection. -/
@[simp]
theorem isIdempotentElem_cokerProjection (hT : _root_.TauCeti.IsFredholm T) :
    IsIdempotentElem hT.cokerProjection :=
  Submodule.isIdempotentElem_projectionL _

/-- A **parametrix** for a Fredholm operator: project the codomain onto `range T`, invert `T`
there against the chosen kernel complement, and include the result back into the domain. -/
noncomputable def parametrix (hT : _root_.TauCeti.IsFredholm T) : F →L[𝕜] E :=
  hT.kerComplement.subtypeL.comp
    ((hT.kerComplementEquivRange.symm :
        LinearMap.range (T : E →ₗ[𝕜] F) →L[𝕜] hT.kerComplement).comp
      ((LinearMap.range (T : E →ₗ[𝕜] F)).projectionOntoL hT.cokerComplement
        hT.isTopCompl_range_cokerComplement))

/-- The parametrix, unfolded: invert `T` on the `range T` component of the argument. Internal
bridge to the definition; the public API is the pair of parametrix identities. -/
private theorem parametrix_apply (hT : _root_.TauCeti.IsFredholm T) (y : F) :
    hT.parametrix y =
      (hT.kerComplementEquivRange.symm
        ((LinearMap.range (T : E →ₗ[𝕜] F)).projectionOntoL hT.cokerComplement
          hT.isTopCompl_range_cokerComplement y) : E) :=
  rfl

/-- Applying `T` to a parametrix recovers the argument up to its cokernel component: the
pointwise form of `TauCeti.IsFredholm.self_comp_parametrix`. -/
@[simp]
theorem apply_parametrix (hT : _root_.TauCeti.IsFredholm T) (y : F) :
    T (hT.parametrix y) = y - hT.cokerProjection y := by
  have h0 : T (hT.parametrix y) =
      (LinearMap.range (T : E →ₗ[𝕜] F)).projectionL hT.cokerComplement
        hT.isTopCompl_range_cokerComplement y := by
    rw [parametrix_apply]
    have h := hT.kerComplementEquivRange_apply
      (hT.kerComplementEquivRange.symm
        ((LinearMap.range (T : E →ₗ[𝕜] F)).projectionOntoL hT.cokerComplement
          hT.isTopCompl_range_cokerComplement y))
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    rw [← h]
    exact Submodule.coe_projectionOntoL_apply hT.isTopCompl_range_cokerComplement y
  rw [h0, cokerProjection, eq_sub_iff_add_eq]
  exact Submodule.projectionL_add_projectionL_eq_self hT.isTopCompl_range_cokerComplement y

/-- A parametrix recovers the argument of `T` up to its kernel component: the pointwise form of
`TauCeti.IsFredholm.parametrix_comp_self`. -/
@[simp]
theorem parametrix_apply_apply (hT : _root_.TauCeti.IsFredholm T) (x : E) :
    hT.parametrix (T x) = x - hT.kerProjection x := by
  have hmem : T x ∈ LinearMap.range (T : E →ₗ[𝕜] F) := ⟨x, rfl⟩
  -- The codomain projection fixes `T x`, which already lies in `range T`.
  have h1 : (LinearMap.range (T : E →ₗ[𝕜] F)).projectionOntoL hT.cokerComplement
      hT.isTopCompl_range_cokerComplement (T x) = ⟨T x, hmem⟩ :=
    Submodule.projectionOntoL_apply_left _ ⟨T x, hmem⟩
  -- `T` sends the kernel-complement component of `x` to `T x`.
  have hc : ((hT.kerComplement.projectionOntoL (LinearMap.ker (T : E →ₗ[𝕜] F))
      hT.isTopCompl_ker_kerComplement.symm x : E)) = x - hT.kerProjection x :=
    Submodule.projectionL_eq_self_sub_projectionL hT.isTopCompl_ker_kerComplement x
  have h2 : hT.kerComplementEquivRange (hT.kerComplement.projectionOntoL
      (LinearMap.ker (T : E →ₗ[𝕜] F)) hT.isTopCompl_ker_kerComplement.symm x) =
      ⟨T x, hmem⟩ := by
    refine Subtype.ext ?_
    rw [hT.kerComplementEquivRange_apply, hc, map_sub, hT.apply_kerProjection, sub_zero]
  rw [parametrix_apply, h1, ← h2, ContinuousLinearEquiv.symm_apply_apply]
  exact hc

/-- The first parametrix identity: `S ∘ T` is the identity minus the projection onto `ker T`. -/
theorem parametrix_comp_self (hT : _root_.TauCeti.IsFredholm T) :
    hT.parametrix.comp T = ContinuousLinearMap.id 𝕜 E - hT.kerProjection := by
  ext x
  simp

/-- The second parametrix identity: `T ∘ S` is the identity minus the projection onto the chosen
cokernel representative. -/
theorem self_comp_parametrix (hT : _root_.TauCeti.IsFredholm T) :
    T.comp hT.parametrix = ContinuousLinearMap.id 𝕜 F - hT.cokerProjection := by
  ext y
  simp

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The error term of the first parametrix identity has range `ker T`. -/
theorem range_kerProjection (hT : _root_.TauCeti.IsFredholm T) :
    LinearMap.range (hT.kerProjection : E →ₗ[𝕜] E) = LinearMap.ker (T : E →ₗ[𝕜] F) :=
  Submodule.range_projectionL hT.isTopCompl_ker_kerComplement

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The error term of the second parametrix identity has range the chosen cokernel
representative. -/
theorem range_cokerProjection (hT : _root_.TauCeti.IsFredholm T) :
    LinearMap.range (hT.cokerProjection : F →ₗ[𝕜] F) = hT.cokerComplement :=
  Submodule.range_projectionL hT.isTopCompl_range_cokerComplement.symm

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The error term of the first parametrix identity has finite rank. -/
theorem finiteDimensional_range_kerProjection (hT : _root_.TauCeti.IsFredholm T) :
    FiniteDimensional 𝕜 (LinearMap.range (hT.kerProjection : E →ₗ[𝕜] E)) := by
  rw [hT.range_kerProjection]
  exact hT.finiteDimensional_ker

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The error term of the second parametrix identity has finite rank. -/
theorem finiteDimensional_range_cokerProjection (hT : _root_.TauCeti.IsFredholm T) :
    FiniteDimensional 𝕜 (LinearMap.range (hT.cokerProjection : F →ₗ[𝕜] F)) := by
  rw [hT.range_cokerProjection]
  infer_instance

/-- A Fredholm operator is invertible modulo finite-rank operators: the existential form of the
two parametrix identities, and the direction of Atkinson's theorem that consumes the
kernel/cokernel splittings. -/
theorem exists_parametrix (hT : _root_.TauCeti.IsFredholm T) :
    ∃ (S : F →L[𝕜] E) (P : E →L[𝕜] E) (Q : F →L[𝕜] F),
      FiniteDimensional 𝕜 (LinearMap.range (P : E →ₗ[𝕜] E)) ∧
        FiniteDimensional 𝕜 (LinearMap.range (Q : F →ₗ[𝕜] F)) ∧
          S.comp T = ContinuousLinearMap.id 𝕜 E - P ∧
            T.comp S = ContinuousLinearMap.id 𝕜 F - Q :=
  ⟨hT.parametrix, hT.kerProjection, hT.cokerProjection,
    hT.finiteDimensional_range_kerProjection, hT.finiteDimensional_range_cokerProjection,
    hT.parametrix_comp_self, hT.self_comp_parametrix⟩

end IsFredholm

/-- **Atkinson's theorem.** Between Banach spaces, a continuous linear map is Fredholm exactly
when it is invertible modulo finite-rank operators. -/
theorem isFredholm_iff_exists_parametrix (T : E →L[𝕜] F) :
    IsFredholm T ↔
      ∃ (S : F →L[𝕜] E) (P : E →L[𝕜] E) (Q : F →L[𝕜] F),
        FiniteDimensional 𝕜 (LinearMap.range (P : E →ₗ[𝕜] E)) ∧
          FiniteDimensional 𝕜 (LinearMap.range (Q : F →ₗ[𝕜] F)) ∧
            S.comp T = ContinuousLinearMap.id 𝕜 E - P ∧
              T.comp S = ContinuousLinearMap.id 𝕜 F - Q :=
  ⟨fun hT => hT.exists_parametrix, fun ⟨_, _, _, hP, hQ, h₁, h₂⟩ =>
    .of_parametrix hP hQ h₁ h₂⟩

/-! ### The parametrix as a Fredholm operator -/

namespace IsFredholm

/-- The kernel of the parametrix is the chosen cokernel representative: the parametrix kills
exactly the part of the codomain that `T` misses. -/
theorem ker_parametrix (hT : _root_.TauCeti.IsFredholm T) :
    LinearMap.ker (hT.parametrix : F →ₗ[𝕜] E) = hT.cokerComplement := by
  ext y
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, parametrix_apply,
    Submodule.coe_eq_zero, ContinuousLinearEquiv.map_eq_zero_iff,
    Submodule.projectionOntoL_apply_eq_zero_iff]

/-- The range of the parametrix is the chosen kernel complement: the parametrix is a genuine
inverse between `range T` and that complement. -/
theorem range_parametrix (hT : _root_.TauCeti.IsFredholm T) :
    LinearMap.range (hT.parametrix : F →ₗ[𝕜] E) = hT.kerComplement := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, rfl⟩
    exact SetLike.coe_mem _
  · intro x hx
    refine ⟨T x, ?_⟩
    have hx0 : hT.kerProjection x = 0 :=
      hT.kerProjection_apply_eq_zero_of_mem_kerComplement hx
    have h := hT.parametrix_apply_apply x
    rw [hx0, sub_zero] at h
    exact h

/-- A parametrix is a generalized inverse of `T`: the two error terms cancel in
`T ∘ S ∘ T`, which is `T` again. -/
theorem self_comp_parametrix_comp_self (hT : _root_.TauCeti.IsFredholm T) :
    T.comp (hT.parametrix.comp T) = T := by
  ext x
  simp

/-- A parametrix is a generalized inverse of `T`: the two error terms cancel in
`S ∘ T ∘ S`, which is `S` again. -/
theorem parametrix_comp_self_comp_parametrix (hT : _root_.TauCeti.IsFredholm T) :
    hT.parametrix.comp (T.comp hT.parametrix) = hT.parametrix := by
  ext y
  have hmem : hT.parametrix y ∈ hT.kerComplement := by
    rw [← hT.range_parametrix]
    exact LinearMap.mem_range_self _ y
  have hx0 : hT.kerProjection (hT.parametrix y) = 0 :=
    hT.kerProjection_apply_eq_zero_of_mem_kerComplement hmem
  simpa [hx0] using hT.parametrix_apply_apply (hT.parametrix y)

/-- The parametrix of a Fredholm operator is itself Fredholm: its kernel is the
finite-dimensional cokernel representative and its range is the closed kernel complement, whose
quotient is the finite-dimensional `ker T`. -/
theorem isFredholm_parametrix (hT : _root_.TauCeti.IsFredholm T) :
    _root_.TauCeti.IsFredholm hT.parametrix := by
  haveI := hT.finiteDimensional_ker
  refine ⟨?_, ?_, ?_⟩
  · rw [hT.ker_parametrix]
    infer_instance
  · rw [hT.range_parametrix]
    exact hT.isClosed_kerComplement
  · rw [hT.range_parametrix]
    exact (Submodule.quotientEquivOfIsTopCompl hT.kerComplement
      (LinearMap.ker (T : E →ₗ[𝕜] F))
      hT.isTopCompl_ker_kerComplement.symm).symm.toLinearEquiv.finiteDimensional

end IsFredholm

namespace ContinuousLinearMap

/-- The parametrix of a Fredholm operator has the opposite index: it exchanges the roles of the
kernel and the cokernel. -/
theorem index_parametrix (hT : IsFredholm T) : index hT.parametrix = -index T := by
  haveI := hT.finiteDimensional_ker
  haveI := hT.finiteDimensional_coker
  rw [index_eq_finrank_sub, index_eq_finrank_sub, hT.ker_parametrix, hT.range_parametrix,
    ← LinearEquiv.finrank_eq hT.cokerEquivComplement.toLinearEquiv,
    LinearEquiv.finrank_eq (Submodule.quotientEquivOfIsTopCompl hT.kerComplement
      (LinearMap.ker (T : E →ₗ[𝕜] F))
      hT.isTopCompl_ker_kerComplement.symm).toLinearEquiv]
  omega

end ContinuousLinearMap

/-! ### Perturbation by an operator of finite rank -/

section FiniteRank

variable {K : E →L[𝕜] F}

/-- Perturbing a Fredholm operator by an operator of finite rank leaves it Fredholm: a parametrix
`S` for `T` remains one for `T + K` once `S ∘ K` and `K ∘ S`, both of finite rank, are absorbed
into the two error terms. -/
theorem IsFredholm.add_of_finiteDimensional_range (hT : IsFredholm T)
    (hK : FiniteDimensional 𝕜 (LinearMap.range (K : E →ₗ[𝕜] F))) :
    IsFredholm (T + K) := by
  haveI := hK
  haveI := hT.finiteDimensional_range_kerProjection
  haveI := hT.finiteDimensional_range_cokerProjection
  set S := hT.parametrix with hS
  haveI : FiniteDimensional 𝕜 (LinearMap.range ((S.comp K : E →L[𝕜] E) : E →ₗ[𝕜] E)) := by
    rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp]
    infer_instance
  haveI : FiniteDimensional 𝕜 (LinearMap.range ((K.comp S : F →L[𝕜] F) : F →ₗ[𝕜] F)) := by
    rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp]
    exact Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (K : E →ₗ[𝕜] F))
      LinearMap.map_le_range
  refine IsFredholm.of_parametrix (S₁ := S) (S₂ := S)
    (P := hT.kerProjection - S.comp K) (Q := hT.cokerProjection - K.comp S) ?_ ?_ ?_ ?_
  · -- `range (P - S ∘ K) ≤ range P ⊔ range (S ∘ K)`, a sum of finite-dimensional subspaces.
    refine Submodule.finiteDimensional_of_le
      (S₂ := LinearMap.range (hT.kerProjection : E →ₗ[𝕜] E) ⊔
        LinearMap.range ((S.comp K : E →L[𝕜] E) : E →ₗ[𝕜] E)) ?_
    rintro x ⟨z, rfl⟩
    exact Submodule.sub_mem _
      (Submodule.mem_sup_left (LinearMap.mem_range_self _ z))
      (Submodule.mem_sup_right (LinearMap.mem_range_self _ z))
  · refine Submodule.finiteDimensional_of_le
      (S₂ := LinearMap.range (hT.cokerProjection : F →ₗ[𝕜] F) ⊔
        LinearMap.range ((K.comp S : F →L[𝕜] F) : F →ₗ[𝕜] F)) ?_
    rintro y ⟨z, rfl⟩
    exact Submodule.sub_mem _
      (Submodule.mem_sup_left (LinearMap.mem_range_self _ z))
      (Submodule.mem_sup_right (LinearMap.mem_range_self _ z))
  · rw [ContinuousLinearMap.comp_add, hS, hT.parametrix_comp_self]
    abel
  · rw [ContinuousLinearMap.add_comp, hS, hT.self_comp_parametrix]
    abel

namespace ContinuousLinearMap

/-- Perturbing a Fredholm operator by an operator of finite rank leaves its index unchanged: both
operators restrict to the same map on the closed, finite-codimensional subspace `ker K`, and
additivity of the index cancels the index shift of that restriction. -/
theorem index_add_of_finiteDimensional_range (hT : IsFredholm T)
    (hK : FiniteDimensional 𝕜 (LinearMap.range (K : E →ₗ[𝕜] F))) :
    index (T + K) = index T := by
  haveI := hK
  set ι := (LinearMap.ker (K : E →ₗ[𝕜] F)).subtypeL with hι
  have hιF : IsFredholm ι := isFredholm_ker_subtypeL hK
  -- `T` and `T + K` agree on `ker K`.
  have hcomp : (T + K).comp ι = T.comp ι := by
    ext x
    have hx : K (x : E) = 0 := LinearMap.mem_ker.mp x.2
    simp [hι, hx]
  have h₁ := index_comp (T + K) ι (hT.add_of_finiteDimensional_range hK) hιF
  have h₂ := index_comp T ι hT hιF
  rw [hcomp, h₂] at h₁
  omega

end ContinuousLinearMap

end FiniteRank

end TauCeti

end
