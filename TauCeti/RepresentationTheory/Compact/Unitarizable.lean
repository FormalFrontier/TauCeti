/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Compact.Averaging
public import TauCeti.RepresentationTheory.Continuous.Unitary
public import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Weyl's unitarian trick

Averaging the inner product of a Hilbert space over a compact group turns it into a
`G`-invariant inner product. This file carries out that averaging for a continuous representation
`π` of a compact group, in the form the roadmap prescribes: rather than producing a second
`InnerProductSpace` structure on `V` — which would not make the given `π` unitary for the fixed
instance Lean already has — the averaged form is represented by its Gram operator

`gramOperator π hπ = ∫ g, (π g)† ∘ (π g) ∂(haarProb G)`,

a positive-definite self-adjoint operator satisfying `⟪v, S w⟫ = ∫ g, ⟪π g v, π g w⟫`. Invariance
of the averaged form is then the operator identity `(π g)† ∘ S ∘ (π g) = S`.

## Main definitions

* `TauCeti.ContRepresentation.gramOperator`: the Gram operator of the Haar-averaged inner product.

## Main statements

* `TauCeti.ContRepresentation.inner_gramOperator`: the defining property
  `⟪v, S w⟫ = ∫ g, ⟪π g v, π g w⟫`.
* `TauCeti.ContRepresentation.isSelfAdjoint_gramOperator` and
  `TauCeti.ContRepresentation.isPositive_gramOperator`: the Gram operator is self-adjoint and
  positive.
* `TauCeti.ContRepresentation.re_inner_gramOperator_self_pos`: it is positive *definite*; the
  proof goes through `TauCeti.ContRepresentation.exists_pos_mul_norm_le_norm_map`, which uses
  compactness of `G` to bound the operator norms `‖π g‖` uniformly, and is what makes the averaged
  form nondegenerate.
* `TauCeti.ContRepresentation.inner_gramOperator_map_map`: the averaged form is `G`-invariant,
  and `TauCeti.ContRepresentation.adjoint_comp_gramOperator_comp` is its operator form.
* `TauCeti.ContRepresentation.isUnitarizable`: the packaged unitarian trick, as pinned by the
  roadmap.
* `TauCeti.ContRepresentation.gramOperator_eq_one`: for an already unitary representation the
  averaging changes nothing.

This is Layer 1 of the [compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/roadmap/representation-theory/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md).
It is the compact-group replacement for the invertibility of `|G|` in Maschke's theorem. The
invariant-complement and complete-reducibility results of
`TauCeti.RepresentationTheory.Continuous.InvariantComplement` take `IsUnitary` as a hypothesis; this
file does not discharge that hypothesis, but the invariant form built here is the input a
unitarization construction needs.

The mathematical development follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open MeasureTheory RCLike
open scoped InnerProductSpace

namespace TauCeti

namespace ContRepresentation

section NormedField

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [Group G] [TopologicalSpace G]
  [CompactSpace G] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- The action operators of a continuous representation of a compact group are uniformly
bounded below: there is a `c > 0` with `c * ‖v‖ ≤ ‖π g v‖` for every `g` and `v`.

The bound comes from applying the inverse operator `π g⁻¹`, whose norm is bounded uniformly in `g`
because `G` is compact and `π` is continuous. Only the normed-space structure is involved, so this
is stated before the inner product enters. -/
theorem exists_pos_mul_norm_le_norm_map (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    ∃ c : ℝ, 0 < c ∧ ∀ (g : G) (v : V), c * ‖v‖ ≤ ‖π g v‖ := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn (f := fun g : G ↦ π g)
    hπ.continuousOn
  set M' := max M 1
  have hM'pos : 0 < M' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨M'⁻¹, inv_pos.mpr hM'pos, fun g v ↦ ?_⟩
  have hcancel : π g⁻¹ (π g v) = v := Representation.inv_self_apply π.toRepresentation g v
  have hstep : ‖v‖ ≤ M' * ‖π g v‖ :=
    calc ‖v‖ = ‖π g⁻¹ (π g v)‖ := by rw [hcancel]
      _ ≤ ‖π g⁻¹‖ * ‖π g v‖ := (π g⁻¹).le_opNorm _
      _ ≤ M' * ‖π g v‖ :=
        mul_le_mul_of_nonneg_right ((hM g⁻¹ (Set.mem_univ _)).trans (le_max_left _ _))
          (norm_nonneg _)
  rw [inv_mul_le_iff₀ hM'pos]
  exact hstep

end NormedField

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

include hπ

/-- The family `g ↦ (π g)† ∘ (π g)` of positive operators, as a continuous map on the group.

This is the integrand of the unitarian trick: its value at `g` is the Gram operator of the
pulled-back form `(v, w) ↦ ⟪π g v, π g w⟫`. -/
private noncomputable def gramFamily : C(G, V →L[𝕜] V) where
  toFun g := (ContinuousLinearMap.adjoint (π g)).comp (π g)
  continuous_toFun :=
    (ContinuousLinearMap.compL 𝕜 V V V).continuous₂.comp
      (((ContinuousLinearMap.adjoint (𝕜 := 𝕜) (E := V) (F := V)).continuous.comp hπ).prodMk hπ)

/-- The Gram operator of the Haar-averaged inner product
`⟪v, w⟫_G = ∫ g, ⟪π g v, π g w⟫ ∂(haarProb G)` of a continuous representation of a compact group.

The averaged form is recorded through this operator rather than as a second
`InnerProductSpace` structure: Lean fixes one inner product on `V`, and it is the operator identity
`(π g)† ∘ gramOperator π hπ ∘ (π g) = gramOperator π hπ` that expresses `G`-invariance of the
averaged form. -/
noncomputable def gramOperator : V →L[𝕜] V :=
  haarAverage G (𝕜 := 𝕜) (gramFamily π hπ)

/-- The defining property of the Gram operator: it represents the Haar-averaged inner product. -/
theorem inner_gramOperator (v w : V) :
    ⟪v, gramOperator π hπ w⟫_𝕜 = ∫ g, ⟪π g v, π g w⟫_𝕜 ∂haarProb G := by
  have h := ((innerSL 𝕜 v).comp (ContinuousLinearMap.apply 𝕜 V w)).haarAverage_comp_comm
    (G := G) (gramFamily π hπ)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at h
  rw [gramOperator, ← innerSL_apply_apply, ← h, haarAverage_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  simp [gramFamily, innerSL_apply_apply, ContinuousLinearMap.adjoint_inner_right]

/-- The Gram operator represents the Haar-averaged inner product, written on the left. -/
theorem inner_gramOperator_left (v w : V) :
    ⟪gramOperator π hπ v, w⟫_𝕜 = ∫ g, ⟪π g v, π g w⟫_𝕜 ∂haarProb G := by
  rw [← inner_conj_symm, inner_gramOperator, ← integral_conj]
  exact integral_congr_ae (Filter.Eventually.of_forall fun g ↦ inner_conj_symm _ _)

/-- The averaged form is Hermitian: the Gram operator is symmetric. -/
theorem isSymmetric_gramOperator : (gramOperator π hπ : V →ₗ[𝕜] V).IsSymmetric := fun v w ↦ by
  simp only [ContinuousLinearMap.coe_coe]
  rw [inner_gramOperator_left, inner_gramOperator]

/-- The Gram operator of the averaged form is self-adjoint. -/
theorem isSelfAdjoint_gramOperator : IsSelfAdjoint (gramOperator π hπ) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (isSymmetric_gramOperator π hπ)

/-! ### Positive definiteness

Nondegeneracy of the averaged form is where compactness of `G` enters a second time: the operator
norms `‖π g‖` are uniformly bounded, so `‖π g v‖` is bounded *below* by a positive multiple of
`‖v‖`, and the average of `‖π g v‖ ^ 2` cannot collapse to zero. -/

omit [CompleteSpace V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] in
/-- Integrability of `g ↦ ‖π g v‖ ^ 2`: the integrand is continuous on a compact group carrying a
measure that is finite on compact sets. -/
private theorem integrable_norm_sq (v : V) :
    Integrable (fun g ↦ ‖π g v‖ ^ 2) (haarProb G) :=
  ((continuous_norm.comp (hπ.clm_apply continuous_const)).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The averaged form evaluated on the diagonal is the average of `‖π g v‖ ^ 2`. -/
theorem inner_gramOperator_self (v : V) :
    ⟪gramOperator π hπ v, v⟫_𝕜 = ((∫ g, ‖π g v‖ ^ 2 ∂haarProb G : ℝ) : 𝕜) := by
  rw [inner_gramOperator_left, ← integral_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  simp [inner_self_eq_norm_sq_to_K]

/-- The Gram operator of the averaged form is a positive operator. -/
theorem isPositive_gramOperator : (gramOperator π hπ).IsPositive := by
  refine ⟨isSymmetric_gramOperator π hπ, fun v ↦ ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_gramOperator_self, ofReal_re]
  exact integral_nonneg fun g ↦ by positivity

/-- **Positive definiteness of the averaged form.** For a nonzero vector the averaged norm square
is strictly positive; this is what makes `⟪v, w⟫_G = ⟪gramOperator π hπ v, w⟫` an inner product
rather than merely a positive semidefinite form. -/
theorem re_inner_gramOperator_self_pos {v : V} (hv : v ≠ 0) :
    0 < re ⟪gramOperator π hπ v, v⟫_𝕜 := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_mul_norm_le_norm_map π hπ
  rw [inner_gramOperator_self, ofReal_re]
  have hconst : (c * ‖v‖) ^ 2 ≤ ∫ g, ‖π g v‖ ^ 2 ∂haarProb G := by
    have h := integral_mono (integrable_const ((c * ‖v‖) ^ 2)) (integrable_norm_sq π hπ v)
      fun g ↦ by
        have := hbound g v
        nlinarith [mul_nonneg hc.le (norm_nonneg v), norm_nonneg (π g v)]
    simpa using h
  have hpos : 0 < (c * ‖v‖) ^ 2 := by
    have : 0 < ‖v‖ := norm_pos_iff.mpr hv
    positivity
  exact lt_of_lt_of_le hpos hconst

/-- The averaged form is nondegenerate, so the Gram operator is injective. -/
theorem gramOperator_injective : Function.Injective (gramOperator π hπ) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  by_contra hne
  have := re_inner_gramOperator_self_pos π hπ hne
  rw [hv, inner_zero_left, map_zero] at this
  exact lt_irrefl 0 this

/-! ### Invariance -/

omit hπ [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [NormedSpace ℝ V]
  [SMulCommClass ℝ 𝕜 V] in
/-- Conjugation `S ↦ (π g)† ∘ S ∘ (π g)` by an action operator, packaged as a continuous linear
map on operators.

Bundling it this way is what lets it commute with Haar averaging, via
`ContinuousLinearMap.haarAverage_comp_comm`. -/
private noncomputable def conjAction (g : G) : (V →L[𝕜] V) →L[𝕜] V →L[𝕜] V :=
  (ContinuousLinearMap.compL 𝕜 V V V (ContinuousLinearMap.adjoint (π g))).comp
    ((ContinuousLinearMap.compL 𝕜 V V V).flip (π g))

omit hπ [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] in
/-- `conjAction` is conjugation, unfolded. -/
private theorem conjAction_apply (g : G) (S : V →L[𝕜] V) :
    conjAction π g S = (ContinuousLinearMap.adjoint (π g)).comp (S.comp (π g)) := by
  simp [conjAction, ContinuousLinearMap.compL_apply]

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [NormedSpace ℝ V]
  [SMulCommClass ℝ 𝕜 V] in
/-- Conjugating by `π g` translates the integrand of the unitarian trick on the right by `g`:
`(π g)† ∘ ((π h)† ∘ (π h)) ∘ (π g) = (π (h * g))† ∘ (π (h * g))`. -/
private theorem conjAction_comp_gramFamily (g : G) :
    (conjAction π g : C(V →L[𝕜] V, V →L[𝕜] V)).comp (gramFamily π hπ) =
      (gramFamily π hπ).comp (ContinuousMap.mulRight g) :=
  ContinuousMap.ext fun h ↦ by
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulRight, conjAction_apply,
      gramFamily, ContinuousMap.coe_mk, map_mul, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.adjoint_comp]
    exact (ContinuousLinearMap.comp_assoc _ _ _).symm

/-- **The operator form of `G`-invariance of the averaged form:** `(π g)† ∘ S ∘ (π g) = S`.

Conjugation by `π g` is a continuous linear map on operators, so it commutes with Haar averaging,
and on the integrand it is right translation by `g`, which the Haar average does not see. -/
@[simp]
theorem adjoint_comp_gramOperator_comp (g : G) :
    (ContinuousLinearMap.adjoint (π g)).comp ((gramOperator π hπ).comp (π g)) =
      gramOperator π hπ := by
  rw [← conjAction_apply π g, gramOperator, ← ContinuousLinearMap.haarAverage_comp_comm,
    conjAction_comp_gramFamily π hπ g, haarAverage_comp_mulRight]

/-- **The averaged form is `G`-invariant.** This is the whole point of the unitarian trick: `π` is
unitary for `⟪v, w⟫_G = ⟪gramOperator π hπ v, w⟫`, even when it is not unitary for the inner
product `V` was given. -/
@[simp]
theorem inner_gramOperator_map_map (g : G) (v w : V) :
    ⟪π g v, gramOperator π hπ (π g w)⟫_𝕜 = ⟪v, gramOperator π hπ w⟫_𝕜 := by
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right] using
    congrArg (fun S : V →L[𝕜] V ↦ ⟪v, S w⟫_𝕜) (adjoint_comp_gramOperator_comp π hπ g)

/-- **Weyl's unitarian trick.** Every continuous representation of a compact group on a Hilbert
space carries a `G`-invariant positive-definite Hermitian form, represented by a positive-definite
self-adjoint operator `S` with `(π g)† ∘ S ∘ (π g) = S`.

This operator is the input to unitarization: retopologizing `V` by `⟪S ·, ·⟫`, or conjugating `π`
by `S ^ (1 / 2)`, makes every `π g` unitary. Neither construction is carried out here, so this file
does not itself produce an `IsUnitary` representation. -/
theorem isUnitarizable :
    ∃ S : V →L[𝕜] V, IsSelfAdjoint S ∧ (∀ v : V, v ≠ 0 → 0 < re ⟪S v, v⟫_𝕜) ∧
      ∀ g : G, (ContinuousLinearMap.adjoint (π g)).comp (S.comp (π g)) = S :=
  ⟨gramOperator π hπ, isSelfAdjoint_gramOperator π hπ,
    fun _ hv ↦ re_inner_gramOperator_self_pos π hπ hv, adjoint_comp_gramOperator_comp π hπ⟩

/-- Averaging a form that is already invariant changes nothing: the Gram operator of a unitary
representation is the identity. -/
theorem gramOperator_eq_one (hunitary : IsUnitary π) : gramOperator π hπ = 1 := by
  have hconst : gramFamily π hπ = ContinuousMap.const G 1 :=
    ContinuousMap.ext fun g ↦ hunitary.adjoint_comp_self g
  rw [gramOperator, hconst, haarAverage_const]

end ContRepresentation

end TauCeti
