/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Tangent-bundle trivializations at their own base point, and open submanifolds

The canonical tangent-bundle trivialization at a point `x` is built from the chart at `x`, so on
the fibre over `x` itself it is the identity.  This file records that fact in both directions.

It then identifies the tangent spaces of an open submanifold with those of its ambient manifold
and shows that, near each point, the inverse tangent-bundle trivializations agree under that
identification.

## Main results

* `TauCeti.Manifold.continuousLinearMapAt_trivializationAt_self` and
  `TauCeti.Manifold.symmL_trivializationAt_self`: the canonical trivialization at `x` and its
  inverse act as the identity on the fibre over `x`.
* `TauCeti.Manifold.localFrame_trivializationAt_self`: consequently its local frame at `x` is the
  chosen basis of the model space.
* `TauCeti.Manifold.contDiffOn_tangentCoordChange`: the tangent coordinate change between the
  charts at two points is `C^n` on the overlap of their sources, read in the chart at the first
  point.
* `TauCeti.Manifold.contMDiffAt_tangentCoordChange`: that coordinate change is `C^n` at the base
  point of its first chart, as a map of manifolds into the linear endomorphisms of the model
  space.
* `TauCeti.Manifold.continuousLinearMapAt_symmL_coordChange`: reading a tangent vector through the
  preferred trivializations of two charts is the tangent coordinate change between them.
* `TauCeti.Manifold.tangentSpaceOpenEquiv`: the canonical continuous linear equivalence between
  the tangent space of an open submanifold and the ambient tangent space.
* `TauCeti.Manifold.mfderiv_subtype_val`: the differential of the inclusion is the canonical
  tangent-space equivalence.
* `TauCeti.Manifold.eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq`: near a point, the
  inverse tangent-bundle trivializations agree through this equivalence.
-/

public section

open Bundle Filter Manifold Module Set TopologicalSpace
open scoped Bundle Manifold Topology ContDiff

noncomputable section

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section TangentChart

section TangentBundleChart

variable [IsManifold I 1 M]

namespace TangentBundle

/-- The second component of the chart of a tangent bundle at `q`, read at a point with base point
in the chart source.  Together with `TangentBundle.coe_chartAt_fst` this describes the
tangent-bundle charts completely. -/
@[simp, mfld_simps]
theorem coe_chartAt_snd {p q : TangentBundle I M} :
    (chartAt (ModelProd H E) q p).2 =
      tangentCoordChange I p.1 q.1 p.1 p.2 := by
  -- After unfolding the tangent-bundle chart, the fibre-to-model-space conversion is
  -- definitionally the tangent coordinate change; no separate conversion lemma is needed.
  rw [TangentBundle.chartAt]
  rfl

end TangentBundle

end TangentBundleChart

/-- The tangent coordinate change between the charts at `x` and `y` is `C^n` on the overlap of
the two chart sources, read in the chart at `x`.  This is Mathlib's
`contDiffOn_fderiv_coord_change` for the preferred charts at two points. -/
theorem contDiffOn_tangentCoordChange {n : ℕ∞ω} [IsManifold I (n + 1) M] (x y : M) :
    haveI : IsManifold I 1 M := IsManifold.of_le (n := n + 1) le_add_self
    ContDiffOn 𝕜 n (fun a : E => tangentCoordChange I x y ((extChartAt I x).symm a))
      (((extChartAt I x).symm ≫ extChartAt I y).source) := by
  have hI : IsManifold I 1 M := IsManifold.of_le (n := n + 1) le_add_self
  refine (contDiffOn_fderiv_coord_change (𝕜 := 𝕜) (n := n) (I := I) (M := M)
    (achart H x) (achart H y)).congr (fun a ha => ?_)
  have ha2 : a ∈ (extChartAt I x).target := by
    rw [PartialEquiv.trans_source] at ha
    exact ha.1
  rw [tangentCoordChange_def, (extChartAt I x).right_inv ha2]
  rfl

/-- The tangent coordinate change between the charts at `x` and `y` is `C^n` at `x`, as a map of
manifolds into the continuous linear endomorphisms of the model space. -/
theorem contMDiffAt_tangentCoordChange {n : ℕ∞ω} [IsManifold I (n + 1) M] {x y : M}
    (hy : x ∈ (extChartAt I y).source) :
    haveI : IsManifold I 1 M := IsManifold.of_le (n := n + 1) le_add_self
    ContMDiffAt I 𝓘(𝕜, E →L[𝕜] E) n (tangentCoordChange I x y) x := by
  have hI : IsManifold I 1 M := IsManifold.of_le (n := n + 1) le_add_self
  rw [contMDiffAt_iff]
  refine ⟨?_, ?_⟩
  · refine (continuousOn_tangentCoordChange (I := I) (𝕜 := 𝕜) x y).continuousAt ?_
    exact Filter.inter_mem (extChartAt_source_mem_nhds (I := I) (x := x))
      ((isOpen_extChartAt_source y).mem_nhds hy)
  · have hmem : extChartAt I x x ∈ ((extChartAt I x).symm ≫ extChartAt I y).source := by
      rw [PartialEquiv.trans_source'', PartialEquiv.symm_symm, PartialEquiv.symm_target]
      exact mem_image_of_mem _ ⟨mem_extChartAt_source x, hy⟩
    have hychart : x ∈ (chartAt H y).source := by
      rw [← OpenPartialHomeomorph.extend_source (f := chartAt H y) (I := I)]
      exact hy
    have hset : ((extChartAt I x).symm ≫ extChartAt I y).source
        ∈ nhdsWithin (extChartAt I x x) (range I) :=
      I.extendCoordChange_source_mem_nhdsWithin' (e := chartAt H x) (e' := chartAt H y)
        (ChartedSpace.mem_chart_source x) hychart
    refine ((contDiffOn_tangentCoordChange (I := I) (𝕜 := 𝕜) x y).contDiffWithinAt
      hmem).mono_of_mem_nhdsWithin hset

section TangentReading

variable [IsManifold I 1 M]

/-- The reading map of the preferred trivialization centred at `x₀` sends the tangent vector at
`y` whose `x`-coordinates are `u` to its `x₀`-coordinates. -/
theorem continuousLinearMapAt_symmL_coordChange {x x₀ y : M}
    (hyx : y ∈ (chartAt H x).source) (hyx₀ : y ∈ (chartAt H x₀).source) (u : E) :
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 y
        ((trivializationAt E (TangentSpace I) x).symmL 𝕜 y u)
      = tangentCoordChange I x x₀ y u := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (I := I) (b₀ := x) (b := y) hyx,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) (b₀ := x₀) (b := y)
      hyx₀]
  simp only [tangentBundleCore_coordChange_achart]
  have hy1 : y ∈ (extChartAt I x).source := by rw [extChartAt_source]; exact hyx
  have hy2 : y ∈ (extChartAt I y).source := by
    rw [extChartAt_source]
    exact mem_chart_source H y
  have hy3 : y ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hyx₀
  exact tangentCoordChange_comp (I := I) (w := x) (x := y) (y := x₀) (z := y) (v := u)
    ⟨⟨hy1, hy2⟩, hy3⟩

end TangentReading

end TangentChart

section BasePoint

variable [IsManifold I 1 M]

/-- Read in the canonical trivialization at `x`, a tangent vector at `x` itself is its own
coordinate vector: the trivialization is built from the chart at `x`, whose transition function
with itself has derivative the identity. -/
@[simp]
theorem continuousLinearMapAt_trivializationAt_self (x : M) (v : TangentSpace I x) :
    (trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 x v = v := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (mem_chart_source H x)]
  exact (tangentBundleCore I M).coordChange_self (achart H x) x (mem_chart_source H x) v

/-- The inverse form of `TauCeti.Manifold.continuousLinearMapAt_trivializationAt_self`: over its
own base point, the inverse of the canonical trivialization is the identity. -/
@[simp]
theorem symmL_trivializationAt_self (x : M) (v : E) :
    (trivializationAt E (TangentSpace I) x).symmL 𝕜 x v = v := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source H x)]
  exact (tangentBundleCore I M).coordChange_self (achart H x) x (mem_chart_source H x) v

private theorem localFrame_apply_eq_symmL {ι : Type*} (b : Basis ι 𝕜 E)
    (e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)) [MemTrivializationAtlas e]
    {x : M} (hx : x ∈ e.baseSet) (i : ι) :
    e.localFrame b i x = e.symmL 𝕜 x (b i) := by
  rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet _ _ hx,
    Bundle.Trivialization.basisAt, Basis.map_apply,
    Bundle.Trivialization.linearEquivAt_symm_apply, ← e.symmL_apply (R := 𝕜) hx]

/-- Over its own base point, the local frame attached to the canonical trivialization at `x` is
the given basis of the model space. -/
@[simp]
theorem localFrame_trivializationAt_self {ι : Type*} (b : Basis ι 𝕜 E) (x : M) (i : ι) :
    (trivializationAt E (TangentSpace I) x).localFrame b i x = b i := by
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) x
  rw [localFrame_apply_eq_symmL b _ hx]
  exact symmL_trivializationAt_self (I := I) x (b i)

end BasePoint

/-- The canonical identification between the tangent space of an open submanifold and the ambient
tangent space. Both are Mathlib's type synonym for the common model vector space.

This is deliberately a named equivalence rather than `ContinuousLinearEquiv.refl 𝕜 E`: because
`TangentSpace` is not reducible, a statement phrased with `refl` is type-correct only after
unfolding it, so `rw` and `simp` fail on such statements. Mathlib introduces
`NormedSpace.fromTangentSpace` for the analogous identification for the same reason. -/
noncomputable def tangentSpaceOpenEquiv {U : Opens M} (x : U) :
    TangentSpace I x ≃L[𝕜] TangentSpace I (x : M) where
  toFun v := v
  invFun v := v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[simp]
theorem tangentSpaceOpenEquiv_apply {U : Opens M} (x : U) (v : TangentSpace I x) :
    tangentSpaceOpenEquiv (I := I) x v = v := by
  exact (rfl)

@[simp]
theorem tangentSpaceOpenEquiv_symm_apply {U : Opens M} (x : U)
    (v : TangentSpace I (x : M)) :
    (tangentSpaceOpenEquiv (I := I) x).symm v = v := by
  exact (rfl)

/-- In inherited charts, the tangent-bundle coordinate changes of an open submanifold and its
ambient manifold agree locally. -/
private theorem eventually_tangentBundleCore_coordChange_open_eq
    [IsManifold I 1 M] {U : Opens M} (x : U) :
    ∀ᶠ y in nhds x,
      (tangentBundleCore I U).coordChange (achart H x) (achart H y) y =
        (tangentBundleCore I M).coordChange
          (achart H (x : M)) (achart H (y : M)) (y : M) := by
  rcases mem_nhds_iff.mp
      (Opens.chartAt_subtype_val_symm_eventuallyEq (H := H) U (x := x)) with
    ⟨V, hV, hVopen, hxV⟩
  have hxV' : chartAt H x x ∈ V := by
    simpa [Opens.chartAt_eq] using hxV
  have hVevent : ∀ᶠ y in nhds x, chartAt H x y ∈ V :=
    ((chartAt H x).continuousAt (by simp)).eventually (hVopen.mem_nhds hxV')
  filter_upwards [hVevent] with y hyV
  have hinv : (chartAt H (x : M)).symm =ᶠ[nhds (chartAt H (x : M) (y : M))]
      Subtype.val ∘ (chartAt H x).symm :=
    Filter.eventuallyEq_of_mem (hVopen.mem_nhds hyV) hV
  have hIsymm : Tendsto I.symm
      (nhds (I (chartAt H (x : M) (y : M))))
      (nhds (chartAt H (x : M) (y : M))) := by
    have hc : Tendsto I.symm
        (nhds (I (chartAt H (x : M) (y : M))))
        (nhds (I.symm (I (chartAt H (x : M) (y : M))))) :=
      I.continuous_symm.continuousAt
    simpa only [I.left_inv] using hc
  have htrans := Filter.EventuallyEq.comp_tendsto
    (hinv.fun_comp (↑I ∘ chartAt H (y : M))) hIsymm
  have hd : fderivWithin 𝕜
      (((↑I ∘ chartAt H (y : M)) ∘ (chartAt H (x : M)).symm) ∘ I.symm)
        (Set.range I) (I (chartAt H (x : M) (y : M))) =
      fderivWithin 𝕜
        (((↑I ∘ chartAt H (y : M)) ∘ Subtype.val ∘ (chartAt H x).symm) ∘ I.symm)
          (Set.range I) (I (chartAt H (x : M) (y : M))) :=
    htrans.fderivWithin_eq_of_nhds
  ext z
  simpa [tangentBundleCore_coordChange_achart, Function.comp_def, Opens.chartAt_eq,
    tangentSpaceOpenEquiv_apply] using DFunLike.congr_fun hd.symm z

/-- The differential of the inclusion of an open submanifold is the canonical tangent-space
identification. -/
@[simp]
theorem mfderiv_subtype_val {U : Opens M} (x : U) :
    mfderiv I I (Subtype.val : U → M) x =
      (tangentSpaceOpenEquiv (I := I) x).toContinuousLinearMap := by
  ext v
  rw [ContinuousLinearEquiv.coe_coe, tangentSpaceOpenEquiv_apply, mfderiv]
  simp only [contMDiff_subtype_val.mdifferentiableAt one_ne_zero, ↓reduceIte]
  have h : writtenInExtChartAt I I x (Subtype.val : U → M) =ᶠ[
      nhdsWithin (extChartAt I x x) (Set.range I)] id := by
    have hmem : I.symm ⁻¹' (chartAt H x).target ∩ Set.range I ∈
        nhdsWithin (extChartAt I x x) (Set.range I) := by
      rw [← I.image_eq (chartAt H x).target]
      exact (chartAt H x).extend_image_target_mem_nhds (mem_chart_source H x)
    filter_upwards [hmem] with y hy
    rcases hy with ⟨hyT, ⟨z, rfl⟩⟩
    have hzT : z ∈ (chartAt H x).target := by
      simpa only [Set.mem_preimage, I.left_inv] using hyT
    simp only [writtenInExtChartAt, Function.comp_apply, extChartAt,
      OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm, I.left_inv, id_eq]
    -- The chart of `U` at `x` is by definition the subtype restriction of the ambient chart, so
    -- its inverse followed by the inclusion is the ambient inverse chart on the restricted target.
    have hsymm : ((chartAt H x).symm z : M) = (chartAt H (x : M)).symm z := by
      rw [Opens.chartAt_eq]
      exact (chartAt H (x : M)).subtypeRestr_symm_apply ⟨x⟩ hzT
    rw [hsymm]
    simp only [(chartAt H (x : M)).right_inv
        ((chartAt H (x : M)).subtypeRestr_target_subset ⟨x⟩ hzT)]
  have hxRange : extChartAt I x x ∈ Set.range I :=
    ⟨chartAt H x x, rfl⟩
  rw [h.fderivWithin_eq_of_mem hxRange,
    fderivWithin_id
      (I.uniqueDiffOn.uniqueDiffWithinAt hxRange)]
  rfl

/-- Near a point of an open submanifold, its inverse tangent-bundle trivialization agrees with the
ambient inverse trivialization under the canonical tangent-space identification. -/
theorem eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq
    [IsManifold I 1 M] {U : Opens M} (x : U) :
    ∀ᶠ y in nhds x, ∀ z : E,
      tangentSpaceOpenEquiv (I := I) y
          ((trivializationAt E (TangentSpace I : U → Type _) x).symmL 𝕜 y z) =
        (trivializationAt E (TangentSpace I : M → Type _) (x : M)).symmL 𝕜 (y : M) z := by
  filter_upwards [
    (trivializationAt E (TangentSpace I : U → Type _) x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I : U → Type _) x),
    continuousAt_subtype_val.eventually
      ((trivializationAt E (TangentSpace I : M → Type _) (x : M)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) (x : M))),
    eventually_tangentBundleCore_coordChange_open_eq (I := I) x] with y hyU hyM hcoord
  intro z
  have hyU' : y ∈ (chartAt H x).source := by
    simpa using hyU
  have hyM' : (y : M) ∈ (chartAt H (x : M)).source := by
    exact hyM
  rw [TangentBundle.symmL_trivializationAt_eq_core hyU',
    TangentBundle.symmL_trivializationAt_eq_core hyM']
  -- The preceding rewrites identify the two `symmL` maps with core coordinate changes, but their
  -- applications still use the definitional identification `TangentSpace I b = E`. The following
  -- `change` intentionally unfolds those map coercions and the local `tangentSpaceOpenEquiv`; no
  -- application-level rewrite lemma exposes this conversion.
  change (tangentBundleCore I U).coordChange (achart H x) (achart H y) y z =
    (tangentBundleCore I M).coordChange (achart H (x : M)) (achart H (y : M)) (y : M) z
  exact DFunLike.congr_fun hcoord z

end TauCeti.Manifold
