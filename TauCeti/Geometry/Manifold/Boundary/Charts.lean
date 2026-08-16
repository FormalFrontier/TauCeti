/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Boundary.Basic
public import TauCeti.Geometry.Manifold.Boundary.Model

/-!
# The boundary of a manifold with boundary is a manifold

Mathlib carries the boundary `I.boundary M` of a manifold with boundary only as a *set*: there is
no manifold structure on it, so nothing can be glued along it. This file supplies that structure in
the basic case, the one Layer 1 of the geometric-topology roadmap pins down first: `M` is a `C^k`
manifold, `k ≠ 0`, modeled on the `(n + 1)`-dimensional Euclidean half-space `𝓡∂ (n + 1)`, and its
boundary becomes a boundaryless `C^k` manifold modeled on `EuclideanSpace ℝ (Fin n)`, one dimension
lower, whose inclusion into `M` is a `C^k` closed embedding.

The boundary atlas consists of charts induced by the preferred ambient charts. Each preferred
ambient chart carries a boundary point to a point of the half-space whose zeroth coordinate
vanishes; deleting that coordinate turns it into a preferred chart of the boundary. Two facts make
this work, and they are the content of the file.

* **The boundary is visible in every chart.** Mathlib defines a boundary point through the chart
  *at that point*, and detecting it in another chart of the atlas is `ModelWithCorners`
  chart-independence, which for `C^1` manifolds is Mathlib's
  `ModelWithCorners.isBoundaryPoint_iff_of_mem_atlas`. The generic range-based restatement lives
  in `TauCeti.Geometry.Manifold.Boundary.Basic`; this file specialises it to the Euclidean
  half-space equation `x ∈ ∂M ↔ (e x) 0 = 0`.
* **The transition maps stay `C^k`.** A boundary transition map is the ambient transition map
  conjugated by the linear parametrization of the coordinate hyperplane, and `ContDiffOn` composes
  with continuous linear maps, so no new analysis is needed.

The charted-space structure depends only on the ambient `C^1` structure and is registered as the
canonical instance. The manifold and embedding results remain valid for every exponent `k ≠ 0`.
Boundarylessness then follows directly from
`ModelWithCorners.Boundaryless.boundary_eq_empty`.

Corners are deliberately out of scope: gluing along a *piece* of the boundary produces corners, and
the quadrant model `modelWithCornersEuclideanQuadrant` needs its own boundary analysis. Collar
neighbourhoods, which are what make a gluing smooth rather than merely topological, are the next
step and are not proved here.

## Main definitions

* `TauCeti.boundaryChartedSpace`: the charted-space structure on `I.boundary M`.

## Main results

* `TauCeti.ModelWithCorners.mem_boundary_euclideanHalfSpace_iff_of_mem_atlas`: boundary points are
  detected by the vanishing zeroth coordinate in any ambient atlas chart.
* `TauCeti.boundaryChartedSpace_atlas`: the boundary atlas is the range of its preferred charts.
* `TauCeti.boundaryChartedSpace_chartAt_source` and its companions characterize the preferred
  boundary charts induced by the ambient preferred charts.
* `TauCeti.isManifold_boundary`: the boundary is a `C^k` manifold over `EuclideanSpace ℝ (Fin n)`.
* `TauCeti.isImmersion_subtypeVal_boundary`, `TauCeti.isSmoothEmbedding_subtypeVal_boundary`: the
  inclusion of the boundary is a closed `C^k` smooth embedding.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 1 (manifolds with boundary).
* J. Lee, *Introduction to Smooth Manifolds*, Springer GTM 218, 2nd ed. (2013), Theorem 1.46 (the
  boundary of a smooth `n`-manifold with boundary is a smooth `(n - 1)`-manifold).
-/

public section

open Function Set Topology

open scoped Manifold ContDiff

namespace TauCeti

section Boundary

variable {n : ℕ} {k : WithTop ℕ∞} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) k M]
  {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))} {x : M}

/-- A point of a `C^k` manifold with boundary modeled on the `(n + 1)`-dimensional Euclidean
half-space lies on the boundary exactly when any chart around it reads it with vanishing zeroth
coordinate. -/
theorem ModelWithCorners.mem_boundary_euclideanHalfSpace_iff_of_mem_atlas (hk : k ≠ 0)
    (he : e ∈ atlas (EuclideanHalfSpace (n + 1)) M) (hx : x ∈ e.source) :
    x ∈ (𝓡∂ (n + 1)).boundary M ↔ (e x).1 0 = 0 := by
  rw [ModelWithCorners.boundary, mem_ofPred_eq,
    ModelWithCorners.isBoundaryPoint_iff_mem_frontier_range hk he hx,
    frontier_range_modelWithCornersEuclideanHalfSpace, modelWithCornersEuclideanHalfSpace_toFun]
  exact eq_comm

/-- The image under `e.symm` of a point of the coordinate hyperplane lying in `e.target` is a
boundary point of `M`. -/
private theorem symm_boundaryParam_mem_boundary (hk : k ≠ 0)
    (he : e ∈ atlas (EuclideanHalfSpace (n + 1)) M) {z : EuclideanSpace ℝ (Fin n)}
    (hz : EuclideanHalfSpace.boundaryParam n z ∈ e.target) :
    e.symm (EuclideanHalfSpace.boundaryParam n z) ∈ (𝓡∂ (n + 1)).boundary M := by
  rw [ModelWithCorners.mem_boundary_euclideanHalfSpace_iff_of_mem_atlas hk he (e.map_target hz),
    e.right_inv hz]
  simp

/-- Reinserting the deleted coordinate recovers the chart value of a boundary point. -/
private theorem boundaryParam_boundaryProj_chart_apply (hk : k ≠ 0)
    (he : e ∈ atlas (EuclideanHalfSpace (n + 1)) M)
    {q : ↥((𝓡∂ (n + 1)).boundary M)} (hq : (q : M) ∈ e.source) :
    EuclideanHalfSpace.boundaryParam n (EuclideanHalfSpace.boundaryProj n (e q.1)) = e q.1 := by
  simpa only [EuclideanHalfSpace.boundaryProj_coe] using
    EuclideanHalfSpace.boundaryParam_boundaryProj
      ((ModelWithCorners.mem_boundary_euclideanHalfSpace_iff_of_mem_atlas hk he hq).1 q.2)

open scoped Classical in
/-- The boundary chart attached to an ambient chart `e` of `M`: read a boundary point through `e`
and delete its (vanishing) zeroth coordinate.

The base point `p` only serves as the irrelevant value of the inverse outside the target; the
boundary of `M` can be empty, so no such value is available otherwise. -/
private noncomputable def boundaryChart (hk : k ≠ 0) (p : ↥((𝓡∂ (n + 1)).boundary M))
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)))
    (he : e ∈ atlas (EuclideanHalfSpace (n + 1)) M) :
    OpenPartialHomeomorph ↥((𝓡∂ (n + 1)).boundary M) (EuclideanSpace ℝ (Fin n)) where
  toFun q := EuclideanHalfSpace.boundaryProj n (e q.1)
  invFun z :=
    if h : EuclideanHalfSpace.boundaryParam n z ∈ e.target then
      ⟨e.symm (EuclideanHalfSpace.boundaryParam n z), symm_boundaryParam_mem_boundary hk he h⟩
    else p
  source := Subtype.val ⁻¹' e.source
  target := EuclideanHalfSpace.boundaryParam n ⁻¹' e.target
  map_source' q hq := by
    -- Unfold the `toFun` and `target` fields currently being defined; their API lemmas can only be
    -- stated after the `boundaryChart` definition is complete.
    change EuclideanHalfSpace.boundaryParam n (EuclideanHalfSpace.boundaryProj n (e q.1)) ∈
      e.target
    rw [boundaryParam_boundaryProj_chart_apply hk he hq]
    exact e.map_source hq
  map_target' z hz := by
    simp only [mem_preimage] at hz ⊢
    rw [dite_eq_left hz]
    exact e.map_target hz
  left_inv' q hq := by
    have hq' := boundaryParam_boundaryProj_chart_apply hk he hq
    have hq'' : EuclideanHalfSpace.boundaryParam n
        (EuclideanHalfSpace.boundaryProj n (e q.1)) ∈ e.target := by
      rw [hq']; exact e.map_source hq
    rw [dite_eq_left hq'']
    refine Subtype.ext ?_
    -- Reduce equality in the boundary subtype to equality of its ambient points, and unfold the
    -- selected `invFun` branch. Both are definitional reductions internal to this constructor.
    change (e.symm (EuclideanHalfSpace.boundaryParam n
      (EuclideanHalfSpace.boundaryProj n (e q.1))) : M) = (q : M)
    rw [hq', e.left_inv hq]
  right_inv' z hz := by
    simp only [mem_preimage] at hz
    rw [dite_eq_left hz]
    simp [e.right_inv hz]
  open_source := e.open_source.preimage continuous_subtype_val
  open_target := e.open_target.preimage EuclideanHalfSpace.continuous_boundaryParam
  continuousOn_toFun :=
    EuclideanHalfSpace.continuous_boundaryProj.comp_continuousOn
      (e.continuousOn.comp continuous_subtype_val.continuousOn (mapsTo_preimage _ _))
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine ContinuousOn.congr (e.symm.continuousOn.comp
      EuclideanHalfSpace.continuous_boundaryParam.continuousOn (mapsTo_preimage _ _)) fun z hz ↦ ?_
    simp only [mem_preimage] at hz
    simp [Function.comp_apply, dite_eq_left hz]

variable {hk : k ≠ 0} {p : ↥((𝓡∂ (n + 1)).boundary M)}
  {he : e ∈ atlas (EuclideanHalfSpace (n + 1)) M}

/-- The source of a boundary chart is the part of the boundary the ambient chart sees. -/
@[simp]
private theorem boundaryChart_source :
    (boundaryChart hk p e he).source = Subtype.val ⁻¹' e.source := (rfl)

/-- The target of a boundary chart is the ambient target, pulled back to the hyperplane. -/
@[simp]
private theorem boundaryChart_target :
    (boundaryChart hk p e he).target = EuclideanHalfSpace.boundaryParam n ⁻¹' e.target := (rfl)

/-- A boundary chart reads a point through the ambient chart and deletes the zeroth coordinate. -/
@[simp]
private theorem boundaryChart_apply (q : ↥((𝓡∂ (n + 1)).boundary M)) :
    boundaryChart hk p e he q = EuclideanHalfSpace.boundaryProj n (e q.1) := (rfl)

/-- On its target, the inverse of a boundary chart is the inverse of the ambient chart applied to
the parametrized point. -/
@[simp]
private theorem boundaryChart_symm_apply {z : EuclideanSpace ℝ (Fin n)}
    (hz : EuclideanHalfSpace.boundaryParam n z ∈ e.target) :
    (((boundaryChart hk p e he).symm z : ↥((𝓡∂ (n + 1)).boundary M)) : M) =
      e.symm (EuclideanHalfSpace.boundaryParam n z) := by
  have hw : (⟨e.symm (EuclideanHalfSpace.boundaryParam n z),
      symm_boundaryParam_mem_boundary hk he hz⟩ : ↥((𝓡∂ (n + 1)).boundary M)) ∈
      (boundaryChart hk p e he).source := by
    rw [boundaryChart_source, mem_preimage]
    exact e.map_target hz
  have key : (⟨e.symm (EuclideanHalfSpace.boundaryParam n z),
      symm_boundaryParam_mem_boundary hk he hz⟩ :
      ↥((𝓡∂ (n + 1)).boundary M)) = (boundaryChart hk p e he).symm z := by
    rw [(boundaryChart hk p e he).eq_symm_apply hw hz, boundaryChart_apply]
    -- Reduce the ambient value of the explicitly constructed boundary subtype before applying the
    -- inverse law for the ambient chart.
    change EuclideanHalfSpace.boundaryProj n
      (e (e.symm (EuclideanHalfSpace.boundaryParam n z))) = z
    rw [e.right_inv hz, EuclideanHalfSpace.boundaryProj_boundaryParam]
  rw [← key]

section BoundaryChartedSpace

variable [IsManifold (𝓡∂ (n + 1)) 1 M]

/-- The canonical charted-space structure on the boundary of a `C^1` manifold modeled on a
Euclidean half-space. Its atlas consists of the boundary charts induced by the ambient preferred
charts. The implementation is intentionally opaque; use the characteristic lemmas below to reason
about its atlas and preferred charts. -/
@[irreducible, instance] noncomputable def boundaryChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) ↥((𝓡∂ (n + 1)).boundary M) where
  atlas := range fun p ↦ boundaryChart one_ne_zero p
    (chartAt (EuclideanHalfSpace (n + 1)) p.1) (chart_mem_atlas _ _)
  chartAt := fun p ↦ boundaryChart one_ne_zero p
    (chartAt (EuclideanHalfSpace (n + 1)) p.1) (chart_mem_atlas _ _)
  mem_chart_source p := mem_chart_source _ p.1
  chart_mem_atlas p := mem_range_self p

variable (M) in
/-- The preferred chart of the boundary at `p` is the boundary chart induced by the ambient
preferred chart at `p`. -/
@[simp]
private theorem boundaryChartedSpace_chartAt (p : ↥((𝓡∂ (n + 1)).boundary M)) :
    chartAt (EuclideanSpace ℝ (Fin n)) p =
      boundaryChart one_ne_zero p (chartAt (EuclideanHalfSpace (n + 1)) (p : M))
        (chart_mem_atlas _ _) :=
  by
    unfold boundaryChartedSpace
    rfl

variable (M) in
/-- The boundary atlas is the range of its preferred charts. -/
theorem boundaryChartedSpace_atlas :
    atlas (EuclideanSpace ℝ (Fin n)) ↥((𝓡∂ (n + 1)).boundary M) =
      range fun p : ↥((𝓡∂ (n + 1)).boundary M) ↦
        chartAt (EuclideanSpace ℝ (Fin n)) p :=
  by
    unfold atlas boundaryChartedSpace chartAt
    rfl

variable (M) in
/-- The source of the preferred boundary chart at `p` is the part of the boundary the ambient
preferred chart at `p` sees. -/
theorem boundaryChartedSpace_chartAt_source (p : ↥((𝓡∂ (n + 1)).boundary M)) :
    (chartAt (EuclideanSpace ℝ (Fin n)) p).source =
      Subtype.val ⁻¹' (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).source :=
  by
    rw [boundaryChartedSpace_chartAt]
    exact boundaryChart_source (hk := one_ne_zero) (p := p) (he := chart_mem_atlas _ _)

variable (M) in
/-- The target of the preferred boundary chart at `p` is the ambient target, pulled back to the
coordinate hyperplane. -/
theorem boundaryChartedSpace_chartAt_target (p : ↥((𝓡∂ (n + 1)).boundary M)) :
    (chartAt (EuclideanSpace ℝ (Fin n)) p).target =
      EuclideanHalfSpace.boundaryParam n ⁻¹'
        (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).target :=
  by
    rw [boundaryChartedSpace_chartAt]
    exact boundaryChart_target (hk := one_ne_zero) (p := p) (he := chart_mem_atlas _ _)

variable (M) in
/-- The preferred boundary chart at `p` reads a point through the ambient preferred chart at `p`
and deletes the zeroth coordinate. -/
theorem boundaryChartedSpace_chartAt_apply (p q : ↥((𝓡∂ (n + 1)).boundary M)) :
    chartAt (EuclideanSpace ℝ (Fin n)) p q =
      EuclideanHalfSpace.boundaryProj n
        (chartAt (EuclideanHalfSpace (n + 1)) (p : M) (q : M)) :=
  by
    rw [boundaryChartedSpace_chartAt]
    exact boundaryChart_apply (hk := one_ne_zero) (p := p) (he := chart_mem_atlas _ _) q

variable (M) in
/-- On its target, the inverse of the preferred boundary chart at `p` is the inverse of the ambient
preferred chart at `p`, applied to the parametrized point. -/
theorem boundaryChartedSpace_chartAt_symm_apply (p : ↥((𝓡∂ (n + 1)).boundary M))
    {z : EuclideanSpace ℝ (Fin n)}
    (hz : EuclideanHalfSpace.boundaryParam n z ∈
      (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).target) :
    (((chartAt (EuclideanSpace ℝ (Fin n)) p).symm z : ↥((𝓡∂ (n + 1)).boundary M)) : M) =
      (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).symm
        (EuclideanHalfSpace.boundaryParam n z) :=
  by
    rw [boundaryChartedSpace_chartAt]
    exact boundaryChart_symm_apply (hk := one_ne_zero) (p := p) (he := chart_mem_atlas _ _) hz

end BoundaryChartedSpace

/-- The transition map between two boundary charts is `C^k`: read through the parametrization of
the coordinate hyperplane it is the ambient transition map, restricted to that hyperplane. -/
private theorem contDiffOn_boundaryChart_symm_trans [IsManifold (𝓡∂ (n + 1)) 1 M]
    (p q : ↥((𝓡∂ (n + 1)).boundary M))
    {e₁ e₂ : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he₁ : e₁ ∈ atlas (EuclideanHalfSpace (n + 1)) M)
    (he₂ : e₂ ∈ atlas (EuclideanHalfSpace (n + 1)) M) :
    ContDiffOn ℝ k
      ((boundaryChart one_ne_zero p e₁ he₁).symm ≫ₕ boundaryChart one_ne_zero q e₂ he₂)
      ((boundaryChart one_ne_zero p e₁ he₁).symm ≫ₕ
        boundaryChart one_ne_zero q e₂ he₂).source := by
  have hg : e₁.symm ≫ₕ e₂ ∈ contDiffGroupoid k (𝓡∂ (n + 1)) :=
    StructureGroupoid.compatible _ he₁ he₂
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hg
  have hG : ContDiffOn ℝ k
      ((𝓡∂ (n + 1)) ∘ (e₁.symm ≫ₕ e₂) ∘ (𝓡∂ (n + 1)).symm)
      ((𝓡∂ (n + 1)).symm ⁻¹' (e₁.symm ≫ₕ e₂).source ∩ range (𝓡∂ (n + 1))) := hg.1
  have hz₁ : ∀ z ∈ ((boundaryChart one_ne_zero p e₁ he₁).symm ≫ₕ
      boundaryChart one_ne_zero q e₂ he₂).source,
      EuclideanHalfSpace.boundaryParam n z ∈ e₁.target := by
    intro z hz
    simpa only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.symm_symm, boundaryChart_target, mem_preimage] using hz.1
  have hsub : ∀ z ∈ ((boundaryChart one_ne_zero p e₁ he₁).symm ≫ₕ
      boundaryChart one_ne_zero q e₂ he₂).source,
      EuclideanHalfSpace.boundaryParam n z ∈ (e₁.symm ≫ₕ e₂).source := by
    intro z hz
    have h₂ := hz.2
    simp only [OpenPartialHomeomorph.symm_symm, boundaryChart_source, mem_preimage,
      boundaryChart_symm_apply (hz₁ z hz)] at h₂
    exact ⟨hz₁ z hz, by simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage] using h₂⟩
  refine ContDiffOn.congr
    ((euclideanHalfSpaceBoundaryProj n).contDiff.comp_contDiffOn
      (hG.comp (euclideanHalfSpaceBoundaryParam n).contDiff.contDiffOn fun z hz ↦ ?_))
    fun z hz ↦ ?_
  · exact ⟨by simpa using hsub z hz, EuclideanHalfSpace.boundaryParam_mem_range z⟩
  · have h₁ := hz₁ z hz
    simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans, boundaryChart_apply,
      EuclideanHalfSpace.modelWithCornersEuclideanHalfSpace_symm_boundaryParam,
      EuclideanHalfSpace.boundaryProj_coe]
    rw [boundaryChart_symm_apply h₁, modelWithCornersEuclideanHalfSpace_toFun]

variable (M) in
/-- **The boundary of a `C^k` manifold with boundary is a `C^k` manifold** of dimension one less:
the transition maps between the boundary charts are `C^k`. -/
theorem isManifold_boundary (hk : k ≠ 0) :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k ↥((𝓡∂ (n + 1)).boundary M) := by
  let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
    IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
  refine isManifold_of_contDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k
    ↥((𝓡∂ (n + 1)).boundary M) ?_
  rw [boundaryChartedSpace_atlas]
  rintro f₁ f₂ ⟨p, rfl⟩ ⟨q, rfl⟩
  simpa [boundaryChartedSpace_chartAt] using
    contDiffOn_boundaryChart_symm_trans p q (chart_mem_atlas _ p.1)
      (chart_mem_atlas _ q.1)

variable (M) in
/-- The inclusion of the boundary into the manifold is a `C^k` immersion. In the preferred
boundary and ambient charts it is the coordinate inclusion with one-dimensional complement. -/
theorem isImmersion_subtypeVal_boundary (hk : k ≠ 0) :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
    Manifold.IsImmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) k
      (Subtype.val : ↥((𝓡∂ (n + 1)).boundary M) → M) := by
  let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
    IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
  let _ := isManifold_boundary (n := n) (k := k) M hk
  apply Manifold.IsImmersionOfComplement.isImmersion (F := ℝ)
  intro p
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    continuous_subtype_val.continuousAt (euclideanHalfSpaceBoundaryNormalEquiv n)
    (chartAt (EuclideanSpace ℝ (Fin n)) p)
    (chartAt (EuclideanHalfSpace (n + 1)) (p : M))
    (mem_chart_source _ p) (mem_chart_source _ (p : M))
    (IsManifold.chart_mem_maximalAtlas p) (IsManifold.chart_mem_maximalAtlas (p : M))
  intro z hz
  rw [OpenPartialHomeomorph.extend_target] at hz
  have hzdom : z ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target := by
    simpa only [modelWithCornersSelf_coe_symm, preimage_id_eq, id_eq] using hz.1
  have hz' : EuclideanHalfSpace.boundaryParam n z ∈
      (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).target := by
    rw [boundaryChartedSpace_chartAt_target M p] at hzdom
    exact hzdom
  have h1 : ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm z : M) =
      (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).symm
        (EuclideanHalfSpace.boundaryParam n z) :=
    boundaryChartedSpace_chartAt_symm_apply M p hz'
  simp only [Function.comp_apply, mfld_simps]
  rw [h1, (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).right_inv hz',
    modelWithCornersEuclideanHalfSpace_toFun, EuclideanHalfSpace.boundaryParam_coe]
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

variable (M) in
/-- The inclusion of the boundary into the manifold is a `C^k` smooth embedding. -/
theorem isSmoothEmbedding_subtypeVal_boundary (hk : k ≠ 0) :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
    Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) k
      (Subtype.val : ↥((𝓡∂ (n + 1)).boundary M) → M) := by
  let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
    IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
  exact ⟨isImmersion_subtypeVal_boundary (n := n) (k := k) M hk,
    ((𝓡∂ (n + 1)).isClosed_boundary hk).isClosedEmbedding_subtypeVal.isEmbedding⟩

end Boundary

end TauCeti
