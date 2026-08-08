/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.Boundary.Model

/-!
# The boundary of a manifold with boundary is a manifold

Mathlib carries the boundary `I.boundary M` of a manifold with boundary only as a *set*: there is
no manifold structure on it, so nothing can be glued along it. This file supplies that structure in
the basic case, the one Layer 1 of the geometric-topology roadmap pins down first: `M` is a `C^k`
manifold, `k ≠ 0`, modeled on the `(n + 1)`-dimensional Euclidean half-space `𝓡∂ (n + 1)`, and its
boundary becomes a boundaryless `C^k` manifold modeled on `EuclideanSpace ℝ (Fin n)`, one dimension
lower, whose inclusion into `M` is a `C^k` closed embedding.

The charts are the obvious ones. An ambient chart `e` of `M` carries a boundary point to a point of
the half-space whose zeroth coordinate vanishes; deleting that coordinate — the linear
identification of `TauCeti.euclideanHalfSpaceBoundaryParam` — turns `e` into a chart of the
boundary. Two facts make this work, and they are the content of the file.

* **The boundary is visible in every chart.** Mathlib defines a boundary point through the chart
  *at that point*, and detecting it in another chart of the atlas is `ModelWithCorners`
  chart-independence, which for `C^1` manifolds is Mathlib's
  `ModelWithCorners.isBoundaryPoint_iff_of_mem_atlas`. That statement reads the point against the
  frontier of the *extended chart target*; `TauCeti.isBoundaryPoint_iff_mem_frontier_range`
  restates it against the frontier of `range I`, which is what a concrete model can compute, and
  `TauCeti.mem_boundary_iff_of_mem_atlas` then specialises it to `x ∈ ∂M ↔ (e x) 0 = 0`.
* **The transition maps stay `C^k`.** A boundary transition map is the ambient transition map
  conjugated by the linear parametrization of the coordinate hyperplane, and `ContDiffOn` composes
  with continuous linear maps, so no new analysis is needed: this is
  `TauCeti.contDiffOn_boundaryChart_symm_trans`.

The results are stated for a general smoothness exponent `k ≠ 0`, which forces the charted-space
structure to be a `def` (`TauCeti.boundaryChartedSpace`) rather than an instance; the `C^∞` case is
registered as an instance at the end of the file.

Corners are deliberately out of scope: gluing along a *piece* of the boundary produces corners, and
the quadrant model `modelWithCornersEuclideanQuadrant` needs its own boundary analysis. Collar
neighbourhoods, which are what make a gluing smooth rather than merely topological, are the next
step and are not proved here.

## Main definitions

* `TauCeti.euclideanHalfSpaceParam`, `TauCeti.euclideanHalfSpaceProj`: the parametrization of the
  frontier of the Euclidean half-space by `EuclideanSpace ℝ (Fin n)`, and its retraction.
* `TauCeti.boundaryChart`: the boundary chart induced by an ambient chart.
* `TauCeti.boundaryChartedSpace`: the charted-space structure on `I.boundary M`.

## Main results

* `TauCeti.isInteriorPoint_iff_mem_interior_range`,
  `TauCeti.isBoundaryPoint_iff_mem_frontier_range`: interior and boundary points are detected in
  any chart of the atlas, against `range I`.
* `TauCeti.mem_boundary_iff_of_mem_atlas`: the half-space form of the previous statement.
* `TauCeti.boundary_isManifold`: the boundary is a `C^k` manifold over `EuclideanSpace ℝ (Fin n)`.
* `TauCeti.boundary_boundary_eq_empty`: it is boundaryless.
* `TauCeti.isClosedEmbedding_boundary_val`, `TauCeti.contMDiff_boundary_val`: the inclusion of the
  boundary is a closed topological embedding, and is `C^k`.
* `TauCeti.boundary_euclideanHalfSpace`: the boundary of the model half-space is the coordinate
  hyperplane, which pins the construction down on a nonempty example.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 1 (manifolds with boundary).
* J. Lee, *Introduction to Smooth Manifolds*, Springer GTM 218, 2nd ed. (2013), Theorem 1.46 (the
  boundary of a smooth `n`-manifold with boundary is a smooth `(n - 1)`-manifold).
-/

public section

open Function Set Topology

open scoped Manifold ContDiff

namespace TauCeti

section ChartIndependence

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {k : WithTop ℕ∞} [IsManifold I k M]
  {e : OpenPartialHomeomorph M H} {x : M}

/-- A point of a `C^k` manifold, `k ≠ 0`, is an interior point exactly when *some* chart of the
atlas containing it in its source reads it inside the interior of the range of the model. -/
theorem isInteriorPoint_iff_mem_interior_range (hk : k ≠ 0) (he : e ∈ atlas H M)
    (hx : x ∈ e.source) : I.IsInteriorPoint x ↔ I (e x) ∈ interior (range I) := by
  rw [I.isInteriorPoint_iff_of_mem_atlas hk he hx]
  exact ⟨fun h ↦ e.interior_extend_target_subset_interior_range h,
    fun h ↦ e.mem_interior_extend_target (e.map_source hx) h⟩

/-- A point of a `C^k` manifold, `k ≠ 0`, is a boundary point exactly when *some* chart of the
atlas containing it in its source reads it on the frontier of the range of the model. -/
theorem isBoundaryPoint_iff_mem_frontier_range (hk : k ≠ 0) (he : e ∈ atlas H M)
    (hx : x ∈ e.source) : I.IsBoundaryPoint x ↔ I (e x) ∈ frontier (range I) := by
  rw [I.isBoundaryPoint_iff_not_isInteriorPoint, isInteriorPoint_iff_mem_interior_range hk he hx,
    I.isClosed_range.frontier_eq]
  simp

end ChartIndependence

section Model

variable {n : ℕ}

/-- The parametrization of the frontier of the `(n + 1)`-dimensional Euclidean half-space by
`EuclideanSpace ℝ (Fin n)`: insert a zero as the zeroth coordinate. -/
@[expose] noncomputable def euclideanHalfSpaceParam (n : ℕ) :
    EuclideanSpace ℝ (Fin n) → EuclideanHalfSpace (n + 1) :=
  fun x ↦ ⟨euclideanHalfSpaceBoundaryParam n x, by simp⟩

/-- Delete the zeroth coordinate of a point of the `(n + 1)`-dimensional Euclidean half-space. -/
@[expose] noncomputable def euclideanHalfSpaceProj (n : ℕ) :
    EuclideanHalfSpace (n + 1) → EuclideanSpace ℝ (Fin n) :=
  fun y ↦ euclideanHalfSpaceBoundaryProj n y.1

/-- The parametrized frontier point, read in the ambient Euclidean space. -/
@[simp]
theorem euclideanHalfSpaceParam_coe (x : EuclideanSpace ℝ (Fin n)) :
    (euclideanHalfSpaceParam n x).1 = euclideanHalfSpaceBoundaryParam n x :=
  rfl

/-- The parametrization lands in the frontier: its zeroth coordinate vanishes. -/
@[simp]
theorem euclideanHalfSpaceParam_apply_zero (x : EuclideanSpace ℝ (Fin n)) :
    (euclideanHalfSpaceParam n x).1 0 = 0 := by
  simp

/-- Deleting the zeroth coordinate undoes the parametrization. -/
@[simp]
theorem euclideanHalfSpaceProj_param (x : EuclideanSpace ℝ (Fin n)) :
    euclideanHalfSpaceProj n (euclideanHalfSpaceParam n x) = x := by
  simp [euclideanHalfSpaceProj]

/-- On the frontier of the half-space, deleting and reinserting the zeroth coordinate is the
identity. -/
theorem euclideanHalfSpaceParam_proj {y : EuclideanHalfSpace (n + 1)} (hy : y.1 0 = 0) :
    euclideanHalfSpaceParam n (euclideanHalfSpaceProj n y) = y :=
  Subtype.ext (euclideanHalfSpaceBoundaryParam_proj (mem_euclideanHalfSpaceBoundary.2 hy))

/-- The parametrization of the frontier is continuous. -/
theorem continuous_euclideanHalfSpaceParam :
    Continuous (euclideanHalfSpaceParam n) :=
  (euclideanHalfSpaceBoundaryParam n).continuous.subtype_mk _

/-- Deleting the zeroth coordinate is continuous. -/
theorem continuous_euclideanHalfSpaceProj :
    Continuous (euclideanHalfSpaceProj n) :=
  (euclideanHalfSpaceBoundaryProj n).continuous.comp continuous_subtype_val

/-- The model map `𝓡∂ (n + 1)` sends the parametrized frontier to the linear parametrization of
the coordinate hyperplane. -/
@[simp]
theorem modelWithCornersEuclideanHalfSpace_param (x : EuclideanSpace ℝ (Fin n)) :
    (𝓡∂ (n + 1)) (euclideanHalfSpaceParam n x) = euclideanHalfSpaceBoundaryParam n x := by
  rw [modelWithCornersEuclideanHalfSpace_toFun]
  exact euclideanHalfSpaceParam_coe x

/-- The inverse of the model map `𝓡∂ (n + 1)` undoes the parametrization of the coordinate
hyperplane. -/
@[simp]
theorem modelWithCornersEuclideanHalfSpace_symm_param (x : EuclideanSpace ℝ (Fin n)) :
    (𝓡∂ (n + 1)).symm (euclideanHalfSpaceBoundaryParam n x) = euclideanHalfSpaceParam n x := by
  refine Subtype.ext ?_
  rw [modelWithCornersEuclideanHalfSpace_symm_apply]
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

/-- The coordinate hyperplane lies in the range of the half-space model. -/
theorem euclideanHalfSpaceBoundaryParam_mem_range (x : EuclideanSpace ℝ (Fin n)) :
    euclideanHalfSpaceBoundaryParam n x ∈ range (𝓡∂ (n + 1)) := by
  rw [range_modelWithCornersEuclideanHalfSpace]
  simp

/-- The boundary of the Euclidean half-space, viewed as a manifold over itself, is the coordinate
hyperplane where the zeroth coordinate vanishes. In particular it is nonempty, so the boundary
theory below is not vacuous. -/
theorem boundary_euclideanHalfSpace (n : ℕ) :
    (𝓡∂ (n + 1)).boundary (EuclideanHalfSpace (n + 1)) = {y | y.1 0 = 0} := by
  ext y
  rw [ModelWithCorners.boundary, mem_ofPred_eq, ModelWithCorners.isBoundaryPoint_iff,
    frontier_range_modelWithCornersEuclideanHalfSpace]
  simp [extChartAt, chartAt_self_eq, eq_comm]

end Model

section Boundary

variable {n : ℕ} {k : WithTop ℕ∞} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) k M]
  {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))} {x : M}

/-- A point of a `C^k` manifold with boundary modeled on the `(n + 1)`-dimensional Euclidean
half-space lies on the boundary exactly when any chart around it reads it with vanishing zeroth
coordinate. -/
theorem mem_boundary_iff_of_mem_atlas (hk : k ≠ 0)
    (he : e ∈ atlas (EuclideanHalfSpace (n + 1)) M) (hx : x ∈ e.source) :
    x ∈ (𝓡∂ (n + 1)).boundary M ↔ (e x).1 0 = 0 := by
  rw [ModelWithCorners.boundary, mem_ofPred_eq, isBoundaryPoint_iff_mem_frontier_range hk he hx,
    frontier_range_modelWithCornersEuclideanHalfSpace, modelWithCornersEuclideanHalfSpace_toFun]
  exact eq_comm

/-- The image under `e.symm` of a point of the coordinate hyperplane lying in `e.target` is a
boundary point of `M`. -/
theorem symm_param_mem_boundary (hk : k ≠ 0) (he : e ∈ atlas (EuclideanHalfSpace (n + 1)) M)
    {z : EuclideanSpace ℝ (Fin n)} (hz : euclideanHalfSpaceParam n z ∈ e.target) :
    e.symm (euclideanHalfSpaceParam n z) ∈ (𝓡∂ (n + 1)).boundary M := by
  rw [mem_boundary_iff_of_mem_atlas hk he (e.map_target hz), e.right_inv hz]
  simp

open scoped Classical in
/-- The boundary chart attached to an ambient chart `e` of `M`: read a boundary point through `e`
and delete its (vanishing) zeroth coordinate.

The base point `p` only serves as the irrelevant value of the inverse outside the target; the
boundary of `M` can be empty, so no such value is available otherwise. -/
@[expose] noncomputable def boundaryChart (hk : k ≠ 0) (p : ↥((𝓡∂ (n + 1)).boundary M))
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)))
    (he : e ∈ atlas (EuclideanHalfSpace (n + 1)) M) :
    OpenPartialHomeomorph ↥((𝓡∂ (n + 1)).boundary M) (EuclideanSpace ℝ (Fin n)) where
  toFun q := euclideanHalfSpaceProj n (e q.1)
  invFun z :=
    if h : euclideanHalfSpaceParam n z ∈ e.target then
      ⟨e.symm (euclideanHalfSpaceParam n z), symm_param_mem_boundary hk he h⟩
    else p
  source := Subtype.val ⁻¹' e.source
  target := euclideanHalfSpaceParam n ⁻¹' e.target
  map_source' q hq := by
    change euclideanHalfSpaceParam n (euclideanHalfSpaceProj n (e q.1)) ∈ e.target
    rw [euclideanHalfSpaceParam_proj ((mem_boundary_iff_of_mem_atlas hk he hq).1 q.2)]
    exact e.map_source hq
  map_target' z hz := by
    simp only [mem_preimage] at hz ⊢
    rw [dif_pos hz]
    exact e.map_target hz
  left_inv' q hq := by
    have hq' : euclideanHalfSpaceParam n (euclideanHalfSpaceProj n (e q.1)) = e q.1 :=
      euclideanHalfSpaceParam_proj ((mem_boundary_iff_of_mem_atlas hk he hq).1 q.2)
    have hq'' : euclideanHalfSpaceParam n (euclideanHalfSpaceProj n (e q.1)) ∈ e.target := by
      rw [hq']; exact e.map_source hq
    rw [dif_pos hq'']
    refine Subtype.ext ?_
    change (e.symm (euclideanHalfSpaceParam n (euclideanHalfSpaceProj n (e q.1))) : M) = (q : M)
    rw [hq', e.left_inv hq]
  right_inv' z hz := by
    simp only [mem_preimage] at hz
    rw [dif_pos hz]
    simp [e.right_inv hz]
  open_source := e.open_source.preimage continuous_subtype_val
  open_target := e.open_target.preimage continuous_euclideanHalfSpaceParam
  continuousOn_toFun :=
    continuous_euclideanHalfSpaceProj.comp_continuousOn
      (e.continuousOn.comp continuous_subtype_val.continuousOn (mapsTo_preimage _ _))
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine ContinuousOn.congr (e.symm.continuousOn.comp
      continuous_euclideanHalfSpaceParam.continuousOn (mapsTo_preimage _ _)) fun z hz ↦ ?_
    simp only [mem_preimage] at hz
    simp [Function.comp_apply, dif_pos hz]

variable {hk : k ≠ 0} {p : ↥((𝓡∂ (n + 1)).boundary M)}
  {he : e ∈ atlas (EuclideanHalfSpace (n + 1)) M}

/-- The source of a boundary chart is the part of the boundary the ambient chart sees. -/
@[simp]
theorem boundaryChart_source :
    (boundaryChart hk p e he).source = Subtype.val ⁻¹' e.source :=
  rfl

/-- The target of a boundary chart is the ambient target, pulled back to the hyperplane. -/
@[simp]
theorem boundaryChart_target :
    (boundaryChart hk p e he).target = euclideanHalfSpaceParam n ⁻¹' e.target :=
  rfl

/-- A boundary chart reads a point through the ambient chart and deletes the zeroth coordinate. -/
@[simp]
theorem boundaryChart_apply (q : ↥((𝓡∂ (n + 1)).boundary M)) :
    boundaryChart hk p e he q = euclideanHalfSpaceProj n (e q.1) :=
  rfl

/-- On its target, the inverse of a boundary chart is the inverse of the ambient chart applied to
the parametrized point. -/
theorem boundaryChart_symm_apply {z : EuclideanSpace ℝ (Fin n)}
    (hz : euclideanHalfSpaceParam n z ∈ e.target) :
    (((boundaryChart hk p e he).symm z : ↥((𝓡∂ (n + 1)).boundary M)) : M) =
      e.symm (euclideanHalfSpaceParam n z) := by
  have hw : (⟨e.symm (euclideanHalfSpaceParam n z), symm_param_mem_boundary hk he hz⟩ :
      ↥((𝓡∂ (n + 1)).boundary M)) ∈ (boundaryChart hk p e he).source := e.map_target hz
  have key : (⟨e.symm (euclideanHalfSpaceParam n z), symm_param_mem_boundary hk he hz⟩ :
      ↥((𝓡∂ (n + 1)).boundary M)) = (boundaryChart hk p e he).symm z := by
    rw [(boundaryChart hk p e he).eq_symm_apply hw hz, boundaryChart_apply]
    change euclideanHalfSpaceProj n (e (e.symm (euclideanHalfSpaceParam n z))) = z
    rw [e.right_inv hz, euclideanHalfSpaceProj_param]
  rw [← key]

variable (M) in
/-- The boundary chart at a boundary point, built from the ambient preferred chart there. -/
@[expose] noncomputable def boundaryChartAt (hk : k ≠ 0) (p : ↥((𝓡∂ (n + 1)).boundary M)) :
    OpenPartialHomeomorph ↥((𝓡∂ (n + 1)).boundary M) (EuclideanSpace ℝ (Fin n)) :=
  boundaryChart hk p (chartAt (EuclideanHalfSpace (n + 1)) p.1) (chart_mem_atlas _ _)

variable (M) in
/-- **The boundary of a `C^k` manifold with boundary is a topological manifold** of dimension one
less: the ambient charts, restricted to the boundary and with their vanishing zeroth coordinate
deleted, are charts modeled on `EuclideanSpace ℝ (Fin n)`. -/
@[instance_reducible] noncomputable def boundaryChartedSpace (hk : k ≠ 0) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) ↥((𝓡∂ (n + 1)).boundary M) where
  atlas := range (boundaryChartAt M hk)
  chartAt := boundaryChartAt M hk
  mem_chart_source p := mem_chart_source _ p.1
  chart_mem_atlas p := mem_range_self p

/-- The transition map between two boundary charts is `C^k`: read through the parametrization of
the coordinate hyperplane it is the ambient transition map, restricted to that hyperplane. -/
theorem contDiffOn_boundaryChart_symm_trans (hk : k ≠ 0)
    (p q : ↥((𝓡∂ (n + 1)).boundary M))
    {e₁ e₂ : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he₁ : e₁ ∈ atlas (EuclideanHalfSpace (n + 1)) M)
    (he₂ : e₂ ∈ atlas (EuclideanHalfSpace (n + 1)) M) :
    ContDiffOn ℝ k ((boundaryChart hk p e₁ he₁).symm ≫ₕ boundaryChart hk q e₂ he₂)
      ((boundaryChart hk p e₁ he₁).symm ≫ₕ boundaryChart hk q e₂ he₂).source := by
  have hg : e₁.symm ≫ₕ e₂ ∈ contDiffGroupoid k (𝓡∂ (n + 1)) :=
    StructureGroupoid.compatible _ he₁ he₂
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hg
  have hG : ContDiffOn ℝ k
      ((𝓡∂ (n + 1)) ∘ (e₁.symm ≫ₕ e₂) ∘ (𝓡∂ (n + 1)).symm)
      ((𝓡∂ (n + 1)).symm ⁻¹' (e₁.symm ≫ₕ e₂).source ∩ range (𝓡∂ (n + 1))) := hg.1
  have hz₁ : ∀ z ∈ ((boundaryChart hk p e₁ he₁).symm ≫ₕ boundaryChart hk q e₂ he₂).source,
      euclideanHalfSpaceParam n z ∈ e₁.target := fun z hz ↦ hz.1
  have hsub : ∀ z ∈ ((boundaryChart hk p e₁ he₁).symm ≫ₕ boundaryChart hk q e₂ he₂).source,
      euclideanHalfSpaceParam n z ∈ (e₁.symm ≫ₕ e₂).source := by
    intro z hz
    have h₂ := hz.2
    simp only [OpenPartialHomeomorph.symm_symm, boundaryChart_source, mem_preimage,
      boundaryChart_symm_apply (hz₁ z hz)] at h₂
    exact ⟨hz₁ z hz, by simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage] using h₂⟩
  refine ContDiffOn.congr
    ((euclideanHalfSpaceBoundaryProj n).contDiff.comp_contDiffOn
      (hG.comp (euclideanHalfSpaceBoundaryParam n).contDiff.contDiffOn fun z hz ↦ ?_))
    fun z hz ↦ ?_
  · exact ⟨by simpa using hsub z hz, euclideanHalfSpaceBoundaryParam_mem_range z⟩
  · have h₁ := hz₁ z hz
    simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans, boundaryChart_apply,
      modelWithCornersEuclideanHalfSpace_symm_param, euclideanHalfSpaceProj]
    rw [boundaryChart_symm_apply h₁, modelWithCornersEuclideanHalfSpace_toFun]

variable (M) in
/-- **The boundary of a `C^k` manifold with boundary is a `C^k` manifold** of dimension one less:
the transition maps between the boundary charts are `C^k`. -/
theorem boundary_isManifold (hk : k ≠ 0) :
    letI := boundaryChartedSpace (n := n) M hk
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k ↥((𝓡∂ (n + 1)).boundary M) := by
  let _ := boundaryChartedSpace (n := n) M hk
  refine isManifold_of_contDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k
    ↥((𝓡∂ (n + 1)).boundary M) ?_
  rintro f₁ f₂ ⟨p, rfl⟩ ⟨q, rfl⟩
  simp only [boundaryChartAt]
  simpa using contDiffOn_boundaryChart_symm_trans hk p q (chart_mem_atlas _ p.1)
    (chart_mem_atlas _ q.1)

variable (M) in
/-- The boundary of a `C^k` manifold with boundary is boundaryless: it is modeled on a
boundaryless model. -/
theorem boundary_boundary_eq_empty (hk : k ≠ 0) :
    letI := boundaryChartedSpace (n := n) M hk
    (𝓘(ℝ, EuclideanSpace ℝ (Fin n))).boundary ↥((𝓡∂ (n + 1)).boundary M) = ∅ := by
  let _ := boundaryChartedSpace (n := n) M hk
  exact ModelWithCorners.Boundaryless.boundary_eq_empty

variable (M) in
/-- The inclusion of the boundary of a `C^k` manifold with boundary is a closed topological
embedding. -/
theorem isClosedEmbedding_boundary_val (hk : k ≠ 0) :
    Topology.IsClosedEmbedding (Subtype.val : ↥((𝓡∂ (n + 1)).boundary M) → M) :=
  ((𝓡∂ (n + 1)).isClosed_boundary hk).isClosedEmbedding_subtypeVal

variable (M) in
/-- The inclusion of the boundary into the manifold is `C^k`: in the boundary chart induced by an
ambient chart it reads as the linear parametrization of the coordinate hyperplane. -/
theorem contMDiff_boundary_val (hk : k ≠ 0) :
    letI := boundaryChartedSpace (n := n) M hk
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) k
      (Subtype.val : ↥((𝓡∂ (n + 1)).boundary M) → M) := by
  let _ := boundaryChartedSpace (n := n) M hk
  intro p
  rw [contMDiffAt_iff]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  have hEq : ∀ z ∈ (boundaryChartAt M hk p).target,
      (extChartAt (𝓡∂ (n + 1)) (p : M) ∘ Subtype.val ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p).symm) z =
        euclideanHalfSpaceBoundaryParam n z := by
    intro z hz
    have hz' : euclideanHalfSpaceParam n z ∈
        (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).target := hz
    have h1 : ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm z : M) =
        (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).symm (euclideanHalfSpaceParam n z) :=
      boundaryChart_symm_apply (hk := hk) (p := p)
        (he := chart_mem_atlas (EuclideanHalfSpace (n + 1)) (p : M)) hz'
    simp only [Function.comp_apply, mfld_simps]
    rw [h1, (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).right_inv hz',
      modelWithCornersEuclideanHalfSpace_param]
  have hmem : extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p p ∈ (boundaryChartAt M hk p).target :=
    (boundaryChartAt M hk p).map_source (mem_chart_source _ p)
  refine ContDiffWithinAt.congr_of_eventuallyEq
    (euclideanHalfSpaceBoundaryParam n).contDiff.contDiffAt.contDiffWithinAt
    (Filter.eventuallyEq_of_mem (nhdsWithin_le_nhds
      ((boundaryChartAt M hk p).open_target.mem_nhds hmem)) hEq) (hEq _ hmem)

end Boundary

section Smooth

variable {n : ℕ} (M : Type*) [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]

/-- The boundary of a `C^∞` manifold with boundary, charted on `EuclideanSpace ℝ (Fin n)`. This is
`TauCeti.boundaryChartedSpace` in the smooth case, registered as an instance. -/
noncomputable instance instChartedSpaceBoundary :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) ↥((𝓡∂ (n + 1)).boundary M) :=
  boundaryChartedSpace (k := ∞) M (by simp)

/-- The boundary of a `C^∞` manifold with boundary is a `C^∞` manifold. -/
instance instIsManifoldBoundary :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ ↥((𝓡∂ (n + 1)).boundary M) :=
  boundary_isManifold (k := ∞) M (by simp)

end Smooth

end TauCeti
