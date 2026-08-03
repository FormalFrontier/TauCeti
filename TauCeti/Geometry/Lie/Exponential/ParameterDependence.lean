/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Exponential.Basic

/-!
# Parameter dependence of invariant integral curves

This file begins the analytic parameter-dependence theory for the invariant integral curves that
define the Lie-group exponential. In the identity chart, the tangent vector and group coordinate
form an autonomous ODE on the product model space. Picard--Lindelöf then supplies a single local
solution family, continuous jointly in its initial condition and time, for all sufficiently small
tangent vectors.

## Main results

* `mulInvariantCoordinateVectorField`: the invariant vector field in the identity chart, with its
  generating tangent vector included as a parameter.
* `contDiffAt_mulInvariantCoordinateVectorField`: this coordinate vector field is smooth at the
  zero vector and identity coordinate.
* `exists_lipschitzOn_local_mulInvariantCoordinateFlow`: a local solution family on a uniform
  closed neighborhood of the zero vector and the identity coordinate, jointly continuous and
  uniformly Lipschitz in its initial state.
* `exists_eventually_hasDerivAt_mulInvariantCoordinateFlow`: a neighborhood form of the local
  solution family whose values remain inside the identity chart.
* `exists_local_coordinate_representation_mulInvariantIntegralCurve`: the local solution family
  represents the canonical invariant integral curves uniformly for all sufficiently small
  generating vectors.
* `continuousAt_mulInvariantExp_modelSpace_zero`: the tangent-space exponential is continuous at
  zero in model-space coordinates.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The exponential map".
-/

public section

open Bundle Function Manifold VectorField
open scoped ContDiff Manifold Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

omit [Group G] in
private theorem isMIntegralCurveAt_extChartAt_symm_of_eventually
    [IsManifold I 1 G] [ContinuousSMul ℝ E]
    {x₀ : G} {f : ℝ → E} {t₀ : ℝ} {v : (x : G) → TangentSpace I x}
    (htarget : ∀ᶠ t in 𝓝 t₀, f t ∈ interior (extChartAt I x₀).target)
    (hderiv : ∀ᶠ t in 𝓝 t₀,
      HasDerivAt f
        (tangentCoordChange I ((extChartAt I x₀).symm (f t)) x₀
          ((extChartAt I x₀).symm (f t)) (v ((extChartAt I x₀).symm (f t)))) t) :
    IsMIntegralCurveAt ((extChartAt I x₀).symm ∘ f) v t₀ := by
  obtain ⟨s, hs, haux⟩ := (hderiv.and htarget).exists_mem
  rw [isMIntegralCurveAt_iff]
  refine ⟨s, hs, ?_⟩
  intro t ht
  let xₜ : G := (extChartAt I x₀).symm (f t)
  have h : HasDerivAt f
      (tangentCoordChange I xₜ x₀ xₜ (v xₜ)) t := (haux t ht).1
  have hf3 := Set.mem_of_mem_of_subset (haux t ht).2 interior_subset
  have hft1 := Set.mem_preimage.mp <|
    Set.mem_of_mem_of_subset hf3 (extChartAt I x₀).target_subset_preimage_source
  have hft2 := mem_extChartAt_source (I := I) xₜ
  have hft1' : xₜ ∈ (extChartAt I x₀).source := by simpa only [xₜ] using hft1
  have hcharts :
      xₜ ∈ (extChartAt I xₜ).source ∩ (extChartAt I x₀).source ∩
        (extChartAt I xₜ).source := ⟨⟨hft2, hft1'⟩, hft2⟩
  apply HasMFDerivAt.hasMFDerivWithinAt
  refine ⟨(continuousAt_extChartAt_symm'' hf3).comp h.continuousAt, ?_⟩
  have hcomp : HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ f)
      (tangentCoordChange I x₀ xₜ xₜ (tangentCoordChange I xₜ x₀ xₜ (v xₜ))) t := by
    apply HasFDerivAt.comp_hasDerivAt _ _ h
    apply HasFDerivWithinAt.hasFDerivAt (s := Set.range I) _ <|
      mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
        subset_trans interior_subset (extChartAt_target_subset_range ..),
        isOpen_interior, (haux t ht).2⟩
    rw [← (extChartAt I x₀).right_inv hf3]
    exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩
  have hd := hcomp.congr_deriv (tangentCoordChange_comp hcharts)
  have hd' := hd.congr_deriv (tangentCoordChange_self hft2)
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    PartialEquiv.refl_symm, modelWithCornersSelf_coe, Function.comp_def, id_eq, Set.range_id]
  -- Restore the named chart preimage before comparing the ordinary and manifold derivatives.
  rw [show (extChartAt I x₀).symm (f t) = xₜ from rfl]
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
  -- In these charts, the source and target tangent spaces are definitionally their model spaces.
  change HasFDerivWithinAt
    (((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ f))
      (ContinuousLinearMap.toSpanSingleton ℝ (v xₜ)) Set.univ t
  exact hd'.hasFDerivAt.hasFDerivWithinAt

/-- The left-invariant vector field, expressed in the identity chart and parameterized by its
generating tangent vector in the model space. -/
noncomputable def mulInvariantCoordinateVectorField [IsManifold I 1 G] (p : E × E) : E :=
  let g := (extChartAt I (1 : G)).symm p.2
  tangentCoordChange I g (1 : G) g
    (mulInvariantVectorField (I := I) (G := G) p.1 g)

/-- The parameterized coordinate field is the invariant vector field transported through the
identity chart. -/
theorem mulInvariantCoordinateVectorField_apply [IsManifold I 1 G] (v y : E) :
    mulInvariantCoordinateVectorField (I := I) (G := G) (v, y) =
      tangentCoordChange I ((extChartAt I (1 : G)).symm y) (1 : G)
        ((extChartAt I (1 : G)).symm y)
        (show E from mulInvariantVectorField (I := I) (G := G)
          (v : GroupLieAlgebra I G) ((extChartAt I (1 : G)).symm y)) := by
  rfl

/-- The coordinate expression of the parameterized left-invariant vector field is smooth at the
zero tangent vector and identity coordinate. -/
theorem contDiffAt_mulInvariantCoordinateVectorField
    [ContMDiffMul I ∞ G] [BoundarylessManifold I G] :
    ContDiffAt ℝ ∞ (mulInvariantCoordinateVectorField (I := I) (G := G))
      (0, extChartAt I (1 : G) (1 : G)) := by
  let _ : ContMDiffMul I (∞ + 1) G := by
    simpa using (inferInstance : ContMDiffMul I ∞ G)
  let V : E × G → TangentBundle I G := fun p =>
    ⟨p.2, mulInvariantVectorField (I := I) (G := G) p.1 p.2⟩
  have hV : ContMDiff (𝓘(ℝ, E).prod I) I.tangent ∞ V :=
    contMDiff_mulInvariantVectorField_modelSpace (n := ∞)
  have hV₀ := hV.contMDiffAt (x := ((0 : E), (1 : G)))
  rw [contMDiffAt_iff] at hV₀
  have h := hV₀.2.contDiffAt
    (range_mem_nhds_isInteriorPoint BoundarylessManifold.isInteriorPoint)
  let w : E × E → E := fun x =>
    ((extChartAt I.tangent (V (0, 1)) ∘ V ∘
      (extChartAt (𝓘(ℝ, E).prod I) (0, 1)).symm) x).2
  have hw_apply (p : E × E) :
      w p = tangentCoordChange I ((extChartAt I (1 : G)).symm p.2) (1 : G)
        ((extChartAt I (1 : G)).symm p.2)
        (show E from mulInvariantVectorField (I := I) (G := G)
          (p.1 : GroupLieAlgebra I G) ((extChartAt I (1 : G)).symm p.2)) := by
    -- This is the second coordinate of the tangent-bundle extended chart at `(0, 1)`.
    change tangentCoordChange I ((extChartAt I (1 : G)).symm p.2) (1 : G)
      ((extChartAt I (1 : G)).symm p.2)
        (show E from mulInvariantVectorField (I := I) (G := G)
          (p.1 : GroupLieAlgebra I G) ((extChartAt I (1 : G)).symm p.2)) = _
    rfl
  have hw : w = mulInvariantCoordinateVectorField (I := I) (G := G) := by
    funext p
    rw [mulInvariantCoordinateVectorField_apply]
    exact hw_apply p
  rw [← hw]
  simpa only [w, extChartAt_prod, extChartAt_self_apply, modelWithCornersSelf_coe,
    PartialEquiv.prod_coe, PartialEquiv.refl_coe, id_eq] using h.snd

/-- Near the zero tangent vector and the identity coordinate, the parameterized invariant ODE has
a single solution family that is continuous jointly in its initial condition and time and
uniformly Lipschitz in its initial state. The tangent-vector coordinate is frozen by the ODE; the
second coordinate follows the invariant vector field. -/
theorem exists_lipschitzOn_local_mulInvariantCoordinateFlow
    [CompleteSpace E] [ContMDiffMul I ∞ G] [BoundarylessManifold I G] :
    ∃ (α : (E × E) × ℝ → E × E) (δ : ℝ) (r L : NNReal), 0 < δ ∧ 0 < r ∧
      ContinuousOn α
        (Metric.closedBall ((0 : E), extChartAt I (1 : G) (1 : G)) r ×ˢ
          Set.Icc (-δ) δ) ∧
      (∀ t ∈ Set.Icc (-δ) δ,
        LipschitzOnWith L (fun x => α (x, t))
          (Metric.closedBall ((0 : E), extChartAt I (1 : G) (1 : G)) r)) ∧
      ∀ x ∈ Metric.closedBall ((0 : E), extChartAt I (1 : G) (1 : G)) r,
        α (x, 0) = x ∧
          (∀ t ∈ Set.Icc (-δ) δ,
            HasDerivWithinAt (fun s => α (x, s))
              ((0 : E),
                mulInvariantCoordinateVectorField (I := I) (G := G) (α (x, t)))
              (Set.Icc (-δ) δ) t) ∧
          ∀ t ∈ Set.Icc (-δ) δ, (α (x, t)).1 = x.1 := by
  let center : E × E := (0, extChartAt I (1 : G) (1 : G))
  let F : E × E → E × E := fun p =>
    (0, mulInvariantCoordinateVectorField (I := I) (G := G) p)
  have hF : ContDiffAt ℝ 1 F center := by
    exact contDiffAt_const.prodMk
      (contDiffAt_mulInvariantCoordinateVectorField.of_le (by norm_num))
  obtain ⟨δ, hδ, _, r, _, _, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hF
  obtain ⟨α, hα, L', hαlip⟩ :=
    (hpl (0 : ℝ)).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  let α' : (E × E) × ℝ → E × E := fun xt => α xt.1 xt.2
  have hαbase : ∀ x ∈ Metric.closedBall center r,
      α x 0 = x ∧ ∀ t ∈ Set.Icc (-δ) δ,
        HasDerivWithinAt (α x) (F (α x t)) (Set.Icc (-δ) δ) t := by
    simpa only [zero_sub, zero_add] using hα
  have hαlip' : ∀ t ∈ Set.Icc (-δ) δ,
      LipschitzOnWith L' (fun x => α x t) (Metric.closedBall center r) := by
    simpa only [zero_sub, zero_add] using hαlip
  have hαcont : ContinuousOn α'
      (Metric.closedBall center r ×ˢ Set.Icc (-δ) δ) := by
    apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L'
    · intro x hx
      exact HasDerivWithinAt.continuousOn (hαbase x hx).2
    · exact hαlip'
  have hα' : ∀ x ∈ Metric.closedBall center r,
      α' (x, 0) = x ∧ ∀ t ∈ Set.Icc (-δ) δ,
        HasDerivWithinAt (fun s => α' (x, s))
          ((0 : E), mulInvariantCoordinateVectorField (I := I) (G := G) (α' (x, t)))
          (Set.Icc (-δ) δ) t := by
    intro x hx
    simpa only [α', F] using hαbase x hx
  refine ⟨α', δ, r, L', hδ, hr, ?_, ?_, ?_⟩
  · simpa only [center, zero_sub, zero_add] using hαcont
  · intro t ht
    simpa only [α'] using hαlip' t ht
  · intro x hx
    have hx' : x ∈ Metric.closedBall center r := by simpa only [center] using hx
    refine ⟨(hα' x hx').1, (hα' x hx').2, ?_⟩
    let β : ℝ → E := fun t => (α' (x, t)).1
    have hβ : ∀ t ∈ Set.Icc (-δ) δ,
        HasDerivWithinAt β 0 (Set.Icc (-δ) δ) t := by
      intro t ht
      -- `β` is definitionally the first continuous-linear projection of the solution family.
      change HasDerivWithinAt
        ((ContinuousLinearMap.fst ℝ E E) ∘ fun s => α' (x, s)) 0
          (Set.Icc (-δ) δ) t
      simpa using (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivWithinAt t
        ((hα' x hx').2 t ht)
    have hconst := constant_of_derivWithin_zero
      (fun t ht => (hβ t ht).differentiableWithinAt)
      (fun t ht => (hβ t (Set.Ico_subset_Icc_self ht)).derivWithin
        ((uniqueDiffOn_Icc (by linarith)).uniqueDiffWithinAt
          (Set.Ico_subset_Icc_self ht)))
    intro t ht
    have hzero : (0 : ℝ) ∈ Set.Icc (-δ) δ := by constructor <;> linarith
    -- Unfold the named first-coordinate path before applying its constancy theorem.
    change β t = x.1
    exact (hconst t ht).trans ((hconst 0 hzero).symm.trans
      (congrArg Prod.fst (hα' x hx').1))

/-- There is a coordinate solution family near the zero tangent vector and time zero which is
continuous at the center, solves the parameterized invariant ODE with an ordinary derivative,
freezes the tangent-vector parameter, and remains in the target of the identity chart. -/
theorem exists_eventually_hasDerivAt_mulInvariantCoordinateFlow
    [CompleteSpace E] [ContMDiffMul I ∞ G] [BoundarylessManifold I G] :
    ∃ α : (E × E) × ℝ → E × E,
      ContinuousAt α (((0 : E), extChartAt I (1 : G) (1 : G)), 0) ∧
      α (((0 : E), extChartAt I (1 : G) (1 : G)), 0) =
        ((0 : E), extChartAt I (1 : G) (1 : G)) ∧
      (∀ᶠ xt in 𝓝 (((0 : E), extChartAt I (1 : G) (1 : G)), 0),
        ContinuousAt α xt) ∧
      ∀ᶠ xt in 𝓝 (((0 : E), extChartAt I (1 : G) (1 : G)), 0),
        HasDerivAt (fun t => α (xt.1, t))
          ((0 : E),
            mulInvariantCoordinateVectorField (I := I) (G := G) (α xt)) xt.2 ∧
        α (xt.1, 0) = xt.1 ∧
        (α xt).1 = xt.1.1 ∧
        (α xt).2 ∈ interior (extChartAt I (1 : G)).target := by
  obtain ⟨α, δ, r, _, hδ, hr, hcont, _, hα⟩ :=
    exists_lipschitzOn_local_mulInvariantCoordinateFlow
      (I := I) (G := G)
  let center : E × E := (0, extChartAt I (1 : G) (1 : G))
  have hdomain :
      Metric.closedBall center r ×ˢ Set.Icc (-δ) δ ∈ 𝓝 (center, 0) := by
    exact prod_mem_nhds (Metric.closedBall_mem_nhds center hr)
      (Icc_mem_nhds (by linarith) (by linarith))
  have hdomainOpen :
      Metric.ball center r ×ˢ Set.Ioo (-δ) δ ∈ 𝓝 (center, 0) := by
    exact prod_mem_nhds (Metric.ball_mem_nhds center hr)
      (Ioo_mem_nhds (by linarith) (by linarith))
  have hcontAt : ContinuousAt α (center, 0) :=
    hcont.continuousAt hdomain
  have hcenter : α (center, 0) = center := by
    exact (hα center (Metric.mem_closedBall_self hr.le)).1
  have htargetCenter : center.2 ∈ interior (extChartAt I (1 : G)).target := by
    exact (I.isInteriorPoint_iff.mp BoundarylessManifold.isInteriorPoint)
  have htarget :
      α ⁻¹' (Set.univ ×ˢ interior (extChartAt I (1 : G)).target) ∈ 𝓝 (center, 0) := by
    apply hcontAt.preimage_mem_nhds
    apply (isOpen_univ.prod isOpen_interior).mem_nhds
    rw [hcenter]
    exact ⟨Set.mem_univ _, htargetCenter⟩
  have hcontNear : ∀ᶠ xt in 𝓝 (center, 0), ContinuousAt α xt := by
    filter_upwards [hdomainOpen] with xt hxt
    apply hcont.continuousAt
    exact prod_mem_nhds
      (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hxt.1) Metric.ball_subset_closedBall)
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hxt.2) Set.Ioo_subset_Icc_self)
  refine ⟨α, by simpa only [center] using hcontAt, by simpa only [center] using hcenter,
    by simpa only [center] using hcontNear, ?_⟩
  filter_upwards [hdomainOpen, htarget] with xt hxt hxtTarget
  have hx := Metric.ball_subset_closedBall hxt.1
  have ht : xt.2 ∈ Set.Icc (-δ) δ := Set.Ioo_subset_Icc_self hxt.2
  have hderiv := (hα xt.1 hx).2.1 xt.2 ht
  refine ⟨hderiv.hasDerivAt (Icc_mem_nhds hxt.2.1 hxt.2.2),
    (hα xt.1 hx).1, (hα xt.1 hx).2.2 xt.2 ht, ?_⟩
  exact (Set.mem_preimage.mp hxtTarget).2

local instance lieGroupMinSmoothnessParameterDependence [LieGroup I ∞ G] :
    LieGroup I (minSmoothness ℝ 3) G := by
  simpa using (inferInstance : LieGroup I (3 : ℕ∞ω) G)

/-- A single coordinate solution family represents the canonical invariant integral curves for
every sufficiently small generating vector and every sufficiently small time. This is the bridge
from Picard--Lindelöf's parameterized model-space solutions to the canonical manifold-valued curves
used to define `lieExp`. -/
theorem exists_local_coordinate_representation_mulInvariantIntegralCurve
    [CompleteSpace E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    ∃ (α : (E × E) × ℝ → E × E) (U : Set E) (δ : ℝ),
      U ∈ 𝓝 (0 : E) ∧ 0 < δ ∧
      ContinuousAt α (((0 : E), extChartAt I (1 : G) (1 : G)), 0) ∧
      (∀ v ∈ U, ∀ t ∈ Set.Ioo (-δ) δ,
        ContinuousAt α ((v, extChartAt I (1 : G) (1 : G)), t) ∧
          (α (((v, extChartAt I (1 : G) (1 : G)), t))).2 ∈
            interior (extChartAt I (1 : G)).target) ∧
      ∀ v ∈ U,
        Set.EqOn
          (fun t => (extChartAt I (1 : G)).symm
            (α (((v, extChartAt I (1 : G) (1 : G)), t))).2)
          (mulInvariantIntegralCurve (I := I) (G := G)
            (v : GroupLieAlgebra I G) 1)
          (Set.Ioo (-δ) δ) := by
  obtain ⟨α, hαcont, _, hαcontNear, hα⟩ :=
    exists_eventually_hasDerivAt_mulInvariantCoordinateFlow (I := I) (G := G)
  let embed : E × ℝ → (E × E) × ℝ := fun vt =>
    ((vt.1, extChartAt I (1 : G) (1 : G)), vt.2)
  have hembed : ContinuousAt embed ((0 : E), 0) := by fun_prop
  have hpull : ∀ᶠ vt in 𝓝 ((0 : E), 0),
      ContinuousAt α (embed vt) ∧
        HasDerivAt (fun t => α ((embed vt).1, t))
          ((0 : E), mulInvariantCoordinateVectorField (I := I) (G := G) (α (embed vt))) vt.2 ∧
        α ((embed vt).1, 0) = (embed vt).1 ∧
        (α (embed vt)).1 = (embed vt).1.1 ∧
        (α (embed vt)).2 ∈ interior (extChartAt I (1 : G)).target := by
    exact hembed.eventually (hαcontNear.and hα)
  rw [nhds_prod_eq] at hpull
  obtain ⟨U, hU, T, hT, hsub⟩ := Filter.mem_prod_iff.mp hpull
  obtain ⟨δ, hδ, hδT⟩ := Metric.mem_nhds_iff.mp hT
  rw [Real.ball_eq_Ioo, zero_sub, zero_add] at hδT
  refine ⟨α, U, δ, hU, hδ, hαcont, ?_, ?_⟩
  · intro v hv t ht
    have hmem : (v, t) ∈ U ×ˢ T := ⟨hv, hδT ht⟩
    refine ⟨by simpa only [embed, Set.mem_ofPred_eq, Prod.fst, Prod.snd] using (hsub hmem).1,
      ?_⟩
    simpa only [embed, Set.mem_ofPred_eq, Prod.fst, Prod.snd] using (hsub hmem).2.2.2.2
  intro v hv
  let f : ℝ → E := fun t =>
    (α (((v, extChartAt I (1 : G) (1 : G)), t))).2
  let γ : ℝ → G := (extChartAt I (1 : G)).symm ∘ f
  have hlocal (t : ℝ) (ht : t ∈ Set.Ioo (-δ) δ) :
      HasDerivAt (fun s => α (((v, extChartAt I (1 : G) (1 : G)), s)))
          ((0 : E), mulInvariantCoordinateVectorField (I := I) (G := G)
            (α (((v, extChartAt I (1 : G) (1 : G)), t)))) t ∧
        α (((v, extChartAt I (1 : G) (1 : G)), 0)) =
          (v, extChartAt I (1 : G) (1 : G)) ∧
        (α (((v, extChartAt I (1 : G) (1 : G)), t))).1 = v ∧
        (α (((v, extChartAt I (1 : G) (1 : G)), t))).2 ∈
          interior (extChartAt I (1 : G)).target := by
    have hmem : (v, t) ∈ U ×ˢ T := ⟨hv, hδT ht⟩
    simpa only [embed, Set.mem_ofPred_eq, Prod.fst, Prod.snd] using (hsub hmem).2
  have hγAt : ∀ t ∈ Set.Ioo (-δ) δ,
      IsMIntegralCurveAt γ
        (mulInvariantVectorField (I := I) (G := G) (v : GroupLieAlgebra I G)) t := by
    intro t ht
    apply isMIntegralCurveAt_extChartAt_symm_of_eventually
    · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact (hlocal s hs).2.2.2
    · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      have hsnd : HasDerivAt f
          (mulInvariantCoordinateVectorField (I := I) (G := G)
            (α (((v, extChartAt I (1 : G) (1 : G)), s)))) s := by
        -- `f` is definitionally the second continuous-linear projection of the solution family.
        change HasDerivAt
          ((ContinuousLinearMap.snd ℝ E E) ∘ fun u =>
            α (((v, extChartAt I (1 : G) (1 : G)), u))) _ s
        simpa using (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt s
          (hlocal s hs).1
      have hpair : α (((v, extChartAt I (1 : G) (1 : G)), s)) = (v, f s) := by
        apply Prod.ext
        · exact (hlocal s hs).2.2.1
        · rfl
      rw [hpair] at hsnd
      simpa only [mulInvariantCoordinateVectorField_apply, f] using hsnd
  have hγOn : IsMIntegralCurveOn γ
      (mulInvariantVectorField (I := I) (G := G) (v : GroupLieAlgebra I G))
      (Set.Ioo (-δ) δ) := IsMIntegralCurveAt.isMIntegralCurveOn hγAt
  have hzero : (0 : ℝ) ∈ Set.Ioo (-δ) δ := ⟨by linarith, by linarith⟩
  have hγzero : γ 0 = 1 := by
    have hinit := (hlocal 0 hzero).2.1
    -- Expand the named chart-valued path so the initial-value equality rewrites its coordinate.
    change (extChartAt I (1 : G)).symm
      (α (((v, extChartAt I (1 : G) (1 : G)), 0))).2 = 1
    rw [congrArg Prod.snd hinit]
    exact (extChartAt I (1 : G)).left_inv (mem_extChartAt_source (I := I) (1 : G))
  exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hzero
    ((contMDiff_mulInvariantVectorField (I := I) (G := G)
      (v : GroupLieAlgebra I G)).of_le (by simp))
    hγOn
    ((isMIntegralCurve_mulInvariantIntegralCurve (I := I) (G := G)
      (v : GroupLieAlgebra I G) 1).isMIntegralCurveOn _)
    (by
      calc
        γ 0 = 1 := hγzero
        _ = mulInvariantIntegralCurve (I := I) (G := G)
            (v : GroupLieAlgebra I G) 1 0 :=
          (mulInvariantIntegralCurve_zero (I := I) (G := G)
            (v : GroupLieAlgebra I G) 1).symm)

/-- The tangent-space exponential is continuous at zero when its domain uses the canonical
model-space identification and its codomain remains the Lie group `G`. -/
theorem continuousAt_mulInvariantExp_modelSpace_zero
    [CompleteSpace E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    ContinuousAt
      (fun v : E => mulInvariantExp (I := I) (G := G) v) 0 := by
  obtain ⟨α, U, δ, hU, hδ, _, hαlocal, hαeq⟩ :=
    exists_local_coordinate_representation_mulInvariantIntegralCurve (I := I) (G := G)
  let c : ℝ := δ / 2
  have hc : c ∈ Set.Ioo (-δ) δ := by
    dsimp only [c]
    constructor <;> linarith
  have hc0 : c ≠ 0 := ne_of_gt (by dsimp only [c]; linarith)
  have hzeroU : (0 : E) ∈ U := mem_of_mem_nhds hU
  let q : E → (E × E) × ℝ := fun v =>
    ((c⁻¹ • v, extChartAt I (1 : G) (1 : G)), c)
  have hq : ContinuousAt q (0 : E) := by fun_prop
  have hqzero : q (0 : E) = ((0, extChartAt I (1 : G) (1 : G)), c) := by
    simp only [q, smul_zero]
  have hαq : ContinuousAt (fun v : E => α (q v)) 0 := by
    simpa only [Function.comp_def] using
      (hαlocal 0 hzeroU c hc).1.comp_of_eq hq hqzero
  have hsnd : ContinuousAt (fun v : E => (α (q v)).2) 0 :=
    continuousAt_snd.comp' hαq
  have htarget := Set.mem_of_mem_of_subset (hαlocal 0 hzeroU c hc).2 interior_subset
  have hinv : ContinuousAt (extChartAt I (1 : G)).symm (α (q 0)).2 := by
    rw [hqzero]
    exact continuousAt_extChartAt_symm'' htarget
  have hcontinuous : ContinuousAt
      (fun v : E => (extChartAt I (1 : G)).symm (α (q v)).2) 0 :=
    by
      simpa only [Function.comp_def] using
        (ContinuousAt.comp_of_eq (f := fun v : E => (α (q v)).2) hinv hsnd rfl)
  apply hcontinuous.congr_of_eventuallyEq
  have hrescale : ContinuousAt (fun v : E => c⁻¹ • v) 0 := by fun_prop
  have hrescaleU : (fun v : E => c⁻¹ • v) ⁻¹' U ∈ 𝓝 0 := by
    have hU' : U ∈ 𝓝 (c⁻¹ • (0 : E)) := by simpa only [smul_zero] using hU
    exact hrescale.preimage_mem_nhds hU'
  filter_upwards [hrescaleU] with v hv
  symm
  calc
    (extChartAt I (1 : G)).symm (α (q v)).2 =
        mulInvariantIntegralCurve (I := I) (G := G) (c⁻¹ • v) 1 c := by
      exact hαeq (c⁻¹ • v) hv hc
    _ = mulInvariantExp
        (c • (c⁻¹ • v)) := by
      exact (mulInvariantExp_smul _ c).symm
    _ = mulInvariantExp
        v := by
      congr 1
      simp only [smul_smul, mul_inv_cancel₀ hc0, one_smul]
      rfl
