/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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
* `contDiffAt_mulInvariantCoordinateVectorField`: this coordinate vector field is `C^n` at every
  generating vector over the identity coordinate when multiplication is `C^(n + 1)`.
* `mulInvariantCoordinateLinearMap`: the coordinate field as an operator on its generating vector.
* `contDiffAt_mulInvariantCoordinateLinearMap_one`: this operator is `C^n` at the identity
  coordinate.
* `hasStrictFDerivAt_mulInvariantCoordinateVectorField_zero_one`: the linearization of the
  parameterized coordinate field at zero and the identity is projection onto the parameter.
* `exists_lipschitzOn_local_mulInvariantCoordinateFlow`: a local solution family on a uniform
  closed neighborhood of the zero vector and the identity coordinate, jointly continuous and
  uniformly Lipschitz in its initial state.
* `exists_eventually_hasDerivAt_mulInvariantCoordinateFlow`: a neighborhood form of the local
  solution family whose values remain inside the identity chart.
* `exists_local_coordinate_representation_mulInvariantIntegralCurve`: the local solution family
  solves the coordinate ODE and represents the canonical integral curves uniformly for all small
  generators.
* `continuousAt_mulInvariantExp_modelSpace_zero`: the tangent-space exponential is continuous at
  zero in model-space coordinates.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The exponential map".
* Winston Yin's Mathlib proof of `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless`, whose
  chart calculation is exposed by `IsMIntegralCurveAt.of_extChartAt_symm` and invoked below.
-/

public section

open Bundle Function Manifold VectorField
open scoped ContDiff Manifold Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- A tangent vector is represented by the model vector type `E`. This private helper isolates the
definitional identification used when a tangent-bundle value enters coordinate calculus. -/
private abbrev tangentVectorModelSpace {g : G} (v : TangentSpace I g) : E := v

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
        (mulInvariantVectorField (I := I) (G := G)
          (v : GroupLieAlgebra I G) ((extChartAt I (1 : G)).symm y)) := by
  rfl

/-- The invariant coordinate field is additive in its generating vector. -/
@[simp]
theorem mulInvariantCoordinateVectorField_add [IsManifold I 1 G] (v w y : E) :
    mulInvariantCoordinateVectorField (I := I) (G := G) (v + w, y) =
      mulInvariantCoordinateVectorField (I := I) (G := G) (v, y) +
        mulInvariantCoordinateVectorField (I := I) (G := G) (w, y) := by
  let g := (extChartAt I (1 : G)).symm y
  let A := tangentCoordChange I g (1 : G) g
  calc
    A (tangentVectorModelSpace (I := I) <|
        mulInvariantVectorField (I := I) (G := G)
          ((v + w : E) : GroupLieAlgebra I G) g) =
        A (tangentVectorModelSpace (I := I) <|
            mulInvariantVectorField (I := I) (G := G) (v : GroupLieAlgebra I G) g) +
          A (tangentVectorModelSpace (I := I) <|
            mulInvariantVectorField (I := I) (G := G) (w : GroupLieAlgebra I G) g) := by
      rw [← map_add]
      apply congrArg A
      -- Compare the underlying tangent vectors before their definitional model-space conversion.
      change mulInvariantVectorField (I := I) (G := G)
          ((v + w : E) : GroupLieAlgebra I G) g =
        mulInvariantVectorField (I := I) (G := G) (v : GroupLieAlgebra I G) g +
          mulInvariantVectorField (I := I) (G := G) (w : GroupLieAlgebra I G) g
      have hparameter : ((v + w : E) : GroupLieAlgebra I G) =
          (v : GroupLieAlgebra I G) + (w : GroupLieAlgebra I G) := rfl
      rw [hparameter]
      exact congrFun (mulInvariantVectorField_add (I := I) (G := G)
        (v : GroupLieAlgebra I G) (w : GroupLieAlgebra I G)) g

/-- The invariant coordinate field respects scalar multiplication in its generating vector. -/
@[simp]
theorem mulInvariantCoordinateVectorField_smul [IsManifold I 1 G] (c : ℝ) (v y : E) :
    mulInvariantCoordinateVectorField (I := I) (G := G) (c • v, y) =
      c • mulInvariantCoordinateVectorField (I := I) (G := G) (v, y) := by
  let g := (extChartAt I (1 : G)).symm y
  let A := tangentCoordChange I g (1 : G) g
  calc
    A (tangentVectorModelSpace (I := I) <|
        mulInvariantVectorField (I := I) (G := G)
          ((c • v : E) : GroupLieAlgebra I G) g) =
        c • A (tangentVectorModelSpace (I := I) <|
          mulInvariantVectorField (I := I) (G := G) (v : GroupLieAlgebra I G) g) := by
      rw [← map_smul]
      apply congrArg A
      -- Compare the underlying tangent vectors before their definitional model-space conversion.
      change mulInvariantVectorField (I := I) (G := G)
          ((c • v : E) : GroupLieAlgebra I G) g =
        c • mulInvariantVectorField (I := I) (G := G) (v : GroupLieAlgebra I G) g
      have hparameter : ((c • v : E) : GroupLieAlgebra I G) =
          c • (v : GroupLieAlgebra I G) := rfl
      rw [hparameter]
      exact congrFun (mulInvariantVectorField_smul (I := I) (G := G)
        c (v : GroupLieAlgebra I G)) g

/-- At the identity coordinate, the parameterized invariant field equals its generator. -/
@[simp]
theorem mulInvariantCoordinateVectorField_one [IsManifold I 1 G] (v : E) :
    mulInvariantCoordinateVectorField (I := I) (G := G)
      (v, I (chartAt H (1 : G) (1 : G))) = v := by
  have hidentityCoordinate : I (chartAt H (1 : G) (1 : G)) =
      extChartAt I (1 : G) (1 : G) := by
    rfl
  rw [hidentityCoordinate]
  rw [mulInvariantCoordinateVectorField_apply]
  have hsymm : (extChartAt I (1 : G)).symm (extChartAt I (1 : G) (1 : G)) = 1 :=
    (extChartAt I (1 : G)).left_inv (mem_extChartAt_source (I := I) (1 : G))
  rw [hsymm]
  have hfieldOne : tangentVectorModelSpace (I := I)
      (mulInvariantVectorField (I := I) (G := G)
        (v : GroupLieAlgebra I G) 1) = v := by
    exact mulInvariantVectorField_one (I := I) (G := G) (v : GroupLieAlgebra I G)
  change tangentCoordChange I 1 1 1
      (tangentVectorModelSpace (I := I) <|
        mulInvariantVectorField (I := I) (G := G) (v : GroupLieAlgebra I G) 1) = v
  rw [hfieldOne]
  exact tangentCoordChange_self (mem_extChartAt_source (I := I) (1 : G))

/-- The invariant coordinate field vanishes when its generating vector vanishes. -/
@[simp]
theorem mulInvariantCoordinateVectorField_zero [IsManifold I 1 G] (y : E) :
    mulInvariantCoordinateVectorField (I := I) (G := G) (0, y) = 0 := by
  simpa using mulInvariantCoordinateVectorField_smul
    (I := I) (G := G) (0 : ℝ) (0 : E) y

/-- The coordinate expression of the parameterized left-invariant vector field is `C^n` at every
generating vector over the identity coordinate when multiplication is `C^(n + 1)`. -/
theorem contDiffAt_mulInvariantCoordinateVectorField (v : E) {n : ℕ∞ω}
    [ContMDiffMul I (n + 1) G] (h1 : I.IsInteriorPoint (1 : G)) :
    let _ : IsManifold I 1 G := IsManifold.of_le (n := n + 1) le_add_self
    ContDiffAt ℝ n (mulInvariantCoordinateVectorField (I := I) (G := G))
      (v, extChartAt I (1 : G) (1 : G)) := by
  let _ : IsManifold I 1 G := IsManifold.of_le (n := n + 1) le_add_self
  dsimp only
  let V : E × G → TangentBundle I G := fun p =>
    ⟨p.2, mulInvariantVectorField (I := I) (G := G) p.1 p.2⟩
  have hV : ContMDiff (𝓘(ℝ, E).prod I) I.tangent n V :=
    contMDiff_mulInvariantVectorField_modelSpace (m := n) (n := n + 1) le_rfl
  have hV₀ := hV.contMDiffAt (x := (v, (1 : G)))
  rw [contMDiffAt_iff] at hV₀
  have hv1 : (𝓘(ℝ, E).prod I).IsInteriorPoint (v, (1 : G)) := by
    -- `ModelWithCorners.interior_prod` is stated for membership in `interior`; unfold
    -- `IsInteriorPoint` to expose precisely that representation.
    change (v, (1 : G)) ∈ (𝓘(ℝ, E).prod I).interior (E × G)
    rw [ModelWithCorners.interior_prod]
    exact ⟨BoundarylessManifold.isInteriorPoint, h1⟩
  have h := hV₀.2.contDiffAt
    (range_mem_nhds_isInteriorPoint hv1)
  let w : E × E → E := fun x =>
    ((extChartAt I.tangent (V (v, 1)) ∘ V ∘
      (extChartAt (𝓘(ℝ, E).prod I) (v, 1)).symm) x).2
  have hw_apply (p : E × E) :
      w p = tangentCoordChange I ((extChartAt I (1 : G)).symm p.2) (1 : G)
        ((extChartAt I (1 : G)).symm p.2)
        (tangentVectorModelSpace (I := I) <|
          mulInvariantVectorField (I := I) (G := G)
            (p.1 : GroupLieAlgebra I G) ((extChartAt I (1 : G)).symm p.2)) := by
    -- This is the defining second coordinate of the tangent-bundle extended chart. Keeping the
    -- implementation-level conversion here prevents its definitional equality from leaking into
    -- the regularity argument below.
    change tangentCoordChange I ((extChartAt I (1 : G)).symm p.2) (1 : G)
      ((extChartAt I (1 : G)).symm p.2)
        (tangentVectorModelSpace (I := I) <|
          mulInvariantVectorField (I := I) (G := G)
            (p.1 : GroupLieAlgebra I G) ((extChartAt I (1 : G)).symm p.2)) = _
    rfl
  have hw : w = mulInvariantCoordinateVectorField (I := I) (G := G) := by
    funext p
    rw [mulInvariantCoordinateVectorField_apply]
    exact hw_apply p
  rw [← hw]
  simpa only [w, extChartAt_prod, extChartAt_self_apply, modelWithCornersSelf_coe,
    PartialEquiv.prod_coe, PartialEquiv.refl_coe, id_eq] using h.snd

/-- At a fixed identity-chart coordinate, the invariant coordinate field as a continuous linear
map of its generating model vector. -/
noncomputable def mulInvariantCoordinateLinearMap [IsManifold I 1 G] (y : E) : E →L[ℝ] E :=
  let g := (extChartAt I (1 : G)).symm y
  (tangentCoordChange I g (1 : G) g).comp
    (mfderiv I I (fun x : G => g * x) (1 : G))

/-- Applying the coordinate-field linear map recovers the parameterized coordinate vector field. -/
@[simp]
theorem mulInvariantCoordinateLinearMap_apply [IsManifold I 1 G] (y v : E) :
    mulInvariantCoordinateLinearMap (I := I) (G := G) y v =
      mulInvariantCoordinateVectorField (I := I) (G := G) (v, y) := by
  rfl

/-- At the identity coordinate, the coordinate-field linear map is the identity operator. -/
@[simp]
theorem mulInvariantCoordinateLinearMap_one [IsManifold I 1 G] :
    mulInvariantCoordinateLinearMap (I := I) (G := G)
      (I (chartAt H (1 : G) (1 : G))) = ContinuousLinearMap.id ℝ E := by
  apply ContinuousLinearMap.ext
  intro v
  rw [mulInvariantCoordinateLinearMap_apply, ContinuousLinearMap.id_apply]
  exact mulInvariantCoordinateVectorField_one (I := I) (G := G) v

/-- In finite dimensions, the coordinate-field linear map is `C^n` at the identity coordinate. -/
theorem contDiffAt_mulInvariantCoordinateLinearMap_one {n : ℕ∞ω}
    [FiniteDimensional ℝ E] [ContMDiffMul I (n + 1) G] (h1 : I.IsInteriorPoint (1 : G)) :
    let _ : IsManifold I 1 G := IsManifold.of_le (n := n + 1) le_add_self
    ContDiffAt ℝ n (mulInvariantCoordinateLinearMap (I := I) (G := G))
      (extChartAt I (1 : G) (1 : G)) := by
  let _ : IsManifold I 1 G := IsManifold.of_le (n := n + 1) le_add_self
  dsimp only
  let d := Module.finrank ℝ E
  let e₁ : E ≃L[ℝ] Fin d → ℝ :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let e₂ : (E →L[ℝ] E) ≃L[ℝ] Fin d → E :=
    (e₁.arrowCongr (ContinuousLinearEquiv.refl ℝ E)).trans
      (ContinuousLinearEquiv.piRing (Fin d))
  rw [← e₂.comp_contDiffAt_iff]
  apply contDiffAt_pi'
  intro i
  let b : E := e₁.symm (Pi.single i 1)
  have h := (contDiffAt_mulInvariantCoordinateVectorField (I := I) (G := G) (v := b)
    (n := n) h1).comp
    (extChartAt I (1 : G) (1 : G)) (contDiffAt_const.prodMk contDiffAt_id)
  convert h using 1
  funext y
  simp [e₂, b, ContinuousLinearEquiv.piRing, mulInvariantCoordinateLinearMap_apply,
    ContinuousLinearEquiv.refl_apply]

/-- At the zero generating vector over the identity coordinate, the parameterized coordinate
vector field has strict derivative equal to projection onto the generating-vector coordinate. -/
theorem hasStrictFDerivAt_mulInvariantCoordinateVectorField_zero_one
    [FiniteDimensional ℝ E] [ContMDiffMul I (1 + 1) G]
    (h1 : I.IsInteriorPoint (1 : G)) :
    let _ : IsManifold I 1 G := IsManifold.of_le (n := 1 + 1) (by norm_num)
    HasStrictFDerivAt (mulInvariantCoordinateVectorField (I := I) (G := G))
      (ContinuousLinearMap.fst ℝ E E)
      ((0 : E), extChartAt I (1 : G) (1 : G)) := by
  let _ : IsManifold I 1 G := IsManifold.of_le (n := 1 + 1) (by norm_num)
  dsimp only
  let A : E → E →L[ℝ] E := mulInvariantCoordinateLinearMap (I := I) (G := G)
  let p : E × E := ((0 : E), extChartAt I (1 : G) (1 : G))
  have hAcd : ContDiffAt ℝ 1 (fun q : E × E => A q.2) p :=
    ContDiffAt.fun_comp p
      (contDiffAt_mulInvariantCoordinateLinearMap_one (I := I) (G := G) (n := 1)
        h1) contDiffAt_snd
  have hA : DifferentiableAt ℝ (fun q : E × E => A q.2) p :=
    hAcd.differentiableAt one_ne_zero
  have h := hA.hasFDerivAt.clm_apply (hasFDerivAt_fst (p := p))
  have hfield : mulInvariantCoordinateVectorField (I := I) (G := G) =
      fun q : E × E => (A q.2) q.1 := by
    funext q
    exact (mulInvariantCoordinateLinearMap_apply (I := I) (G := G) q.2 q.1).symm
  have hderiv : HasFDerivAt (mulInvariantCoordinateVectorField (I := I) (G := G))
      (ContinuousLinearMap.fst ℝ E E) p := by
    rw [hfield]
    apply h.congr_fderiv
    apply ContinuousLinearMap.ext
    rintro ⟨q₁, q₂⟩
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      p, map_zero, A, add_zero]
    have hidentityCoordinate : extChartAt I (1 : G) (1 : G) =
        I (chartAt H (1 : G) (1 : G)) := by
      rw [extChartAt_coe]
      rfl
    rw [hidentityCoordinate]
    rw [mulInvariantCoordinateLinearMap_one]
    rfl
  exact (contDiffAt_mulInvariantCoordinateVectorField (I := I) (G := G) (v := 0) (n := 1)
    h1).hasStrictFDerivAt' hderiv one_ne_zero

/-- Near the zero tangent vector and the identity coordinate, the parameterized invariant ODE has
a single solution family that is continuous jointly in its initial condition and time and
uniformly Lipschitz in its initial state. The tangent-vector coordinate is frozen by the ODE; the
second coordinate follows the invariant vector field. -/
theorem exists_lipschitzOn_local_mulInvariantCoordinateFlow
    [CompleteSpace E] [ContMDiffMul I (1 + 1) G] (h1 : I.IsInteriorPoint (1 : G)) :
    let _ : IsManifold I 1 G := IsManifold.of_le (n := 1 + 1) (by norm_num)
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
  let _ : IsManifold I 1 G := IsManifold.of_le (n := 1 + 1) (by norm_num)
  dsimp only
  let center : E × E := (0, extChartAt I (1 : G) (1 : G))
  let F : E × E → E × E := fun p =>
    (0, mulInvariantCoordinateVectorField (I := I) (G := G) p)
  have hF : ContDiffAt ℝ 1 F center := by
    exact contDiffAt_const.prodMk
      (contDiffAt_mulInvariantCoordinateVectorField (v := 0) (n := 1) h1)
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
      have hβ_def : β =
          (ContinuousLinearMap.fst ℝ E E) ∘ fun s => α' (x, s) := by
        rfl
      rw [hβ_def]
      simpa using (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivWithinAt t
        ((hα' x hx').2 t ht)
    have hconst := constant_of_derivWithin_zero
      (fun t ht => (hβ t ht).differentiableWithinAt)
      (fun t ht => (hβ t (Set.Ico_subset_Icc_self ht)).derivWithin
        ((uniqueDiffOn_Icc (by linarith)).uniqueDiffWithinAt
          (Set.Ico_subset_Icc_self ht)))
    intro t ht
    have hzero : (0 : ℝ) ∈ Set.Icc (-δ) δ := by constructor <;> linarith
    have hβeq : β t = x.1 := (hconst t ht).trans ((hconst 0 hzero).symm.trans
      (congrArg Prod.fst (hα' x hx').1))
    simpa only [β] using hβeq

/-- There is a coordinate solution family near the zero tangent vector and time zero which is
continuous at the center, solves the parameterized invariant ODE with an ordinary derivative,
freezes the tangent-vector parameter, and remains in the target of the identity chart. -/
theorem exists_eventually_hasDerivAt_mulInvariantCoordinateFlow
    [CompleteSpace E] [ContMDiffMul I (1 + 1) G] (h1 : I.IsInteriorPoint (1 : G)) :
    let _ : IsManifold I 1 G := IsManifold.of_le (n := 1 + 1) (by norm_num)
    ∃ α : (E × E) × ℝ → E × E,
      (∀ᶠ xt in 𝓝 (((0 : E), extChartAt I (1 : G) (1 : G)), 0),
        ContinuousAt α xt) ∧
      ∀ᶠ xt in 𝓝 (((0 : E), extChartAt I (1 : G) (1 : G)), 0),
        HasDerivAt (fun t => α (xt.1, t))
          ((0 : E),
            mulInvariantCoordinateVectorField (I := I) (G := G) (α xt)) xt.2 ∧
        α (xt.1, 0) = xt.1 ∧
        (α xt).1 = xt.1.1 ∧
        (α xt).2 ∈ interior (extChartAt I (1 : G)).target := by
  let _ : IsManifold I 1 G := IsManifold.of_le (n := 1 + 1) (by norm_num)
  dsimp only
  obtain ⟨α, δ, r, _, hδ, hr, hcont, _, hα⟩ :=
    exists_lipschitzOn_local_mulInvariantCoordinateFlow
      (I := I) (G := G) h1
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
    exact I.isInteriorPoint_iff.mp h1
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
  refine ⟨α, by simpa only [center] using hcontNear, ?_⟩
  filter_upwards [hdomainOpen, htarget] with xt hxt hxtTarget
  have hx := Metric.ball_subset_closedBall hxt.1
  have ht : xt.2 ∈ Set.Icc (-δ) δ := Set.Ioo_subset_Icc_self hxt.2
  have hderiv := (hα xt.1 hx).2.1 xt.2 ht
  refine ⟨hderiv.hasDerivAt (Icc_mem_nhds hxt.2.1 hxt.2.2),
    (hα xt.1 hx).1, (hα xt.1 hx).2.2 xt.2 ht, ?_⟩
  exact (Set.mem_preimage.mp hxtTarget).2

/-- A single coordinate solution family solves the invariant coordinate ODE and represents the
canonical invariant integral curves for every sufficiently small generating vector and every
sufficiently small time. This bridges Picard--Lindelöf's parameterized model-space solutions to the
canonical manifold-valued curves used to define `lieExp`. -/
theorem exists_local_coordinate_representation_mulInvariantIntegralCurve
    [CompleteSpace E] [LieGroup I (minSmoothness ℝ 3) G]
    [T2Space G] [BoundarylessManifold I G] :
    ∃ (α : (E × E) × ℝ → E × E) (U : Set E) (δ : ℝ),
      U ∈ 𝓝 (0 : E) ∧ 0 < δ ∧
      (∀ v ∈ U, ∀ t ∈ Set.Ioo (-δ) δ,
        ContinuousAt α ((v, extChartAt I (1 : G) (1 : G)), t) ∧
          HasDerivAt
            (fun s => α (((v, extChartAt I (1 : G) (1 : G)), s)))
            ((0 : E), mulInvariantCoordinateVectorField (I := I) (G := G)
              (α (((v, extChartAt I (1 : G) (1 : G)), t)))) t ∧
          α (((v, extChartAt I (1 : G) (1 : G)), 0)) =
            (v, extChartAt I (1 : G) (1 : G)) ∧
          (α (((v, extChartAt I (1 : G) (1 : G)), t))).1 = v ∧
          (α (((v, extChartAt I (1 : G) (1 : G)), t))).2 ∈
            interior (extChartAt I (1 : G)).target) ∧
      ∀ v ∈ U,
        Set.EqOn
          (fun t => (extChartAt I (1 : G)).symm
            (α (((v, extChartAt I (1 : G) (1 : G)), t))).2)
          (mulInvariantIntegralCurve (I := I) (G := G)
            (v : GroupLieAlgebra I G) 1)
          (Set.Ioo (-δ) δ) := by
  let _ : ContMDiffMul I (1 + 1) G :=
    ContMDiffMul.of_le (m := 1 + 1) (n := minSmoothness ℝ 3) (by norm_num)
  let _ : IsManifold I 1 G := IsManifold.of_le (n := minSmoothness ℝ 3) (by norm_num)
  obtain ⟨α, hαcontNear, hα⟩ :=
    exists_eventually_hasDerivAt_mulInvariantCoordinateFlow (I := I) (G := G)
      BoundarylessManifold.isInteriorPoint
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
  refine ⟨α, U, δ, hU, hδ, ?_, ?_⟩
  · intro v hv t ht
    have hmem : (v, t) ∈ U ×ˢ T := ⟨hv, hδT ht⟩
    simpa only [embed, Set.mem_ofPred_eq, Prod.fst, Prod.snd] using hsub hmem
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
    exact (hsub hmem).2
  have hγAt : ∀ t ∈ Set.Ioo (-δ) δ,
      IsMIntegralCurveAt γ
        (mulInvariantVectorField (I := I) (G := G) (v : GroupLieAlgebra I G)) t := by
    intro t ht
    apply IsMIntegralCurveAt.of_extChartAt_symm
    · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact (hlocal s hs).2.2.2
    · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      have hsnd : HasDerivAt f
          (mulInvariantCoordinateVectorField (I := I) (G := G)
            (α (((v, extChartAt I (1 : G) (1 : G)), s)))) s := by
        have hf_def : f = (ContinuousLinearMap.snd ℝ E E) ∘ fun u =>
            α (((v, extChartAt I (1 : G) (1 : G)), u)) := by
          rfl
        rw [hf_def]
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
    have hγ_def : γ 0 = (extChartAt I (1 : G)).symm
        (α (((v, extChartAt I (1 : G) (1 : G)), 0))).2 := by
      rfl
    rw [hγ_def]
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
    [CompleteSpace E] [LieGroup I (minSmoothness ℝ 3) G]
    [T2Space G] [BoundarylessManifold I G] :
    ContinuousAt
      (fun v : E => mulInvariantExp (I := I) (G := G) v) 0 := by
  let _ : ContMDiffMul I (1 + 1) G :=
    ContMDiffMul.of_le (m := 1 + 1) (n := minSmoothness ℝ 3) (by norm_num)
  let _ : IsManifold I 1 G := IsManifold.of_le (n := minSmoothness ℝ 3) (by norm_num)
  obtain ⟨α, U, δ, hU, hδ, hαlocal, hαeq⟩ :=
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
  have htarget := Set.mem_of_mem_of_subset (hαlocal 0 hzeroU c hc).2.2.2.2 interior_subset
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
