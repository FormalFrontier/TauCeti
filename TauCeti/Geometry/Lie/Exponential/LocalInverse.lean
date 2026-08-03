/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import TauCeti.Geometry.Lie.Exponential.Derivative
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
/-!
# Local inverse of the Lie-group exponential

The smooth coordinate exponential has derivative the identity at zero, so the inverse function
theorem supplies a smooth local logarithm in model-space identity coordinates.

Transporting that logarithm through the identity chart gives a group-valued local inverse for the
tangent-space exponential.

## Main results

* `mulInvariantLog`: the canonical local logarithm from the group to its tangent Lie algebra.
* `eventually_mulInvariantExp_log`: exponential followed after logarithm is locally the identity.
* `isLocalDiffeomorphAt_mulInvariantExpModelSpace_zero`: the coordinate exponential is a local
  diffeomorphism at zero.
* `exists_injOn_mulInvariantExp_modelSpace`: exponential is injective near zero.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The exponential map".
-/
public section
open Function Manifold
open scoped ContDiff Manifold Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [IsManifold I 1 G]
local instance lieGroupMinSmoothnessLocalInverse [LieGroup I ∞ G] :
    LieGroup I (minSmoothness ℝ 3) G := by
  simpa using (inferInstance : LieGroup I (3 : ℕ∞ω) G)
/-- The tangent-space exponential expressed in model-space identity coordinates. -/
@[expose]
noncomputable def mulInvariantExpModelSpace [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] (v : E) : E := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact extChartAt I (1 : G)
    (mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G))
/-- The coordinate exponential sends zero to the identity coordinate. -/
@[simp]
theorem mulInvariantExpModelSpace_zero [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    mulInvariantExpModelSpace (I := I) (G := G) 0 =
      extChartAt I (1 : G) (1 : G) := by
  change extChartAt I (1 : G)
    (mulInvariantExp (I := I) (G := G) (0 : GroupLieAlgebra I G)) = _
  rw [mulInvariantExp_zero]
/-- The coordinate exponential is smooth at zero. -/
theorem contDiffAt_mulInvariantExpModelSpace_zero [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    ContDiffAt ℝ ∞ (mulInvariantExpModelSpace (I := I) (G := G)) 0 := by
  rw [show mulInvariantExpModelSpace (I := I) (G := G) =
      fun v : E => extChartAt I (1 : G)
        (mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G)) by
    funext v
    rw [mulInvariantExpModelSpace]]
  exact contDiffAt_mulInvariantExp_modelSpace_zero (I := I) (G := G)
/-- The coordinate exponential has derivative the identity at zero. -/
theorem hasFDerivAt_mulInvariantExpModelSpace_zero [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    HasFDerivAt (mulInvariantExpModelSpace (I := I) (G := G))
      (ContinuousLinearMap.id ℝ E) 0 := by
  rw [show mulInvariantExpModelSpace (I := I) (G := G) =
      fun v : E => extChartAt I (1 : G)
        (mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G)) by
    funext v
    rw [mulInvariantExpModelSpace]]
  exact hasFDerivAt_mulInvariantExp_modelSpace_zero (I := I) (G := G)
/-- The coordinate exponential on the canonical neighborhoods selected by the inverse function
theorem. -/
@[expose]
noncomputable def mulInvariantExpLocalHomeomorph [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] : OpenPartialHomeomorph E E := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let h' : HasFDerivAt (mulInvariantExpModelSpace (I := I) (G := G))
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) 0 := by
    simpa using hasFDerivAt_mulInvariantExpModelSpace_zero (I := I) (G := G)
  exact (contDiffAt_mulInvariantExpModelSpace_zero (I := I) (G := G))
    |>.toOpenPartialHomeomorph _ h' (by simp)
/-- The local homeomorphism agrees with the coordinate exponential. -/
@[simp]
theorem mulInvariantExpLocalHomeomorph_apply [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] (v : E) :
    mulInvariantExpLocalHomeomorph (I := I) (G := G) v =
      mulInvariantExpModelSpace (I := I) (G := G) v := by
  unfold mulInvariantExpLocalHomeomorph
  rfl

/-- Zero belongs to the source of the local coordinate exponential. -/
theorem zero_mem_mulInvariantExpLocalHomeomorph_source [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    0 ∈ (mulInvariantExpLocalHomeomorph (I := I) (G := G)).source := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let h' : HasFDerivAt (mulInvariantExpModelSpace (I := I) (G := G))
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) 0 := by
    simpa using hasFDerivAt_mulInvariantExpModelSpace_zero (I := I) (G := G)
  exact (contDiffAt_mulInvariantExpModelSpace_zero (I := I) (G := G))
    |>.mem_toOpenPartialHomeomorph_source h' (by simp)

/-- The identity coordinate belongs to the target of the local coordinate exponential. -/
theorem identity_mem_mulInvariantExpLocalHomeomorph_target [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    extChartAt I (1 : G) (1 : G) ∈
      (mulInvariantExpLocalHomeomorph (I := I) (G := G)).target := by
  rw [← mulInvariantExpModelSpace_zero (I := I) (G := G)]
  exact (mulInvariantExpLocalHomeomorph (I := I) (G := G)).map_source
    zero_mem_mulInvariantExpLocalHomeomorph_source

/-- The canonical local logarithm in model-space identity coordinates. -/
@[expose]
noncomputable def mulInvariantLogModelSpace [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] : E → E :=
  (mulInvariantExpLocalHomeomorph (I := I) (G := G)).symm

/-- The coordinate logarithm sends the identity coordinate to zero. -/
@[simp]
theorem mulInvariantLogModelSpace_identity [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    mulInvariantLogModelSpace (I := I) (G := G)
      (I (chartAt H (1 : G) (1 : G))) = 0 := by
  change mulInvariantLogModelSpace (I := I) (G := G)
    (extChartAt I (1 : G) (1 : G)) = 0
  rw [← mulInvariantExpModelSpace_zero (I := I) (G := G)]
  exact (mulInvariantExpLocalHomeomorph (I := I) (G := G)).left_inv
    zero_mem_mulInvariantExpLocalHomeomorph_source

/-- Locally around zero, logarithm is a left inverse to the coordinate exponential. -/
theorem eventually_mulInvariantLogModelSpace_exp [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    ∀ᶠ v in 𝓝 (0 : E),
      mulInvariantLogModelSpace (I := I) (G := G)
        (mulInvariantExpModelSpace (I := I) (G := G) v) = v :=
  (mulInvariantExpLocalHomeomorph (I := I) (G := G)).eventually_left_inverse
    zero_mem_mulInvariantExpLocalHomeomorph_source

/-- Locally around the identity coordinate, exponential is a left inverse to logarithm. -/
theorem eventually_mulInvariantExpModelSpace_log [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    ∀ᶠ y in 𝓝 (extChartAt I (1 : G) (1 : G)),
      mulInvariantExpModelSpace (I := I) (G := G)
        (mulInvariantLogModelSpace (I := I) (G := G) y) = y := by
  rw [← mulInvariantExpModelSpace_zero (I := I) (G := G)]
  exact (mulInvariantExpLocalHomeomorph (I := I) (G := G)).eventually_right_inverse'
    zero_mem_mulInvariantExpLocalHomeomorph_source

/-- The coordinate logarithm is smooth at the identity coordinate. -/
theorem contDiffAt_mulInvariantLogModelSpace_identity [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    ContDiffAt ℝ ∞ (mulInvariantLogModelSpace (I := I) (G := G))
      (extChartAt I (1 : G) (1 : G)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let φ := mulInvariantExpLocalHomeomorph (I := I) (G := G)
  change ContDiffAt ℝ ∞ φ.symm (extChartAt I (1 : G) (1 : G))
  have hpre : φ.symm (extChartAt I (1 : G) (1 : G)) = 0 := by
    exact mulInvariantLogModelSpace_identity (I := I) (G := G)
  have hφ : (φ : E → E) = mulInvariantExpModelSpace (I := I) (G := G) := by
    funext v
    exact mulInvariantExpLocalHomeomorph_apply (I := I) (G := G) v
  apply φ.contDiffAt_symm (f₀' := ContinuousLinearEquiv.refl ℝ E)
    identity_mem_mulInvariantExpLocalHomeomorph_target
  · rw [hpre, hφ]
    simpa using hasFDerivAt_mulInvariantExpModelSpace_zero (I := I) (G := G)
  · rw [hpre, hφ]
    exact contDiffAt_mulInvariantExpModelSpace_zero (I := I) (G := G)

/-- The local logarithm of a group element, valued in the tangent Lie algebra at the identity. It
is the coordinate logarithm transported back from the manifold model space. -/
noncomputable def mulInvariantLog [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] (g : G) : GroupLieAlgebra I G := by
  change E
  exact mulInvariantLogModelSpace (I := I) (G := G) (extChartAt I (1 : G) g)

/-- The group-valued local logarithm is the coordinate logarithm after applying the identity
chart. -/
theorem mulInvariantLog_eq_modelSpace [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] (g : G) :
    (show E from mulInvariantLog (I := I) (G := G) g) =
      mulInvariantLogModelSpace (I := I) (G := G) (extChartAt I (1 : G) g) := by
  rfl

/-- The local logarithm sends the group identity to the zero tangent vector. -/
@[simp]
theorem mulInvariantLog_one [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    mulInvariantLog (I := I) (G := G) (1 : G) = 0 := by
  change (show E from mulInvariantLog (I := I) (G := G) (1 : G)) = 0
  rw [mulInvariantLog_eq_modelSpace]
  change mulInvariantLogModelSpace (I := I) (G := G)
    (I (chartAt H (1 : G) (1 : G))) = 0
  exact mulInvariantLogModelSpace_identity (I := I) (G := G)

/-- Locally around the identity, exponentiating the local logarithm recovers the original group
element. -/
theorem eventually_mulInvariantExp_log [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    ∀ᶠ g in 𝓝 (1 : G),
      mulInvariantExp (I := I) (G := G) (mulInvariantLog (I := I) (G := G) g) = g := by
  let F : E → E := mulInvariantExpModelSpace (I := I) (G := G)
  let L : E → E := mulInvariantLogModelSpace (I := I) (G := G)
  have hFL : ∀ᶠ y in 𝓝 (extChartAt I (1 : G) (1 : G)), F (L y) = y := by
    simpa only [F, L] using eventually_mulInvariantExpModelSpace_log (I := I) (G := G)
  have hchartFL : ∀ᶠ g in 𝓝 (1 : G), F (L (extChartAt I (1 : G) g)) =
      extChartAt I (1 : G) g :=
    (continuousAt_extChartAt (I := I) (1 : G)).tendsto.eventually hFL
  have hlogCont : ContinuousAt (fun g : G => L (extChartAt I (1 : G) g)) 1 :=
    (contDiffAt_mulInvariantLogModelSpace_identity (I := I) (G := G)).continuousAt.comp
      (continuousAt_extChartAt (I := I) (1 : G))
  have hlogOne : L (extChartAt I (1 : G) (1 : G)) = 0 := by
    change mulInvariantLogModelSpace (I := I) (G := G)
      (I (chartAt H (1 : G) (1 : G))) = 0
    exact mulInvariantLogModelSpace_identity (I := I) (G := G)
  have hexpCont : ContinuousAt
      (fun g : G => mulInvariantExp (I := I) (G := G)
        (L (extChartAt I (1 : G) g) : GroupLieAlgebra I G)) 1 :=
    (continuousAt_mulInvariantExp_modelSpace_zero (I := I) (G := G)).comp_of_eq
      hlogCont hlogOne
  have hexpOne :
      mulInvariantExp (I := I) (G := G)
        (L (extChartAt I (1 : G) (1 : G)) : GroupLieAlgebra I G) = (1 : G) := by
    rw [hlogOne]
    change mulInvariantExp (I := I) (G := G) (0 : GroupLieAlgebra I G) = 1
    exact mulInvariantExp_zero (I := I) (G := G)
  have hexpSource : ∀ᶠ g in 𝓝 (1 : G),
      mulInvariantExp (I := I) (G := G)
          (L (extChartAt I (1 : G) g) : GroupLieAlgebra I G) ∈
        (extChartAt I (1 : G)).source :=
    hexpCont.preimage_mem_nhds
      (by simpa only [hexpOne] using extChartAt_source_mem_nhds (I := I) (1 : G))
  filter_upwards [hchartFL, hexpSource,
    extChartAt_source_mem_nhds (I := I) (1 : G)] with g hcoord hexp hg
  rw [mulInvariantLog]
  change mulInvariantExp (I := I) (G := G)
    (L (extChartAt I (1 : G) g) : GroupLieAlgebra I G) = g
  apply (extChartAt I (1 : G)).injOn hexp hg
  simpa only [F, mulInvariantExpModelSpace] using hcoord

/-- In model-space coordinates, the tangent-space exponential is injective on a neighborhood of
zero. -/
theorem exists_injOn_mulInvariantExp_modelSpace [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    ∃ U ∈ 𝓝 (0 : E), Set.InjOn
      (fun v : E => mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G)) U := by
  let φ := mulInvariantExpLocalHomeomorph (I := I) (G := G)
  refine ⟨φ.source, φ.open_source.mem_nhds
    zero_mem_mulInvariantExpLocalHomeomorph_source, ?_⟩
  intro x hx y hy hxy
  apply φ.injOn hx hy
  rw [mulInvariantExpLocalHomeomorph_apply, mulInvariantExpLocalHomeomorph_apply]
  exact congrArg (extChartAt I (1 : G)) hxy

/-- The coordinate exponential is a `C¹` local diffeomorphism at zero. Together with
`contMDiff_mulInvariantExp` and `contDiffAt_mulInvariantLogModelSpace_identity`, this packages the
local-diffeomorphism conclusion of the inverse function theorem for the smooth exponential. -/
theorem isLocalDiffeomorphAt_mulInvariantExpModelSpace_zero [FiniteDimensional ℝ E]
    [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1
      (mulInvariantExpModelSpace (I := I) (G := G)) 0 := by
  let φ := mulInvariantExpLocalHomeomorph (I := I) (G := G)
  obtain ⟨U, hUopen, hzeroU, hFU⟩ :=
    (contDiffAt_mulInvariantExpModelSpace_zero (I := I) (G := G)).contDiffOn'
      (m := (1 : ℕ∞ω)) (by simp) (by simp)
  obtain ⟨V, hVopen, hyV, hLV⟩ :=
    (contDiffAt_mulInvariantLogModelSpace_identity (I := I) (G := G)).contDiffOn'
      (m := (1 : ℕ∞ω)) (by simp) (by simp)
  have hFU' : ContDiffOn ℝ 1 (mulInvariantExpModelSpace (I := I) (G := G)) U := by
    simpa using hFU
  have hLV' : ContDiffOn ℝ 1 (mulInvariantLogModelSpace (I := I) (G := G)) V := by
    simpa using hLV
  let ψ : OpenPartialHomeomorph E E :=
    (φ.restrOpen U hUopen).trans (OpenPartialHomeomorph.ofSet V hVopen)
  have hzeroψ : (0 : E) ∈ ψ.source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · rw [OpenPartialHomeomorph.restrOpen_source]
      exact ⟨zero_mem_mulInvariantExpLocalHomeomorph_source (I := I) (G := G), hzeroU⟩
    · change φ 0 ∈ V
      rw [mulInvariantExpLocalHomeomorph_apply,
        mulInvariantExpModelSpace_zero]
      exact hyV
  let ψe : PartialEquiv E E := {
    toFun := mulInvariantExpModelSpace (I := I) (G := G)
    invFun := ψ.symm
    source := ψ.source
    target := ψ.target
    map_source' := by
      intro x hx
      exact ψ.map_source hx
    map_target' := by
      intro x hx
      exact ψ.map_target hx
    left_inv' := by
      intro x hx
      change ψ.symm (ψ x) = x
      exact ψ.left_inv hx
    right_inv' := by
      intro x hx
      change ψ (ψ.symm x) = x
      exact ψ.right_inv hx
  }
  let ψd : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E 1 := {
    toPartialEquiv := ψe
    open_source := ψ.open_source
    open_target := ψ.open_target
    contMDiffOn_toFun := by
      rw [contMDiffOn_iff_contDiffOn]
      apply hFU'.mono
      intro v hv
      rw [OpenPartialHomeomorph.trans_source] at hv
      exact hv.1.2
    contMDiffOn_invFun := by
      rw [contMDiffOn_iff_contDiffOn]
      apply hLV'.mono
      intro y hy
      rw [OpenPartialHomeomorph.trans_target] at hy
      exact hy.1
  }
  exact ψd.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1 hzeroψ
