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

Transporting that logarithm through the identity chart gives a group-level local inverse for the
tangent-space exponential.

## Main results

* `mulInvariantLog`: the canonical local logarithm from the group to its tangent Lie algebra.
* `eventually_mulInvariantExp_log`: exponential followed after logarithm is locally the identity.
* `eventually_mulInvariantLog_exp`: logarithm followed after exponential is locally the identity.
* `isLocalDiffeomorphAt_mulInvariantExpChart_zero`: the fully charted exponential is a local
  diffeomorphism of every finite differentiability order at zero.
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

private theorem smoothOrder_ne_zero : (∞ : ℕ∞ω) ≠ 0 := by
  simp

/-- The tangent-space exponential with both domain and codomain expressed in identity-chart
coordinates. -/
noncomputable def mulInvariantExpChart [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] (v : E) : E := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact extChartAt I (1 : G)
    (mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G))

/-- The fully charted exponential is the identity chart applied to the tangent-space
exponential. -/
theorem mulInvariantExpChart_apply [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] (v : E) :
    mulInvariantExpChart (I := I) (G := G) v =
      extChartAt I (1 : G)
        (mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G)) := by
  rfl

/-- The fully charted exponential as a composition, for rewriting under higher-order
predicates. -/
private theorem mulInvariantExpChart_eq [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    mulInvariantExpChart (I := I) (G := G) = fun v : E =>
      extChartAt I (1 : G)
        (mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G)) := by
  funext v
  exact mulInvariantExpChart_apply (I := I) (G := G) v

/-- The coordinate exponential sends zero to the identity coordinate. -/
@[simp]
theorem mulInvariantExpChart_zero [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    mulInvariantExpChart (I := I) (G := G) 0 =
      extChartAt I (1 : G) (1 : G) := by
  rw [mulInvariantExpChart_apply]
  -- `GroupLieAlgebra I G` is definitionally the model space `E`.
  change extChartAt I (1 : G)
    (mulInvariantExp (I := I) (G := G) (0 : GroupLieAlgebra I G)) = _
  rw [mulInvariantExp_zero]

/-- The coordinate exponential is smooth at zero. -/
theorem contDiffAt_mulInvariantExpChart_zero [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    ContDiffAt ℝ ∞ (mulInvariantExpChart (I := I) (G := G)) 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let f : E → G := fun v =>
    mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G)
  have hfzero : f 0 = 1 := by
    exact mulInvariantExp_zero (I := I) (G := G)
  have hsource : f 0 ∈ (chartAt H (1 : G)).source := by
    rw [hfzero]
    exact mem_chart_source H (1 : G)
  have hsmooth := contMDiffAt_mulInvariantExp_modelSpace_zero (I := I) (G := G)
  have hcoord :=
    (contMDiffAt_iff_target_of_mem_source (f := f) (y := (1 : G)) hsource).mp hsmooth
  rw [contMDiffAt_iff_contDiffAt] at hcoord
  rw [mulInvariantExpChart_eq]
  exact hcoord.2

/-- The coordinate exponential has derivative the identity at zero. -/
theorem hasFDerivAt_mulInvariantExpChart_zero [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    HasFDerivAt (mulInvariantExpChart (I := I) (G := G))
      (ContinuousLinearMap.id ℝ E) 0 := by
  rw [mulInvariantExpChart_eq]
  exact hasFDerivAt_extChartAt_mulInvariantExp_zero (I := I) (G := G)

/-- The derivative of the fully charted exponential at zero, packaged as a continuous linear
equivalence for the inverse function theorem. -/
private theorem hasFDerivAt_mulInvariantExpChart_zero_equiv [FiniteDimensional ℝ E]
    [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    HasFDerivAt (mulInvariantExpChart (I := I) (G := G))
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) 0 := by
  simpa using hasFDerivAt_mulInvariantExpChart_zero (I := I) (G := G)

/-- The fully charted exponential on the canonical neighborhoods selected by the inverse function
theorem. -/
noncomputable def mulInvariantExpOpenPartialHomeomorph [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] : OpenPartialHomeomorph E E := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact (contDiffAt_mulInvariantExpChart_zero (I := I) (G := G))
    |>.toOpenPartialHomeomorph _
      (hasFDerivAt_mulInvariantExpChart_zero_equiv (I := I) (G := G)) smoothOrder_ne_zero

/-- The local homeomorphism agrees with the coordinate exponential. -/
@[simp]
theorem mulInvariantExpOpenPartialHomeomorph_apply [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] (v : E) :
    mulInvariantExpOpenPartialHomeomorph (I := I) (G := G) v =
      mulInvariantExpChart (I := I) (G := G) v := by
  unfold mulInvariantExpOpenPartialHomeomorph
  rfl

/-- Zero belongs to the source of the local coordinate exponential. -/
theorem zero_mem_mulInvariantExpOpenPartialHomeomorph_source [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    0 ∈ (mulInvariantExpOpenPartialHomeomorph (I := I) (G := G)).source := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact (contDiffAt_mulInvariantExpChart_zero (I := I) (G := G))
    |>.mem_toOpenPartialHomeomorph_source
      (hasFDerivAt_mulInvariantExpChart_zero_equiv (I := I) (G := G)) smoothOrder_ne_zero

/-- The identity coordinate belongs to the target of the local coordinate exponential. -/
theorem identity_mem_mulInvariantExpOpenPartialHomeomorph_target [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    extChartAt I (1 : G) (1 : G) ∈
      (mulInvariantExpOpenPartialHomeomorph (I := I) (G := G)).target := by
  rw [← mulInvariantExpChart_zero (I := I) (G := G)]
  exact (mulInvariantExpOpenPartialHomeomorph (I := I) (G := G)).map_source
    zero_mem_mulInvariantExpOpenPartialHomeomorph_source

/-- The canonical local logarithm with both domain and codomain in identity-chart coordinates. -/
noncomputable def mulInvariantLogChart [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] : E → E :=
  (mulInvariantExpOpenPartialHomeomorph (I := I) (G := G)).symm

/-- The fully charted logarithm is the inverse of the canonical local homeomorphism. -/
theorem mulInvariantLogChart_apply [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] (y : E) :
    mulInvariantLogChart (I := I) (G := G) y =
      (mulInvariantExpOpenPartialHomeomorph (I := I) (G := G)).symm y := by
  rfl

/- This private wrapper gives a stable name to Mathlib's inverse-function-theorem local inverse. -/
private noncomputable def mulInvariantLogLocalInverse [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] : E → E := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact (contDiffAt_mulInvariantExpChart_zero (I := I) (G := G)).localInverse
    (hasFDerivAt_mulInvariantExpChart_zero_equiv (I := I) (G := G)) smoothOrder_ne_zero

/- The logarithm chosen through the local homeomorphism is exactly Mathlib's named local inverse.
The `rfl` proof relies on the definitional identity between `ContDiffAt.localInverse` and the
inverse of `ContDiffAt.toOpenPartialHomeomorph`; Mathlib currently has no public lemma for this
bridge. -/
private theorem mulInvariantLogChart_eq_localInverse [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    mulInvariantLogChart (I := I) (G := G) =
      mulInvariantLogLocalInverse (I := I) (G := G) := by
  rfl

/-- The coordinate logarithm sends the identity coordinate to zero. -/
@[simp]
theorem mulInvariantLogChart_identity [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    mulInvariantLogChart (I := I) (G := G)
      (I (chartAt H (1 : G) (1 : G))) = 0 := by
  have hcoord := congrFun (extChartAt_coe (I := I) (1 : G)) (1 : G)
  simp only [Function.comp_apply] at hcoord
  rw [← hcoord]
  rw [← mulInvariantExpChart_zero (I := I) (G := G)]
  exact (mulInvariantExpOpenPartialHomeomorph (I := I) (G := G)).left_inv
    zero_mem_mulInvariantExpOpenPartialHomeomorph_source

/-- Locally around zero, logarithm is a left inverse to the coordinate exponential. -/
theorem eventually_mulInvariantLogChart_exp [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    ∀ᶠ v in 𝓝 (0 : E),
      mulInvariantLogChart (I := I) (G := G)
        (mulInvariantExpChart (I := I) (G := G) v) = v :=
  (mulInvariantExpOpenPartialHomeomorph (I := I) (G := G)).eventually_left_inverse
    zero_mem_mulInvariantExpOpenPartialHomeomorph_source

/-- Locally around the identity coordinate, exponential is a left inverse to logarithm. -/
theorem eventually_mulInvariantExpChart_log [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    ∀ᶠ y in 𝓝 (extChartAt I (1 : G) (1 : G)),
      mulInvariantExpChart (I := I) (G := G)
        (mulInvariantLogChart (I := I) (G := G) y) = y := by
  rw [← mulInvariantExpChart_zero (I := I) (G := G)]
  exact (mulInvariantExpOpenPartialHomeomorph (I := I) (G := G)).eventually_right_inverse'
    zero_mem_mulInvariantExpOpenPartialHomeomorph_source

/-- The coordinate logarithm is smooth at the identity coordinate. -/
theorem contDiffAt_mulInvariantLogChart_identity [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    ContDiffAt ℝ ∞ (mulInvariantLogChart (I := I) (G := G))
      (extChartAt I (1 : G) (1 : G)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let hf := contDiffAt_mulInvariantExpChart_zero (I := I) (G := G)
  rw [mulInvariantLogChart_eq_localInverse]
  unfold mulInvariantLogLocalInverse
  simpa only [mulInvariantExpChart_zero] using hf.to_localInverse
    (hasFDerivAt_mulInvariantExpChart_zero_equiv (I := I) (G := G)) smoothOrder_ne_zero

/-- The local logarithm of a group element, valued in the tangent Lie algebra at the identity. It
is the coordinate logarithm transported back from the manifold model space. -/
noncomputable def mulInvariantLog [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] (g : G) : GroupLieAlgebra I G := by
  -- `GroupLieAlgebra I G` is definitionally the model space `E`.
  change E
  exact mulInvariantLogChart (I := I) (G := G) (extChartAt I (1 : G) g)

/-- The group-level local logarithm is the coordinate logarithm after applying the identity
chart. -/
theorem mulInvariantLog_eq_chart [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] (g : G) :
    (show E from mulInvariantLog (I := I) (G := G) g) =
      mulInvariantLogChart (I := I) (G := G) (extChartAt I (1 : G) g) := by
  rfl

/-- Locally around zero, taking the local logarithm after exponentiating recovers the original
tangent vector. -/
theorem eventually_mulInvariantLog_exp [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    ∀ᶠ v in 𝓝 (0 : E),
      (show E from mulInvariantLog (I := I) (G := G)
        (mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G))) = v := by
  refine (eventually_mulInvariantLogChart_exp (I := I) (G := G)).mono ?_
  intro v hv
  rw [mulInvariantLog_eq_chart]
  exact hv

/-- The local logarithm sends the group identity to the zero tangent vector. -/
@[simp]
theorem mulInvariantLog_one [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    mulInvariantLog (I := I) (G := G) (1 : G) = 0 := by
  -- `GroupLieAlgebra I G` is definitionally the model space `E`; the bridge lemma below then
  -- performs the substantive rewrite.
  change (show E from mulInvariantLog (I := I) (G := G) (1 : G)) = 0
  rw [mulInvariantLog_eq_chart]
  exact mulInvariantLogChart_identity (I := I) (G := G)

/-- Locally around the identity, exponentiating the local logarithm recovers the original group
element. -/
theorem eventually_mulInvariantExp_log [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    ∀ᶠ g in 𝓝 (1 : G),
      mulInvariantExp (I := I) (G := G) (mulInvariantLog (I := I) (G := G) g) = g := by
  let F : E → E := mulInvariantExpChart (I := I) (G := G)
  let L : E → E := mulInvariantLogChart (I := I) (G := G)
  have hFL : ∀ᶠ y in 𝓝 (extChartAt I (1 : G) (1 : G)), F (L y) = y := by
    simpa only [F, L] using eventually_mulInvariantExpChart_log (I := I) (G := G)
  have hchartFL : ∀ᶠ g in 𝓝 (1 : G), F (L (extChartAt I (1 : G) g)) =
      extChartAt I (1 : G) g :=
    (continuousAt_extChartAt (I := I) (1 : G)).tendsto.eventually hFL
  have hlogCont : ContinuousAt (fun g : G => L (extChartAt I (1 : G) g)) 1 :=
    (contDiffAt_mulInvariantLogChart_identity (I := I) (G := G)).continuousAt.comp
      (continuousAt_extChartAt (I := I) (1 : G))
  have hlogOne : L (extChartAt I (1 : G) (1 : G)) = 0 := by
    simpa only [L, extChartAt_coe, Function.comp_apply] using
      mulInvariantLogChart_identity (I := I) (G := G)
  have hexpCont : ContinuousAt
      (fun g : G => mulInvariantExp (I := I) (G := G)
        (L (extChartAt I (1 : G) g) : GroupLieAlgebra I G)) 1 :=
    (continuousAt_mulInvariantExp_modelSpace_zero (I := I) (G := G)).comp_of_eq
      hlogCont hlogOne
  have hexpOne :
      mulInvariantExp (I := I) (G := G)
        (L (extChartAt I (1 : G) (1 : G)) : GroupLieAlgebra I G) = (1 : G) := by
    rw [hlogOne]
    exact mulInvariantExp_zero (I := I) (G := G)
  have hexpSource : ∀ᶠ g in 𝓝 (1 : G),
      mulInvariantExp (I := I) (G := G)
          (L (extChartAt I (1 : G) g) : GroupLieAlgebra I G) ∈
        (extChartAt I (1 : G)).source :=
    hexpCont.preimage_mem_nhds
      (by simpa only [hexpOne] using extChartAt_source_mem_nhds (I := I) (1 : G))
  filter_upwards [hchartFL, hexpSource,
    extChartAt_source_mem_nhds (I := I) (1 : G)] with g hcoord hexp hg
  -- Pass through the named group-to-chart bridge before comparing identity-chart coordinates.
  change mulInvariantExp (I := I) (G := G)
    (show E from mulInvariantLog (I := I) (G := G) g) = g
  rw [mulInvariantLog_eq_chart]
  apply (extChartAt I (1 : G)).injOn (by simpa only [L] using hexp) hg
  simpa only [F, L, mulInvariantExpChart_apply] using hcoord

/-- In model-space coordinates, the tangent-space exponential is injective on a neighborhood of
zero. -/
theorem exists_injOn_mulInvariantExp_modelSpace [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    ∃ U ∈ 𝓝 (0 : E), Set.InjOn
      (fun v : E => mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G)) U := by
  let φ := mulInvariantExpOpenPartialHomeomorph (I := I) (G := G)
  refine ⟨φ.source, φ.open_source.mem_nhds
    zero_mem_mulInvariantExpOpenPartialHomeomorph_source, ?_⟩
  intro x hx y hy hxy
  apply φ.injOn hx hy
  rw [mulInvariantExpOpenPartialHomeomorph_apply, mulInvariantExpOpenPartialHomeomorph_apply]
  exact congrArg (extChartAt I (1 : G)) hxy

/-- The fully charted exponential is a local diffeomorphism of every finite differentiability
order at zero. Together with `contMDiff_mulInvariantExp` and
`contDiffAt_mulInvariantLogChart_identity`, this packages the smooth inverse-function-theorem
conclusion available from Mathlib's finite-order local-neighborhood API. -/
theorem isLocalDiffeomorphAt_mulInvariantExpChart_zero (n : ℕ) [FiniteDimensional ℝ E]
    [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) (n : ℕ∞ω)
      (mulInvariantExpChart (I := I) (G := G)) 0 := by
  let φ := mulInvariantExpOpenPartialHomeomorph (I := I) (G := G)
  -- Choose neighborhoods on which the exponential and logarithm are both `C^n`.
  obtain ⟨U, hUopen, hzeroU, hFU⟩ :=
    (contDiffAt_mulInvariantExpChart_zero (I := I) (G := G)).contDiffOn'
      (m := (n : ℕ∞ω)) (by exact_mod_cast le_top) (by simp)
  obtain ⟨V, hVopen, hyV, hLV⟩ :=
    (contDiffAt_mulInvariantLogChart_identity (I := I) (G := G)).contDiffOn'
      (m := (n : ℕ∞ω)) (by exact_mod_cast le_top) (by simp)
  have hFU' : ContDiffOn ℝ n (mulInvariantExpChart (I := I) (G := G)) U := by
    simpa using hFU
  have hLV' : ContDiffOn ℝ n (mulInvariantLogChart (I := I) (G := G)) V := by
    simpa using hLV
  -- Restrict the inverse-function-theorem homeomorphism to those two neighborhoods.
  let ψ : OpenPartialHomeomorph E E :=
    (φ.restrOpen U hUopen).trans (OpenPartialHomeomorph.ofSet V hVopen)
  have hψ_apply (x : E) : ψ x = mulInvariantExpChart (I := I) (G := G) x := by
    exact mulInvariantExpOpenPartialHomeomorph_apply (I := I) (G := G) x
  have hφzeroV : φ 0 ∈ V := by
    rw [mulInvariantExpOpenPartialHomeomorph_apply, mulInvariantExpChart_zero]
    exact hyV
  have hzeroψ : (0 : E) ∈ ψ.source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · rw [OpenPartialHomeomorph.restrOpen_source]
      exact ⟨zero_mem_mulInvariantExpOpenPartialHomeomorph_source (I := I) (G := G), hzeroU⟩
    · exact hφzeroV
  -- Give the restricted homeomorphism the public coordinate exponential as its forward map.
  let ψe : PartialEquiv E E := {
    toFun := mulInvariantExpChart (I := I) (G := G)
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
      rw [← hψ_apply]
      exact ψ.left_inv hx
    right_inv' := by
      intro x hx
      rw [← hψ_apply]
      exact ψ.right_inv hx
  }
  -- Attach the two finite-order smoothness proofs to obtain the partial diffeomorphism.
  let ψd : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E n := {
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
  exact ψd.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) n hzeroψ
