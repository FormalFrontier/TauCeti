/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import TauCeti.Geometry.Lie.Exponential.Derivative.Basic
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
/-!
# Local inverse of the Lie-group exponential

The smooth coordinate exponential has derivative the identity at zero, so the inverse function
theorem supplies a chosen smooth local logarithm in model-space identity coordinates.

Transporting that logarithm through the identity chart gives a group-level local inverse for the
tangent-space exponential.

## Main results

* `mulInvariantLog`: a local logarithm from the group to its tangent Lie algebra.
* `lieLog`: the same chosen local logarithm, valued in left-invariant derivations.
* `hasFDerivAt_mulInvariantLogChart_one`: the coordinate logarithm has derivative the identity
  at the identity coordinate.
* `eventually_mulInvariantExp_log`: exponential followed after logarithm is locally the identity.
* `eventually_mulInvariantLog_exp`: logarithm followed after exponential is locally the identity.
* `isLocalDiffeomorphAt_lieExp_zero`: the canonical Lie-group exponential is a local
  `C∞` local diffeomorphism at zero.
* `isLocalDiffeomorphAt_mulInvariantExpChart_zero`: the fully charted exponential is a local
  `C∞` local diffeomorphism at zero.
* `exists_injOn_mulInvariantExp_modelSpace`: exponential is injective near zero.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The exponential map".
-/
public section
open Filter Function Manifold
open scoped ContDiff Manifold Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [IsManifold I 1 G]
attribute [local instance] LieGroup.minSmoothnessThree

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

/-- The fully charted exponential on the neighborhoods selected by the inverse function
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
  simp [mulInvariantExpOpenPartialHomeomorph]

/-- Zero belongs to the source of the local coordinate exponential. -/
theorem zero_mem_mulInvariantExpOpenPartialHomeomorph_source [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    0 ∈ (mulInvariantExpOpenPartialHomeomorph (I := I) (G := G)).source := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact (contDiffAt_mulInvariantExpChart_zero (I := I) (G := G))
    |>.mem_toOpenPartialHomeomorph_source
      (hasFDerivAt_mulInvariantExpChart_zero_equiv (I := I) (G := G)) smoothOrder_ne_zero

/-- The identity coordinate belongs to the target of the local coordinate exponential. -/
theorem one_mem_mulInvariantExpOpenPartialHomeomorph_target [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    extChartAt I (1 : G) (1 : G) ∈
      (mulInvariantExpOpenPartialHomeomorph (I := I) (G := G)).target := by
  rw [← mulInvariantExpChart_zero (I := I) (G := G)]
  exact (mulInvariantExpOpenPartialHomeomorph (I := I) (G := G)).map_source
    zero_mem_mulInvariantExpOpenPartialHomeomorph_source

/-- The logarithm selected by the inverse function theorem, with domain and codomain in
identity-chart coordinates. Its values outside the selected target neighborhood carry no
logarithmic meaning. -/
noncomputable def mulInvariantLogChart [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] : E → E :=
  (mulInvariantExpOpenPartialHomeomorph (I := I) (G := G)).symm

/-- The fully charted logarithm is the inverse of the chosen local homeomorphism. -/
theorem mulInvariantLogChart_apply [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] (y : E) :
    mulInvariantLogChart (I := I) (G := G) y =
      (mulInvariantExpOpenPartialHomeomorph (I := I) (G := G)).symm y := by
  rfl

/-- The coordinate logarithm sends the identity coordinate to zero. -/
@[simp]
theorem mulInvariantLogChart_one [FiniteDimensional ℝ E] [LieGroup I ∞ G]
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
theorem contDiffAt_mulInvariantLogChart_one [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    ContDiffAt ℝ ∞ (mulInvariantLogChart (I := I) (G := G))
      (extChartAt I (1 : G) (1 : G)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let φ := mulInvariantExpOpenPartialHomeomorph (I := I) (G := G)
  have hφ : (φ : E → E) = mulInvariantExpChart (I := I) (G := G) := by
    funext v
    exact mulInvariantExpOpenPartialHomeomorph_apply (I := I) (G := G) v
  have hlog : φ.symm (extChartAt I (1 : G) (1 : G)) = 0 :=
    mulInvariantLogChart_one (I := I) (G := G)
  apply φ.contDiffAt_symm one_mem_mulInvariantExpOpenPartialHomeomorph_target
  · rw [hlog, hφ]
    exact hasFDerivAt_mulInvariantExpChart_zero_equiv (I := I) (G := G)
  · rw [hlog, hφ]
    exact contDiffAt_mulInvariantExpChart_zero (I := I) (G := G)

/-- The coordinate logarithm has derivative the identity at the identity coordinate. -/
theorem hasFDerivAt_mulInvariantLogChart_one [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    HasFDerivAt (mulInvariantLogChart (I := I) (G := G))
      (ContinuousLinearMap.id ℝ E) (extChartAt I (1 : G) (1 : G)) := by
  let φ := mulInvariantExpOpenPartialHomeomorph (I := I) (G := G)
  have hlog : φ.symm (extChartAt I (1 : G) (1 : G)) = 0 :=
    mulInvariantLogChart_one (I := I) (G := G)
  have h := φ.hasFDerivAt_symm
    one_mem_mulInvariantExpOpenPartialHomeomorph_target
    (f' := ContinuousLinearEquiv.refl ℝ E) (by
      have hφ : (φ : E → E) = mulInvariantExpChart (I := I) (G := G) := by
        funext v
        exact mulInvariantExpOpenPartialHomeomorph_apply (I := I) (G := G) v
      rw [hlog, hφ]
      simpa using hasFDerivAt_mulInvariantExpChart_zero (I := I) (G := G))
  simpa [mulInvariantLogChart, φ] using h

/-- The local logarithm of a group element, valued in the tangent Lie algebra at the identity. It
is the coordinate logarithm transported back from the manifold model space. Its values outside
the selected identity neighborhood carry no logarithmic meaning. -/
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

/-- The tangent-valued local logarithm is smooth at the group identity. -/
theorem contMDiffAt_mulInvariantLog_one [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun g : G => (show E from mulInvariantLog (I := I) (G := G) g)) (1 : G) := by
  rw [show (fun g : G => (show E from mulInvariantLog (I := I) (G := G) g)) = fun g : G =>
      mulInvariantLogChart (I := I) (G := G) (extChartAt I (1 : G) g) by
    funext g
    exact mulInvariantLog_eq_chart (I := I) (G := G) g]
  exact (contDiffAt_mulInvariantLogChart_one (I := I) (G := G)).contMDiffAt.comp
    (1 : G) (contMDiffAt_extChartAt (I := I) (x := (1 : G)))

/-- The local Lie logarithm, valued in the canonical Lie algebra of left-invariant derivations.
Its values outside the identity neighborhood selected by the inverse function theorem carry no
logarithmic meaning. -/
noncomputable def lieLog [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] (g : G) : LeftInvariantDerivation I G :=
  (leftInvariantDerivationLinearIsometryEquivModelVectorSpace
    (I := I) (G := G)).symm (mulInvariantLog (I := I) (G := G) g)

/-- The derivation-valued local Lie logarithm is the tangent-valued logarithm transported through
the derivation–tangent equivalence. -/
theorem lieLog_eq [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] (g : G) :
    lieLog (I := I) (G := G) g =
      (leftInvariantDerivationLinearIsometryEquivModelVectorSpace
        (I := I) (G := G)).symm (mulInvariantLog (I := I) (G := G) g) := by
  rfl

/-- The derivation-valued local Lie logarithm is smooth at the group identity. -/
theorem contMDiffAt_lieLog_one [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    ContMDiffAt I (modelWithCornersSelf ℝ (LeftInvariantDerivation I G)) ∞
      (lieLog (I := I) (G := G)) (1 : G) := by
  let L := leftInvariantDerivationLinearIsometryEquivModelVectorSpace
    (I := I) (G := G)
  have hL : ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ (LeftInvariantDerivation I G)) ∞ L.symm :=
    L.toContinuousLinearEquiv.symm.contDiff.contMDiff
  rw [show lieLog (I := I) (G := G) = fun g : G =>
      L.symm (mulInvariantLog (I := I) (G := G) g) by
    funext g
    exact lieLog_eq (I := I) (G := G) g]
  exact hL.contMDiffAt.comp (1 : G) (contMDiffAt_mulInvariantLog_one (I := I) (G := G))

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
  exact mulInvariantLogChart_one (I := I) (G := G)

/-- The derivation-valued local Lie logarithm sends the group identity to the zero derivation. -/
@[simp]
theorem lieLog_one [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    lieLog (I := I) (G := G) (1 : G) = 0 := by
  rw [lieLog_eq]
  -- `GroupLieAlgebra I G` is definitionally the model space `E`, so the linear equivalence can
  -- consume the model-space presentation of `mulInvariantLog`.
  change (leftInvariantDerivationLinearIsometryEquivModelVectorSpace
    (I := I) (G := G)).symm
      (show E from mulInvariantLog (I := I) (G := G) (1 : G)) = 0
  have hlog : (show E from mulInvariantLog (I := I) (G := G) (1 : G)) = 0 := by
    -- Return across the same definitional identification to reuse the group-valued zero theorem.
    change mulInvariantLog (I := I) (G := G) (1 : G) =
      (0 : GroupLieAlgebra I G)
    exact mulInvariantLog_one (I := I) (G := G)
  rw [hlog]
  exact LinearEquiv.map_zero _

/-- Locally around zero, the derivation-valued Lie logarithm is a left inverse to `lieExp`. -/
theorem eventually_lieLog_lieExp [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    ∀ᶠ X in 𝓝 (0 : LeftInvariantDerivation I G),
      lieLog (I := I) (G := G) (lieExp X) = X := by
  let L := leftInvariantDerivationLinearIsometryEquivModelVectorSpace
    (I := I) (G := G)
  have hL : Tendsto L (𝓝 (0 : LeftInvariantDerivation I G)) (𝓝 (0 : E)) := by
    have h : ContinuousAt L (0 : LeftInvariantDerivation I G) := L.continuousAt
    exact (show L (0 : LeftInvariantDerivation I G) = (0 : E) by
      exact LinearEquiv.map_zero _) ▸ h
  have h := hL.eventually (eventually_mulInvariantLog_exp (I := I) (G := G))
  filter_upwards [h] with X hX
  rw [lieLog_eq, lieExp_eq_mulInvariantExp]
  rw [← leftInvariantDerivationLinearIsometryEquivModelVectorSpace_apply]
  -- `GroupLieAlgebra I G` is definitionally `E`; expose that identification around the two
  -- mutually inverse linear equivalences.
  change L.symm (show E from mulInvariantLog (I := I) (G := G)
    (mulInvariantExp (I := I) (G := G) (L X : GroupLieAlgebra I G))) = X
  rw [hX, L.symm_apply_apply]

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
    (contDiffAt_mulInvariantLogChart_one (I := I) (G := G)).continuousAt.comp
      (continuousAt_extChartAt (I := I) (1 : G))
  have hlogOne : L (extChartAt I (1 : G) (1 : G)) = 0 := by
    simpa only [L, extChartAt_coe, Function.comp_apply] using
      mulInvariantLogChart_one (I := I) (G := G)
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

/-- Locally around the identity, `lieExp` is a left inverse to the derivation-valued Lie
logarithm. -/
theorem eventually_lieExp_lieLog [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    ∀ᶠ g in 𝓝 (1 : G), lieExp (lieLog (I := I) (G := G) g) = g := by
  let L := leftInvariantDerivationLinearIsometryEquivModelVectorSpace
    (I := I) (G := G)
  refine (eventually_mulInvariantExp_log (I := I) (G := G)).mono ?_
  intro g hg
  rw [lieLog_eq, lieExp_eq_mulInvariantExp]
  rw [← leftInvariantDerivationLinearIsometryEquivModelVectorSpace_apply]
  -- `GroupLieAlgebra I G` is definitionally `E`; expose it so `L.apply_symm_apply` applies.
  change mulInvariantExp (I := I) (G := G)
    (L (L.symm (show E from mulInvariantLog (I := I) (G := G) g)) :
      GroupLieAlgebra I G) = g
  rw [L.apply_symm_apply]
  exact hg

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

/-- A smooth partial diffeomorphism for the fully charted exponential, whose source stays inside
the identity chart. -/
private theorem exists_mulInvariantExpChartPartialDiffeomorph [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    ∃ d : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      0 ∈ d.source ∧
      d.source ⊆ (fun v : E =>
        mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G)) ⁻¹'
          (extChartAt I (1 : G)).source ∧
      mulInvariantExpChart (I := I) (G := G) = d := by
  let f : E → G := fun v =>
    mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G)
  let F : E → E := mulInvariantExpChart (I := I) (G := G)
  let S := f ⁻¹' (extChartAt I (1 : G)).source
  have hf : ContMDiff 𝓘(ℝ, E) I ∞ f := by
    simpa only [f] using contMDiff_mulInvariantExp (I := I) (G := G)
  have hSopen : IsOpen S := hf.continuous.isOpen_preimage _
    (isOpen_extChartAt_source (I := I) (1 : G))
  have hzeroS : (0 : E) ∈ S := by
    change f 0 ∈ (extChartAt I (1 : G)).source
    rw [show f 0 = (1 : G) by exact mulInvariantExp_zero]
    exact mem_extChartAt_source (I := I) (1 : G)
  -- Global smoothness of the exponential gives smoothness of its identity-chart expression on
  -- the fixed open set where that chart is valid.
  have hF : ContDiffOn ℝ ∞ F S := by
    have hcoord := (contMDiff_iff_target.mp hf).2 (1 : G)
    rw [contMDiffOn_iff_contDiffOn] at hcoord
    simpa only [F, S, f, mulInvariantExpChart_eq, Function.comp_def] using hcoord
  have hDF : ContinuousOn (fderiv ℝ F) S :=
    hF.continuousOn_fderiv_of_isOpen hSopen (by simp)
  -- Invertible continuous linear endomorphisms form an open set. Shrinking to its derivative
  -- preimage makes the derivative invertible at every point of one common source neighborhood.
  let U := S ∩ (fderiv ℝ F) ⁻¹' {A : E →L[ℝ] E | IsUnit A}
  have hUopen : IsOpen U := hDF.isOpen_inter_preimage hSopen Units.isOpen
  have hzeroU : (0 : E) ∈ U := by
    refine ⟨hzeroS, ?_⟩
    change IsUnit (fderiv ℝ F 0)
    rw [show fderiv ℝ F 0 = ContinuousLinearMap.id ℝ E by
      simpa only [F] using
        (hasFDerivAt_mulInvariantExpChart_zero (I := I) (G := G)).fderiv]
    exact (ContinuousLinearEquiv.toUnit (ContinuousLinearEquiv.refl ℝ E)).isUnit
  let φ := mulInvariantExpOpenPartialHomeomorph (I := I) (G := G)
  let ψ := φ.restrOpen U hUopen
  have hψ_apply (x : E) : ψ x = F x := by
    exact mulInvariantExpOpenPartialHomeomorph_apply (I := I) (G := G) x
  have hzeroψ : (0 : E) ∈ ψ.source := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨zero_mem_mulInvariantExpOpenPartialHomeomorph_source (I := I) (G := G), hzeroU⟩
  have hψsmooth : ContDiffOn ℝ ∞ ψ ψ.source := by
    rw [show (ψ : E → E) = F by funext x; exact hψ_apply x]
    apply hF.mono
    intro x hx
    rw [OpenPartialHomeomorph.restrOpen_source] at hx
    exact hx.2.1
  -- At every target point the derivative is invertible, so smoothness of the global forward map
  -- bootstraps the homeomorphism's inverse to `C∞` on the entire fixed target neighborhood.
  have hψsymmSmooth : ContDiffOn ℝ ∞ ψ.symm ψ.target := by
    intro y hy
    have hxy := ψ.map_target hy
    have hxyU : ψ.symm y ∈ U := by
      rw [OpenPartialHomeomorph.restrOpen_source] at hxy
      exact hxy.2
    have hxyS : ψ.symm y ∈ S := hxyU.1
    have hFxy : ContDiffAt ℝ ∞ F (ψ.symm y) :=
      (hF (ψ.symm y) hxyS).contDiffAt (hSopen.mem_nhds hxyS)
    obtain ⟨A, hA⟩ := hxyU.2
    apply (ψ.contDiffAt_symm hy (f₀' := ContinuousLinearEquiv.ofUnit A) ?_ ?_).contDiffWithinAt
    · rw [show (ψ : E → E) = F by funext x; exact hψ_apply x]
      rw [show ((ContinuousLinearEquiv.ofUnit A : E ≃L[ℝ] E) : E →L[ℝ] E) =
          fderiv ℝ F (ψ.symm y) by exact hA]
      exact (hFxy.differentiableAt (by simp)).hasFDerivAt
    · rw [show (ψ : E → E) = F by funext x; exact hψ_apply x]
      exact hFxy
  let d : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ := {
    toPartialEquiv := ψ.toPartialEquiv
    open_source := ψ.open_source
    open_target := ψ.open_target
    contMDiffOn_toFun := by
      rw [contMDiffOn_iff_contDiffOn]
      exact hψsmooth
    contMDiffOn_invFun := by
      rw [contMDiffOn_iff_contDiffOn]
      exact hψsymmSmooth
  }
  refine ⟨d, hzeroψ, ?_, ?_⟩
  · intro x hx
    change x ∈ ψ.source at hx
    rw [OpenPartialHomeomorph.restrOpen_source] at hx
    exact hx.2.1
  · funext x
    exact (hψ_apply x).symm

/-- The fully charted exponential is a smooth local diffeomorphism at zero. -/
theorem isLocalDiffeomorphAt_mulInvariantExpChart_zero [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (mulInvariantExpChart (I := I) (G := G)) 0 := by
  obtain ⟨d, hzero, _, hd⟩ :=
    exists_mulInvariantExpChartPartialDiffeomorph (I := I) (G := G)
  rw [hd]
  exact d.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ hzero

/-- The tangent-space exponential, viewed as a group-valued map on model coordinates, is a smooth
local diffeomorphism at zero. -/
theorem isLocalDiffeomorphAt_mulInvariantExp_modelSpace_zero [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞
      (fun v : E => mulInvariantExp (I := I) (G := G)
        (v : GroupLieAlgebra I G)) 0 := by
  let f : E → G := fun v =>
    mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G)
  obtain ⟨d, hzero, hdsource, hd⟩ :=
    exists_mulInvariantExpChartPartialDiffeomorph (I := I) (G := G)
  let chart := extChartAt I (1 : G)
  let V := interior chart.target
  have hVopen : IsOpen V := isOpen_interior
  have honeV : extChartAt I (1 : G) (1 : G) ∈ V := by
    exact (ModelWithCorners.isInteriorPoint_iff (I := I)).mp
      BoundarylessManifold.isInteriorPoint
  have hsourceOpen : IsOpen (chart.source ∩ chart ⁻¹' V) :=
    (continuousOn_extChartAt (I := I) (1 : G)).isOpen_inter_preimage
      (isOpen_extChartAt_source (I := I) (1 : G)) hVopen
  -- Boundarylessness puts the identity coordinate in the interior of the chart target. Restricting
  -- the chart to that interior gives an honest smooth partial diffeomorphism in both directions.
  let ce : PartialEquiv G E := {
    toFun := chart
    invFun := chart.symm
    source := chart.source ∩ chart ⁻¹' V
    target := V
    map_source' := fun _ hx => hx.2
    map_target' := by
      intro y hy
      refine ⟨chart.map_target (interior_subset hy), ?_⟩
      change chart (chart.symm y) ∈ V
      rw [chart.right_inv (interior_subset hy)]
      exact hy
    left_inv' := fun _ hx => chart.left_inv hx.1
    right_inv' := fun _ hy => chart.right_inv (interior_subset hy)
  }
  let c : PartialDiffeomorph I 𝓘(ℝ, E) G E ∞ := {
    toPartialEquiv := ce
    open_source := hsourceOpen
    open_target := hVopen
    contMDiffOn_toFun := by
      apply (contMDiffOn_extChartAt (I := I) (n := ∞) (x := (1 : G))).mono
      intro x hx
      change x ∈ chart.source ∩ chart ⁻¹' V at hx
      simpa only [chart, extChartAt_source] using hx.1
    contMDiffOn_invFun :=
      (contMDiffOn_extChartAt_symm (I := I) (1 : G)).mono interior_subset
  }
  -- Transport the charted local diffeomorphism `d : E ↔ E` back through the restricted identity
  -- chart. The resulting `q : E ↔ G` has the desired source, target, and smooth inverse.
  let q := d.trans c.symm
  have hzeroq : (0 : E) ∈ q.source := by
    change 0 ∈ d.source ∩ d ⁻¹' c.symm.source
    refine ⟨hzero, ?_⟩
    change d 0 ∈ c.target
    rw [← hd, mulInvariantExpChart_zero]
    exact honeV
  have hq (x : E) (hx : x ∈ q.source) : f x = q x := by
    change x ∈ d.source ∩ d ⁻¹' c.symm.source at hx
    change f x = (extChartAt I (1 : G)).symm (d x)
    rw [← hd]
    change f x = (extChartAt I (1 : G)).symm
      (extChartAt I (1 : G) (f x))
    exact ((extChartAt I (1 : G)).left_inv (hdsource hx.1)).symm
  -- Although `q` agrees with `f` on its source, its total forward function retains the composed
  -- chart implementation. Re-wrap its partial equivalence using literally `f` so the final local
  -- diffeomorphism theorem has the canonical exponential as its function.
  let e : PartialEquiv E G := {
    toFun := f
    invFun := q.symm
    source := q.source
    target := q.target
    map_source' := by
      intro x hx
      rw [hq x hx]
      exact q.map_source hx
    map_target' := by
      intro y hy
      exact q.map_target hy
    left_inv' := by
      intro x hx
      rw [hq x hx]
      exact q.left_inv hx
    right_inv' := by
      intro y hy
      rw [hq (q.symm y) (q.map_target hy)]
      exact q.right_inv hy
  }
  let p : PartialDiffeomorph 𝓘(ℝ, E) I E G ∞ := {
    toPartialEquiv := e
    open_source := q.open_source
    open_target := q.open_target
    contMDiffOn_toFun := by
      simpa only [f] using
        (contMDiff_mulInvariantExp (I := I) (G := G)).contMDiffOn
    contMDiffOn_invFun := q.contMDiffOn_invFun
  }
  change IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ f 0
  exact p.isLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ hzeroq

/-- The canonical Lie-group exponential is a smooth local diffeomorphism at zero. -/
theorem isLocalDiffeomorphAt_lieExp_zero [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    IsLocalDiffeomorphAt
      (modelWithCornersSelf ℝ (LeftInvariantDerivation I G)) I ∞
      (lieExp (I := I) (G := G)) 0 := by
  let L := leftInvariantDerivationLinearIsometryEquivModelVectorSpace
    (I := I) (G := G)
  let d : LeftInvariantDerivation I G ≃ₘ^∞⟮
      modelWithCornersSelf ℝ (LeftInvariantDerivation I G), 𝓘(ℝ, E)⟯ E := {
    toEquiv := L.toEquiv
    contMDiff_toFun := L.toContinuousLinearEquiv.contDiff.contMDiff
    contMDiff_invFun := L.toContinuousLinearEquiv.symm.contDiff.contMDiff
  }
  have hL : IsLocalDiffeomorphAt
      (modelWithCornersSelf ℝ (LeftInvariantDerivation I G)) 𝓘(ℝ, E) ∞ L 0 :=
    d.isLocalDiffeomorph 0
  have hmodel : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞
      (fun v : E => mulInvariantExp (I := I) (G := G)
        (v : GroupLieAlgebra I G)) (L 0) := by
    rw [show L (0 : LeftInvariantDerivation I G) = (0 : E) by
      exact LinearEquiv.map_zero _]
    exact isLocalDiffeomorphAt_mulInvariantExp_modelSpace_zero (I := I) (G := G)
  have hcomp := hL.comp I G hmodel
  rw [show lieExp (I := I) (G := G) =
      (fun v : E => mulInvariantExp (I := I) (G := G)
        (v : GroupLieAlgebra I G)) ∘ L by
    funext X
    rw [Function.comp_apply, lieExp_eq_mulInvariantExp,
      leftInvariantDerivationLinearIsometryEquivModelVectorSpace_apply]]
  exact hcomp
