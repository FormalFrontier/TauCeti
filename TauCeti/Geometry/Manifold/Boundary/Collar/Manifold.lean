/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Chart

/-!
# The manifold structure of collar coordinates

The collar charts of `Boundary.Collar.Chart` express a manifold modeled on the Euclidean
half-space in tangential and inward-normal coordinates. This file proves that those charts have
`C^k` transition maps. Consequently, the charted space `TauCeti.collarChartedSpace n M` is a
manifold modeled on `(𝓡 n).prod (𝓡∂ 1)` whenever the original half-space charted space is a
`C^k` manifold.

This is the local product-manifold step in Layer 1's collar-neighbourhood target of the
GeometricTopology roadmap (`TauCetiRoadmap/GeometricTopology/README.md`). It is deliberately not
the global collar theorem: a collar chart still has an arbitrary open target in the product model,
not a target of the form `V × [0, ε)`. The global step must shrink and patch these local product
coordinates along the entire boundary.

For ambient atlas charts `e` and `e'`, their collar transition is the composite of the smooth
inverse of `collarChart e` with the smooth map `collarChart e'`. The only bookkeeping left after
this composition is translating manifold smoothness on the product model to the coordinate form
used by `isManifold_of_contDiffOn`.

## Main result

* `TauCeti.isManifold_collarChartedSpace`: the collar charted space is a `C^k` manifold over the
  product model.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Theorem 6.1.
* J. Lee, *Introduction to Smooth Manifolds*, Springer GTM 218, 2nd ed. (2013), Theorem 9.25.
-/

public section

noncomputable section

open Function Set Topology

open scoped Manifold ContDiff

namespace TauCeti

variable {n : ℕ} {k : WithTop ℕ∞} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-- The collar charts make a `C^k` manifold atlas for the product model
`(𝓡 n).prod (𝓡∂ 1)`. This is the given half-space manifold structure expressed in tangential and
inward-normal coordinates.

The charted-space argument is explicit in the conclusion because `M` already has its original
half-space charted-space instance. A consumer can install the result locally with
`letI := collarChartedSpace n M` followed by `letI := isManifold_collarChartedSpace`. -/
theorem isManifold_collarChartedSpace [IsManifold (𝓡∂ (n + 1)) k M] :
    @IsManifold ℝ _ _ _ _ _ _ ((𝓡 n).prod (𝓡∂ 1)) k M _
      (collarChartedSpace n M) := by
  let collar : ChartedSpace
      (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1)) M :=
    collarChartedSpace n M
  refine @isManifold_of_contDiffOn ℝ _ _ _ _ _ _
    ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))).prod
      (modelWithCornersEuclideanHalfSpace 1)) k M _ collar ?_
  rintro _ _ he he'
  rw [collarChartedSpace_atlas] at he he'
  obtain ⟨e, he, rfl⟩ := he
  obtain ⟨e', he', rfl⟩ := he'
  let φ := (collarChart e).symm ≫ₕ collarChart e'
  have hφ : ContMDiffOn
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))).prod
        (modelWithCornersEuclideanHalfSpace 1))
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))).prod
        (modelWithCornersEuclideanHalfSpace 1)) k φ φ.source := by
    simpa only [φ, OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, collarChart_source, Function.comp_apply] using
      (contMDiffOn_collarChart
        (IsManifold.subset_maximalAtlas
          (I := modelWithCornersEuclideanHalfSpace (n + 1)) (n := k) he')).comp'
        (contMDiffOn_collarChart_symm
          (IsManifold.subset_maximalAtlas
            (I := modelWithCornersEuclideanHalfSpace (n + 1)) (n := k) he))
  rw [contMDiffOn_iff] at hφ
  convert hφ.2 (0, 0) (0, 0) using 1
  · rfl
  · ext p
    have hprod : Prod.map id (modelWithCornersEuclideanHalfSpace 1).symm p =
        (p.1, (modelWithCornersEuclideanHalfSpace 1).symm p.2) := rfl
    have hsource :
        (collarChart e).symm
              (p.1, (modelWithCornersEuclideanHalfSpace 1).symm p.2) ∈ e'.source ↔
          e.symm (EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n
              (p.1, (modelWithCornersEuclideanHalfSpace 1).symm p.2)) ∈ e'.source := by
      rw [collarChart_symm_apply]
    have hnormalized :
        ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n
                (p.1, (modelWithCornersEuclideanHalfSpace 1).symm p.2) ∈ e.target ∧
              (collarChart e).symm
                (p.1, (modelWithCornersEuclideanHalfSpace 1).symm p.2) ∈ e'.source) ∧
            ∃ y : ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1),
              y.1 = p.1 ∧ y.2.1 = p.2) ↔
          (∃ y : EuclideanHalfSpace 1, y.1 = p.2) ∧
            EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n
              (p.1, (modelWithCornersEuclideanHalfSpace 1).symm p.2) ∈ e.target ∧
            e.symm (EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n
              (p.1, (modelWithCornersEuclideanHalfSpace 1).symm p.2)) ∈ e'.source := by
      constructor
      · rintro ⟨⟨htarget, hsource⟩, ⟨y, -, hy⟩⟩
        refine ⟨⟨y.2, hy⟩, htarget, ?_⟩
        rw [collarChart_symm_apply] at hsource
        exact hsource
      · rintro ⟨⟨y, hy⟩, htarget, hsource⟩
        refine ⟨⟨htarget, ?_⟩, ⟨(p.1, y), rfl, hy⟩⟩
        rw [collarChart_symm_apply]
        exact hsource
    simpa [φ, chartAt_self_eq, Prod.ext_iff, hprod, hsource] using hnormalized

end TauCeti
