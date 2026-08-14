/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.Boundary.Collar

/-!
# Collar charts on a manifold with boundary

`Boundary.Collar` identifies the model half-space `EuclideanHalfSpace (n + 1)` with the product
`EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1` of its boundary model and an inward normal
coordinate. That is a statement about the *model*; this file transports it to an arbitrary
manifold `M` modeled on that half-space, by composing an ambient chart of `M` with the
identification.

The resulting *collar chart* reads a point of `M` as a pair: a tangential coordinate in the
boundary model, and a normal coordinate in `[0, ∞)`. Two facts make it deserve the name, and they
are the content of the file.

* **The boundary is the zero slice.** A point in the source of a collar chart lies on
  `I.boundary M` exactly when its normal coordinate vanishes. So in collar coordinates the
  boundary is cut out by a single equation, rather than detected chartwise as in
  `Boundary.Charts`.
* **The tangential coordinate is the boundary chart.** On boundary points the first component of
  the collar chart induced by the preferred ambient chart is the preferred chart of the boundary
  manifold built in `Boundary.Charts`. The two files therefore describe one coordinate system,
  not two.

The chart is built from `collarDiffeomorph` at the top regularity `⊤` and used only through its
underlying homeomorphism: charts are topological data, and the map underlying `collarDiffeomorph`
does not depend on the regularity exponent. Smoothness statements instantiate the diffeomorphism
at whatever exponent they need.

This is the first step of the collar-neighbourhood target in Layer 1 of the GeometricTopology
roadmap, taken after `Boundary.Collar`'s standard-model calculation: it puts the product
coordinates on a general manifold. The two steps that remain for the collar theorem itself are
not proved here — that the collar charts have `C^k` transitions, so `M` is also a manifold for
the product model `(𝓡 n).prod (𝓡∂ 1)`; and the global statement, that a whole neighbourhood of
`I.boundary M` is diffeomorphic to `I.boundary M × [0, 1)`, which needs these local product
coordinates patched with a partition of unity.

## Main definitions

* `TauCeti.collarChart`: the collar chart induced by an ambient chart.
* `TauCeti.collarModelChartedSpace`: the model half-space charted over the product by the single
  collar identification.
* `TauCeti.collarChartedSpace`: `M` as a charted space over the product, obtained from the
  previous two by `ChartedSpace.comp`. Both are `def`s, not `instance`s: `M` already carries a
  `ChartedSpace` over the half-space, and the two must not compete in instance search.

## Main results

* `TauCeti.mem_boundary_iff_collarChart_snd_eq_zero`: the boundary is the zero slice of the
  normal coordinate.
* `TauCeti.collarChart_fst_eq_chartAt_boundary`: on the boundary, the tangential coordinate is
  the preferred boundary chart of `Boundary.Charts`.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Theorem 6.1 (the collaring
  theorem).
* J. Lee, *Introduction to Smooth Manifolds*, Springer GTM 218, 2nd ed. (2013), Theorem 9.25
  (the collar neighbourhood theorem).
-/

public section

noncomputable section

open Function Set Topology

open scoped Manifold ContDiff

namespace TauCeti

variable {n : ℕ} {k : WithTop ℕ∞} {M : Type*} [TopologicalSpace M]

/-- The collar chart attached to an ambient chart `e` of `M`: read a point through `e`, then split
the model half-space into its boundary model and the inward normal coordinate.

`collarDiffeomorph` is taken at the top regularity because only its underlying homeomorphism is
used here; the map does not depend on the exponent. -/
noncomputable def collarChart (e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
  e ≫ₕ (EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm.toHomeomorph.toOpenPartialHomeomorph

/-- A collar chart sees exactly what the ambient chart it comes from sees. -/
@[simp]
theorem collarChart_source (e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))) :
    (collarChart e).source = e.source := by
  simp [collarChart]

/-- The tangential coordinate of a collar chart deletes the zeroth ambient coordinate. -/
@[simp]
theorem collarChart_fst (e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))) (x : M) :
    (collarChart e x).1 = EuclideanHalfSpace.boundaryProj n (e x) :=
  EuclideanHalfSpace.collarDiffeomorph_symm_apply_fst (k := ⊤) n (e x)

/-- The normal coordinate of a collar chart is the zeroth ambient coordinate. -/
@[simp]
theorem collarChart_snd_apply_zero (e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)))
    (x : M) : (collarChart e x).2.1 0 = (e x).1 0 :=
  EuclideanHalfSpace.collarDiffeomorph_symm_apply_snd_apply_zero (k := ⊤) n (e x)

/-- The model half-space as a charted space over the product, with the collar identification of
`Boundary.Collar` as its single chart. This is what makes a chart of `M` into a collar chart:
`collarChartedSpace` below is the composition of this with the atlas of `M`.

Deliberately not an instance, for the reason given at `collarChartedSpace`. -/
@[expose, instance_reducible]
noncomputable def collarModelChartedSpace (n : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1)
      (EuclideanHalfSpace (n + 1)) :=
  (EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm.toHomeomorph.toOpenPartialHomeomorph
    |>.singletonChartedSpace (by simp)

section Atlas

variable [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-- **In collar coordinates the boundary is the zero slice of the normal coordinate.** Where
`Boundary.Charts` detects a boundary point by the vanishing of a coordinate of the ambient chart,
the collar chart isolates that coordinate as a factor, so the boundary is cut out by one
equation. -/
theorem mem_boundary_iff_collarChart_snd_eq_zero [IsManifold (𝓡∂ (n + 1)) k M] (hk : k ≠ 0)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (n + 1)) M) {x : M} (hx : x ∈ e.source) :
    x ∈ (𝓡∂ (n + 1)).boundary M ↔ (collarChart e x).2.1 0 = 0 := by
  rw [collarChart_snd_apply_zero]
  exact ModelWithCorners.mem_boundary_euclideanHalfSpace_iff_of_mem_atlas hk he hx

/-- **On the boundary, the tangential coordinate of a collar chart is the boundary chart.** The
collar coordinates of `Boundary.Collar` and the boundary manifold structure of `Boundary.Charts`
are the same coordinate system: the boundary chart is the restriction of the collar chart's first
component. -/
theorem collarChart_fst_eq_chartAt_boundary [IsManifold (𝓡∂ (n + 1)) 1 M]
    (p q : ↥((𝓡∂ (n + 1)).boundary M)) :
    (collarChart (chartAt (EuclideanHalfSpace (n + 1)) (p : M)) (q : M)).1 =
      chartAt (EuclideanSpace ℝ (Fin n)) p q := by
  rw [collarChart_fst, boundaryChartedSpace_chartAt_apply]

/-- The collar charts present `M` as a charted space over the product of the boundary model and
the one-dimensional half-space.

It is `ChartedSpace.comp` applied to `collarModelChartedSpace`, rather than an atlas written out
by hand, so that `chartAt_comp`, the `extChartAt` composition lemmas and `HasGroupoid.comp` all
apply to it — `HasGroupoid.comp` is the route to the `C^k` transitions named above.

Deliberately not an instance: `M` already carries a `ChartedSpace` over
`EuclideanHalfSpace (n + 1)`, and letting a second one be found by instance search would make
every statement about charts of `M` ambiguous. Use it explicitly with `letI`. -/
@[expose, instance_reducible]
noncomputable def collarChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) M :=
  letI := collarModelChartedSpace n
  ChartedSpace.comp _ (EuclideanHalfSpace (n + 1)) M

end Atlas

end TauCeti
