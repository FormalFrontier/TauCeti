/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.Boundary.Collar.Basic

/-!
# Collar charts on a manifold with boundary

`Boundary.Collar.Basic` identifies the model half-space `EuclideanHalfSpace (n + 1)` with the
product `EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1` of its boundary model and an inward normal
coordinate. That is a statement about the *model*; this file transports it to an arbitrary
manifold `M` modeled on that half-space, by composing an ambient chart of `M` with the
identification.

The resulting *collar chart* reads a point of `M` as a pair: a tangential coordinate in the
boundary model, and a normal coordinate in `[0, ∞)`. Two facts make it deserve the name, and they
are the content of the file.

* **The boundary is the zero slice.** For an atlas chart `e` and a point of `e.source`, lying on
  `I.boundary M` becomes the vanishing of one product factor — the normal coordinate — of the
  collar chart of `e`.
* **The tangential coordinate is the boundary chart.** On boundary points the first component of
  the collar chart induced by the preferred ambient chart is the preferred chart of the boundary
  manifold built in `Boundary.Charts`. The two files therefore describe one coordinate system,
  not two.

The chart is built from `collarDiffeomorph` at the top regularity `⊤` and used only through its
underlying homeomorphism: charts are topological data, and the map underlying `collarDiffeomorph`
does not depend on the regularity exponent. Smoothness statements instantiate the diffeomorphism
at whatever exponent they need.

This is the first step of the collar-neighbourhood target in Layer 1 of the GeometricTopology
roadmap, taken after `Boundary.Collar.Basic`'s standard-model calculation: it puts the product
coordinates on a general manifold. The two steps that remain for the collar theorem itself are
not proved here — that the collar charts have `C^k` transitions, so `M` is also a manifold for
the product model `(𝓡 n).prod (𝓡∂ 1)`; and the global statement, that a whole neighbourhood of
`I.boundary M` is diffeomorphic to `I.boundary M × [0, 1)`, which needs these local product
coordinates patched with a partition of unity.

## Main definitions

* `TauCeti.collarChart`: the collar chart induced by an ambient chart.
* `TauCeti.collarChartedSpace`: `M` as a charted space over the product, composing
  `EuclideanHalfSpace.collarModelChartedSpace` with the ambient atlas of `M`. It is a `def`, not
  an `instance`: `M` already carries a `ChartedSpace` over the half-space, and the two must not
  compete in instance search.

## Main results

* `TauCeti.mem_boundary_iff_collarChart_snd_apply_zero_eq_zero`: the boundary is the zero slice
  of the normal coordinate.
* `TauCeti.collarChart_fst_eq_boundaryChartedSpace_chartAt_apply`: on the boundary, the
  tangential coordinate is the preferred boundary chart of `Boundary.Charts`.
* `TauCeti.collarChart_apply`, `_target` and `_symm_apply`: the value, target and inverse of a
  collar chart, so it never has to be unfolded.
* `TauCeti.collarChartedSpace_chartAt` and `TauCeti.collarChartedSpace_atlas`: its preferred
  charts and its atlas.

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
used here; the map does not depend on the exponent.

No body here or below is exposed: the lemmas in this section name the value, source, target and
inverse of a collar chart, so downstream code rewrites with those instead of unfolding. -/
noncomputable def collarChart (e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :=
  e ≫ₕ (EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm.toHomeomorph.toOpenPartialHomeomorph

/-- Reading a point through a collar chart is reading it through the ambient chart and then
applying the inverse collar identification.

Not `@[simp]`: it would rewrite the collar phrasing of the two main results back into ambient
coordinates via `Boundary.Collar.Basic`'s simp lemmas, which is the normal-form clash the collar
statements exist to avoid. Use it explicitly, as `collarChart_fst` and `collarChart_snd_apply_zero`
do. -/
theorem collarChart_apply (e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))) (x : M) :
    collarChart e x = (EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm (e x) := by
  simp [collarChart]

/-- A collar chart sees exactly what the ambient chart it comes from sees. -/
@[simp]
theorem collarChart_source (e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))) :
    (collarChart e).source = e.source := by
  simp [collarChart]

/-- A collar chart lands where the collar identification carries the ambient chart's target. -/
@[simp]
theorem collarChart_target (e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))) :
    (collarChart e).target = ⇑(EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n) ⁻¹' e.target := by
  simp [collarChart]

/-- The inverse of a collar chart reassembles the pair and reads it back through the ambient
chart. -/
@[simp]
theorem collarChart_symm_apply (e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)))
    (p : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :
    (collarChart e).symm p = e.symm (EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n p) := by
  simp [collarChart]

/-- The tangential coordinate of a collar chart deletes the zeroth ambient coordinate.

Not `@[simp]`: the collar phrasing is the user-facing normal form here, so this must not rewrite
`collarChart_fst_eq_boundaryChartedSpace_chartAt_apply`'s left-hand side away. -/
theorem collarChart_fst (e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))) (x : M) :
    (collarChart e x).1 = EuclideanHalfSpace.boundaryProj n (e x) := by
  rw [collarChart_apply, EuclideanHalfSpace.collarDiffeomorph_symm_apply_fst]

/-- The normal coordinate of a collar chart is the zeroth ambient coordinate.

Not `@[simp]`, for the reason given at `collarChart_fst`. -/
theorem collarChart_snd_apply_zero (e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)))
    (x : M) : (collarChart e x).2.1 0 = (e x).1 0 := by
  rw [collarChart_apply, EuclideanHalfSpace.collarDiffeomorph_symm_apply_snd_apply_zero]

section Atlas

variable [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-- **In collar coordinates the boundary is the zero slice of the normal coordinate.** For an
atlas chart `e` and a point of `e.source`, the collar chart isolates the coordinate that
`Boundary.Charts` tests as a product factor, so the boundary condition is one equation in it. -/
theorem mem_boundary_iff_collarChart_snd_apply_zero_eq_zero [IsManifold (𝓡∂ (n + 1)) k M]
    (hk : k ≠ 0) {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (n + 1)) M) {x : M} (hx : x ∈ e.source) :
    x ∈ (𝓡∂ (n + 1)).boundary M ↔ (collarChart e x).2.1 0 = 0 := by
  rw [collarChart_snd_apply_zero]
  exact ModelWithCorners.mem_boundary_euclideanHalfSpace_iff_of_mem_atlas hk he hx

/-- **On the boundary, the tangential coordinate of a collar chart is the boundary chart.** The
collar coordinates of `Boundary.Collar.Basic` and the boundary manifold structure of
`Boundary.Charts` are the same coordinate system: the boundary chart is the restriction of the
collar chart's first component. -/
theorem collarChart_fst_eq_boundaryChartedSpace_chartAt_apply [IsManifold (𝓡∂ (n + 1)) 1 M]
    (p q : ↥((𝓡∂ (n + 1)).boundary M)) :
    (collarChart (chartAt (EuclideanHalfSpace (n + 1)) (p : M)) (q : M)).1 =
      chartAt (EuclideanSpace ℝ (Fin n)) p q := by
  rw [collarChart_fst, boundaryChartedSpace_chartAt_apply]

/-- The collar charts present `M` as a charted space over the product of the boundary model and
the one-dimensional half-space.

It is `ChartedSpace.comp` applied to `EuclideanHalfSpace.collarModelChartedSpace`, rather than an
atlas written out by hand, so that `chartAt_comp`, the `extChartAt` composition lemmas and
`HasGroupoid.comp` all apply to it — `HasGroupoid.comp` is the route to the `C^k` transitions
named above.

`n` and `M` are explicit so that `letI := collarChartedSpace n M` determines both; there is no
expected type at a `letI` to solve them from.

Deliberately not an instance: `M` already carries a `ChartedSpace` over
`EuclideanHalfSpace (n + 1)`, and letting a second one be found by instance search would make
every statement about charts of `M` ambiguous. -/
@[instance_reducible]
noncomputable def collarChartedSpace (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] :
    ChartedSpace (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) M :=
  letI := EuclideanHalfSpace.collarModelChartedSpace n
  ChartedSpace.comp _ (EuclideanHalfSpace (n + 1)) M

/-- **The preferred chart of `collarChartedSpace` is the collar chart of the preferred ambient
chart.** Consumers should rewrite with this rather than unfold the definition. -/
@[simp]
theorem collarChartedSpace_chartAt (x : M) :
    @chartAt (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) _ M _ (collarChartedSpace n M) x =
      collarChart (chartAt (EuclideanHalfSpace (n + 1)) x) := by
  let := EuclideanHalfSpace.collarModelChartedSpace n
  rw [collarChartedSpace, chartAt_comp, EuclideanHalfSpace.collarModelChartedSpace_chartAt]
  rfl

/-- The atlas of `collarChartedSpace` is the collar chart of every ambient chart. -/
@[simp]
theorem collarChartedSpace_atlas :
    @atlas (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) _ M _ (collarChartedSpace n M) =
      collarChart '' atlas (EuclideanHalfSpace (n + 1)) M := by
  let := EuclideanHalfSpace.collarModelChartedSpace n
  rw [collarChartedSpace]
  -- `ChartedSpace.comp` stores its atlas as `image2 trans (atlas H' M) (atlas H H')`. That is
  -- the field itself, not a rewrite target, so name it with `change` before the `image2` lemmas
  -- can apply; `rw` cannot reach through the structure projection on its own.
  change Set.image2 OpenPartialHomeomorph.trans (atlas (EuclideanHalfSpace (n + 1)) M) _ = _
  rw [EuclideanHalfSpace.collarModelChartedSpace_atlas, Set.image2_singleton_right]
  -- what remains is that composing with the collar identification *is* `collarChart`; after
  -- unfolding, the two sides differ only in the name of the bound chart.
  unfold collarChart
  rfl

end Atlas

end TauCeti
