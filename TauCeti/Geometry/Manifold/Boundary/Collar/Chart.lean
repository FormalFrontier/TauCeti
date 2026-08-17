/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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
boundary model, and a normal coordinate in `[0, ∞)`. Two facts make it deserve the name.

* **The boundary is the zero slice.** For an atlas chart `e` and a point of `e.source`, lying on
  `I.boundary M` becomes the vanishing of one product factor — the normal coordinate — of the
  collar chart of `e`.
* **The tangential coordinate is the boundary chart.** On boundary points the first component of
  the collar chart induced by the preferred ambient chart is the preferred chart of the boundary
  manifold built in `Boundary.Charts`. The two files therefore describe one coordinate system,
  not two.

The chart is built from `collarDiffeomorph` at the top regularity `⊤`. Since `⊤` is the top of
`WithTop ℕ∞`, `ContMDiff.of_le le_top` downcasts its smoothness to whatever exponent a caller
needs, so one chart serves every regularity.

Those coordinates are smooth, not merely continuous: `contMDiffOn_collarChart` and
`contMDiffOn_collarChart_symm` make a collar chart a `C^k` diffeomorphism between its source and
its target, for a chart in `IsManifold.maximalAtlas`. Read with
`mem_boundary_iff_collarChart_snd_apply_zero_eq_zero`, they give smooth local product
*coordinates* whose normal component cuts out the boundary. They do not give a collar: the target
of a collar chart is `⇑collarDiffeomorph ⁻¹' e.target`, an open subset of the product model, and
shrinking it to a product neighbourhood `V × [0, 1)` is not proved here.

This serves the collar-neighbourhood target in Layer 1 of the GeometricTopology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`), after `Boundary.Collar.Basic`'s standard-model
calculation. Two steps remain, neither proved here.

* That the collar charts have `C^k` transitions, so `M` is also a manifold for the product model
  `(𝓡 n).prod (𝓡∂ 1)` via `collarChartedSpace`. The two lemmas above bring this within reach —
  they are about single charts against the half-space model, not about the transitions — but no
  `HasGroupoid` or `IsManifold` instance for `collarChartedSpace` exists yet.
* The global statement, that a whole neighbourhood of `I.boundary M` is diffeomorphic to
  `I.boundary M × [0, 1)`. The two textbook routes differ in what they need. Lee Thm 9.25 goes
  through the Boundary Flowout Theorem, gluing an inward-pointing vector field and flowing it,
  which needs flows from boundary points; Mathlib's integral curves are still restricted to
  interior points, so that route waits on them. Hirsch Thm 6.1 instead glues local retractions
  with a bump function and pairs the resulting retraction `r` with a `g` vanishing on the boundary
  and regular there, taking `h = (r, g)`; that route needs no flows. (Hirsch §5.2 gives the
  differential-equations proof as an alternative.)

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
* `TauCeti.contMDiffOn_collarChart` and `TauCeti.contMDiffOn_collarChart_symm`: a collar chart
  and its inverse are `C^k`, so the local product coordinates are smooth.

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

`collarDiffeomorph` is taken at the top regularity `⊤` because `ContMDiff.of_le le_top` downcasts
its smoothness to any `k`, so this one chart serves every regularity. Its underlying map does not
depend on the exponent either, so the topological lemmas below are equally unaffected.

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

section Smooth

variable [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-- **A collar chart is `C^k` on its source.** The collar identification is a diffeomorphism, so
splitting an ambient chart into a tangential and a normal coordinate costs no regularity. -/
theorem contMDiffOn_collarChart {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) k M) :
    ContMDiffOn (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k (collarChart e) e.source :=
  (((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm.contMDiff.of_le le_top).comp_contMDiffOn
    (contMDiffOn_of_mem_maximalAtlas he)).congr fun x _ => collarChart_apply e x

/-- **The inverse of a collar chart is `C^k` on its target.** With `contMDiffOn_collarChart`,
a collar chart of a `maximalAtlas` member is a `C^k` diffeomorphism between its source and its
target, so on that source `M` carries smooth tangential and normal coordinates. The target is an
open subset of the product model, not a product neighbourhood. -/
theorem contMDiffOn_collarChart_symm
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) k M) :
    ContMDiffOn ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k (collarChart e).symm
      (collarChart e).target := by
  have hmaps : Set.MapsTo (EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n)
      (collarChart e).target e.target := fun p hp => by
    rwa [collarChart_target] at hp
  exact ((contMDiffOn_symm_of_mem_maximalAtlas he).comp
    ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).contMDiff.of_le le_top).contMDiffOn
    hmaps).congr fun p _ => collarChart_symm_apply e p

end Smooth

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
`HasGroupoid.comp` all apply to it — `HasGroupoid.comp` is the route to the `C^k` transitions that
would make `M` a manifold for the product model, which is not proved yet.

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
