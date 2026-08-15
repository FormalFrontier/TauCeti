/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Geometric presentation of knots and links

This file builds the geometric presentation layer of knot theory, as specified in Layer 4 of the
GeometricTopology roadmap (`TauCetiRoadmap/GeometricTopology/README.md`, layer 4, "knot theory,
done properly"). Knots have no single privileged representation; the geometric presentation
represents an unoriented knot as a smooth embedding of the 1-sphere $S^1$ into an ambient
manifold $M$. Oriented and framed presentations are deferred until their prerequisite differential
topology (manifold orientations and tubular neighbourhoods) is available.

This file introduces:
* `TauCeti.Sphere1` / `TauCeti.Sphere3`: the standard 1-sphere and 3-sphere in Euclidean space.
* `TauCeti.UnorientedSmoothKnot`: unoriented smooth embeddings $S^1 \hookrightarrow M$.
* `TauCeti.UnorientedSmoothKnot3`: unoriented smooth knots in the 3-sphere $S^3$.
* `TauCeti.SmoothKnot`: alias for `UnorientedSmoothKnot`.
* `TauCeti.SmoothKnot3`: alias for `UnorientedSmoothKnot3`.
* `TauCeti.SmoothLink`: $k$-component smooth links in a manifold $M$, bundling $k$ component knots
  with pairwise disjoint embedding images.
* `TauCeti.SmoothLink3`: smooth $k$-component links in $S^3$.
* `TauCeti.UnorientedSmoothLink` / `TauCeti.UnorientedSmoothLink3`: aliases for `SmoothLink` and
  `SmoothLink3`.

## Main definitions

* `TauCeti.Sphere1`: the standard 1-sphere $S^1 \subset \mathbb{R}^2$.
* `TauCeti.Sphere3`: the standard 3-sphere $S^3 \subset \mathbb{R}^4$.
* `TauCeti.UnorientedSmoothKnot`: type of smooth embeddings $S^1 \hookrightarrow M$.
* `TauCeti.SmoothLink`: type of $k$-component smooth links in $M$.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997).
* D. Rolfsen, *Knots and Links*, AMS Chelsea Publishing (1976).
-/

public section

noncomputable section

open scoped Manifold ContDiff
open Set

namespace TauCeti

/-- The standard 1-sphere $S^1 \subset \mathbb{R}^2$ as a subset of Euclidean space. -/
public abbrev Sphere1 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

/-- The standard 3-sphere $S^3 \subset \mathbb{R}^4$ as a subset of Euclidean space. -/
public abbrev Sphere3 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- An unoriented smooth-knot presentation in an ambient manifold `M` is a bundled `C^∞` smooth
embedding of the standard 1-sphere `Sphere1` into `M`. -/
public abbrev UnorientedSmoothKnot (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : Type _ :=
  SmoothEmbedding (𝓡 1) I ∞ Sphere1 M

/-- An unoriented smooth knot in the standard 3-sphere `Sphere3`. -/
public abbrev UnorientedSmoothKnot3 : Type _ := UnorientedSmoothKnot (𝓡 3) Sphere3

/-- Alias for `UnorientedSmoothKnot` as the geometric smooth-knot presentation. -/
public abbrev SmoothKnot (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : Type _ :=
  UnorientedSmoothKnot I M

/-- Alias for `UnorientedSmoothKnot3`. -/
public abbrev SmoothKnot3 : Type _ := UnorientedSmoothKnot3

/-- A `k`-component smooth link in a manifold `M` consists of `k` unoriented component knots with
pairwise disjoint embedding images. -/
@[ext]
structure SmoothLink (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] (k : ℕ) where
  /-- The individual component knots of the link. -/
  component : Fin k → UnorientedSmoothKnot I M
  /-- Different components have pairwise disjoint embedding images in `M`. -/
  pairwise_disjoint : Pairwise fun i j =>
    Disjoint (range (component i)) (range (component j))

/-- Alias for `SmoothLink`. -/
public abbrev UnorientedSmoothLink (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] (k : ℕ) : Type _ :=
  SmoothLink I M k

/-- A `k`-component smooth link in the standard 3-sphere `Sphere3`. -/
public abbrev SmoothLink3 (k : ℕ) : Type _ := SmoothLink (𝓡 3) Sphere3 k

/-- Alias for `SmoothLink3`. -/
public abbrev UnorientedSmoothLink3 (k : ℕ) : Type _ := SmoothLink3 k

namespace SmoothLink

variable {I M}

/-- Convert a single unoriented smooth knot into a 1-component smooth link. -/
def ofKnot (K : UnorientedSmoothKnot I M) : SmoothLink I M 1 where
  component _ := K
  pairwise_disjoint := Subsingleton.pairwise

@[simp]
theorem ofKnot_component (K : UnorientedSmoothKnot I M) (i : Fin 1) :
    (ofKnot K).component i = K := (rfl)

/-- Distinct components of a smooth link are distinct knot embeddings. -/
theorem component_injective {k : ℕ} (L : SmoothLink I M k) :
    Function.Injective L.component := by
  let _ : Nonempty Sphere1 := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  intro i j hij
  apply L.pairwise_disjoint.eq
  intro hdisj
  have hrange : range (L.component i) = range (L.component j) :=
    congrArg (fun K : UnorientedSmoothKnot I M ↦ range (⇑K)) hij
  rw [hrange, disjoint_self] at hdisj
  exact (range_nonempty (L.component j)).ne_empty hdisj

end SmoothLink

end TauCeti
