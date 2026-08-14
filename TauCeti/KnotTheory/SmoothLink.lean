/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.LinearAlgebra.Orientation
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.ContinuousAmbientIsotopy.Basic

/-!
# Geometric presentation of knots and links

This file builds the geometric presentation layer of knot theory, as specified in Layer 4 of the
GeometricTopology roadmap (`TauCetiRoadmap/GeometricTopology/README.md`, layer 4, "knot theory,
done properly"). Knots have no single privileged representation; the geometric presentation
represents an unoriented knot as a smooth embedding of the 1-sphere $S^1$ into an ambient
manifold $M$. Oriented presentations carry an orientation of the one-dimensional source model,
and framed presentations additionally carry a disjoint, ambient-isotopic push-off.

This file introduces:
* `TauCeti.Sphere1` / `TauCeti.Sphere3`: the standard 1-sphere and 3-sphere in Euclidean space.
* `TauCeti.UnorientedSmoothKnot`: unoriented smooth embeddings $S^1 \hookrightarrow M$.
* `TauCeti.OrientedSmoothKnot`: smooth knots carrying a source orientation.
* `TauCeti.SmoothKnot`: framed, oriented smooth knots carrying a chosen push-off.
* `TauCeti.SmoothKnot3`: smooth knots in the 3-sphere $S^3$.
* `TauCeti.SmoothLink`: $k$-component smooth links in a general manifold $M$, bundling $k$
  component knots with pairwise disjoint images.
* `TauCeti.SmoothLink3`: smooth $k$-component links in $S^3$.

## Main definitions

* `TauCeti.UnorientedSmoothKnot`: type of smooth embeddings $S^1 \hookrightarrow M$.
* `TauCeti.OrientedSmoothKnot`: oriented smooth geometric presentations.
* `TauCeti.SmoothKnot`: framed, oriented smooth geometric presentations.
* `TauCeti.SmoothLink`: type of $k$-component links in $M$.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997).
-/

public section

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

/-- An oriented smooth-knot presentation consists of an underlying smooth embedding together with
an orientation of its one-dimensional source model. -/
structure OrientedSmoothKnot (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] where
  /-- The underlying unoriented smooth knot. -/
  knot : UnorientedSmoothKnot I M
  /-- The chosen direction on the knot. -/
  orientation : Orientation ℝ (EuclideanSpace ℝ (Fin 1)) (Fin 1)

namespace OrientedSmoothKnot

/-- Forget the orientation of an oriented smooth knot. -/
def forgetOrientation (K : OrientedSmoothKnot I M) : UnorientedSmoothKnot I M := K.knot

end OrientedSmoothKnot

/-- A framing of an oriented smooth knot is a disjoint, continuously ambient-isotopic push-off.
The push-off itself records the framing choice; continuous ambient isotopy verifies that it is a
parallel copy of the original knot rather than an unrelated component. -/
structure FramedOrientedSmoothKnot (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] where
  /-- The underlying oriented smooth knot. -/
  knot : OrientedSmoothKnot I M
  /-- The chosen push-off representing the framing. -/
  pushOff : UnorientedSmoothKnot I M
  /-- The push-off represents the same knot up to continuous ambient isotopy. -/
  isPushOff : SmoothEmbedding.ContinuousAmbientIsotopic knot.knot pushOff
  /-- The push-off is disjoint from the original knot. -/
  disjoint_pushOff :
    Disjoint (range (knot.knot : Sphere1 → M)) (range (pushOff : Sphere1 → M))

namespace FramedOrientedSmoothKnot

/-- Forget the framing of a framed, oriented smooth knot. -/
def forgetFraming (K : FramedOrientedSmoothKnot I M) : OrientedSmoothKnot I M := K.knot

/-- Forget both the framing and orientation of a framed, oriented smooth knot. -/
def forget (K : FramedOrientedSmoothKnot I M) : UnorientedSmoothKnot I M :=
  K.knot.forgetOrientation

end FramedOrientedSmoothKnot

/-- The default smooth-knot presentation carries both orientation and framing data. -/
public abbrev SmoothKnot (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : Type _ :=
  FramedOrientedSmoothKnot I M

/-- An unoriented smooth knot in the standard 3-sphere `Sphere3`. -/
public abbrev UnorientedSmoothKnot3 : Type _ := UnorientedSmoothKnot (𝓡 3) Sphere3

/-- An oriented smooth knot in the standard 3-sphere `Sphere3`. -/
public abbrev OrientedSmoothKnot3 : Type _ := OrientedSmoothKnot (𝓡 3) Sphere3

/-- A framed, oriented smooth knot in the standard 3-sphere `Sphere3`. -/
public abbrev SmoothKnot3 : Type _ := SmoothKnot (𝓡 3) Sphere3

/-- A `k`-component smooth link in an ambient manifold `M` consists of `k` smooth embeddings of
`Sphere1` into `M` with pairwise disjoint images. -/
structure SmoothLink (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (k : ℕ) where
  /-- The individual component knots of the link. -/
  component : Fin k → SmoothKnot I M
  /-- Different component knots have disjoint images in `M`. -/
  pairwise_disjoint : Pairwise fun i j =>
    Disjoint (range (component i).forget) (range (component j).forget)

/-- A `k`-component smooth link in the standard 3-sphere `Sphere3`. -/
public abbrev SmoothLink3 (k : ℕ) : Type _ := SmoothLink (𝓡 3) Sphere3 k

namespace SmoothLink

variable {I M}

/-- Convert a single smooth knot into a 1-component smooth link. -/
def ofKnot (K : SmoothKnot I M) : SmoothLink I M 1 where
  component _ := K
  pairwise_disjoint := Subsingleton.pairwise

/-- Distinct components of a smooth link are distinct smooth embeddings. -/
theorem component_injective {k : ℕ} (L : SmoothLink I M k) : Function.Injective L.component := by
  let _ : Nonempty Sphere1 := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  intro i j hij
  by_contra hne
  have hdisjoint := L.pairwise_disjoint hne
  have hrange : range (L.component i).forget = range (L.component j).forget :=
    congrArg (fun K : SmoothKnot I M ↦ range K.forget) hij
  exact hdisjoint.ne (range_nonempty (L.component i).forget).ne_empty hrange

end SmoothLink

end TauCeti
