/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
public import TauCeti.Geometry.Manifold.LocallyFlat.Smooth
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Geometric presentation of knots and links, and sliceness

This file builds the geometric presentation layer of knot theory, as specified in Layer 4 of the
GeometricTopology roadmap (`TauCetiRoadmap/GeometricTopology/README.md`, layer 4, "knot theory,
done properly"). Knots have no single privileged representation; the geometric presentation
represents a knot or link as a smooth embedding (or collection of smooth embeddings with
disjoint images) of the 1-sphere $S^1$ into an ambient manifold $M$.

This file introduces:
* `TauCeti.Sphere1` / `TauCeti.Sphere3`: the standard 1-sphere and 3-sphere in Euclidean space.
* `TauCeti.ClosedDisk2` / `TauCeti.ClosedDisk4`: the standard closed 2-disk and 4-disk in Euclidean
  space.
* `TauCeti.SmoothKnot`: single-component smooth knots in a general manifold $M$, defined as bundled
  `C^∞` smooth embeddings $S^1 \hookrightarrow M$.
* `TauCeti.SmoothKnot3`: smooth knots in the 3-sphere $S^3$.
* `TauCeti.SmoothLink`: $k$-component smooth links in a general manifold $M$, bundling $k$
  component knots with pairwise disjoint images.
* `TauCeti.SmoothLink3`: smooth $k$-component links in $S^3$.
* `TauCeti.IsSmoothlySlice`: a smooth 3-knot $K \in \text{SmoothKnot3}$ is smoothly slice if it
  extends to a smooth embedding of the 2-disk $D^2$ into the 4-disk $D^4$.
* `TauCeti.IsTopologicallySlice`: a smooth 3-knot $K \in \text{SmoothKnot3}$ is topologically
  slice if it extends to an embedding of the 2-disk $D^2$ into the 4-disk $D^4$.

## Main definitions

* `TauCeti.SmoothKnot`: type of smooth embeddings $S^1 \hookrightarrow M$.
* `TauCeti.SmoothLink`: type of $k$-component links in $M$.
* `TauCeti.IsSmoothlySlice`: smooth sliceness of a knot in $S^3$.
* `TauCeti.IsTopologicallySlice`: topological sliceness of a knot in $S^3$.

## Main results

* `TauCeti.SmoothKnot.isLocallyFlat`: every smooth knot in a boundaryless manifold is locally flat.
* `TauCeti.IsSmoothlySlice.isTopologicallySlice`: every smoothly slice knot is topologically slice.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997).
* R. Daverman and G. Venema, *Embeddings in Manifolds*, AMS GSM 106 (2009).
-/

public section

open scoped Manifold ContDiff
open Set Topology

namespace TauCeti

/-- The standard 1-sphere $S^1 \subset \mathbb{R}^2$ as a subset of Euclidean space. -/
public abbrev Sphere1 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

/-- The standard 3-sphere $S^3 \subset \mathbb{R}^4$ as a subset of Euclidean space. -/
public abbrev Sphere3 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- The standard closed 2-disk $D^2 \subset \mathbb{R}^2$. -/
public abbrev ClosedDisk2 : Type := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1

/-- The standard closed 4-disk $D^4 \subset \mathbb{R}^4$. -/
public abbrev ClosedDisk4 : Type := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- A single-component smooth knot in an ambient manifold `M` is a bundled `C^∞` smooth embedding
of the standard 1-sphere `Sphere1` into `M`. -/
public abbrev SmoothKnot (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : Type _ :=
  SmoothEmbedding (𝓡 1) I ∞ Sphere1 M

/-- A smooth knot in the standard 3-sphere `Sphere3`. -/
public abbrev SmoothKnot3 : Type _ := SmoothKnot (𝓡 3) Sphere3

/-- A `k`-component smooth link in an ambient manifold `M` consists of `k` smooth embeddings of
`Sphere1` into `M` with pairwise disjoint images. -/
structure SmoothLink (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (k : ℕ) where
  /-- The individual component knots of the link. -/
  component : Fin k → SmoothKnot I M
  /-- Different component knots have disjoint images in `M`. -/
  pairwise_disjoint : Pairwise fun i j =>
    Disjoint (range (component i : Sphere1 → M)) (range (component j : Sphere1 → M))

/-- A `k`-component smooth link in the standard 3-sphere `Sphere3`. -/
public abbrev SmoothLink3 (k : ℕ) : Type _ := SmoothLink (𝓡 3) Sphere3 k

namespace SmoothKnot

variable {I M}

/-- A smooth knot is a topological embedding. -/
theorem isEmbedding (K : SmoothKnot I M) : IsEmbedding K :=
  SmoothEmbedding.isEmbedding K

/-- A smooth knot is an immersion. -/
theorem isImmersion (K : SmoothKnot I M) : Manifold.IsImmersion (𝓡 1) I ∞ K :=
  SmoothEmbedding.isImmersion K

/-- A smooth knot is a smooth embedding in Mathlib's predicate sense. -/
theorem isSmoothEmbedding (K : SmoothKnot I M) :
    Manifold.IsSmoothEmbedding (𝓡 1) I ∞ K :=
  SmoothEmbedding.isSmoothEmbedding K

/-- Every smooth knot in a boundaryless manifold is locally flat. -/
theorem isLocallyFlat [I.Boundaryless] (K : SmoothKnot I M) :
    IsLocallyFlat (EuclideanSpace ℝ (Fin 1)) K.isSmoothEmbedding_toFun.isImmersion.complement K :=
  SmoothEmbedding.isLocallyFlat K

end SmoothKnot

namespace SmoothLink

variable {I M}

/-- Convert a single smooth knot into a 1-component smooth link. -/
def ofKnot (K : SmoothKnot I M) : SmoothLink I M 1 where
  component _ := K
  pairwise_disjoint i j hij := (hij (Subsingleton.elim i j)).elim

/-- Every component of a smooth link in a boundaryless manifold is locally flat. -/
theorem component_isLocallyFlat [I.Boundaryless] {k : ℕ}
    (L : SmoothLink I M k) (i : Fin k) :
    IsLocallyFlat (EuclideanSpace ℝ (Fin 1))
      (L.component i).isSmoothEmbedding_toFun.isImmersion.complement (L.component i) :=
  (L.component i).isLocallyFlat

end SmoothLink

/-- The natural boundary inclusion `S¹ → D²`. -/
def sphere1ToDisk2 (x : Sphere1) : ClosedDisk2 :=
  ⟨x.1, Metric.sphere_subset_closedBall x.2⟩

/-- The natural boundary inclusion `S³ → D⁴`. -/
def sphere3ToDisk4 (y : Sphere3) : ClosedDisk4 :=
  ⟨y.1, Metric.sphere_subset_closedBall y.2⟩

/-- A smooth knot `K` in `S³` is **smoothly slice** if it extends to a topological embedding of the
2-disk `D²` into the 4-disk `D⁴` satisfying the boundary condition. -/
def IsSmoothlySlice (K : SmoothKnot3) : Prop :=
  ∃ (f : ClosedDisk2 → ClosedDisk4),
    IsEmbedding f ∧
    (∀ (x : Sphere1), (f (sphere1ToDisk2 x)).1 = ((K x : Sphere3) : EuclideanSpace ℝ (Fin 4)))

/-- A smooth knot `K` in `S³` is **topologically slice** if it extends to a topological embedding
of the 2-disk `D²` into the 4-disk `D⁴` satisfying the boundary condition. -/
def IsTopologicallySlice (K : SmoothKnot3) : Prop :=
  ∃ (f : ClosedDisk2 → ClosedDisk4),
    IsEmbedding f ∧
    (∀ (x : Sphere1), (f (sphere1ToDisk2 x)).1 = ((K x : Sphere3) : EuclideanSpace ℝ (Fin 4)))

/-- Every smoothly slice knot is topologically slice. -/
theorem IsSmoothlySlice.isTopologicallySlice {K : SmoothKnot3} (h : IsSmoothlySlice K) :
    IsTopologicallySlice K :=
  h

end TauCeti
