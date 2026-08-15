/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Sphere.Defs

/-!
# Geometric presentation of knots and links

This file builds the geometric presentation layer of knot theory, as specified in Layer 4 of the
GeometricTopology roadmap (`TauCetiRoadmap/GeometricTopology/README.md`, layer 4, "knot theory,
done properly"). Knots have no single privileged representation; the geometric presentation
represents a knot as a smooth embedding of the circle `Circle` into an ambient charted space $M$.
The embedding is parametrized and no quotient by reparametrization or reversal is taken, so
orientation is not tracked as a separate structure yet.

This file introduces:
* `TauCeti.SmoothKnot`: smooth embeddings $\mathrm{Circle} \hookrightarrow M$.
* `TauCeti.SmoothKnotSphere3`: smooth knots in the 3-sphere $S^3$.
* `TauCeti.SmoothLink`: $k$-component smooth-link presentations in a charted space $M$, bundling
  $k$ component knots with pairwise disjoint embedding images.
* `TauCeti.SmoothLinkSphere3`: smooth $k$-component links in $S^3$.

## Main definitions

* `TauCeti.SmoothKnot`: type of smooth embeddings $\mathrm{Circle} \hookrightarrow M$.
* `TauCeti.SmoothKnotSphere3`: type of smooth knots in the standard 3-sphere $S^3$.
* `TauCeti.SmoothLink`: type of $k$-component smooth links in $M$.
* `TauCeti.SmoothLinkSphere3`: type of $k$-component smooth links in $S^3$.
* `TauCeti.SmoothLink.disjoint_range`: disjointness of component embedding images.
* `TauCeti.SmoothLink.apply_ne_apply`: distinct components take different values at any
  pair of points.
* `TauCeti.SmoothLink.pairwise_disjoint_range_iff`: equivalence between pairwise disjoint
  component ranges and pointwise separation.
* `TauCeti.SmoothLink.component_injective`: distinct components of a smooth link are distinct
  knot embeddings.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997).
* D. Rolfsen, *Knots and Links*, AMS Chelsea Publishing (1976).
-/

public section

noncomputable section

open scoped Manifold ContDiff
open Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- A smooth-knot presentation in an ambient charted space `M` is a bundled `C^∞` smooth
embedding of the standard circle `Circle` into `M`. The embedding is parametrized and no quotient
by reparametrization or reversal is taken, so orientation is not tracked as a separate
structure yet. -/
public abbrev SmoothKnot (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : Type _ :=
  SmoothEmbedding (𝓡 1) I ∞ Circle M

/-- A smooth knot in the standard 3-sphere `Sphere3`. -/
public abbrev SmoothKnotSphere3 : Type _ := SmoothKnot (𝓡 3) Sphere3

/-- A `k`-component smooth-link presentation in a charted space `M` consists of `k` component
knots with pairwise disjoint embedding images. -/
@[ext]
structure SmoothLink (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] (k : ℕ) where
  /-- The individual component knots of the link. -/
  component : Fin k → SmoothKnot I M
  /-- Different components have pairwise disjoint embedding images in `M`. -/
  pairwise_disjoint_range : Pairwise fun i j =>
    Disjoint (range (component i)) (range (component j))

/-- A `k`-component smooth link in the standard 3-sphere `Sphere3`. -/
public abbrev SmoothLinkSphere3 (k : ℕ) : Type _ := SmoothLink (𝓡 3) Sphere3 k

namespace SmoothLink

variable {I M}

/-- Convert a single smooth knot into a 1-component smooth link. -/
def ofKnot (K : SmoothKnot I M) : SmoothLink I M 1 where
  component _ := K
  pairwise_disjoint_range := Subsingleton.pairwise

@[simp]
theorem ofKnot_component (K : SmoothKnot I M) (i : Fin 1) :
    (ofKnot K).component i = K := (rfl)

/-- The embedding images of distinct components of a smooth link are disjoint. -/
theorem disjoint_range {k : ℕ} (L : SmoothLink I M k) {i j : Fin k} (h : i ≠ j) :
    Disjoint (range (L.component i)) (range (L.component j)) :=
  L.pairwise_disjoint_range h

/-- Two distinct components of a smooth link take different values at any pair of points. -/
theorem apply_ne_apply {k : ℕ} (L : SmoothLink I M k) {i j : Fin k} (h : i ≠ j)
    (x y : Circle) : L.component i x ≠ L.component j y :=
  Disjoint.ne_of_mem (L.disjoint_range h) (mem_range_self x) (mem_range_self y)

/-- Characterisation of pairwise disjointness of component ranges in terms of pointwise
separation. -/
theorem pairwise_disjoint_range_iff {k : ℕ} (c : Fin k → SmoothKnot I M) :
    (Pairwise fun i j => Disjoint (range (c i)) (range (c j))) ↔
      ∀ i j, i ≠ j → ∀ x y, c i x ≠ c j y := by
  constructor
  · intro h i j hij x y
    exact Disjoint.ne_of_mem (h hij) (mem_range_self x) (mem_range_self y)
  · intro h i j hij
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    exact h i j hij x y hy.symm

/-- Distinct components of a smooth link are distinct knot embeddings. -/
theorem component_injective {k : ℕ} (L : SmoothLink I M k) :
    Function.Injective L.component := by
  intro i j hij
  apply L.pairwise_disjoint_range.eq
  intro hdisj
  rw [hij, disjoint_self, Set.bot_eq_empty] at hdisj
  exact (range_nonempty (L.component j)).ne_empty hdisj

end SmoothLink

end TauCeti
