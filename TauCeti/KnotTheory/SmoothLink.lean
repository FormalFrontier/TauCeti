/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Geometric presentation of knots and links

This file builds the geometric presentation layer of knot theory, as specified in Layer 4 of the
GeometricTopology roadmap (`TauCetiRoadmap/GeometricTopology/README.md`, layer 4, "knot theory,
done properly"). Knots have no single privileged representation; the geometric presentation
represents an unoriented knot as a smooth embedding of the 1-sphere $S^1$ into an ambient
manifold $M$. Oriented presentations carry a manifold orientation of the circle source,
represented by a smooth nowhere-zero tangent vector field, and framed presentations in a
3-manifold additionally carry a framed tubular embedding.

This file introduces:
* `TauCeti.Sphere1` / `TauCeti.Sphere3`: the standard 1-sphere and 3-sphere in Euclidean space.
* `TauCeti.UnorientedSmoothKnot`: unoriented smooth embeddings $S^1 \hookrightarrow M$.
* `TauCeti.OrientedSmoothKnot`: smooth knots carrying a source orientation.
* `TauCeti.SmoothKnot`: framed, oriented smooth knots carrying a tubular embedding.
* `TauCeti.SmoothKnot3`: smooth knots in the 3-sphere $S^3$.
* `TauCeti.SmoothLink`: $k$-component smooth links in a 3-manifold $M$, bundling $k$
  component knots with pairwise disjoint tubular neighborhoods.
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
a smooth nowhere-zero tangent vector field on its circle source. In one dimension, such a field is
equivalent to a manifold orientation and records a direction around the knot. -/
structure OrientedSmoothKnot (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] where
  /-- The underlying unoriented smooth knot. -/
  knot : UnorientedSmoothKnot I M
  /-- The chosen tangent direction at each point of the circle source. -/
  direction : ∀ x : Sphere1, TangentSpace (𝓡 1) x
  /-- The chosen tangent direction never vanishes. -/
  direction_ne_zero (x : Sphere1) : direction x ≠ 0
  /-- The chosen tangent direction varies smoothly around the circle. -/
  direction_smooth : ContMDiff (𝓡 1) (𝓡 1).tangent ∞
    (fun x ↦ (⟨x, direction x⟩ : TangentBundle (𝓡 1) Sphere1))

namespace OrientedSmoothKnot

/-- Forget the orientation of an oriented smooth knot. -/
def forgetOrientation (K : OrientedSmoothKnot I M) : UnorientedSmoothKnot I M := K.knot

/-- The tangent direction along the embedded knot induced by its source orientation. -/
noncomputable def tangentDirection (K : OrientedSmoothKnot I M) (x : Sphere1) :
    TangentSpace I (K.knot x) :=
  mfderiv (𝓡 1) I K.knot x (K.direction x)

/-- Reverse the orientation of an oriented smooth knot. -/
noncomputable def reverseOrientation (K : OrientedSmoothKnot I M) : OrientedSmoothKnot I M where
  knot := K.knot
  direction x := -K.direction x
  direction_ne_zero x := neg_ne_zero.mpr (K.direction_ne_zero x)
  direction_smooth := K.direction_smooth.neg_section

@[simp]
theorem tangentDirection_reverseOrientation (K : OrientedSmoothKnot I M) (x : Sphere1) :
    tangentDirection I M (reverseOrientation I M K) x = -tangentDirection I M K x := by
  change (mfderiv (𝓡 1) I K.knot x) (-K.direction x) =
    -(mfderiv (𝓡 1) I K.knot x) (K.direction x)
  exact map_neg _ _

end OrientedSmoothKnot

/-- A framed oriented smooth knot in a 3-manifold consists of an oriented core together with an
embedding of its trivial rank-two normal bundle as a tubular neighborhood. The two normal
coordinates record the framing. -/
structure FramedOrientedSmoothKnot
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] where
  /-- The underlying oriented smooth knot. -/
  knot : OrientedSmoothKnot I M
  /-- A tubular embedding with two framed normal coordinates. -/
  tubularEmbedding :
    SmoothEmbedding
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))) I ∞
      (Sphere1 × EuclideanSpace ℝ (Fin 2)) M
  /-- The zero section of the tubular embedding is the underlying knot. -/
  tubularEmbedding_zero (x : Sphere1) : tubularEmbedding (x, 0) = knot.knot x

namespace FramedOrientedSmoothKnot

variable {H₃ : Type*} [TopologicalSpace H₃]
  {I₃ : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H₃}
  {M₃ : Type*} [TopologicalSpace M₃] [ChartedSpace H₃ M₃]

/-- Forget the framing of a framed, oriented smooth knot. -/
def forgetFraming (K : FramedOrientedSmoothKnot I₃ M₃) : OrientedSmoothKnot I₃ M₃ := K.knot

/-- Forget both the framing and orientation of a framed, oriented smooth knot. -/
def forget (K : FramedOrientedSmoothKnot I₃ M₃) : UnorientedSmoothKnot I₃ M₃ :=
  K.knot.knot

end FramedOrientedSmoothKnot

/-- The default smooth-knot presentation carries both orientation and framing data. -/
public abbrev SmoothKnot (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : Type _ :=
  FramedOrientedSmoothKnot I M

/-- An unoriented smooth knot in the standard 3-sphere `Sphere3`. -/
public abbrev UnorientedSmoothKnot3 : Type _ := UnorientedSmoothKnot (𝓡 3) Sphere3

/-- An oriented smooth knot in the standard 3-sphere `Sphere3`. -/
public abbrev OrientedSmoothKnot3 : Type _ := OrientedSmoothKnot (𝓡 3) Sphere3

/-- A framed, oriented smooth knot in the standard 3-sphere `Sphere3`. -/
public abbrev SmoothKnot3 : Type _ := SmoothKnot (𝓡 3) Sphere3

/-- A `k`-component smooth link in a 3-manifold `M` consists of `k` framed oriented knots with
pairwise disjoint tubular neighborhoods. -/
structure SmoothLink (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] (k : ℕ) where
  /-- The individual component knots of the link. -/
  component : Fin k → SmoothKnot I M
  /-- Different components have disjoint tubular neighborhoods in `M`. -/
  pairwise_disjoint : Pairwise fun i j =>
    Disjoint (range (component i).tubularEmbedding) (range (component j).tubularEmbedding)

/-- A `k`-component smooth link in the standard 3-sphere `Sphere3`. -/
public abbrev SmoothLink3 (k : ℕ) : Type _ := SmoothLink (𝓡 3) Sphere3 k

namespace SmoothLink

variable {H₃ : Type*} [TopologicalSpace H₃]
  {I₃ : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H₃}
  {M₃ : Type*} [TopologicalSpace M₃] [ChartedSpace H₃ M₃]

/-- Convert a single smooth knot into a 1-component smooth link. -/
def ofKnot (K : SmoothKnot I₃ M₃) : SmoothLink I₃ M₃ 1 where
  component _ := K
  pairwise_disjoint := Subsingleton.pairwise

/-- Distinct components of a smooth link are distinct framed knot presentations. -/
theorem component_injective {k : ℕ} (L : SmoothLink I₃ M₃ k) :
    Function.Injective L.component := by
  let _ : Nonempty Sphere1 := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  intro i j hij
  by_contra hne
  have hdisjoint := L.pairwise_disjoint hne
  have hrange : range (L.component i).tubularEmbedding =
      range (L.component j).tubularEmbedding :=
    congrArg (fun K : SmoothKnot I₃ M₃ ↦ range K.tubularEmbedding) hij
  exact hdisjoint.ne (range_nonempty (L.component i).tubularEmbedding).ne_empty hrange

end SmoothLink

end TauCeti
