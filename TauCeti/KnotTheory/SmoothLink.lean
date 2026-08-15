/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.LinearAlgebra.Orientation
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Geometric presentation of knots and links

This file builds the geometric presentation layer of knot theory, as specified in Layer 4 of the
GeometricTopology roadmap (`TauCetiRoadmap/GeometricTopology/README.md`, layer 4, "knot theory,
done properly"). Knots have no single privileged representation; the geometric presentation
represents an unoriented knot as a smooth embedding of the 1-sphere $S^1$ into an ambient
manifold $M$. Oriented presentations carry a manifold orientation of the circle source,
represented by the orientation of its 1-dimensional tangent model space, and framed presentations
in a 3-manifold carry a framing of the normal bundle, represented by the normal-bundle twist
coefficient relative to the canonical reference framing.

This file introduces:
* `TauCeti.Sphere1` / `TauCeti.Sphere3`: the standard 1-sphere and 3-sphere in Euclidean space.
* `TauCeti.Sphere1.Orientation`: manifold orientation of $S^1$ via the orientation of its 1D
  tangent model space.
* `TauCeti.UnorientedSmoothKnot`: unoriented smooth embeddings $S^1 \hookrightarrow M$.
* `TauCeti.OrientedSmoothKnot`: smooth knots carrying a source orientation.
* `TauCeti.KnotFraming`: normal-bundle framings of an oriented knot parameterized by twist
  coefficient.
* `TauCeti.FramedOrientedSmoothKnot`: framed, oriented smooth knots in a 3-manifold.
* `TauCeti.FramedOrientedSmoothKnot3`: framed, oriented smooth knots in the 3-sphere $S^3$.
* `TauCeti.FramedOrientedSmoothLink`: $k$-component framed oriented smooth links in a 3-manifold
  $M$, bundling $k$ component knots with pairwise disjoint core embedding images.
* `TauCeti.FramedOrientedSmoothLink3`: framed oriented smooth $k$-component links in $S^3$.

## Main definitions

* `TauCeti.Sphere1.Orientation`: manifold orientation of $S^1$.
* `TauCeti.UnorientedSmoothKnot`: type of smooth embeddings $S^1 \hookrightarrow M$.
* `TauCeti.OrientedSmoothKnot`: oriented smooth geometric presentations.
* `TauCeti.KnotFraming`: normal-bundle framing parameter for oriented smooth knots.
* `TauCeti.FramedOrientedSmoothKnot`: framed, oriented smooth geometric presentations.
* `TauCeti.FramedOrientedSmoothLink`: type of $k$-component framed oriented links in $M$.

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

/-- A manifold orientation of the standard 1-sphere `Sphere1`, defined as an orientation of its
1-dimensional tangent model space `EuclideanSpace ℝ (Fin 1)`. -/
public abbrev Sphere1.Orientation : Type :=
  _root_.Orientation ℝ (EuclideanSpace ℝ (Fin 1)) (Fin 1)

namespace Sphere1.Orientation

/-- The canonical positive (counterclockwise) orientation of `Sphere1`, given by the standard
basis of `EuclideanSpace ℝ (Fin 1)`. -/
def standard : Sphere1.Orientation :=
  (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation

/-- The opposite (clockwise) orientation of `Sphere1`. -/
def opposite : Sphere1.Orientation := -standard

instance : Inhabited Sphere1.Orientation := ⟨standard⟩

@[simp]
theorem neg_standard : -standard = opposite := by
  dsimp [opposite]

@[simp]
theorem neg_opposite : -opposite = standard := by
  dsimp [opposite]
  exact _root_.neg_neg standard

@[simp]
theorem neg_neg (o : Sphere1.Orientation) : - (- o) = o :=
  _root_.neg_neg o

/-- Every circle orientation is either the standard orientation or its opposite. -/
theorem eq_standard_or_opposite (o : Sphere1.Orientation) :
    o = standard ∨ o = opposite :=
  Module.Basis.orientation_eq_or_eq_neg (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis o

/-- The standard circle orientation is distinct from the opposite orientation. -/
theorem standard_ne_opposite : standard ≠ opposite := by
  dsimp [opposite]
  exact Module.Ray.ne_neg_self standard

/-- The opposite circle orientation is distinct from the standard orientation. -/
theorem opposite_ne_standard : opposite ≠ standard :=
  standard_ne_opposite.symm

/-- Induction principle for circle orientations. -/
@[elab_as_elim]
theorem induction {P : Sphere1.Orientation → Prop}
    (h_std : P standard) (h_opp : P opposite) (o : Sphere1.Orientation) : P o := by
  rcases eq_standard_or_opposite o with rfl | rfl
  · exact h_std
  · exact h_opp

end Sphere1.Orientation

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
a manifold orientation of its circle source `Sphere1`. -/
@[ext]
structure OrientedSmoothKnot (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] where
  /-- The underlying unoriented smooth knot. -/
  knot : UnorientedSmoothKnot I M
  /-- The chosen manifold orientation of the circle source. -/
  orientation : Sphere1.Orientation

namespace OrientedSmoothKnot

/-- Forget the orientation of an oriented smooth knot. -/
def forgetOrientation (K : OrientedSmoothKnot I M) : UnorientedSmoothKnot I M := K.knot

@[simp]
theorem forgetOrientation_mk (k : UnorientedSmoothKnot I M) (o : Sphere1.Orientation) :
    (mk k o).forgetOrientation = k := (rfl)

@[simp]
theorem orientation_mk (k : UnorientedSmoothKnot I M) (o : Sphere1.Orientation) :
    (mk k o).orientation = o := (rfl)

/-- Reverse the orientation of an oriented smooth knot. -/
def reverseOrientation (K : OrientedSmoothKnot I M) : OrientedSmoothKnot I M where
  knot := K.knot
  orientation := -K.orientation

@[simp]
theorem knot_reverseOrientation (K : OrientedSmoothKnot I M) :
    (reverseOrientation I M K).knot = K.knot := (rfl)

@[simp]
theorem forgetOrientation_reverseOrientation (K : OrientedSmoothKnot I M) :
    (reverseOrientation I M K).forgetOrientation = K.forgetOrientation := (rfl)

@[simp]
theorem orientation_reverseOrientation (K : OrientedSmoothKnot I M) :
    (reverseOrientation I M K).orientation = -K.orientation := (rfl)

@[simp]
theorem reverseOrientation_reverseOrientation (K : OrientedSmoothKnot I M) :
    reverseOrientation I M (reverseOrientation I M K) = K := by
  cases K
  simp [reverseOrientation]

end OrientedSmoothKnot

variable {H₃ : Type*} [TopologicalSpace H₃]
  {I₃ : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H₃}
  {M₃ : Type*} [TopologicalSpace M₃] [ChartedSpace H₃ M₃]

/-- A framing of an oriented smooth knot `K` in a 3-manifold `M`, represented by its integer
framing coefficient (the self-linking / twist number of the normal push-off relative to the
canonical reference framing). -/
@[ext]
structure KnotFraming (K : OrientedSmoothKnot I₃ M₃) where
  /-- The integer framing coefficient (number of full twists of the normal push-off). -/
  twist : ℤ

namespace KnotFraming

variable {K : OrientedSmoothKnot I₃ M₃}

/-- The canonical (zero / untwisted) framing of an oriented smooth knot. -/
def zero (K : OrientedSmoothKnot I₃ M₃) : KnotFraming K := ⟨0⟩

instance : Inhabited (KnotFraming K) := ⟨zero K⟩

instance : Zero (KnotFraming K) := ⟨zero K⟩

@[simp]
theorem zero_twist : (0 : KnotFraming K).twist = 0 := (rfl)

@[simp]
theorem zero_eq_zero : zero K = 0 := (rfl)

/-- Induction principle for knot framings. -/
@[elab_as_elim]
theorem induction {P : KnotFraming K → Prop}
    (h : ∀ n : ℤ, P ⟨n⟩) (F : KnotFraming K) : P F := by
  cases F
  apply h

end KnotFraming

/-- A framed oriented smooth knot in a 3-manifold consists of an oriented core together with a
framing of its normal bundle. -/
@[ext]
structure FramedOrientedSmoothKnot
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] where
  /-- The underlying oriented smooth knot. -/
  knot : OrientedSmoothKnot I M
  /-- The framing of the oriented knot. -/
  framing : KnotFraming knot

namespace FramedOrientedSmoothKnot

variable {H₃ : Type*} [TopologicalSpace H₃]
  {I₃ : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H₃}
  {M₃ : Type*} [TopologicalSpace M₃] [ChartedSpace H₃ M₃]

/-- Forget the framing of a framed, oriented smooth knot. -/
def forgetFraming (K : FramedOrientedSmoothKnot I₃ M₃) : OrientedSmoothKnot I₃ M₃ := K.knot

/-- Forget both the framing and orientation of a framed, oriented smooth knot. -/
def forget (K : FramedOrientedSmoothKnot I₃ M₃) : UnorientedSmoothKnot I₃ M₃ :=
  K.knot.knot

@[simp]
theorem knot_mk (k : OrientedSmoothKnot I₃ M₃) (f : KnotFraming k) :
    (mk (I := I₃) (M := M₃) k f).knot = k := (rfl)

@[simp]
theorem framing_mk (k : OrientedSmoothKnot I₃ M₃) (f : KnotFraming k) :
    (mk (I := I₃) (M := M₃) k f).framing = f := (rfl)

@[simp]
theorem forgetFraming_mk (k : OrientedSmoothKnot I₃ M₃) (f : KnotFraming k) :
    (mk (I := I₃) (M := M₃) k f).forgetFraming = k := (rfl)

@[simp]
theorem forget_mk (k : OrientedSmoothKnot I₃ M₃) (f : KnotFraming k) :
    (mk (I := I₃) (M := M₃) k f).forget = k.knot := (rfl)

theorem forgetFraming_knot (K : FramedOrientedSmoothKnot I₃ M₃) :
    K.forgetFraming = K.knot := (rfl)

theorem forget_knot (K : FramedOrientedSmoothKnot I₃ M₃) :
    K.forget = K.knot.knot := (rfl)

@[simp]
theorem forget_forgetFraming (K : FramedOrientedSmoothKnot I₃ M₃) :
    K.forgetFraming.forgetOrientation = K.forget := (rfl)

end FramedOrientedSmoothKnot

/-- An unoriented smooth knot in the standard 3-sphere `Sphere3`. -/
public abbrev UnorientedSmoothKnot3 : Type _ := UnorientedSmoothKnot (𝓡 3) Sphere3

/-- An oriented smooth knot in the standard 3-sphere `Sphere3`. -/
public abbrev OrientedSmoothKnot3 : Type _ := OrientedSmoothKnot (𝓡 3) Sphere3

/-- A framed, oriented smooth knot in the standard 3-sphere `Sphere3`. -/
public abbrev FramedOrientedSmoothKnot3 : Type _ := FramedOrientedSmoothKnot (𝓡 3) Sphere3

/-- A `k`-component framed oriented smooth link in a 3-manifold `M` consists of `k` framed oriented
knots with pairwise disjoint core embedding images. -/
@[ext]
structure FramedOrientedSmoothLink (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] (k : ℕ) where
  /-- The individual component knots of the link. -/
  component : Fin k → FramedOrientedSmoothKnot I M
  /-- Different components have pairwise disjoint core embedding images in `M`. -/
  pairwise_disjoint : Pairwise fun i j =>
    Disjoint (range (component i).knot.knot) (range (component j).knot.knot)

/-- A `k`-component framed oriented smooth link in the standard 3-sphere `Sphere3`. -/
public abbrev FramedOrientedSmoothLink3 (k : ℕ) : Type _ := FramedOrientedSmoothLink (𝓡 3) Sphere3 k

namespace FramedOrientedSmoothLink

variable {H₃ : Type*} [TopologicalSpace H₃]
  {I₃ : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H₃}
  {M₃ : Type*} [TopologicalSpace M₃] [ChartedSpace H₃ M₃]

/-- Convert a single framed oriented smooth knot into a 1-component framed oriented smooth link. -/
def ofKnot (K : FramedOrientedSmoothKnot I₃ M₃) : FramedOrientedSmoothLink I₃ M₃ 1 where
  component _ := K
  pairwise_disjoint := Subsingleton.pairwise

@[simp]
theorem ofKnot_component (K : FramedOrientedSmoothKnot I₃ M₃) (i : Fin 1) :
    (ofKnot K).component i = K := (rfl)

/-- Distinct components of a framed oriented smooth link are distinct framed knot presentations. -/
theorem component_injective {k : ℕ} (L : FramedOrientedSmoothLink I₃ M₃ k) :
    Function.Injective L.component := by
  let _ : Nonempty Sphere1 := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  intro i j hij
  apply L.pairwise_disjoint.eq
  intro hdisj
  have hrange : range (L.component i).knot.knot = range (L.component j).knot.knot :=
    congrArg (fun K : FramedOrientedSmoothKnot I₃ M₃ ↦ range K.knot.knot) hij
  rw [hrange, disjoint_self] at hdisj
  exact (range_nonempty (L.component j).knot.knot).ne_empty hdisj

end FramedOrientedSmoothLink

end TauCeti
