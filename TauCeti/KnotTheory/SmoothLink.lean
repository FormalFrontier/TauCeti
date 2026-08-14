/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.LinearAlgebra.Ray
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Geometric presentation of knots and links

This file builds the geometric presentation layer of knot theory, as specified in Layer 4 of the
GeometricTopology roadmap (`TauCetiRoadmap/GeometricTopology/README.md`, layer 4, "knot theory,
done properly"). Knots have no single privileged representation; the geometric presentation
represents an unoriented knot as a smooth embedding of the 1-sphere $S^1$ into an ambient
manifold $M$. Oriented presentations carry a manifold orientation of the circle source,
represented as an equivalence class of smooth nowhere-zero tangent vector fields modulo positive
scaling, and framed presentations in a 3-manifold carry a framing of the normal bundle,
represented as an equivalence class of tubular neighborhood embeddings modulo agreement of their
induced normal derivative along the core.

This file introduces:
* `TauCeti.Sphere1` / `TauCeti.Sphere3`: the standard 1-sphere and 3-sphere in Euclidean space.
* `TauCeti.Sphere1.NonvanishingTangentField`: smooth nowhere-zero tangent vector fields on $S^1$.
* `TauCeti.Sphere1.Orientation`: manifold orientations of $S^1$ as the quotient of nonvanishing
  tangent fields under pointwise positive scaling.
* `TauCeti.UnorientedSmoothKnot`: unoriented smooth embeddings $S^1 \hookrightarrow M$.
* `TauCeti.OrientedSmoothKnot`: smooth knots carrying a source orientation.
* `TauCeti.KnotTubularEmbedding`: tubular neighborhood embeddings of an oriented knot.
* `TauCeti.KnotFraming`: framings of an oriented knot as the quotient of tubular embeddings
  modulo equality of induced normal derivatives.
* `TauCeti.FramedOrientedSmoothKnot`: framed, oriented smooth knots in a 3-manifold.
* `TauCeti.FramedOrientedSmoothKnot3`: framed, oriented smooth knots in the 3-sphere $S^3$.
* `TauCeti.FramedOrientedSmoothLink`: $k$-component framed oriented smooth links in a 3-manifold
  $M$, bundling $k$ component knots with pairwise disjoint core embedding images.
* `TauCeti.FramedOrientedSmoothLink3`: framed oriented smooth $k$-component links in $S^3$.

## Main definitions

* `TauCeti.Sphere1.Orientation`: manifold orientation of $S^1$.
* `TauCeti.UnorientedSmoothKnot`: type of smooth embeddings $S^1 \hookrightarrow M$.
* `TauCeti.OrientedSmoothKnot`: oriented smooth geometric presentations.
* `TauCeti.KnotTubularEmbedding`: tubular neighborhood embeddings of an oriented knot.
* `TauCeti.KnotFraming`: framing quotient for oriented smooth knots.
* `TauCeti.FramedOrientedSmoothKnot`: framed, oriented smooth geometric presentations.
* `TauCeti.FramedOrientedSmoothLink`: type of $k$-component framed oriented links in $M$.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997).
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

/-- A smooth nowhere-zero tangent vector field on the standard 1-sphere `Sphere1`. -/
structure Sphere1.NonvanishingTangentField where
  /-- The tangent vector at each point of the circle source. -/
  toFun : ∀ x : Sphere1, TangentSpace (𝓡 1) x
  /-- The vector field is nowhere zero. -/
  ne_zero' (x : Sphere1) : toFun x ≠ 0
  /-- The vector field varies smoothly around the circle. -/
  smooth' : ContMDiff (𝓡 1) (𝓡 1).tangent ∞
    (fun x ↦ (⟨x, toFun x⟩ : TangentBundle (𝓡 1) Sphere1))

namespace Sphere1.NonvanishingTangentField

instance : CoeFun Sphere1.NonvanishingTangentField
    (fun _ ↦ ∀ x : Sphere1, TangentSpace (𝓡 1) x) where
  coe v := v.toFun

@[simp]
theorem coe_mk (f : ∀ x : Sphere1, TangentSpace (𝓡 1) x) (hne) (hsmooth) :
    ⇑(mk f hne hsmooth) = f := (rfl)

/-- Negating a nowhere-zero tangent vector field on `Sphere1`. -/
def neg (v : Sphere1.NonvanishingTangentField) : Sphere1.NonvanishingTangentField where
  toFun x := -v.toFun x
  ne_zero' x := neg_ne_zero.mpr (v.ne_zero' x)
  smooth' := ContMDiff.neg_section v.smooth'

instance : Neg Sphere1.NonvanishingTangentField where
  neg := neg

@[simp]
theorem coe_neg (v : Sphere1.NonvanishingTangentField) (x : Sphere1) :
    (-v) x = -v x := (rfl)

/-- Two nonvanishing tangent vector fields on `Sphere1` determine the same orientation if they
belong to the same ray (are positive multiples of each other) at every point. -/
def SameOrientation (v₁ v₂ : Sphere1.NonvanishingTangentField) : Prop :=
  ∀ x : Sphere1, SameRay ℝ (v₁ x) (v₂ x)

theorem sameOrientation_refl (v : Sphere1.NonvanishingTangentField) :
    SameOrientation v v :=
  fun x ↦ SameRay.refl (v x)

theorem sameOrientation_symm {v₁ v₂ : Sphere1.NonvanishingTangentField}
    (h : SameOrientation v₁ v₂) : SameOrientation v₂ v₁ :=
  fun x ↦ (h x).symm

theorem sameOrientation_trans {v₁ v₂ v₃ : Sphere1.NonvanishingTangentField}
    (h₁ : SameOrientation v₁ v₂) (h₂ : SameOrientation v₂ v₃) : SameOrientation v₁ v₃ :=
  fun x ↦ (h₁ x).trans (h₂ x) fun hzero ↦ (v₂.ne_zero' x hzero).elim

/-- Equivalence relation for positive-ray scaling of nonvanishing tangent fields on `Sphere1`. -/
instance setoid : Setoid Sphere1.NonvanishingTangentField where
  r := SameOrientation
  iseqv := {
    refl := sameOrientation_refl
    symm := sameOrientation_symm
    trans := sameOrientation_trans
  }

theorem sameOrientation_neg {v₁ v₂ : Sphere1.NonvanishingTangentField}
    (h : SameOrientation v₁ v₂) : SameOrientation (-v₁) (-v₂) :=
  fun x ↦ sameRay_neg_iff.2 (h x)

end Sphere1.NonvanishingTangentField

/-- A manifold orientation of the standard 1-sphere `Sphere1`, defined as the equivalence class
of smooth nowhere-zero tangent vector fields modulo pointwise positive scaling (`SameRay`). -/
def Sphere1.Orientation : Type :=
  Quotient Sphere1.NonvanishingTangentField.setoid

namespace Sphere1.Orientation

/-- The circle orientation represented by a smooth nowhere-zero tangent field. -/
def ofField (v : Sphere1.NonvanishingTangentField) : Sphere1.Orientation :=
  Quotient.mk Sphere1.NonvanishingTangentField.setoid v

theorem ofField_eq_ofField {v₁ v₂ : Sphere1.NonvanishingTangentField}
    (h : Sphere1.NonvanishingTangentField.SameOrientation v₁ v₂) : ofField v₁ = ofField v₂ :=
  Quotient.sound (s := Sphere1.NonvanishingTangentField.setoid) h

/-- Two nonvanishing tangent fields represent the same circle orientation if and only if they
have the same pointwise ray orientation. -/
@[simp]
theorem ofField_inj {v₁ v₂ : Sphere1.NonvanishingTangentField} :
    ofField v₁ = ofField v₂ ↔ Sphere1.NonvanishingTangentField.SameOrientation v₁ v₂ := by
  constructor
  · exact Quotient.exact (s := Sphere1.NonvanishingTangentField.setoid)
  · exact ofField_eq_ofField

/-- Induction principle for circle orientations. -/
@[elab_as_elim]
theorem induction {P : Sphere1.Orientation → Prop}
    (h : ∀ v : Sphere1.NonvanishingTangentField, P (ofField v)) (o : Sphere1.Orientation) : P o :=
  Quotient.inductionOn (s := Sphere1.NonvanishingTangentField.setoid) o h

/-- Reversing a circle orientation. -/
def neg (o : Sphere1.Orientation) : Sphere1.Orientation :=
  Quotient.liftOn (s := Sphere1.NonvanishingTangentField.setoid) o
    (fun v ↦ ofField (-v))
    (fun _ _ h ↦ ofField_eq_ofField (Sphere1.NonvanishingTangentField.sameOrientation_neg h))

instance : Neg Sphere1.Orientation where
  neg := neg

@[simp]
theorem neg_ofField (v : Sphere1.NonvanishingTangentField) :
    -ofField v = ofField (-v) := (rfl)

@[simp]
theorem neg_neg (o : Sphere1.Orientation) : - (- o) = o := by
  induction o using induction with | h v =>
  simp only [neg_ofField]
  refine ofField_eq_ofField (fun x ↦ ?_)
  simp only [Sphere1.NonvanishingTangentField.coe_neg, _root_.neg_neg, SameRay.rfl]

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

/-- A tubular neighborhood embedding for an oriented smooth knot `K` in a 3-manifold `M`. -/
structure KnotTubularEmbedding (K : OrientedSmoothKnot I₃ M₃) where
  /-- The ambient smooth embedding of the solid torus `Sphere1 × ℝ²` into `M`. -/
  toSmoothEmbedding :
    SmoothEmbedding ((𝓡 1).prod (𝓡 2)) I₃ ∞ (Sphere1 × EuclideanSpace ℝ (Fin 2)) M₃
  /-- The zero section of the tubular embedding coincides with the underlying knot. -/
  zero_section (x : Sphere1) : toSmoothEmbedding (x, (0 : EuclideanSpace ℝ (Fin 2))) = K.knot x

namespace KnotTubularEmbedding

variable {K : OrientedSmoothKnot I₃ M₃}

/-- Two tubular neighborhood embeddings of an oriented smooth knot define the same normal framing
if their differentials along the zero section agree in the normal coordinates. -/
def SameNormalFraming (T₁ T₂ : KnotTubularEmbedding K) : Prop :=
  ∀ (x : Sphere1) (w : EuclideanSpace ℝ (Fin 2)),
    mfderiv ((𝓡 1).prod (𝓡 2)) I₃
      T₁.toSmoothEmbedding (x, (0 : EuclideanSpace ℝ (Fin 2))) ((0 : TangentSpace (𝓡 1) x), w) =
    mfderiv ((𝓡 1).prod (𝓡 2)) I₃
      T₂.toSmoothEmbedding (x, (0 : EuclideanSpace ℝ (Fin 2))) ((0 : TangentSpace (𝓡 1) x), w)

theorem sameNormalFraming_refl (T : KnotTubularEmbedding K) :
    SameNormalFraming T T :=
  fun _ _ ↦ rfl

theorem sameNormalFraming_symm {T₁ T₂ : KnotTubularEmbedding K}
    (h : SameNormalFraming T₁ T₂) : SameNormalFraming T₂ T₁ :=
  fun x w ↦ (h x w).symm

theorem sameNormalFraming_trans {T₁ T₂ T₃ : KnotTubularEmbedding K}
    (h₁ : SameNormalFraming T₁ T₂) (h₂ : SameNormalFraming T₂ T₃) :
    SameNormalFraming T₁ T₃ :=
  fun x w ↦ (h₁ x w).trans (h₂ x w)

/-- Equivalence relation for tubular embeddings with the same induced normal framing. -/
instance setoid (K : OrientedSmoothKnot I₃ M₃) : Setoid (KnotTubularEmbedding K) where
  r := SameNormalFraming
  iseqv := {
    refl := sameNormalFraming_refl
    symm := sameNormalFraming_symm
    trans := sameNormalFraming_trans
  }

end KnotTubularEmbedding

/-- A framing of an oriented smooth knot `K` in a 3-manifold `M`, defined as the equivalence
class of tubular neighborhood embeddings modulo equality of their induced normal derivative
along the zero section. -/
def KnotFraming (K : OrientedSmoothKnot I₃ M₃) : Type _ :=
  Quotient (KnotTubularEmbedding.setoid K)

namespace KnotFraming

variable {K : OrientedSmoothKnot I₃ M₃}

/-- The framing represented by a tubular neighborhood embedding. -/
def ofTubularEmbedding (T : KnotTubularEmbedding K) :
    KnotFraming K :=
  Quotient.mk (KnotTubularEmbedding.setoid K) T

theorem ofTubularEmbedding_eq_ofTubularEmbedding
    {T₁ T₂ : KnotTubularEmbedding K}
    (h : KnotTubularEmbedding.SameNormalFraming T₁ T₂) :
    ofTubularEmbedding T₁ = ofTubularEmbedding T₂ :=
  Quotient.sound (s := KnotTubularEmbedding.setoid K) h

/-- Two tubular embeddings represent the same knot framing if and only if their normal
differentials along the zero section agree. -/
@[simp]
theorem ofTubularEmbedding_inj
    {T₁ T₂ : KnotTubularEmbedding K} :
    ofTubularEmbedding T₁ = ofTubularEmbedding T₂ ↔
      KnotTubularEmbedding.SameNormalFraming T₁ T₂ := by
  constructor
  · exact Quotient.exact (s := KnotTubularEmbedding.setoid K)
  · exact ofTubularEmbedding_eq_ofTubularEmbedding

/-- Induction principle for knot framings. -/
@[elab_as_elim]
theorem induction {P : KnotFraming K → Prop}
    (h : ∀ T : KnotTubularEmbedding K, P (ofTubularEmbedding T))
    (F : KnotFraming K) : P F :=
  Quotient.inductionOn (s := KnotTubularEmbedding.setoid K) F h

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
