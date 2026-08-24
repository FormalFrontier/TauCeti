/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Restriction

/-!
# The Riemannian distance on inner product spaces and their convex open subsets

The standard Riemannian metric of an inner product space `F` restricts to any open subset `U ⊆ F`
through the open-submanifold instances of `TauCeti.Geometry.Manifold.Riemannian.Restriction`. This
file computes the resulting Riemannian distance when `U` is convex: straight segments stay in `U`,
so every two points of `U` are joined by a curve of length exactly the ambient norm distance,
while no curve can be shorter than that chord. Hence

* the Riemannian extended distance of a convex open subset equals the ambient norm distance;
* with its ambient metric, a convex open subset satisfies `IsRiemannianManifold`, which makes the
  ordinary-metric layer (`dist`, closed balls, `ProperSpace`, `CompleteSpace`) available on it.

This computation is the Layer 0 target that lets downstream Hopf--Rinow work treat examples such as
the open unit ball in the ordinary metric presentation. No finite-dimensionality assumption is
needed: convexity is the only substantive hypothesis.

Along the way we record reusable facts about Mathlib's path length:

* `TauCeti.Manifold.le_riemannianEDist_of_forall_pathELength_ge`: the Riemannian extended distance
  is bounded below by any bound valid for the lengths of all `C¹` curves between two points;
* `TauCeti.Manifold.enorm_sub_le_pathELength`: a `C¹` curve in an inner product space is at least
  as long as the chord between its endpoints;
* `TauCeti.Manifold.pathELength_lineMap`: the straight segment has length the norm distance;
* `TauCeti.Manifold.pathELength_comp_subtype_val`: path length is intrinsic, i.e. unchanged under
  restriction of the metric to an open submanifold.

## Main results

* `TauCeti.Manifold.riemannianEDist_eq_enorm_sub`: in an inner product space, the canonical
  Riemannian extended distance is the ambient norm distance.
* `TauCeti.Manifold.riemannianEDist_eq_enorm_sub_of_convex`: on a convex open subset, the
  restricted Riemannian extended distance is the ambient norm distance.
* `TauCeti.isRiemannianManifold_of_convex`: the ambient metric makes a convex open subset a
  Riemannian manifold.

## References

* [Geodesics, the exponential map, and the Hopf--Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 0, "Restriction to open submanifolds".
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 1, §2 (arc length; the length of a
  segment).
-/

public section

open Bundle Manifold MeasureTheory Set TopologicalSpace Topology
open scoped Bundle ContDiff ENNReal Manifold Topology

noncomputable section

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

namespace Manifold

section General

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The Riemannian extended distance is bounded below by any bound that is valid for the lengths
of *all* `C¹` curves joining the two points: it is the infimum of those lengths. -/
theorem le_riemannianEDist_of_forall_pathELength_ge {x y : M} {c : ℝ≥0∞}
    (h : ∀ γ : ℝ → M, γ 0 = x → γ 1 = y → CMDiff[Icc 0 1] 1 γ →
      c ≤ pathELength I γ 0 1) :
    c ≤ riemannianEDist I x y := by
  by_contra hle
  rw [not_le] at hle
  obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hle
  obtain ⟨γ, h0, h1, hγ, hl⟩ := exists_lt_of_riemannianEDist_lt hr1
  exact absurd ((h γ h0 h1 hγ).trans hl.le) (not_le.2 hr2)

end General

/-! ### Chords and straight segments in an inner product space -/

section VectorSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A `C¹` curve in an inner product space is at least as long as the chord joining its endpoints:
the integral of its speed dominates the norm distance between any two of its points. -/
theorem enorm_sub_le_pathELength {a b : ℝ} (hab : a ≤ b) {γ : ℝ → F}
    (hγ : CMDiff[Icc a b] 1 γ) :
    ‖γ b - γ a‖ₑ ≤ pathELength 𝓘(ℝ, F) γ a b := by
  rw [pathELength_eq_lintegral_mfderivWithin_Icc]
  simp only [mfderivWithin_eq_fderivWithin, enorm_tangentSpace_vectorSpace]
  exact enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc
    (contMDiffOn_iff_contDiffOn.mp hγ) hab

/-- The straight segment between two points of an inner product space has length equal to the
norm distance between them. -/
theorem pathELength_lineMap (x y : F) :
    pathELength 𝓘(ℝ, F)
      (⇑(ContinuousAffineMap.lineMap (R := ℝ) x y)) 0 1 = ‖x - y‖ₑ := by
  rw [pathELength_eq_lintegral_mfderivWithin_Icc]
  simp only [mfderivWithin_eq_fderivWithin, enorm_tangentSpace_vectorSpace]
  exact lintegral_fderiv_lineMap_eq_edist .. |>.trans (edist_eq_enorm_sub ..)

/-- In an inner product space endowed with its canonical Riemannian metric, the Riemannian
extended distance between two points is their ambient norm distance: no curve beats the chord. -/
theorem enorm_sub_le_riemannianEDist (x y : F) :
    ‖x - y‖ₑ ≤ riemannianEDist 𝓘(ℝ, F) x y := by
  refine le_riemannianEDist_of_forall_pathELength_ge fun γ h0 h1 hγ ↦ ?_
  have h := enorm_sub_le_pathELength zero_le_one hγ
  rwa [h0, h1, ← neg_sub, enorm_neg] at h

/-- In an inner product space endowed with its canonical Riemannian metric, the Riemannian
extended distance between two points is their ambient norm distance. -/
theorem riemannianEDist_eq_enorm_sub (x y : F) :
    riemannianEDist 𝓘(ℝ, F) x y = ‖x - y‖ₑ :=
  (riemannianEDist_le_pathELength
      (contMDiffOn_iff_contDiffOn.mpr
        (ContinuousAffineMap.lineMap (R := ℝ) x y).contDiff.contDiffOn)
      (by simp [ContinuousAffineMap.coe_lineMap_eq])
      (by simp [ContinuousAffineMap.coe_lineMap_eq]) zero_le_one).trans_eq
    (pathELength_lineMap x y) |>.antisymm (enorm_sub_le_riemannianEDist x y)

end VectorSpace

/-! ### Path length through an open immersion -/

section OpenSubmanifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {U : Opens M}

/-- Path length is intrinsic: restricting the metric of `M` to an open submanifold `U` does not
change the length of a `C¹` curve read in `U`. -/
theorem pathELength_comp_subtype_val {γ : ℝ → U} {a b : ℝ}
    (hγ : CMDiff[Icc a b] 1 γ) :
    pathELength I γ a b = pathELength I ((Subtype.val : U → M) ∘ γ) a b := by
  rw [pathELength_eq_lintegral_mfderiv_Icc, pathELength_eq_lintegral_mfderiv_Icc,
    ← restrict_Ioo_eq_restrict_Icc]
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
  have hd : ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ t :=
    (hγ t (Set.Ioo_subset_Icc_self ht)).contMDiffAt (Icc_mem_nhds ht.1 ht.2)
  have hval : ContMDiffAt I I 1 (Subtype.val : U → M) (γ t) :=
    contMDiff_subtype_val (γ t)
  have hv' : MDiffAt (Subtype.val : U → M) (γ t) := hval.mdifferentiableAt one_ne_zero
  have hd' : MDiffAt γ t := hd.mdifferentiableAt one_ne_zero
  rw [(HasMFDerivAt.comp t hv'.hasMFDerivAt hd'.hasMFDerivAt).mfderiv, mfderiv_subtype_val]
  simp

end OpenSubmanifold

/-! ### Convex open subsets of an inner product space -/

section ConvexOpenSubset

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable (U : Opens F)

/-- The straight segment in `U`, affinely parametrized on `[0, 1]` at constant speed and clamped
to `[0, 1]` outside, so as to be defined on all of `ℝ`. -/
private def convexSegment (hU : Convex ℝ (U : Set F)) (x y : U) : ℝ → U := fun t =>
  Subtype.mk
    (⇑(ContinuousAffineMap.lineMap (R := ℝ) (↑x : F) (↑y : F))
      (Set.projIcc 0 1 zero_le_one t))
    (by rw [ContinuousAffineMap.coe_lineMap_eq]
        exact hU.lineMap_mem x.property y.property
          (Set.projIcc 0 1 zero_le_one t).property)

private theorem contMDiffOn_convexSegment (hU : Convex ℝ (U : Set F)) (x y : U) :
    CMDiff[Icc 0 1] 1 (convexSegment U hU x y) := by
  have hlm : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1
      ⇑(ContinuousAffineMap.lineMap (R := ℝ) (↑x : F) (↑y : F)) (Icc 0 1) :=
    contMDiffOn_iff_contDiffOn.mpr
      (ContinuousAffineMap.contDiff
        (ContinuousAffineMap.lineMap (R := ℝ) (↑x : F) (↑y : F))).contDiffOn
  have heq : ∀ t ∈ Icc 0 1,
      ((Subtype.val : U → F) ∘ convexSegment U hU x y) t =
        ⇑(ContinuousAffineMap.lineMap (R := ℝ) (↑x : F) (↑y : F)) t := by
    intro t ht
    simp only [Function.comp_apply, convexSegment, Subtype.coe_mk,
      ContinuousAffineMap.coe_lineMap_eq, Set.projIcc_of_mem zero_le_one ht]
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1
      ((Subtype.val : U → F) ∘ convexSegment U hU x y) (Icc 0 1) :=
    ContMDiffOn.congr hlm heq
  exact contMDiffOn_subtypeVal_comp_iff U (convexSegment U hU x y) (Icc 0 1) |>.mp hcomp

private theorem pathELength_convexSegment (hU : Convex ℝ (U : Set F)) (x y : U) :
    pathELength 𝓘(ℝ, F) (convexSegment U hU x y) 0 1 = ‖((x : F) - (y : F))‖ₑ := by
  have hval : ∀ t ∈ Icc 0 1,
      ((Subtype.val : U → F) ∘ convexSegment U hU x y) t =
        ⇑(ContinuousAffineMap.lineMap (R := ℝ) (↑x : F) (↑y : F)) t := by
    intro t ht
    simp only [Function.comp_apply, convexSegment, Subtype.coe_mk,
      ContinuousAffineMap.coe_lineMap_eq, Set.projIcc_of_mem zero_le_one ht]
  rw [pathELength_comp_subtype_val (contMDiffOn_convexSegment U hU x y),
    pathELength_congr hval]
  exact pathELength_lineMap _ _

/-- In a convex open subset endowed with the restriction of the standard Riemannian metric, no
curve is shorter than the chord between its endpoints. -/
theorem enorm_sub_le_riemannianEDist_of_convex (x y : U) :
    ‖((x : F) - (y : F))‖ₑ ≤ riemannianEDist 𝓘(ℝ, F) x y := by
  refine le_riemannianEDist_of_forall_pathELength_ge (M := U)
    (I := 𝓘(ℝ, F)) fun γ h0 h1 hγ ↦ ?_
  have hv : CMDiff[Icc 0 1] 1 ((Subtype.val : U → F) ∘ γ) :=
    contMDiff_subtype_val.comp_contMDiffOn hγ
  rw [pathELength_comp_subtype_val hγ]
  have h := enorm_sub_le_pathELength zero_le_one hv
  rw [Function.comp_apply, Function.comp_apply, h1, h0, ← neg_sub, enorm_neg] at h
  exact h

private theorem convexSegment_endpoints (hU : Convex ℝ (U : Set F)) (x y : U) :
    convexSegment U hU x y 0 = x ∧ convexSegment U hU x y 1 = y := by
  constructor
  · refine Subtype.ext ?_
    simp only [convexSegment, Subtype.coe_mk]
    rw [Set.projIcc_of_mem zero_le_one (left_mem_Icc.2 zero_le_one)]
    simp [ContinuousAffineMap.coe_lineMap_eq]
  · refine Subtype.ext ?_
    simp only [convexSegment, Subtype.coe_mk]
    rw [Set.projIcc_of_mem zero_le_one (right_mem_Icc.2 zero_le_one)]
    simp [ContinuousAffineMap.coe_lineMap_eq]

/-- **The Riemannian distance of a convex open subset is the ambient norm distance.** For an
open subset `U` of a real inner product space `F`, endowed with the restriction of the standard
Riemannian metric, the Riemannian extended distance between two points of `U` equals their norm
distance read in `F`: the straight segment stays in `U` and realizes the distance. Together with
`TauCeti.isRiemannianManifold_of_convex`, this is what makes the ordinary-metric layer available
on such a `U`, e.g. for the open unit ball example of the Hopf--Rinow roadmap. -/
theorem riemannianEDist_eq_enorm_sub_of_convex (hU : Convex ℝ (U : Set F)) (x y : U) :
    riemannianEDist 𝓘(ℝ, F) x y = ‖((x : F) - (y : F))‖ₑ :=
  ((riemannianEDist_le_pathELength (contMDiffOn_convexSegment U hU x y)
      (convexSegment_endpoints U hU x y).1 (convexSegment_endpoints U hU x y).2
      zero_le_one).trans_eq
    (pathELength_convexSegment U hU x y)).antisymm
    (enorm_sub_le_riemannianEDist_of_convex U x y)

/-- A convex open subset of an inner product space, endowed with its ambient metric, satisfies
the `IsRiemannianManifold` predicate: its ambient extended distance is the infimum of the lengths
of `C¹` curves, because that infimum is exactly the norm distance. -/
theorem isRiemannianManifold_of_convex (hU : Convex ℝ (U : Set F)) :
    IsRiemannianManifold 𝓘(ℝ, F) U :=
  ⟨fun x y ↦ by
    rw [Subtype.edist_eq, edist_eq_enorm_sub,
      riemannianEDist_eq_enorm_sub_of_convex U hU x y]⟩

end ConvexOpenSubset

end Manifold

end TauCeti
