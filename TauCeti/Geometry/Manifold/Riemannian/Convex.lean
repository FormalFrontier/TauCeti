/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Geometry.Manifold.Riemannian.PathELength
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
needed: convexity is the only substantive hypothesis. The general facts about path length used
along the way live in their canonical modules:
`TauCeti.Manifold.le_riemannianEDist_of_forall_le_pathELength`
(`Riemannian.Distance`), `TauCeti.Manifold.pathELength_lineMap`
(`Riemannian.PathELength`), and `TauCeti.Manifold.pathELength_subtypeVal_comp`
(`Riemannian.Restriction`).

## Main results

* `TauCeti.Manifold.enorm_sub_le_riemannianEDist_subtype`: on any open subset of an inner product
  space, no curve is shorter than the chord between its endpoints;
* `TauCeti.Manifold.riemannianEDist_eq_enorm_sub_of_convex`: on a convex open subset, the
  restricted Riemannian extended distance is the ambient norm distance.
* `TauCeti.Manifold.isRiemannianManifold_of_convex`: the ambient metric makes a convex open
  subset a Riemannian manifold.

## References

* The ambient distance computation adapts the proof of the `IsRiemannianManifold 𝓘(ℝ, F) F`
  instance in [Mathlib, `Mathlib/Geometry/Manifold/Riemannian/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Geometry/Manifold/Riemannian/Basic.lean)
  by S. Gouëzel.
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

namespace Manifold

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

private theorem convexSegment_val_eqOn (hU : Convex ℝ (U : Set F)) (x y : U) :
    ∀ t ∈ Icc 0 1,
      ((Subtype.val : U → F) ∘ convexSegment U hU x y) t =
        ⇑(ContinuousAffineMap.lineMap (R := ℝ) (↑x : F) (↑y : F)) t := by
  intro t ht
  simp only [Function.comp_apply, convexSegment, Subtype.coe_mk,
    ContinuousAffineMap.coe_lineMap_eq, Set.projIcc_of_mem zero_le_one ht]

private theorem contMDiffOn_convexSegment (hU : Convex ℝ (U : Set F)) (x y : U) :
    CMDiff[Icc 0 1] 1 (convexSegment U hU x y) := by
  have hlm : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1
      ⇑(ContinuousAffineMap.lineMap (R := ℝ) (↑x : F) (↑y : F)) (Icc 0 1) :=
    contMDiffOn_iff_contDiffOn.mpr
      (ContinuousAffineMap.contDiff
        (ContinuousAffineMap.lineMap (R := ℝ) (↑x : F) (↑y : F))).contDiffOn
  have heq := convexSegment_val_eqOn U hU x y
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1
      ((Subtype.val : U → F) ∘ convexSegment U hU x y) (Icc 0 1) :=
    ContMDiffOn.congr hlm heq
  exact (ContMDiffOn.subtypeVal_comp_iff U (convexSegment U hU x y) (Icc 0 1)).mp hcomp

private theorem pathELength_convexSegment (hU : Convex ℝ (U : Set F)) (x y : U) :
    pathELength 𝓘(ℝ, F) (convexSegment U hU x y) 0 1 = ‖((x : F) - (y : F))‖ₑ := by
  have hval := convexSegment_val_eqOn U hU x y
  rw [pathELength_subtypeVal_comp (contMDiffOn_convexSegment U hU x y),
    pathELength_congr hval]
  exact pathELength_lineMap _ _

/-- In an open subset of an inner product space, endowed with the restriction of the standard
Riemannian metric, no curve is shorter than the chord between its endpoints read in the ambient
space. -/
theorem enorm_sub_le_riemannianEDist_subtype (x y : U) :
    ‖((x : F) - (y : F))‖ₑ ≤ riemannianEDist 𝓘(ℝ, F) x y := by
  have hamb : ∀ z w : F, riemannianEDist 𝓘(ℝ, F) z w = ‖z - w‖ₑ := fun z w =>
    (IsRiemannianManifold.out (I := 𝓘(ℝ, F)) z w).symm.trans (edist_eq_enorm_sub ..)
  refine le_riemannianEDist_of_forall_le_pathELength (M := U)
    (I := 𝓘(ℝ, F)) fun γ h0 h1 hγ ↦ ?_
  rw [pathELength_subtypeVal_comp hγ]
  calc ‖((x : F) - (y : F))‖ₑ
      = riemannianEDist 𝓘(ℝ, F)
          (((Subtype.val : U → F) ∘ γ) 0) (((Subtype.val : U → F) ∘ γ) 1) := by
        rw [Function.comp_apply, Function.comp_apply, h0, h1]
        exact (hamb _ _).symm
    _ ≤ pathELength 𝓘(ℝ, F) ((Subtype.val : U → F) ∘ γ) 0 1 :=
        riemannianEDist_le_pathELength (contMDiff_subtype_val.comp_contMDiffOn hγ) rfl rfl
          zero_le_one

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
`TauCeti.Manifold.isRiemannianManifold_of_convex`, this is what makes the ordinary-metric layer
available
on such a `U`, e.g. for the open unit ball example of the Hopf--Rinow roadmap. -/
@[simp]
theorem riemannianEDist_eq_enorm_sub_of_convex (hU : Convex ℝ (U : Set F)) (x y : U) :
    riemannianEDist 𝓘(ℝ, F) x y = ‖((x : F) - (y : F))‖ₑ :=
  ((riemannianEDist_le_pathELength (contMDiffOn_convexSegment U hU x y)
      (convexSegment_endpoints U hU x y).1 (convexSegment_endpoints U hU x y).2
      zero_le_one).trans_eq
    (pathELength_convexSegment U hU x y)).antisymm
    (enorm_sub_le_riemannianEDist_subtype U x y)

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
