/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# Directional derivatives and the manifold Lie bracket

This file transports Mathlib's normed-space identity `fderivWithin_apply_lieBracket` through a
manifold chart. It identifies the differential of a scalar function on the manifold Lie bracket with
the commutator of its directional derivatives.

The chart argument follows the pullback idiom used for the manifold bracket in
`Mathlib/Geometry/Manifold/VectorField/LieBracket.lean`. The resulting lemma is a general manifold
prerequisite for Deliverable A, Layer 1 of the Lie-groups roadmap.

## Main result

* `mvfderiv_mlieBracket`: a scalar differential sends the manifold bracket to the commutator of
  directional derivatives.

## References

* `Mathlib/Analysis/Calculus/VectorField.lean`, theorem `fderivWithin_apply_lieBracket`.
* `Mathlib/Geometry/Manifold/VectorField/LieBracket.lean`, for the chart-transport construction.
* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1.
-/

public section

noncomputable section

open Bundle Filter Manifold VectorField
open scoped ContDiff Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

omit [CompleteSpace E] in
private theorem fderivWithin_chart_apply_mpullbackWithin
    {p : M → 𝕜} {U : ∀ y : M, TangentSpace I y} {x : M} {z : E}
    (hz : z ∈ (extChartAt I x).target)
    (hpz : MDiffAt p ((extChartAt I x).symm z)) :
    (fderivWithin 𝕜 (p ∘ (extChartAt I x).symm) (Set.range I) z)
        (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm U (Set.range I) z) =
      mvfderiv I p ((extChartAt I x).symm z) (U ((extChartAt I x).symm z)) := by
  rw [← mfderivWithin_eq_fderivWithin]
  -- `TangentSpace I _` is definitionally the model space `E`; no public rewrite lemma exposes the
  -- coordinate composition in the form needed by the chain rule.
  change (mfderiv[Set.range I] (p ∘ (extChartAt I x).symm) z)
    ((mfderiv[Set.range I] (extChartAt I x).symm z).inverse
      (U ((extChartAt I x).symm z))) =
    (mfderiv% p ((extChartAt I x).symm z)) (U ((extChartAt I x).symm z))
  rw [mfderiv_comp_mfderivWithin
    (I := 𝓘(𝕜, E)) (I' := I) (I'' := 𝓘(𝕜, 𝕜))
    (f := (extChartAt I x).symm) (g := p) (s := Set.range I) z hpz
    (mdifferentiableWithinAt_extChartAt_symm hz)
    (show UniqueMDiffAt[Set.range I] z by
      rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact I.uniqueDiffOn.uniqueDiffWithinAt (extChartAt_target_subset_range x hz))]
  rw [ContinuousLinearMap.comp_apply]
  exact congrArg (mfderiv% p ((extChartAt I x).symm z))
    ((isInvertible_mfderivWithin_extChartAt_symm hz).self_apply_inverse _)

omit [CompleteSpace E] in
private theorem eventuallyEq_chart_directionalDerivative
    {f : M → 𝕜} {U : ∀ y : M, TangentSpace I y} {x : M}
    (hf : CMDiffAt 2 f x) :
    (fun z ↦ (fderivWithin 𝕜 (f ∘ (extChartAt I x).symm) (Set.range I) z)
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm U (Set.range I) z)) =ᶠ[
      𝓝[Set.range I] (extChartAt I x x)]
    (fun y ↦ mvfderiv I f y (U y)) ∘ (extChartAt I x).symm := by
  have hf_eventually : ∀ᶠ y in 𝓝 x, MDiffAt f y := by
    filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by norm_num)).1 hf]
      with y hy
    exact hy.mdifferentiableAt (by norm_num)
  have hsymm_tendsto : Tendsto (extChartAt I x).symm
      (𝓝[Set.range I] (extChartAt I x x)) (𝓝 x) := by
    simpa only [extChartAt_to_inv] using
      (contMDiffWithinAt_extChartAt_symm_range_self
        (I := I) (n := 2) x).continuousWithinAt.tendsto
  have htarget : ∀ᶠ z in 𝓝[Set.range I] (extChartAt I x x),
      z ∈ (extChartAt I x).target :=
    extChartAt_target_mem_nhdsWithin x
  filter_upwards [htarget, hsymm_tendsto hf_eventually] with z hz hfz
  exact fderivWithin_chart_apply_mpullbackWithin hz hfz

/-- Over a field whose minimum smoothness for second derivatives is at most two, let `f` be twice
differentiable at `x`, and let `V` and `W` be differentiable vector fields there. If the directional
derivatives of `f` along `V` and `W` are differentiable at `x`, then the differential of `f` on the
manifold bracket is their commutator. This is the manifold counterpart of Mathlib's
`fderivWithin_apply_lieBracket`. -/
theorem mvfderiv_mlieBracket {f : M → 𝕜} {V W : ∀ x : M, TangentSpace I x} {x : M}
    (hmin : minSmoothness 𝕜 2 ≤ 2)
    (hf : CMDiffAt 2 f x)
    (hV : MDiffAt (fun y ↦ (V y : TangentBundle I M)) x)
    (hW : MDiffAt (fun y ↦ (W y : TangentBundle I M)) x)
    (hVf : MDiffAt (fun y ↦ mvfderiv I f y (V y)) x)
    (hWf : MDiffAt (fun y ↦ mvfderiv I f y (W y)) x) :
    mvfderiv I f x (mlieBracket I V W x) =
      mvfderiv I (fun y ↦ mvfderiv I f y (W y)) x (V x) -
        mvfderiv I (fun y ↦ mvfderiv I f y (V y)) x (W x) := by
  -- Express the manifold bracket and the outer differential in the chart at `x`.
  rw [← mlieBracketWithin_univ, mlieBracketWithin_apply]
  have hinv :
      (mfderiv% (extChartAt I x) x).inverse =
        mfderiv[Set.range I] (extChartAt I x).symm (extChartAt I x x) := by
    exact ContinuousLinearMap.inverse_eq
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'
        (mem_extChartAt_source x))
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
        (mem_extChartAt_source x))
  rw [hinv]
  -- Normalize the same definitional tangent-space representation before applying the chart chain
  -- rule. The following `change`s only expose applications of that single linear-map identity.
  change (mfderiv% f x) _ = _
  have hf' : MDiffAt f x := hf.mdifferentiableAt (by norm_num)
  have hchain := mfderiv_comp_mfderivWithin_of_eq
    (I := 𝓘(𝕜, E)) (I' := I) (I'' := 𝓘(𝕜, 𝕜))
    (f := (extChartAt I x).symm) (g := f) (s := Set.range I)
    hf' (mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target x))
    (by apply I.uniqueMDiffOn; exact Set.mem_range_self (f := I) _)
    (extChartAt_to_inv x)
  change @Eq (E →L[𝕜] 𝕜) _ _ at hchain
  let Z : E := lieBracketWithin 𝕜
    (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (Set.range I))
    (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (Set.range I))
    ((extChartAt I x).symm ⁻¹' Set.univ ∩ Set.range I) (extChartAt I x x)
  have hchain_apply := congrArg (fun L : E →L[𝕜] 𝕜 ↦ L Z) hchain
  change _ = (mfderiv% f x) ((mfderiv[Set.range I]
    (extChartAt I x).symm (extChartAt I x x)) Z) at hchain_apply
  change (mfderiv% f x) ((mfderiv[Set.range I]
    (extChartAt I x).symm (extChartAt I x x)) Z) = _
  rw [← hchain_apply]
  simp only [mfderivWithin_eq_fderivWithin]
  -- Pull the vector fields back and invoke the normed-space bracket identity.
  have hfcoord : ContDiffWithinAt 𝕜 2 (f ∘ (extChartAt I x).symm)
      (Set.range I) (extChartAt I x x) := by
    have hsymm := contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := 2) x
    have hcomp := ContMDiffWithinAt.comp_of_eq
      (show ContMDiffWithinAt I 𝓘(𝕜, 𝕜) 2 f Set.univ x from hf)
      hsymm (Set.mapsTo_univ _ _) (extChartAt_to_inv x)
    exact contMDiffWithinAt_iff_contDiffWithinAt.mp hcomp
  have hVcoord : DifferentiableWithinAt 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (Set.range I))
      (Set.range I) (extChartAt I x x) := by
    have hV' : MDiffAt[Set.univ] (fun y ↦ (V y : TangentBundle I M)) x :=
      hV.mdifferentiableWithinAt
    simpa using hV'.differentiableWithinAt_mpullbackWithin_vectorField
  have hWcoord : DifferentiableWithinAt 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (Set.range I))
      (Set.range I) (extChartAt I x x) := by
    have hW' : MDiffAt[Set.univ] (fun y ↦ (W y : TangentBundle I M)) x :=
      hW.mdifferentiableWithinAt
    simpa using hW'.differentiableWithinAt_mpullbackWithin_vectorField
  -- Identify chart directional derivatives with their manifold counterparts.
  have hf_chart : MDiffAt f ((extChartAt I x).symm (extChartAt I x x)) := by
    simpa only [extChartAt_to_inv] using hf'
  have hcoordW := (eventuallyEq_chart_directionalDerivative (I := I) (U := W) hf).fderivWithin_eq
    (𝕜 := 𝕜) (by
      simpa only [Function.comp_apply, extChartAt_to_inv] using
        fderivWithin_chart_apply_mpullbackWithin
          (I := I) (U := W) (mem_extChartAt_target x) hf_chart)
  have hcoordV := (eventuallyEq_chart_directionalDerivative (I := I) (U := V) hf).fderivWithin_eq
    (𝕜 := 𝕜) (by
      simpa only [Function.comp_apply, extChartAt_to_inv] using
        fderivWithin_chart_apply_mpullbackWithin
          (I := I) (U := V) (mem_extChartAt_target x) hf_chart)
  have houterW := fderivWithin_chart_apply_mpullbackWithin
    (I := I) (p := fun y ↦ mvfderiv I f y (W y)) (U := V)
    (mem_extChartAt_target x) (by simpa only [extChartAt_to_inv] using hWf)
  have houterV := fderivWithin_chart_apply_mpullbackWithin
    (I := I) (p := fun y ↦ mvfderiv I f y (V y)) (U := W)
    (mem_extChartAt_target x) (by simpa only [extChartAt_to_inv] using hVf)
  rw [extChartAt_to_inv] at houterW houterV
  rw [show Z = lieBracketWithin 𝕜
    (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (Set.range I))
    (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (Set.range I))
    (Set.range I) (extChartAt I x x) by
      simp only [Z, Set.preimage_univ, Set.univ_inter]]
  rw [fderivWithin_apply_lieBracket hfcoord hmin I.uniqueDiffOn
    (I.range_subset_closure_interior (Set.mem_range_self (f := I) _))
    (Set.mem_range_self (f := I) _) hWcoord hVcoord]
  rw [hcoordW, hcoordV]
  exact congrArg₂ (· - ·) houterW houterV
