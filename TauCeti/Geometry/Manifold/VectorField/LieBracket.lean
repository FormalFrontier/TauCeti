/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Directional derivatives and the manifold Lie bracket

This file transports Mathlib's normed-space identity `fderivWithin_apply_lieBracket` through a
manifold chart. It identifies the differential of a vector-valued function on the manifold Lie
bracket with the commutator of its directional derivatives.

The chart argument follows the pullback idiom used for the manifold bracket in
`Mathlib/Geometry/Manifold/VectorField/LieBracket.lean`. The resulting lemma is a general manifold
prerequisite for Deliverable A, Layer 1 of the Lie-groups roadmap.

## Main result

* `mvfderiv_mlieBracket`: a differential sends the manifold bracket to the commutator of
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

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (minSmoothness 𝕜 2) M]

omit [CompleteSpace E] in
private theorem fderivWithin_chart_apply_mpullbackWithin
    {p : M → F} {U : ∀ y : M, TangentSpace I y} {x : M} {z : E}
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
  have hunique : UniqueMDiffAt[Set.range I] z := by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact I.uniqueDiffOn.uniqueDiffWithinAt (extChartAt_target_subset_range x hz)
  rw [mfderiv_comp_mfderivWithin
    (I := 𝓘(𝕜, E)) (I' := I) (I'' := 𝓘(𝕜, F))
    (f := (extChartAt I x).symm) (g := p) (s := Set.range I) z hpz
    (mdifferentiableWithinAt_extChartAt_symm hz) hunique]
  rw [ContinuousLinearMap.comp_apply]
  exact congrArg (mfderiv% p ((extChartAt I x).symm z))
    ((isInvertible_mfderivWithin_extChartAt_symm hz).self_apply_inverse _)

omit [CompleteSpace E] in
private theorem eventually_mdifferentiableAt_of_contMDiffAt
    {f : M → F} {x : M} (hf : CMDiffAt n f x) (hn : minSmoothness 𝕜 2 ≤ n) :
    ∀ᶠ y in 𝓝 x, MDiffAt f y := by
  have h2n : (2 : ℕ∞ω) ≤ n :=
    (le_minSmoothness (𝕜 := 𝕜) (n := (2 : ℕ∞ω))).trans hn
  filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by norm_num)).1
    (hf.of_le h2n)] with y hy
  exact hy.mdifferentiableAt (by norm_num)

omit [CompleteSpace E] in
private theorem eventuallyEq_chart_directionalDerivative
    {f : M → F} {U : ∀ y : M, TangentSpace I y} {x : M}
    (hf : CMDiffAt n f x) (hn : minSmoothness 𝕜 2 ≤ n) :
    (fun z ↦ (fderivWithin 𝕜 (f ∘ (extChartAt I x).symm) (Set.range I) z)
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm U (Set.range I) z)) =ᶠ[
      𝓝[Set.range I] (extChartAt I x x)]
    (fun y ↦ mvfderiv I f y (U y)) ∘ (extChartAt I x).symm := by
  have hf_eventually := eventually_mdifferentiableAt_of_contMDiffAt hf hn
  have hsymm_tendsto : Tendsto (extChartAt I x).symm
      (𝓝[Set.range I] (extChartAt I x x)) (𝓝 x) := by
    simpa only [extChartAt_to_inv] using
      (contMDiffWithinAt_extChartAt_symm_range_self
        (I := I) (n := minSmoothness 𝕜 2) x).continuousWithinAt.tendsto
  have htarget : ∀ᶠ z in 𝓝[Set.range I] (extChartAt I x x),
      z ∈ (extChartAt I x).target :=
    extChartAt_target_mem_nhdsWithin x
  filter_upwards [htarget, hsymm_tendsto hf_eventually] with z hz hfz
  exact fderivWithin_chart_apply_mpullbackWithin hz hfz

omit [CompleteSpace E] in
private theorem mdifferentiableAt_tangentMapWithin_apply
    {f : M → F} {U : ∀ y : M, TangentSpace I y} {x : M} {t : Set M}
    (ht_open : IsOpen t) (hft : ContMDiffOn I 𝓘(𝕜, F) 2 f t)
    (hxt : x ∈ t) (hU : MDiffAt (fun y ↦ (U y : TangentBundle I M)) x) :
    MDiffAt (fun y ↦ tangentMapWithin I 𝓘(𝕜, F) f t
      (U y : TangentBundle I M)) x := by
  let u : M → TangentBundle I M := fun y ↦ (U y : TangentBundle I M)
  have hu_mem : u x ∈ π E (TangentSpace I) ⁻¹' t := hxt
  have htangent := hft.contMDiffOn_tangentMapWithin
    (I := I) (I' := 𝓘(𝕜, F)) (m := 1) (by norm_num) ht_open.uniqueMDiffOn
  have hpre : π E (TangentSpace I) ⁻¹' t ∈ 𝓝 (u x) :=
    (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt
      (ht_open.mem_nhds hxt)
  have htangentAt : MDiffAt (tangentMapWithin I 𝓘(𝕜, F) f t) (u x) := by
    rw [← mdifferentiableWithinAt_univ]
    exact ((htangent (u x) hu_mem).mdifferentiableWithinAt (by norm_num)).mono_of_mem_nhdsWithin
      (by simpa only [nhdsWithin_univ] using hpre)
  exact htangentAt.comp x hU

omit [CompleteSpace E] in
private theorem exists_open_contMDiffOn_two
    {f : M → F} {x : M} (hf : CMDiffAt n f x) (hn : minSmoothness 𝕜 2 ≤ n) :
    ∃ t : Set M, IsOpen t ∧ t ∈ 𝓝 x ∧ ContMDiffOn I 𝓘(𝕜, F) 2 f t := by
  have h2n : (2 : ℕ∞ω) ≤ n :=
    (le_minSmoothness (𝕜 := 𝕜) (n := (2 : ℕ∞ω))).trans hn
  rcases (contMDiffAt_iff_contMDiffOn_nhds (n := 2) (by norm_num)).1 (hf.of_le h2n) with
    ⟨s, hs, hfs⟩
  exact ⟨interior s, isOpen_interior,
    isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hs), hfs.mono interior_subset⟩

omit [CompleteSpace E] in
private theorem eventuallyEq_tangentMapWithin_apply
    {f : M → F} {U : ∀ y : M, TangentSpace I y} {x : M} {t : Set M}
    (ht_open : IsOpen t) (ht : t ∈ 𝓝 x)
    (hf : CMDiffAt n f x) (hn : minSmoothness 𝕜 2 ≤ n) :
    (fun y ↦ tangentMapWithin I 𝓘(𝕜, F) f t (U y : TangentBundle I M)) =ᶠ[𝓝 x]
      fun y ↦ tangentMap I 𝓘(𝕜, F) f (U y : TangentBundle I M) := by
  filter_upwards [ht, eventually_mdifferentiableAt_of_contMDiffAt hf hn] with y hyt hfy
  exact tangentMapWithin_eq_tangentMap (ht_open.uniqueMDiffWithinAt hyt) hfy

omit [CompleteSpace E] in
private theorem mdifferentiableAt_tangentMap_apply
    {f : M → F} {U : ∀ y : M, TangentSpace I y} {x : M}
    (hf : CMDiffAt n f x) (hn : minSmoothness 𝕜 2 ≤ n)
    (hU : MDiffAt (fun y ↦ (U y : TangentBundle I M)) x) :
    MDiffAt (fun y ↦ tangentMap I 𝓘(𝕜, F) f
      (U y : TangentBundle I M)) x := by
  rcases exists_open_contMDiffOn_two hf hn with ⟨t, ht_open, ht, hft⟩
  have hx : x ∈ t := mem_of_mem_nhds ht
  have htangentAt := mdifferentiableAt_tangentMapWithin_apply ht_open hft hx hU
  exact htangentAt.congr_of_eventuallyEq
    (eventuallyEq_tangentMapWithin_apply (U := U) ht_open ht hf hn).symm

omit [CompleteSpace E] in
private theorem mdifferentiableAt_mvfderiv_apply
    {f : M → F} {U : ∀ y : M, TangentSpace I y} {x : M}
    (hf : CMDiffAt n f x) (hn : minSmoothness 𝕜 2 ≤ n)
    (hU : MDiffAt (fun y ↦ (U y : TangentBundle I M)) x) :
    MDiffAt (fun y ↦ mvfderiv I f y (U y)) x := by
  have htangent := mdifferentiableAt_tangentMap_apply hf hn hU
  have hsnd : MDiffAt (fun p : TangentBundle 𝓘(𝕜, F) F ↦ @id F p.2)
      (tangentMap I 𝓘(𝕜, F) f (U x : TangentBundle I M)) :=
    (contMDiff_snd_tangentBundle_modelSpace F 𝓘(𝕜, F)
      (n := 1)).mdifferentiable (by norm_num) |>.mdifferentiableAt
  apply (hsnd.comp x htangent).congr_of_eventuallyEq
  filter_upwards with y
  rw [Function.comp_apply, tangentMap_snd, mvfderiv_apply_eq_mfderiv_apply]
  rfl

/-- Let `f` have enough derivatives for symmetry of its second derivative at `x`, and let `V` and
`W` be differentiable vector fields there. Then the differential of `f` on the manifold bracket is
the commutator of its directional derivatives. This is the manifold counterpart of Mathlib's
`fderivWithin_apply_lieBracket`. -/
theorem mvfderiv_mlieBracket {f : M → F} {V W : ∀ x : M, TangentSpace I x} {x : M}
    (hf : CMDiffAt n f x) (hn : minSmoothness 𝕜 2 ≤ n)
    (hV : MDiffAt (fun y ↦ (V y : TangentBundle I M)) x)
    (hW : MDiffAt (fun y ↦ (W y : TangentBundle I M)) x) :
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
  have h2n : (2 : ℕ∞ω) ≤ n :=
    (le_minSmoothness (𝕜 := 𝕜) (n := (2 : ℕ∞ω))).trans hn
  have hf' : MDiffAt f x := (hf.of_le h2n).mdifferentiableAt (by norm_num)
  have hchain := mfderiv_comp_mfderivWithin_of_eq
    (I := 𝓘(𝕜, E)) (I' := I) (I'' := 𝓘(𝕜, F))
    (f := (extChartAt I x).symm) (g := f) (s := Set.range I)
    hf' (mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target x))
    (by apply I.uniqueMDiffOn; exact Set.mem_range_self (f := I) _)
    (extChartAt_to_inv x)
  change @Eq (E →L[𝕜] F) _ _ at hchain
  let Z : E := lieBracketWithin 𝕜
    (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (Set.range I))
    (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (Set.range I))
    ((extChartAt I x).symm ⁻¹' Set.univ ∩ Set.range I) (extChartAt I x x)
  have hchain_apply := congrArg (fun L : E →L[𝕜] F ↦ L Z) hchain
  change _ = (mfderiv% f x) ((mfderiv[Set.range I]
    (extChartAt I x).symm (extChartAt I x x)) Z) at hchain_apply
  change (mfderiv% f x) ((mfderiv[Set.range I]
    (extChartAt I x).symm (extChartAt I x x)) Z) = _
  rw [← hchain_apply]
  simp only [mfderivWithin_eq_fderivWithin]
  -- Pull the vector fields back and invoke the normed-space bracket identity.
  have hfcoord := contMDiffWithinAt_iff_contDiffWithinAt.mp
    (contMDiffAt_iff_source.mp (hf.of_le hn))
  have hVcoord : DifferentiableWithinAt 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (Set.range I))
      (Set.range I) (extChartAt I x x) := by
    simpa using (hV.mdifferentiableWithinAt (s := Set.univ))
      |>.differentiableWithinAt_mpullbackWithin_vectorField
  have hWcoord : DifferentiableWithinAt 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (Set.range I))
      (Set.range I) (extChartAt I x x) := by
    simpa using (hW.mdifferentiableWithinAt (s := Set.univ))
      |>.differentiableWithinAt_mpullbackWithin_vectorField
  -- Identify chart directional derivatives with their manifold counterparts.
  have hf_chart : MDiffAt f ((extChartAt I x).symm (extChartAt I x x)) := by
    simpa only [extChartAt_to_inv] using hf'
  have hVf := mdifferentiableAt_mvfderiv_apply hf hn hV
  have hWf := mdifferentiableAt_mvfderiv_apply hf hn hW
  have hcoordW := (eventuallyEq_chart_directionalDerivative
    (I := I) (U := W) hf hn).fderivWithin_eq
    (𝕜 := 𝕜) (by
      simpa only [Function.comp_apply, extChartAt_to_inv] using
        fderivWithin_chart_apply_mpullbackWithin
          (I := I) (U := W) (mem_extChartAt_target x) hf_chart)
  have hcoordV := (eventuallyEq_chart_directionalDerivative
    (I := I) (U := V) hf hn).fderivWithin_eq
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
  have hZ : Z = lieBracketWithin 𝕜
    (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (Set.range I))
    (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (Set.range I))
    (Set.range I) (extChartAt I x x) := by
    simp only [Z, Set.preimage_univ, Set.univ_inter]
  rw [hZ]
  rw [fderivWithin_apply_lieBracket hfcoord le_rfl I.uniqueDiffOn
    (I.range_subset_closure_interior (Set.mem_range_self (f := I) _))
    (Set.mem_range_self (f := I) _) hWcoord hVcoord]
  rw [hcoordW, hcoordV]
  exact congrArg₂ (· - ·) houterW houterV
