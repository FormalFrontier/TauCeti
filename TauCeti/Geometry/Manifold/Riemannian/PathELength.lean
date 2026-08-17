/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.PathELength

/-!
# Smoothing corners without changing Riemannian path length

A `C¹` path on `[0, 1]` can be reparametrized so that it is constant near both endpoints. The
reparametrized path is globally `C¹`, has the same endpoints, and has exactly the same
`Manifold.pathELength`. Consequently, two `C¹` path segments with a common endpoint can be joined
to a globally `C¹` path whose length is the sum of their lengths. This is the basic corner-smoothing
step used to compare piecewise-`C¹` and `C¹` definitions of Riemannian distance.

The construction uses Mathlib's `Real.smoothTransition` and
`Manifold.pathELength_comp_of_monotoneOn`. No new notion of path length is introduced.

## Main results

* `TauCeti.exists_contMDiff_pathELength_eq`: flatten a `C¹` path near both endpoints without
  changing its endpoints or length.
* `TauCeti.exists_contMDiff_pathELength_eq_add`: smooth the common corner of two `C¹` path
  segments, preserving the sum of their lengths.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 1, Definition 2.9 and Chapter 7, Section 2.
* [The Hopf--Rinow roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 0, "Corner smoothing and the piecewise-`C¹` comparison".
-/

public section

open Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [∀ x : M, ENorm (TangentSpace I x)]
  [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]

/-- A `C¹` path on `[0, 1]` admits a globally `C¹` reparametrization which is constant near both
endpoints and has exactly the same length. -/
theorem exists_contMDiff_pathELength_eq {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1)) :
    ∃ η : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 η ∧
      η 0 = γ 0 ∧
      η 1 = γ 1 ∧
      Manifold.pathELength I η 0 1 = Manifold.pathELength I γ 0 1 ∧
      η =ᶠ[𝓝 0] (fun _ ↦ γ 0) ∧
      η =ᶠ[𝓝 1] (fun _ ↦ γ 1) := by
  let f : ℝ → ℝ := fun t ↦ Real.smoothTransition (3 * t - 1)
  have hf_smooth : ContDiff ℝ 1 f := by
    apply Real.smoothTransition.contDiff.comp
    fun_prop
  have hf_range (t : ℝ) : f t ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hf_zero : f 0 = 0 := by
    exact Real.smoothTransition.zero_of_nonpos (by norm_num)
  have hf_one : f 1 = 1 := by
    exact Real.smoothTransition.one_of_one_le (by norm_num)
  have hf_monotone : Monotone f := by
    apply Real.smoothTransition.monotone.comp
    intro s t hst
    dsimp only
    gcongr
  have hcomp : ContMDiff 𝓘(ℝ, ℝ) I 1 (γ ∘ f) := by
    rw [← contMDiffOn_univ]
    exact hγ.comp hf_smooth.contMDiff.contMDiffOn fun t _ ↦ hf_range t
  refine ⟨γ ∘ f, hcomp, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hf_zero]
  · simp [hf_one]
  · have hlength := Manifold.pathELength_comp_of_monotoneOn (I := I) (γ := γ) (f := f)
      zero_le_one (hf_monotone.monotoneOn _)
      (hf_smooth.differentiable one_ne_zero).differentiableOn
      (by simpa [hf_zero, hf_one] using hγ.mdifferentiableOn one_ne_zero)
    simpa [hf_zero, hf_one] using hlength
  · filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 3 by norm_num)] with t ht
    simp only [Function.comp_apply]
    rw [show f t = 0 by
      apply Real.smoothTransition.zero_of_nonpos
      norm_num at ht ⊢
      linarith]
  · filter_upwards [Ioi_mem_nhds (show (2 / 3 : ℝ) < 1 by norm_num)] with t ht
    simp only [Function.comp_apply]
    rw [show f t = 1 by
      apply Real.smoothTransition.one_of_one_le
      norm_num at ht ⊢
      linarith]

/-- Two `C¹` paths on `[0, 1]` whose endpoints match can be joined after flattening their common
corner. The resulting path is globally `C¹`, is constant near its outer endpoints, and its length
is the sum of the two original lengths. -/
theorem exists_contMDiff_pathELength_eq_add {γ₁ γ₂ : ℝ → M}
    (hγ₁ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ₁ (Icc 0 1))
    (hγ₂ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ₂ (Icc 0 1)) (h₁₂ : γ₁ 1 = γ₂ 0) :
    ∃ η : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 η ∧
      η 0 = γ₁ 0 ∧
      η 1 = γ₂ 1 ∧
      Manifold.pathELength I η 0 1 =
        Manifold.pathELength I γ₁ 0 1 + Manifold.pathELength I γ₂ 0 1 ∧
      η =ᶠ[𝓝 0] (fun _ ↦ γ₁ 0) ∧
      η =ᶠ[𝓝 1] (fun _ ↦ γ₂ 1) := by
  obtain ⟨α, hα, hα₀, hα₁, hαlen, hαconst₀, hαconst₁⟩ :=
    exists_contMDiff_pathELength_eq hγ₁
  obtain ⟨β, hβ, hβ₀, hβ₁, hβlen, hβconst₀, hβconst₁⟩ :=
    exists_contMDiff_pathELength_eq hγ₂
  let f : ℝ → M := fun t ↦ α (2 * t)
  let g : ℝ → M := fun t ↦ β (2 * t - 1)
  let η : ℝ → M := piecewise (Iic (1 / 2 : ℝ)) f g
  have hf : ContMDiff 𝓘(ℝ, ℝ) I 1 f := by
    apply hα.comp
    simpa only [contMDiff_iff_contDiff] using
      (show ContDiff ℝ 1 (fun t : ℝ ↦ 2 * t) by fun_prop)
  have hg : ContMDiff 𝓘(ℝ, ℝ) I 1 g := by
    apply hβ.comp
    simpa only [contMDiff_iff_contDiff] using
      (show ContDiff ℝ 1 (fun t : ℝ ↦ 2 * t - 1) by fun_prop)
  have hf_const : f =ᶠ[𝓝 (1 / 2 : ℝ)] (fun _ ↦ γ₁ 1) := by
    apply hαconst₁.comp_tendsto
    have h : ContinuousAt (fun t : ℝ ↦ 2 * t) (1 / 2) := by fun_prop
    -- Expose the value hidden in `ContinuousAt` so `norm_num` can identify the target filter.
    change Tendsto (fun t : ℝ ↦ 2 * t) (𝓝 (1 / 2)) (𝓝 (2 * (1 / 2))) at h
    norm_num at h
    exact h
  have hg_const : g =ᶠ[𝓝 (1 / 2 : ℝ)] (fun _ ↦ γ₂ 0) := by
    apply hβconst₀.comp_tendsto
    have h : ContinuousAt (fun t : ℝ ↦ 2 * t - 1) (1 / 2) := by fun_prop
    -- Expose the value hidden in `ContinuousAt` so `norm_num` can identify the target filter.
    change Tendsto (fun t : ℝ ↦ 2 * t - 1) (𝓝 (1 / 2))
      (𝓝 (2 * (1 / 2) - 1)) at h
    norm_num at h
    exact h
  have hfg : f =ᶠ[𝓝 (1 / 2 : ℝ)] g :=
    hf_const.trans <| (h₁₂ ▸ hg_const.symm)
  have hη : ContMDiff 𝓘(ℝ, ℝ) I 1 η := hf.piecewise_Iic hg hfg
  have hη₀ : η 0 = γ₁ 0 := by
    simp [η, f, hα₀]
  have hη₁ : η 1 = γ₂ 1 := by
    rw [show η 1 = g 1 by
      exact (Iic (1 / 2 : ℝ)).piecewise_eq_of_notMem f g (by norm_num)]
    -- Unfold the rescaling at the endpoint without unfolding `η` or the piecewise construction.
    change β (2 * 1 - 1) = γ₂ 1
    norm_num
    exact hβ₁
  have hη_left : Manifold.pathELength I η 0 (1 / 2) =
      Manifold.pathELength I α 0 1 := by
    rw [Manifold.pathELength_congr (γ' := f) (fun t ht ↦ by
      exact (Iic (1 / 2 : ℝ)).piecewise_eq_of_mem f g ht.2)]
    rw [show f = α ∘ fun t : ℝ ↦ 2 * t by rfl]
    have hmono : Monotone (fun t : ℝ ↦ 2 * t) := fun _ _ hst ↦ by linarith
    have hlength := Manifold.pathELength_comp_of_monotoneOn (I := I) (γ := α)
      (f := fun t : ℝ ↦ 2 * t) (a := 0) (b := 1 / 2) (by norm_num)
      (hmono.monotoneOn _) (by fun_prop)
      (hα.mdifferentiable one_ne_zero).mdifferentiableOn
    norm_num at hlength
    exact hlength
  have hη_right : Manifold.pathELength I η (1 / 2) 1 =
      Manifold.pathELength I β 0 1 := by
    rw [Manifold.pathELength_congr_Ioo (γ' := g) (fun t ht ↦ by
      exact (Iic (1 / 2 : ℝ)).piecewise_eq_of_notMem f g (not_le_of_gt ht.1))]
    rw [show g = β ∘ fun t : ℝ ↦ 2 * t - 1 by rfl]
    have hmono : Monotone (fun t : ℝ ↦ 2 * t - 1) := fun _ _ hst ↦ by linarith
    have hlength := Manifold.pathELength_comp_of_monotoneOn (I := I) (γ := β)
      (f := fun t : ℝ ↦ 2 * t - 1) (a := 1 / 2) (b := 1) (by norm_num)
      (hmono.monotoneOn _) (by fun_prop)
      (hβ.mdifferentiable one_ne_zero).mdifferentiableOn
    norm_num at hlength
    exact hlength
  have hηlen : Manifold.pathELength I η 0 1 =
      Manifold.pathELength I γ₁ 0 1 + Manifold.pathELength I γ₂ 0 1 := by
    rw [← Manifold.pathELength_add (I := I) (γ := η) (a := 0) (b := 1 / 2) (c := 1)
      (by norm_num) (by norm_num),
      hη_left, hη_right, hαlen, hβlen]
  have hηconst₀ : η =ᶠ[𝓝 0] (fun _ ↦ γ₁ 0) := by
    have hmap : Tendsto (fun t : ℝ ↦ 2 * t) (𝓝 0) (𝓝 0) := by
      have h : ContinuousAt (fun t : ℝ ↦ 2 * t) 0 := by fun_prop
      -- Expose the value hidden in `ContinuousAt` so `norm_num` can identify the target filter.
      change Tendsto (fun t : ℝ ↦ 2 * t) (𝓝 0) (𝓝 (2 * 0)) at h
      norm_num at h
      exact h
    filter_upwards [hαconst₀.comp_tendsto hmap,
      Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)] with t htα ht
    have ht' : t < 1 / 2 := ht
    rw [show η t = f t by
      exact (Iic (1 / 2 : ℝ)).piecewise_eq_of_mem f g ht'.le]
    simpa only [f, Function.comp_apply] using htα
  have hηconst₁ : η =ᶠ[𝓝 1] (fun _ ↦ γ₂ 1) := by
    have hmap : Tendsto (fun t : ℝ ↦ 2 * t - 1) (𝓝 1) (𝓝 1) := by
      have h : ContinuousAt (fun t : ℝ ↦ 2 * t - 1) 1 := by fun_prop
      -- Expose the value hidden in `ContinuousAt` so `norm_num` can identify the target filter.
      change Tendsto (fun t : ℝ ↦ 2 * t - 1) (𝓝 1) (𝓝 (2 * 1 - 1)) at h
      norm_num at h
      exact h
    filter_upwards [hβconst₁.comp_tendsto hmap,
      Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)] with t htβ ht
    have ht' : 1 / 2 < t := ht
    rw [show η t = g t by
      exact (Iic (1 / 2 : ℝ)).piecewise_eq_of_notMem f g (not_le_of_gt ht')]
    simpa only [g, Function.comp_apply] using htβ
  exact ⟨η, hη, hη₀, hη₁, hηlen, hηconst₀, hηconst₁⟩

end TauCeti
