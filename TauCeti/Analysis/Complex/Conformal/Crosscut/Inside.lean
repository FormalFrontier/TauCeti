/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Analysis.Complex.Conformal.Crosscut.SmallJordanCurve
public import TauCeti.Analysis.Normed.Module.FilledHull
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.Analysis.Complex.Conformal.Crosscut.Basic
public import TauCeti.Analysis.Complex.Conformal.Crosscut.Image
import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected
import TauCeti.Analysis.Complex.Conformal.InverseFunction
import TauCeti.Analysis.Contour.Winding.Separation
import TauCeti.Topology.MetricSpace.Cut
import TauCeti.Topology.JordanCurve.Separation

/-!
# One image piece of a crosscut lies inside a compact enclosing set

For a holomorphic injection of `ball c r`, one of the two image pieces — the near side
`ball c r ∩ ball ζ ρ` or the far side `ball c r \ closedBall ζ ρ` — lies in the filled hull of a
compact set through the image crosscut. The transversal segment through a point of the crosscut has
the near side on one side and the far side on the other, and the enclosing set is adherent from both
sides; the winding-number two-sidedness theorem puts one end in the filled hull. No Jordan curve
theorem is used.

This is the planar-separation step of the `ConformalMapping` roadmap (L5).

## Main results

* `TauCeti.exists_mem_image_inter_ball_and_image_sdiff_closedBall` — **the transversal
  segment through a point of the image crosscut, with near side and far side on opposite sides.**
* `TauCeti.mem_closure_image_inter_sphere_inter_setOf_im_pos_and_im_neg` — **the image crosscut is
  adherent to each of its points from both sides of the transversal.**
* `TauCeti.image_inter_ball_subset_filledHull_or_image_sdiff_closedBall_subset_filledHull` —
  **one of the two image pieces lies in the filled hull of a closed bounded set through the image
  crosscut.**
* `TauCeti.image_inter_ball_subset_filledHull_of_diam_lt'` — diameter selection: when the enclosing
  set is narrower than the far side, the near side is enclosed. Consumes the disjunction above
  without the `hp`/`hin` plane-separation input.
* `TauCeti.image_subset_filledHull_of_disjoint_inter_sphere` — an image side meeting the inside of
  such a curve lies inside it.
* `TauCeti.nonempty_image_inter_ball_inter_filledHull_or_image_sdiff_closedBall_inter_filledHull` —
  one of the two image sides meets the inside of a curve when an image-domain point lies in
  `closure (filledHull K \ K)`. This is where the inside assumption
  `hin : p ∈ closure (filledHull K \ K)` is introduced; the diameter criterion below passes it on
  unchanged.
* `TauCeti.image_inter_ball_subset_filledHull_of_diam_lt` — such a curve, if narrower than the far
  side, encloses the *near* side.
* `TauCeti.image_inter_ball_subset_filledHull_of_frontier_subset` — the enclosure hypothesis is
  implied by the boundary-piece hypothesis of `Conformal/CutDiameter.lean`.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Section 2.2.
* J. B. Garnett and D. E. Marshall, *Harmonic Measure*, Theorem I.3.1.
-/

public section

open Bornology Complex Filter Metric Set

open scoped Topology

namespace TauCeti

variable {f : ℂ → ℂ} {c ζ z₀ : ℂ} {r ρ : ℝ}

/-- A point of a sphere of positive radius is not its centre. -/
private theorem sub_ne_zero_of_mem_sphere (hρ : 0 < ρ) (hz₀ : z₀ ∈ sphere ζ ρ) :
    z₀ - ζ ≠ 0 := by
  intro h
  rw [mem_sphere, dist_eq_norm, h, norm_zero] at hz₀
  exact hρ.ne hz₀

private theorem hasDerivAt_invFunOn_comp_segment {f : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hinj : InjOn f U) {z₀ : ℂ}
    (hz₀ : z₀ ∈ U) (n : ℂ) :
    HasDerivAt (fun t : ℝ => Function.invFunOn f U (deriv f z₀ * n * t + f z₀)) n 0 := by
  have h1 : HasDerivAt (fun t : ℝ => deriv f z₀ * n * (t : ℂ) + f z₀)
      (deriv f z₀ * n) 0 := by
    simpa using
      (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul (deriv f z₀ * n)).add_const (f z₀))
  have h2 : HasDerivAt (Function.invFunOn f U) (deriv f z₀)⁻¹
      (deriv f z₀ * n * ((0 : ℝ) : ℂ) + f z₀) := by
    simpa using hf.hasDerivAt_invFunOn hU hinj hz₀
  have h3 := HasDerivAt.scomp (0 : ℝ) h2 h1
  have h4 : (deriv f z₀ * n) • (deriv f z₀)⁻¹ = n := by
    rw [smul_eq_mul]
    field_simp [hf.deriv_ne_zero_of_injOn hU hinj hz₀]
  rw [h4] at h3
  exact h3

/-- **The transversal segment through a point of the image crosscut.** For small negative `t` the
segment lies in the image of the near side, and for small positive `t` in the far side. -/
theorem exists_mem_image_inter_ball_and_image_sdiff_closedBall
    (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hz₀ : z₀ ∈ ball c r ∩ sphere ζ ρ) (hρ : 0 < ρ) :
    ∃ η : ℝ, 0 < η ∧
      (∀ t : ℝ, t ∈ Ioo (-η) 0 →
        deriv f z₀ * (z₀ - ζ) * (t : ℂ) + f z₀ ∈ f '' (ball c r ∩ ball ζ ρ)) ∧
      ∀ t : ℝ, t ∈ Ioo 0 η →
        deriv f z₀ * (z₀ - ζ) * (t : ℂ) + f z₀ ∈ f '' (ball c r \ closedBall ζ ρ) := by
  obtain ⟨hz₀b, hz₀s⟩ := hz₀
  have hΩ : IsOpen (f '' ball c r) := isOpen_image_of_differentiableOn_of_injOn isOpen_ball hf hinj
  have hp : f z₀ ∈ f '' ball c r := mem_image_of_mem f hz₀b
  set g := Function.invFunOn f (ball c r) with hg_def
  have hg : DifferentiableOn ℂ g (f '' ball c r) :=
    TauCeti.DifferentiableOn.invFunOn hf isOpen_ball hinj
  have hgf : ∀ z ∈ ball c r, g (f z) = z := fun z hz => hinj.leftInvOn_invFunOn hz
  have hfg : ∀ w ∈ f '' ball c r, f (g w) = w := fun w hw => Function.invFunOn_eq hw
  have hgmem : ∀ w ∈ f '' ball c r, g w ∈ ball c r := fun w hw => Function.invFunOn_mem hw
  have hd0 : deriv f z₀ ≠ 0 :=
    hf.deriv_ne_zero_of_injOn isOpen_ball hinj hz₀b
  have hzζ : z₀ - ζ ≠ 0 := sub_ne_zero_of_mem_sphere hρ hz₀s
  set v := deriv f z₀ * (z₀ - ζ) with hv_def
  have hv : v ≠ 0 := mul_ne_zero hd0 hzζ
  -- the pulled-back segment has velocity `z₀ - ζ` at `t = 0`
  have hφ : HasDerivAt (fun t : ℝ => g (v * t + f z₀)) (z₀ - ζ) 0 :=
    hasDerivAt_invFunOn_comp_segment hf isOpen_ball hinj hz₀b (z₀ - ζ)
  have hφ0 : g (v * ((0 : ℝ) : ℂ) + f z₀) = z₀ := by simp [hgf z₀ hz₀b]
  -- the little-`o` estimate at `t = 0`, and the segment staying in the image domain
  have hev : ∀ᶠ t : ℝ in 𝓝 0,
      ‖g (v * t + f z₀) - g (v * ((0 : ℝ) : ℂ) + f z₀) - (t - 0) • (z₀ - ζ)‖ ≤
        ρ / 2 * ‖t - 0‖ :=
    (hasDerivAt_iff_isLittleO.mp hφ).def (by positivity)
  have hΩev : ∀ᶠ t : ℝ in 𝓝 0, v * t + f z₀ ∈ f '' ball c r := by
    have hcont : Continuous fun t : ℝ => v * (t : ℂ) + f z₀ := by fun_prop
    have h0 : (fun t : ℝ => v * (t : ℂ) + f z₀) 0 ∈ f '' ball c r := by simpa using hp
    exact hcont.continuousAt.preimage_mem_nhds (hΩ.mem_nhds h0)
  obtain ⟨η, hη, hηball⟩ := Metric.eventually_nhds_iff.mp (hev.and hΩev)
  have hnorm : ‖z₀ - ζ‖ = ρ := by rwa [← dist_eq_norm, ← mem_sphere]
  refine ⟨min η 1, lt_min hη one_pos, fun t ht => ?_, fun t ht => ?_⟩
  · -- `t < 0`: the pulled-back point is closer to `ζ` than `ρ`
    have htη : dist t 0 < η := by
      rw [Real.dist_eq, sub_zero, abs_of_neg ht.2]
      linarith [ht.1, min_le_left η 1]
    have ht1 : -1 < t := by linarith [ht.1, min_le_right η 1]
    obtain ⟨hlo, hmem⟩ := hηball htη
    rw [hφ0, sub_zero, Real.norm_eq_abs, abs_of_neg ht.2] at hlo
    have hfactor : z₀ - ζ + t • (z₀ - ζ) = (1 + t) • (z₀ - ζ) := by
      rw [add_smul, one_smul]
    refine ⟨g (v * t + f z₀), ⟨hgmem _ hmem, ?_⟩, hfg _ hmem⟩
    rw [mem_ball, dist_eq_norm]
    calc ‖g (v * t + f z₀) - ζ‖
        ≤ ‖z₀ - ζ + t • (z₀ - ζ)‖ +
            ‖g (v * t + f z₀) - z₀ - t • (z₀ - ζ)‖ := by
          have := norm_le_insert' (g (v * t + f z₀) - ζ) (z₀ - ζ + t • (z₀ - ζ))
          have e : g (v * t + f z₀) - ζ - (z₀ - ζ + t • (z₀ - ζ))
              = g (v * t + f z₀) - z₀ - t • (z₀ - ζ) := by abel
          rwa [e] at this
      _ ≤ (1 + t) * ρ + ρ / 2 * (-t) := by
          gcongr
          · rw [hfactor, norm_smul, hnorm, Real.norm_eq_abs,
              abs_of_pos (by linarith)]
      _ < ρ := by nlinarith [ht.2]
  · -- `t > 0`: the pulled-back point is farther from `ζ` than `ρ`
    have htη : dist t 0 < η := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
      linarith [ht.2, min_le_left η 1]
    obtain ⟨hlo, hmem⟩ := hηball htη
    rw [hφ0, sub_zero, Real.norm_eq_abs, abs_of_pos ht.1] at hlo
    have hfactor : z₀ - ζ + t • (z₀ - ζ) = (1 + t) • (z₀ - ζ) := by
      rw [add_smul, one_smul]
    refine ⟨g (v * t + f z₀), ⟨hgmem _ hmem, fun hcb => ?_⟩, hfg _ hmem⟩
    rw [mem_closedBall, dist_eq_norm] at hcb
    have hlow : (1 + t) * ρ - ρ / 2 * t ≤ ‖g (v * t + f z₀) - ζ‖ := by
      calc (1 + t) * ρ - ρ / 2 * t
          ≤ ‖z₀ - ζ + t • (z₀ - ζ)‖ -
              ‖g (v * t + f z₀) - z₀ - t • (z₀ - ζ)‖ := by
            rw [hfactor, norm_smul, hnorm, Real.norm_eq_abs,
              abs_of_pos (by linarith [ht.1])]
            linarith
        _ ≤ ‖g (v * t + f z₀) - ζ‖ := by
            have := norm_sub_norm_le (z₀ - ζ + t • (z₀ - ζ)) (g (v * t + f z₀) - ζ)
            have e : z₀ - ζ + t • (z₀ - ζ) - (g (v * t + f z₀) - ζ)
                = -(g (v * t + f z₀) - z₀ - t • (z₀ - ζ)) := by abel
            rw [e, norm_neg] at this
            linarith
    nlinarith [ht.1]

/-- **The image crosscut is adherent from both sides of the transversal segment.** In the
transversal coordinate the crosscut has velocity `i` at the crossing point. -/
theorem mem_closure_image_inter_sphere_inter_setOf_im_pos_and_im_neg
    (hf : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) (hz₀ : z₀ ∈ ball c r ∩ sphere ζ ρ) (hρ : 0 < ρ) :
    f z₀ ∈ closure (f '' (ball c r ∩ sphere ζ ρ) ∩
        {q | 0 < ((q - f z₀) / (deriv f z₀ * (z₀ - ζ))).im}) ∧
    f z₀ ∈ closure (f '' (ball c r ∩ sphere ζ ρ) ∩
        {q | ((q - f z₀) / (deriv f z₀ * (z₀ - ζ))).im < 0}) := by
  obtain ⟨hz₀b, hz₀s⟩ := hz₀
  have hd0 : deriv f z₀ ≠ 0 :=
    hf.deriv_ne_zero_of_injOn isOpen_ball hinj hz₀b
  have hzζ : z₀ - ζ ≠ 0 := sub_ne_zero_of_mem_sphere hρ hz₀s
  set v := deriv f z₀ * (z₀ - ζ) with hv_def
  have hfz : HasDerivAt f (deriv f z₀) z₀ :=
    (hf.differentiableAt (isOpen_ball.mem_nhds hz₀b)).hasDerivAt
  obtain ⟨θ₀, -, hθ₀⟩ := exists_mem_Icc_circleMap_eq 0 hz₀s
  rw [zero_add] at hθ₀
  -- the imaginary coordinate of the crosscut, as a function of the angle
  set χ : ℝ → ℝ := fun θ => ((f (circleMap ζ ρ θ) - f z₀) / v).im with hχ_def
  have hχ : HasDerivAt χ 1 θ₀ := by
    have h1 : HasDerivAt (circleMap ζ ρ) (circleMap 0 ρ θ₀ * I) θ₀ :=
      hasDerivAt_circleMap ζ ρ θ₀
    have h2 : HasDerivAt f (deriv f z₀) (circleMap ζ ρ θ₀) := by rw [hθ₀]; exact hfz
    have h3 := HasDerivAt.scomp θ₀ h2 h1
    have h4 : HasDerivAt (fun θ => (f (circleMap ζ ρ θ) - f z₀) / v)
        ((circleMap 0 ρ θ₀ * I) * deriv f z₀ / v) θ₀ := by
      simpa [Function.comp_def, smul_eq_mul] using (h3.sub_const (f z₀)).div_const v
    have h5 : HasDerivAt χ (((circleMap 0 ρ θ₀ * I) * deriv f z₀ / v).im) θ₀ :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ₀ h4
    have hcm : circleMap 0 ρ θ₀ = z₀ - ζ := by rw [← circleMap_sub_center, hθ₀]
    have h6 : ((circleMap 0 ρ θ₀ * I) * deriv f z₀ / v).im = 1 := by
      rw [hcm, hv_def]
      have : (z₀ - ζ) * I * deriv f z₀ / (deriv f z₀ * (z₀ - ζ)) = I := by
        field_simp
      rw [this, Complex.I_im]
    rw [h6] at h5
    exact h5
  have hχ0 : χ θ₀ = 0 := by
    simp [χ, hθ₀]
  -- the sign of `χ` on either side of `θ₀`
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < χ (θ₀ + t) := by
    filter_upwards [hχ.tendsto_slope_zero_right.eventually (lt_mem_nhds zero_lt_one),
      self_mem_nhdsWithin] with t ht ht0
    rw [hχ0, sub_zero, smul_eq_mul] at ht
    exact (pos_iff_pos_of_mul_pos ht).mp (inv_pos.mpr ht0)
  have hneg : ∀ᶠ t in 𝓝[<] (0 : ℝ), χ (θ₀ + t) < 0 := by
    filter_upwards [hχ.tendsto_slope_zero_left.eventually (lt_mem_nhds zero_lt_one),
      self_mem_nhdsWithin] with t ht ht0
    rw [hχ0, sub_zero, smul_eq_mul] at ht
    exact (neg_iff_neg_of_mul_pos ht).mp (inv_lt_zero.mpr ht0)
  -- nearby crosscut points lie in the disc, and their images are close to `f z₀`
  have hcirc : Continuous fun t : ℝ => circleMap ζ ρ (θ₀ + t) :=
    (continuous_circleMap ζ ρ).comp (continuous_const.add continuous_id)
  have hcirc0 : circleMap ζ ρ (θ₀ + 0) = z₀ := by rw [add_zero, hθ₀]
  have hball : ∀ᶠ t in 𝓝 (0 : ℝ), circleMap ζ ρ (θ₀ + t) ∈ ball c r := by
    refine hcirc.continuousAt.preimage_mem_nhds ?_
    rw [hcirc0]
    exact isOpen_ball.mem_nhds hz₀b
  have hclose : ∀ ε > 0, ∀ᶠ t in 𝓝 (0 : ℝ),
      dist (f (circleMap ζ ρ (θ₀ + t))) (f z₀) < ε := by
    intro ε hε
    have hfc : ContinuousAt (fun t : ℝ => f (circleMap ζ ρ (θ₀ + t))) 0 :=
      (hf.continuousOn.continuousAt (isOpen_ball.mem_nhds hz₀b)).comp_of_eq
        hcirc.continuousAt hcirc0
    have := hfc.eventually (Metric.ball_mem_nhds _ hε)
    simpa [hθ₀] using this
  have hmemγ : ∀ t : ℝ, circleMap ζ ρ (θ₀ + t) ∈ ball c r →
      f (circleMap ζ ρ (θ₀ + t)) ∈ f '' (ball c r ∩ sphere ζ ρ) := fun t ht =>
    mem_image_of_mem f ⟨ht, circleMap_mem_sphere ζ hρ.le _⟩
  constructor
  · rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨t, ⟨ht1, ht2⟩, ht3⟩ :=
      ((((hclose ε hε).and hball).filter_mono nhdsWithin_le_nhds).and hpos).exists
    exact ⟨_, ⟨hmemγ t ht2, ht3⟩, by rw [dist_comm]; exact ht1⟩
  · rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨t, ⟨ht1, ht2⟩, ht3⟩ :=
      ((((hclose ε hε).and hball).filter_mono nhdsWithin_le_nhds).and hneg).exists
    exact ⟨_, ⟨hmemγ t ht2, ht3⟩, by rw [dist_comm]; exact ht1⟩

/-- **One of the two image pieces lies in the filled hull of a closed bounded set through the image
crosscut.** The transversal segment meets the set only at the crossing point, and the set minus that
point is preconnected, so the winding-number two-sidedness theorem applies. The preconnectedness
hypothesis `hKp` is required only at the selected crossing point `z₀`, not at every crosscut
point. -/
theorem image_inter_ball_subset_filledHull_or_image_sdiff_closedBall_subset_filledHull
    (hζ : dist ζ c = r) (hρ : 0 < ρ) (hρr : ρ < 2 * r)
    (hf : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) {K : Set ℂ} (hK : IsClosed K) (hKb : IsBounded K)
    (hγK : f '' (ball c r ∩ sphere ζ ρ) ⊆ K)
    (hKsub : K ⊆ closure (f '' (ball c r ∩ sphere ζ ρ)) ∪ frontier (f '' ball c r))
    {z₀ : ℂ} (hz₀ : z₀ ∈ ball c r ∩ sphere ζ ρ)
    (hKp : IsPreconnected (K \ {f z₀})) :
    f '' (ball c r ∩ ball ζ ρ) ⊆ filledHull K ∨
      f '' (ball c r \ closedBall ζ ρ) ⊆ filledHull K := by
  have hγKcl : closure (f '' (ball c r ∩ sphere ζ ρ)) ⊆ K :=
    hK.closure_subset_iff.mpr hγK
  have hr : 0 < r := by linarith
  have hΩ : IsOpen (f '' ball c r) := isOpen_image_of_differentiableOn_of_injOn isOpen_ball hf hinj
  set p := f z₀ with hp_def
  set v := deriv f z₀ * (z₀ - ζ) with hv_def
  have hv : v ≠ 0 :=
    mul_ne_zero (hf.deriv_ne_zero_of_injOn isOpen_ball hinj hz₀.1)
      (sub_ne_zero_of_mem_sphere hρ hz₀.2)
  obtain ⟨η, hη, hnear, hfar⟩ :=
    exists_mem_image_inter_ball_and_image_sdiff_closedBall hf hinj hz₀ hρ
  obtain ⟨hleft, hright⟩ :=
    mem_closure_image_inter_sphere_inter_setOf_im_pos_and_im_neg hf hinj hz₀ hρ
  -- neither image piece meets `K`
  have hnearK : Disjoint (f '' (ball c r ∩ ball ζ ρ)) K :=
    disjoint_image_of_subset_closure_image_inter_sphere_union_frontier_image
      isOpen_ball hf hinj inter_subset_left disjoint_inter_ball_inter_sphere hKsub
  have hfarK : Disjoint (f '' (ball c r \ closedBall ζ ρ)) K :=
    disjoint_image_of_subset_closure_image_inter_sphere_union_frontier_image
      isOpen_ball hf hinj sdiff_subset disjoint_sdiff_closedBall_inter_sphere hKsub
  -- the two-sidedness theorem, applied to `K` and the segment on `[-η/2, η/2]`
  have hpγ : p ∈ f '' (ball c r ∩ sphere ζ ρ) := mem_image_of_mem f hz₀
  have hpK : p ∈ K := hγKcl (subset_closure hpγ)
  have hseg : ∀ t ∈ Icc (-(η / 2)) (η / 2), v * t + p ∈ K → t = 0 := by
    intro t ht hKt
    by_contra ht0
    rcases lt_or_gt_of_ne ht0 with hneg | hpos
    · exact Set.disjoint_left.mp hnearK (hnear t ⟨by linarith [ht.1], hneg⟩) hKt
    · exact Set.disjoint_left.mp hfarK (hfar t ⟨hpos, by linarith [ht.2]⟩) hKt
  have hγK' : ∀ S : Set ℂ, f '' (ball c r ∩ sphere ζ ρ) ∩ S ⊆ K ∩ S := fun S =>
    inter_subset_inter (subset_closure.trans hγKcl) subset_rfl
  have key := Contour.mem_filledHull_or_mem_filledHull_of_isPreconnected_sdiff_singleton
    (K := K) (v := v) (z₀ := p) (a := -(η / 2)) (b := η / 2) (s := 0)
    hK hKb hv ⟨by linarith, by linarith⟩
    (by simpa using hseg) (by simpa using hKp)
    (by simpa using closure_mono (hγK' _) hleft) (by simpa using closure_mono (hγK' _) hright)
  rcases key with hx | hy
  · left
    have hA : IsPreconnected (f '' (ball c r ∩ ball ζ ρ)) :=
      ((isConnected_ball_inter_ball hr hρ (by rw [dist_comm, hζ]; linarith)).image f
        (hf.continuousOn.mono inter_subset_left)).isPreconnected
    exact IsPreconnected.subset_filledHull hA hnearK
      ⟨_, hnear (-(η / 2)) ⟨by linarith, by linarith⟩, by simpa using hx⟩
  · right
    have hB : IsPreconnected (f '' (ball c r \ closedBall ζ ρ)) :=
      ((isConnected_ball_diff_closedBall hζ hρ hρr).image f
        (hf.continuousOn.mono sdiff_subset)).isPreconnected
    exact IsPreconnected.subset_filledHull hB hfarK
      ⟨_, hfar (η / 2) ⟨by linarith, by linarith⟩, hy⟩

/-- **Diameter selection: when the enclosing set is narrower than the far side, the near side is
enclosed.** This consumes the disjunction
`TauCeti.image_inter_ball_subset_filledHull_or_image_sdiff_closedBall_subset_filledHull` by
excluding the far-side case: trapping the far side inside `K` gives
`diam (f '' (ball c r \ closedBall ζ ρ)) ≤ diam K`, contradicting the hypothesis. Unlike
`TauCeti.image_inter_ball_subset_filledHull_of_diam_lt`, no `hp`/`hin` plane-separation input is
needed — the preconnectedness hypothesis `hKp` on `K \ {p}` is discharged by
`IsJordanCurve.isPathConnected_sdiff_singleton` in the intended application. -/
theorem image_inter_ball_subset_filledHull_of_diam_lt'
    (hζ : dist ζ c = r) (hρ : 0 < ρ) (hρr : ρ < 2 * r)
    (hf : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) {K : Set ℂ} (hK : IsClosed K) (hKb : IsBounded K)
    (hγK : f '' (ball c r ∩ sphere ζ ρ) ⊆ K)
    (hKsub : K ⊆ closure (f '' (ball c r ∩ sphere ζ ρ)) ∪ frontier (f '' ball c r))
    {z₀ : ℂ} (hz₀ : z₀ ∈ ball c r ∩ sphere ζ ρ)
    (hKp : IsPreconnected (K \ {f z₀}))
    (hlt : diam K < diam (f '' (ball c r \ closedBall ζ ρ))) :
    f '' (ball c r ∩ ball ζ ρ) ⊆ filledHull K := by
  rcases image_inter_ball_subset_filledHull_or_image_sdiff_closedBall_subset_filledHull
    hζ hρ hρr hf hinj hK hKb hγK hKsub hz₀ hKp with h | h
  · exact h
  · exact absurd (diam_le_diam_of_subset_filledHull hKb h) (not_le.mpr hlt)

/-! ## An enclosed side is trapped, and narrow -/

section OldInside

variable {U K V : Set ℂ} {p : ℂ}

open Topology

/-- **An image side that meets the inside of such a curve lies inside it.** The side is
preconnected as a continuous image of a preconnected set and disjoint from `K` by
`TauCeti.disjoint_image_of_subset_closure_image_inter_sphere_union_frontier_image`,
so `TauCeti.IsPreconnected.subset_filledHull`
traps it in the bounded component of `Kᶜ` it meets. Instantiate `V` at `U ∩ ball ζ ρ` for the near
side and at `U \ closedBall ζ ρ` for the far side. -/
theorem image_subset_filledHull_of_disjoint_inter_sphere (hUo : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U) (hVU : V ⊆ U)
    (hV : Disjoint V (U ∩ sphere ζ ρ)) (hVc : IsPreconnected V)
    (hK : K ⊆ closure (f '' (U ∩ sphere ζ ρ)) ∪ frontier (f '' U))
    (hne : (f '' V ∩ filledHull K).Nonempty) : f '' V ⊆ filledHull K :=
  IsPreconnected.subset_filledHull (hVc.image f (hd.continuousOn.mono hVU))
    (disjoint_image_of_subset_closure_image_inter_sphere_union_frontier_image
      hUo hd hinj hVU hV hK) hne

/-- **One of the two image sides meets the inside of a curve with an image-domain point adherent to
its inside.** If a point `p` of the image domain lies in `closure (filledHull K \ K)` — i.e. is a
limit of points of `filledHull K \ K` — then a point `q` close enough to `p` lies in the open image
domain; being off `K` it is off the image crosscut, so it lies on one of the two image sides, and it
lies in `filledHull K`.

This is where the inside assumption is introduced, at one point as a hypothesis; the diameter
criterion below passes it on unchanged. For a Jordan curve `K` the hypothesis is the
plane-separation statement `J ⊆ closure (filledHull J \ J)` recorded in the roadmap section of
`TauCeti/Topology/FilledHull.lean`, read at `p`. -/
theorem nonempty_image_inter_ball_inter_filledHull_or_image_sdiff_closedBall_inter_filledHull
    (hΩo : IsOpen (f '' U)) (hγ : f '' (U ∩ sphere ζ ρ) ⊆ K)
    (hp : p ∈ f '' U) (hin : p ∈ closure (filledHull K \ K)) :
    (f '' (U ∩ ball ζ ρ) ∩ filledHull K).Nonempty ∨
      (f '' (U \ closedBall ζ ρ) ∩ filledHull K).Nonempty := by
  obtain ⟨q, hqΩ, hqH, hqK⟩ :=
    mem_closure_iff.mp hin _ hΩo hp
  rw [image_eq_image_inter_ball_union_image_sdiff_closedBall_union_image_inter_sphere] at hqΩ
  exact (hqΩ.resolve_right fun h => hqK (hγ h)).imp (fun h => ⟨q, h, hqH⟩) fun h => ⟨q, h, hqH⟩

/-- **A narrow curve next to a crosscut encloses the near side.** Let `K` be bounded, run from the
image crosscut along the boundary of the image domain, and have a point of its inside next to the
image crosscut. If `K` is narrower than the *far* image side — the situation at a small crosscut
radius, where the far side is nearly the whole image domain — then it is the *near* side that `K`
encloses, and by `TauCeti.diam_le_diam_of_subset_filledHull` that side is no wider than `K`.

Of the two alternatives
`TauCeti.nonempty_image_inter_ball_inter_filledHull_or_image_sdiff_closedBall_inter_filledHull`
offers, the far one
is excluded: it would trap the far side inside `K` and so make it no wider than `K`. The theorem
still requires both cut sides to be preconnected, a point in the image domain, and the strict
far-side diameter bound; those inputs are not produced here. -/
theorem image_inter_ball_subset_filledHull_of_diam_lt (hUo : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    (hAc : IsPreconnected (U ∩ ball ζ ρ)) (hBc : IsPreconnected (U \ closedBall ζ ρ))
    (hKb : IsBounded K) (hγ : f '' (U ∩ sphere ζ ρ) ⊆ K)
    (hK : K ⊆ closure (f '' (U ∩ sphere ζ ρ)) ∪ frontier (f '' U))
    (hlt : diam K < diam (f '' (U \ closedBall ζ ρ)))
    (hp : p ∈ f '' U) (hin : p ∈ closure (filledHull K \ K)) :
    f '' (U ∩ ball ζ ρ) ⊆ filledHull K := by
  rcases nonempty_image_inter_ball_inter_filledHull_or_image_sdiff_closedBall_inter_filledHull
    (isOpen_image_of_differentiableOn_of_injOn hUo hd hinj) hγ hp hin with h | h
  · exact image_subset_filledHull_of_disjoint_inter_sphere hUo hd hinj inter_subset_left
      disjoint_inter_ball_inter_sphere hAc hK h
  · exact absurd (diam_le_diam_of_subset_filledHull hKb
      (image_subset_filledHull_of_disjoint_inter_sphere hUo hd hinj sdiff_subset
        disjoint_sdiff_closedBall_inter_sphere hBc hK h)) (not_le.mpr hlt)

/-- **A boundary piece enclosing what the near side clings to encloses the near side.** If every
boundary point of the image domain on the frontier of the near image side lies in `E`, then the
frontier of that side lies in `f '' (U ∩ sphere ζ ρ) ∪ E` by
`TauCeti.frontier_image_inter_ball_subset`, so `TauCeti.subset_filledHull_of_frontier_subset`
encloses the side.

Thus the frontier route supplies the same filled-hull inclusion as the enclosure route, with the
same `E`; either inclusion becomes a width bound on the near side by
`TauCeti.diam_le_diam_of_subset_filledHull`. -/
theorem image_inter_ball_subset_filledHull_of_frontier_subset (hUo : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    (hb : IsBounded (f '' (U ∩ ball ζ ρ))) {E : Set ℂ}
    (hE : frontier (f '' U) ∩ frontier (f '' (U ∩ ball ζ ρ)) ⊆ E) :
    f '' (U ∩ ball ζ ρ) ⊆ filledHull (f '' (U ∩ sphere ζ ρ) ∪ E) :=
  subset_filledHull_of_frontier_subset
    hb
    fun _ hw => (frontier_image_inter_ball_subset hUo hd hinj hw).imp id fun h => hE ⟨h, hw⟩

end OldInside

end TauCeti
