/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.FilledHull
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.Analysis.Complex.Conformal.Crosscut.Basic
public import TauCeti.Analysis.Complex.Conformal.Crosscut.Image
import TauCeti.Analysis.Complex.Conformal.Inverse.Function
import TauCeti.Analysis.Contour.Winding.Separation
import TauCeti.Topology.MetricSpace.Cut

/-!
# One image piece of a crosscut lies inside a compact enclosing set

For a holomorphic injection of an open set `U`, one of the two image pieces — the near
side `U ∩ ball ζ ρ` or the far side `U \ closedBall ζ ρ` — lies in the filled hull of a
closed bounded set `K` through the image crosscut. The hypotheses are:

* `K` contains the image crosscut and is contained in its closure union `frontier (f '' U)`.
* `K \ {f z₀}` is preconnected at a chosen crosscut point `z₀`.
* The two image pieces are preconnected (`hAc`, `hBc`). For `U = ball c r` these follow from the
  ball geometry (`isConnected_ball_inter_ball`, `isConnected_ball_diff_closedBall`).

The transversal segment through a point of the crosscut has the near side on one side and the
far side on the other; the winding-number two-sidedness theorem
(`Contour.mem_filledHull_or_mem_filledHull_of_isPreconnected_sdiff_singleton`) puts one end in the
filled hull. No Jordan curve theorem is used.

This is the planar-separation step of the `ConformalMapping` roadmap (L5).

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, and Mathlib has no boundary correspondence for
conformal maps, so this is new Lean formalization rather than a temporary shim.

## Main results

* `TauCeti.exists_pos_forall_mem_image_inter_ball_and_image_sdiff_closedBall` — **the transversal
  segment through a point of the image crosscut, with near side and far side on opposite sides.**
* `TauCeti.mem_closure_image_inter_sphere_inter_setOf_im_pos_and_mem_closure_inter_setOf_im_neg`
  — **the image crosscut is
  adherent to each of its points from both sides of the transversal.**
* `TauCeti.image_inter_ball_subset_filledHull_or_image_sdiff_closedBall_subset_filledHull` —
  **one of the two image pieces lies in the filled hull of a closed bounded set through the image
  crosscut.** Requires `K \ {f z₀}` preconnected.
* `TauCeti.image_inter_ball_subset_filledHull_of_diam_lt_of_isPreconnected_sdiff_singleton`
  — diameter selection: when the enclosing set is narrower than the far side, the near side is
  enclosed.
  Consumes the disjunction above; `IsJordanCurve.isPathConnected_sdiff_singleton` discharges the
  preconnectedness hypothesis in the intended application.
* `TauCeti.image_inter_ball_subset_filledHull_of_frontier_subset` — the enclosure hypothesis is
  implied by the boundary-piece hypothesis of `Conformal/CutDiameter.lean`.

## References

* C. Carathéodory, *Über die Begrenzung einfach zusammenhängender Gebiete*, Math. Ann. 73, 1913.
* P. L. Duren, *Univalent Functions*, Chapter 3.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Section 2.3.
* J. B. Garnett and D. E. Marshall, *Harmonic Measure*, Theorem I.3.1.
-/

public section

open Bornology Complex Filter Metric Set

open scoped Topology

namespace TauCeti

variable {f : ℂ → ℂ} {c ζ z₀ : ℂ} {r ρ : ℝ}

/-- **The transversal segment through a point of the image crosscut.** For small negative `t` the
segment lies in the image of the near side, and for small positive `t` in the far side. -/
theorem exists_pos_forall_mem_image_inter_ball_and_image_sdiff_closedBall {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hinj : InjOn f U)
    (hz₀ : z₀ ∈ U ∩ sphere ζ ρ) (hρ : 0 < ρ) :
    ∃ η : ℝ, 0 < η ∧
      (∀ t : ℝ, t ∈ Ioo (-η) 0 →
        deriv f z₀ * (z₀ - ζ) * (t : ℂ) + f z₀ ∈ f '' (U ∩ ball ζ ρ)) ∧
      ∀ t : ℝ, t ∈ Ioo 0 η →
        deriv f z₀ * (z₀ - ζ) * (t : ℂ) + f z₀ ∈ f '' (U \ closedBall ζ ρ) := by
  obtain ⟨hz₀b, hz₀s⟩ := hz₀
  have hΩ : IsOpen (f '' U) := isOpen_image_of_differentiableOn_of_injOn hU hf hinj
  have hp : f z₀ ∈ f '' U := mem_image_of_mem f hz₀b
  set g := Function.invFunOn f U
  have hgf : ∀ z ∈ U, g (f z) = z := fun z hz => hinj.leftInvOn_invFunOn hz
  have hfg : ∀ w ∈ f '' U, f (g w) = w := fun w hw => Function.invFunOn_eq hw
  have hgmem : ∀ w ∈ f '' U, g w ∈ U := fun w hw => Function.invFunOn_mem hw
  have hd0 : deriv f z₀ ≠ 0 :=
    deriv_ne_zero_of_injOn hf hU hinj hz₀b
  have hzζ : z₀ - ζ ≠ 0 := sub_ne_zero.mpr (Metric.ne_of_mem_sphere hz₀s hρ.ne')
  set v := deriv f z₀ * (z₀ - ζ) with hv_def
  -- the pulled-back segment has velocity `z₀ - ζ` at `t = 0`
  have hφ : HasDerivAt (fun t : ℝ => g (v * t + f z₀)) (z₀ - ζ) 0 :=
    hasDerivAt_invFunOn_comp_segment hf hU hinj hz₀b (z₀ - ζ)
  have hφ0 : g (v * ((0 : ℝ) : ℂ) + f z₀) = z₀ := by simp [hgf z₀ hz₀b]
  have hnorm : ‖z₀ - ζ‖ = ρ := by rwa [← dist_eq_norm, ← mem_sphere]
  -- derivative of ‖g(v*t + f z₀) - ζ‖² at t = 0 is 2ρ², via HasDerivAt.norm_sq
  set ψ := fun t : ℝ => ‖g (v * t + f z₀) - ζ‖ ^ 2
  have hψ : HasDerivAt ψ (2 * ρ ^ 2) 0 := by
    have h1 := (hφ.sub_const ζ).norm_sq
    rw [hφ0, real_inner_self_eq_norm_sq, hnorm] at h1
    exact h1
  have hψ0 : ψ 0 = ρ ^ 2 := by
    dsimp only [ψ]
    simp only [Complex.ofReal_zero, mul_zero, zero_add, hgf z₀ hz₀b,
      hnorm]
  have hρsq : (0 : ℝ) < ρ ^ 2 := sq_pos_of_pos hρ
  have hev : ∀ᶠ t : ℝ in 𝓝 0,
      |ψ t - ρ ^ 2 - t * (2 * ρ ^ 2)| ≤ ρ ^ 2 * |t| := by
    have := (hasDerivAt_iff_isLittleO.mp hψ).def hρsq
    simp only [hψ0, sub_zero, Real.norm_eq_abs] at this
    exact this
  have hΩev : ∀ᶠ t : ℝ in 𝓝 0, v * t + f z₀ ∈ f '' U := by
    have hcont : Continuous fun t : ℝ => v * (t : ℂ) + f z₀ := by fun_prop
    have h0 : (fun t : ℝ => v * (t : ℂ) + f z₀) 0 ∈ f '' U := by simpa using hp
    exact hcont.continuousAt.preimage_mem_nhds (hΩ.mem_nhds h0)
  obtain ⟨η, hη, hηball⟩ := Metric.eventually_nhds_iff.mp (hev.and hΩev)
  refine ⟨η, hη, fun t ht => ?_, fun t ht => ?_⟩
  · -- `t < 0`: ψ(t) < ρ², so the pulled-back point is inside `ball ζ ρ`
    have htη : dist t 0 < η := by
      rw [Real.dist_eq, sub_zero, abs_of_neg ht.2]; linarith [ht.1]
    obtain ⟨hsq, hmem⟩ := hηball htη
    rw [abs_of_neg ht.2] at hsq
    have hle := (abs_le.mp hsq).2
    have hlt : ψ t < ρ ^ 2 := by
      have := mul_neg_of_pos_of_neg hρsq ht.2
      linarith
    refine ⟨g (v * t + f z₀), ⟨hgmem _ hmem, ?_⟩, hfg _ hmem⟩
    rw [mem_ball, dist_eq_norm]
    nlinarith [sq_nonneg (‖g (v * t + f z₀) - ζ‖ - ρ)]
  · -- `t > 0`: ψ(t) > ρ², so the pulled-back point is outside `closedBall ζ ρ`
    have htη : dist t 0 < η := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]; exact ht.2
    obtain ⟨hsq, hmem⟩ := hηball htη
    rw [abs_of_pos ht.1] at hsq
    have hle := (abs_le.mp hsq).1
    have hgt : ρ ^ 2 < ψ t := by
      have := mul_pos hρsq ht.1
      linarith
    refine ⟨g (v * t + f z₀), ⟨hgmem _ hmem, fun hcb => ?_⟩,
      hfg _ hmem⟩
    rw [mem_closedBall, dist_eq_norm] at hcb
    have hnsq : ‖g (v * ↑t + f z₀) - ζ‖ ^ 2 ≤ ρ ^ 2 :=
      sq_le_sq' (by linarith [norm_nonneg (g (v * ↑t + f z₀) - ζ)]) hcb
    linarith

/-- **The image crosscut is adherent from both sides of the transversal segment.** In the
transversal coordinate the crosscut has velocity `i` at the crossing point. -/
theorem mem_closure_image_inter_sphere_inter_setOf_im_pos_and_mem_closure_inter_setOf_im_neg
    {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U)
    (hinj : InjOn f U) (hz₀ : z₀ ∈ U ∩ sphere ζ ρ) (hρ : 0 < ρ) :
    f z₀ ∈ closure (f '' (U ∩ sphere ζ ρ) ∩
        {q | 0 < ((q - f z₀) / (deriv f z₀ * (z₀ - ζ))).im}) ∧
    f z₀ ∈ closure (f '' (U ∩ sphere ζ ρ) ∩
        {q | ((q - f z₀) / (deriv f z₀ * (z₀ - ζ))).im < 0}) := by
  obtain ⟨hz₀b, hz₀s⟩ := hz₀
  have hd0 : deriv f z₀ ≠ 0 :=
    deriv_ne_zero_of_injOn hf hU hinj hz₀b
  have hzζ : z₀ - ζ ≠ 0 := sub_ne_zero.mpr (Metric.ne_of_mem_sphere hz₀s hρ.ne')
  set v := deriv f z₀ * (z₀ - ζ) with hv_def
  have hfz : HasDerivAt f (deriv f z₀) z₀ :=
    (hf.differentiableAt (hU.mem_nhds hz₀b)).hasDerivAt
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
  have hball : ∀ᶠ t in 𝓝 (0 : ℝ), circleMap ζ ρ (θ₀ + t) ∈ U := by
    refine hcirc.continuousAt.preimage_mem_nhds ?_
    rw [hcirc0]
    exact hU.mem_nhds hz₀b
  have hclose : ∀ ε > 0, ∀ᶠ t in 𝓝 (0 : ℝ),
      dist (f (circleMap ζ ρ (θ₀ + t))) (f z₀) < ε := by
    intro ε hε
    have hfc : ContinuousAt (fun t : ℝ => f (circleMap ζ ρ (θ₀ + t))) 0 :=
      (hf.continuousOn.continuousAt (hU.mem_nhds hz₀b)).comp_of_eq
        hcirc.continuousAt hcirc0
    have := hfc.eventually (Metric.ball_mem_nhds _ hε)
    simpa [hθ₀] using this
  have hmemγ : ∀ t : ℝ, circleMap ζ ρ (θ₀ + t) ∈ U →
      f (circleMap ζ ρ (θ₀ + t)) ∈ f '' (U ∩ sphere ζ ρ) := fun t ht =>
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

/-- **An image side that meets the inside of such a curve lies inside it.** The side is
preconnected as a continuous image of a preconnected set and disjoint from `K` by
`TauCeti.disjoint_image_of_subset_closure_image_inter_sphere_union_frontier_image`,
so `TauCeti.IsPreconnected.subset_filledHull`
traps it in the bounded component of `Kᶜ` it meets. Instantiate `V` at `U ∩ ball ζ ρ` for the near
side and at `U \ closedBall ζ ρ` for the far side. -/
private theorem image_subset_filledHull_of_disjoint_inter_sphere {U V K : Set ℂ} (hUo : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U) (hVU : V ⊆ U)
    (hV : Disjoint V (U ∩ sphere ζ ρ)) (hVc : IsPreconnected V)
    (hK : K ⊆ closure (f '' (U ∩ sphere ζ ρ)) ∪ frontier (f '' U))
    (hne : (f '' V ∩ filledHull K).Nonempty) : f '' V ⊆ filledHull K :=
  IsPreconnected.subset_filledHull (hVc.image f (hd.continuousOn.mono hVU))
    (disjoint_image_of_subset_closure_image_inter_sphere_union_frontier_image
      hUo hd hinj hVU hV hK) hne

/-- **One of the two image pieces lies in the filled hull of a closed bounded set through the image
crosscut.** The transversal segment meets the set only at the crossing point, and the set minus that
point is preconnected, so the winding-number two-sidedness theorem applies. The preconnectedness
hypothesis `hKp` is required only at the selected crossing point `z₀`, not at every crosscut
point. -/
theorem image_inter_ball_subset_filledHull_or_image_sdiff_closedBall_subset_filledHull {U : Set ℂ}
    (hUo : IsOpen U) (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) (hAc : IsPreconnected (U ∩ ball ζ ρ))
    (hBc : IsPreconnected (U \ closedBall ζ ρ))
    {K : Set ℂ} (hK : IsClosed K) (hKb : IsBounded K)
    (hγK : f '' (U ∩ sphere ζ ρ) ⊆ K)
    (hKsub : K ⊆ closure (f '' (U ∩ sphere ζ ρ)) ∪ frontier (f '' U))
    {z₀ : ℂ} (hz₀ : z₀ ∈ U ∩ sphere ζ ρ)
    (hKp : IsPreconnected (K \ {f z₀})) :
    f '' (U ∩ ball ζ ρ) ⊆ filledHull K ∨
      f '' (U \ closedBall ζ ρ) ⊆ filledHull K := by
  have hγKcl : closure (f '' (U ∩ sphere ζ ρ)) ⊆ K :=
    hK.closure_subset_iff.mpr hγK
  set p := f z₀ with hp_def
  set v := deriv f z₀ * (z₀ - ζ) with hv_def
  have hv : v ≠ 0 :=
    mul_ne_zero (deriv_ne_zero_of_injOn hf hUo hinj hz₀.1)
      (sub_ne_zero.mpr (Metric.ne_of_mem_sphere hz₀.2 hρ.ne'))
  obtain ⟨η, hη, hnear, hfar⟩ :=
    exists_pos_forall_mem_image_inter_ball_and_image_sdiff_closedBall hf hUo hinj hz₀ hρ
  obtain ⟨hleft, hright⟩ :=
    mem_closure_image_inter_sphere_inter_setOf_im_pos_and_mem_closure_inter_setOf_im_neg
      hf hUo hinj hz₀ hρ
  -- neither image piece meets `K`
  have hnearK : Disjoint (f '' (U ∩ ball ζ ρ)) K :=
    disjoint_image_of_subset_closure_image_inter_sphere_union_frontier_image
      hUo hf hinj inter_subset_left disjoint_inter_ball_inter_sphere hKsub
  have hfarK : Disjoint (f '' (U \ closedBall ζ ρ)) K :=
    disjoint_image_of_subset_closure_image_inter_sphere_union_frontier_image
      hUo hf hinj sdiff_subset disjoint_sdiff_closedBall_inter_sphere hKsub
  -- the two-sidedness theorem, applied to `K` and the segment on `[-η/2, η/2]`
  have hpγ : p ∈ f '' (U ∩ sphere ζ ρ) := mem_image_of_mem f hz₀
  have hpK : p ∈ K := hγKcl (subset_closure hpγ)
  have hseg : ∀ t ∈ Icc (-(η / 2)) (η / 2), v * t + p ∈ K → t = 0 := by
    intro t ht hKt
    by_contra ht0
    rcases lt_or_gt_of_ne ht0 with hneg | hpos
    · exact Set.disjoint_left.mp hnearK (hnear t ⟨by linarith [ht.1], hneg⟩) hKt
    · exact Set.disjoint_left.mp hfarK (hfar t ⟨hpos, by linarith [ht.2]⟩) hKt
  have hγK' : ∀ S : Set ℂ, f '' (U ∩ sphere ζ ρ) ∩ S ⊆ K ∩ S := fun S =>
    inter_subset_inter (subset_closure.trans hγKcl) subset_rfl
  have key := Contour.mem_filledHull_or_mem_filledHull_of_isPreconnected_sdiff_singleton
    (K := K) (v := v) (z₀ := p) (a := -(η / 2)) (b := η / 2) (s := 0)
    hK hKb hv ⟨by linarith, by linarith⟩
    (by simpa using hseg) (by simpa using hKp)
    (by simpa using closure_mono (hγK' _) hleft) (by simpa using closure_mono (hγK' _) hright)
  rcases key with hx | hy
  · left
    exact image_subset_filledHull_of_disjoint_inter_sphere hUo hf hinj inter_subset_left
      disjoint_inter_ball_inter_sphere hAc hKsub
      ⟨_, hnear (-(η / 2)) ⟨by linarith, by linarith⟩, by simpa using hx⟩
  · right
    exact image_subset_filledHull_of_disjoint_inter_sphere hUo hf hinj sdiff_subset
      disjoint_sdiff_closedBall_inter_sphere hBc hKsub
      ⟨_, hfar (η / 2) ⟨by linarith, by linarith⟩, hy⟩

/-- **Diameter selection: when the enclosing set is narrower than the far side, the near side is
enclosed.** This consumes the disjunction
`TauCeti.image_inter_ball_subset_filledHull_or_image_sdiff_closedBall_subset_filledHull` by
excluding the far-side case: trapping the far side inside `K` gives
`diam (f '' (U \ closedBall ζ ρ)) ≤ diam K`, contradicting the hypothesis. The plane-separation
input `p ∈ closure (filledHull K \ K)` is replaced by preconnectedness of `K \ {f z₀}`, which is
discharged by
`IsJordanCurve.isPathConnected_sdiff_singleton` in the intended application. -/
theorem
    image_inter_ball_subset_filledHull_of_diam_lt_of_isPreconnected_sdiff_singleton
    {U : Set ℂ}
    (hUo : IsOpen U) (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) (hAc : IsPreconnected (U ∩ ball ζ ρ))
    (hBc : IsPreconnected (U \ closedBall ζ ρ))
    {K : Set ℂ} (hK : IsClosed K) (hKb : IsBounded K)
    (hγK : f '' (U ∩ sphere ζ ρ) ⊆ K)
    (hKsub : K ⊆ closure (f '' (U ∩ sphere ζ ρ)) ∪ frontier (f '' U))
    {z₀ : ℂ} (hz₀ : z₀ ∈ U ∩ sphere ζ ρ)
    (hKp : IsPreconnected (K \ {f z₀}))
    (hlt : diam K < diam (f '' (U \ closedBall ζ ρ))) :
    f '' (U ∩ ball ζ ρ) ⊆ filledHull K := by
  rcases image_inter_ball_subset_filledHull_or_image_sdiff_closedBall_subset_filledHull
    hUo hρ hf hinj hAc hBc hK hKb hγK hKsub hz₀ hKp with h | h
  · exact h
  · exact absurd (diam_le_diam_of_subset_filledHull hKb h) (not_le.mpr hlt)

/-! ## The frontier route to enclosure -/

section GeneralDomain

variable {U K V : Set ℂ} {p : ℂ}

open Topology

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

end GeneralDomain

end TauCeti
