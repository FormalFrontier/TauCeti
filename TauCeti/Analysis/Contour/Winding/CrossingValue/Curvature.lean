/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.CrossingValue.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# The crossing value of the real winding integrand for a twice-differentiable curve

Hungerbühler–Wasem Proposition 2.3 states that the real winding integrand of a plane curve
`Λ = x + i y` about a point it passes through stays *bounded*: at a crossing parameter `t̃` the
apparently singular quotient `(x ẏ - y ẋ) / (x² + y²)` converges, with limit `½ k_Λ(t̃) |Λ̇(t̃)|`,
half the signed curvature times the speed.

`Contour.tendsto_realWindingIntegrand_at_crossing` already delivers that limit from two Peano
expansions with abstract coefficients `L` (velocity) and `A` (acceleration). This file discharges
those expansions from the differentiability of `γ` alone, and so states the crossing value in the
explicit second-derivative form

`(ẋ ÿ - ẏ ẍ) / (2 (ẋ² + ẏ²))`,   `ẋ + i ẏ = γ' t₀`,  `ẍ + i ÿ = γ'' t₀`.

That explicit expression *is* `½ k_Λ(t₀) |Λ̇(t₀)|`; the roadmap prescribes stating it this way
because Mathlib carries no signed-curvature API for plane curves to cite, so there is no `k_Λ` to
name. The regularity is pinned per part, as the roadmap asks: the crossing value needs the second
derivative at `t₀` (the `C²` half of Prop 2.3), whereas the boundedness that the residue theorem
consumes needs only `C^{1,1}`.

## Main results

* `Contour.tendsto_realWindingIntegrand_at_crossing_of_hasDerivAt_deriv` — the crossing value for a
  curve that is differentiable near `t₀` and whose derivative is differentiable at `t₀`, stated with
  the acceleration `A` supplied by `HasDerivAt (deriv γ) A t₀`.
* `Contour.tendsto_realWindingIntegrand_at_crossing_of_contDiffAt` — the same limit under the
  roadmap's `C²` hypothesis, with the acceleration read off as `deriv (deriv γ) t₀`.
* `Contour.tendsto_realWindingIntegrand_circleMap_crossing` — the value `½` at every point of a
  circle, the smooth-crossing check (`½ · |r|⁻¹ · |r|`) of the formula above.

The second-order chord expansion behind the first result is obtained from Mathlib's mean-value
engine `Convex.isLittleO_pow_succ_real`, the same lemma Mathlib's `taylor_isLittleO` runs on; it is
proved here for the weaker "twice differentiable at `t₀`" hypothesis rather than assumed from `C²`.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), Proposition 2.3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Asymptotics Complex Filter Topology

variable {γ : ℝ → ℂ} {t₀ : ℝ} {A : ℂ}

/-- The second-order chord expansion at `t₀`: if `γ` is differentiable near `t₀` and its derivative
has derivative `A` at `t₀`, then the chord `γ t - γ t₀` differs from its first-order part by
`(t - t₀)² · A / 2` to leading order.

The proof feeds the first-order expansion of `deriv γ` at `t₀` into Mathlib's mean-value estimate
`Convex.isLittleO_pow_succ_real` on a ball around `t₀`. -/
private theorem tendsto_chord_secondOrder
    (hdiff : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ γ t) (hA : HasDerivAt (deriv γ) A t₀) :
    Tendsto (fun t ↦ (γ t - γ t₀ - ((t - t₀ : ℝ) : ℂ) * deriv γ t₀) / ((t - t₀ : ℝ) : ℂ) ^ 2)
      (𝓝[≠] t₀) (𝓝 (A / 2)) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hdiff
  set V : Set ℝ := Metric.ball t₀ δ
  have hVopen : IsOpen V := Metric.isOpen_ball
  have ht₀V : t₀ ∈ V := Metric.mem_ball_self hδ
  set L : ℂ := deriv γ t₀ with hLdef
  -- The second-order remainder and its derivative.
  set F : ℝ → ℂ :=
    fun t ↦ γ t - γ t₀ - ((t - t₀ : ℝ) : ℂ) * L - ((t - t₀ : ℝ) : ℂ) ^ 2 * (A / 2) with hF
  set F' : ℝ → ℂ := fun t ↦ deriv γ t - L - ((t - t₀ : ℝ) : ℂ) * A with hF'
  have hff' : ∀ t ∈ V, HasDerivWithinAt F (F' t) V t := by
    intro t ht
    have hu : HasDerivAt (fun x : ℝ ↦ ((x - t₀ : ℝ) : ℂ)) 1 t := by
      simpa using (((hasDerivAt_id t).sub_const t₀).ofReal_comp)
    have hγt : HasDerivAt γ (deriv γ t) t := (hball (Metric.mem_ball.1 ht)).hasDerivAt
    refine HasDerivAt.hasDerivWithinAt ?_
    refine (((hγt.sub_const (γ t₀)).sub (hu.mul_const L)).sub
      ((hu.pow 2).mul_const (A / 2))).congr_deriv ?_
    simp only [hF']
    push_cast
    ring
  have hFo : F' =o[𝓝[V] t₀] fun t ↦ (t - t₀) ^ 1 := by
    have hlit := hasDerivAt_iff_isLittleO.1 hA
    refine (hlit.mono nhdsWithin_le_nhds).congr' ?_ (Eventually.of_forall fun t ↦ ?_)
    · filter_upwards with t
      simp [hF', hLdef, Complex.real_smul]
    · simp
  have hmain := (convex_ball t₀ δ).isLittleO_pow_succ_real ht₀V hff' hFo
  have hFt₀ : F t₀ = 0 := by simp [hF]
  rw [hFt₀, hVopen.nhdsWithin_eq ht₀V] at hmain
  simp only [sub_zero] at hmain
  -- Move the comparison function to the complex square, then divide. The real square `(t - t₀) ^ 2`
  -- and its complex coercion have the same norm, so comparing norms transfers the estimate.
  have hnorm : ∀ t : ℝ, ‖(t - t₀) ^ (1 + 1)‖ = ‖((t - t₀ : ℝ) : ℂ) ^ 2‖ := fun t ↦ by
    rw [norm_pow, norm_pow, Complex.norm_real]
  have hcx : F =o[𝓝 t₀] fun t ↦ ((t - t₀ : ℝ) : ℂ) ^ 2 := by
    rw [← isLittleO_norm_right] at hmain ⊢
    exact hmain.congr' EventuallyEq.rfl (Eventually.of_forall hnorm)
  have hzero := (hcx.tendsto_div_nhds_zero).mono_left (nhdsWithin_le_nhds (s := {t₀}ᶜ))
  have hshift := hzero.add_const (A / 2)
  rw [zero_add] at hshift
  refine hshift.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hτ : ((t - t₀ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr ht
  field_simp [hF]
  ring

/-- **Hungerbühler–Wasem Proposition 2.3, crossing value, in second-derivative form.** Let `γ` be
differentiable near `t₀`, with `deriv γ` differentiable at `t₀` with derivative `A`, and let the
velocity `deriv γ t₀` be nonzero (the immersion condition). At the crossing `γ t₀ = z₀` the real
winding integrand converges,

`(x ẏ - y ẋ) / (x² + y²) → (ẋ ÿ - ẏ ẍ) / (2 (ẋ² + ẏ²))`,

with `x + i y = γ - z₀`, `ẋ + i ẏ = deriv γ t₀` and `ẍ + i ÿ = A`. The limit is
`½ k_γ(t₀) |γ̇(t₀)|`, half the signed curvature times the speed, written out explicitly because
Mathlib has no signed-curvature API to cite. -/
theorem tendsto_realWindingIntegrand_at_crossing_of_hasDerivAt_deriv {z₀ : ℂ} (hcross : γ t₀ = z₀)
    (hL : deriv γ t₀ ≠ 0) (hdiff : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ γ t)
    (hA : HasDerivAt (deriv γ) A t₀) :
    Tendsto (fun t ↦ realWindingIntegrand (γ t - z₀) (deriv γ t)) (𝓝[≠] t₀)
      (𝓝 (((deriv γ t₀).re * A.im - (deriv γ t₀).im * A.re) /
        (2 * ((deriv γ t₀).re ^ 2 + (deriv γ t₀).im ^ 2)))) := by
  have hden : (2 : ℝ) * ((deriv γ t₀).re ^ 2 + (deriv γ t₀).im ^ 2)
      = 2 * Complex.normSq (deriv γ t₀) := by
    rw [Complex.normSq_apply]; ring
  rw [hden]
  refine tendsto_realWindingIntegrand_at_crossing (t := fun t : ℝ ↦ t) hL
    (tendsto_id.mono_left nhdsWithin_le_nhds) hcross ?_ ?_ self_mem_nhdsWithin
  · -- The normalized second-order chord expansion.
    subst hcross
    refine (tendsto_chord_secondOrder hdiff hA).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hτ : ((t - t₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr ht
    field_simp
  · -- The first-order velocity expansion is the slope form of `hA`.
    refine (hasDerivAt_iff_tendsto_slope.1 hA).congr fun t ↦ ?_
    rw [slope_def_module, Complex.real_smul, Complex.ofReal_inv, ← div_eq_inv_mul,
      Complex.ofReal_sub]

/-- **Hungerbühler–Wasem Proposition 2.3, crossing value, under the roadmap's `C²` hypothesis.**
For a curve that is `C²` at the crossing parameter `t₀` with nonvanishing velocity there, the real
winding integrand about `z₀ = γ t₀` tends to `(ẋ ÿ - ẏ ẍ) / (2 (ẋ² + ẏ²))`, where `ẋ + i ẏ` and
`ẍ + i ÿ` are the first and second derivatives of `γ` at `t₀`. -/
theorem tendsto_realWindingIntegrand_at_crossing_of_contDiffAt {z₀ : ℂ}
    (hγ : ContDiffAt ℝ 2 γ t₀) (hcross : γ t₀ = z₀) (hL : deriv γ t₀ ≠ 0) :
    Tendsto (fun t ↦ realWindingIntegrand (γ t - z₀) (deriv γ t)) (𝓝[≠] t₀)
      (𝓝 (((deriv γ t₀).re * (deriv (deriv γ) t₀).im
            - (deriv γ t₀).im * (deriv (deriv γ) t₀).re) /
        (2 * ((deriv γ t₀).re ^ 2 + (deriv γ t₀).im ^ 2)))) := by
  obtain ⟨u, hu, hcd⟩ := hγ.contDiffOn le_rfl (by simp)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.1 hu
  have hVopen : IsOpen (Metric.ball t₀ δ) := Metric.isOpen_ball
  have ht₀ : t₀ ∈ Metric.ball t₀ δ := Metric.mem_ball_self hδ
  have hcdV : ContDiffOn ℝ 2 γ (Metric.ball t₀ δ) := hcd.mono hsub
  have hdiff : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ γ t :=
    eventually_of_mem (hVopen.mem_nhds ht₀) fun t ht ↦
      (hcdV.differentiableOn (by norm_num) t ht).differentiableAt (hVopen.mem_nhds ht)
  have hA : HasDerivAt (deriv γ) (deriv (deriv γ) t₀) t₀ :=
    ((hcdV.deriv_of_isOpen (m := 1) hVopen (by norm_num)).differentiableOn_one t₀
      ht₀).differentiableAt (hVopen.mem_nhds ht₀) |>.hasDerivAt
  exact tendsto_realWindingIntegrand_at_crossing_of_hasDerivAt_deriv hcross hL hdiff hA

/-- **The smooth-crossing check.** At every parameter of a circle of nonzero radius, the real
winding integrand about the point of the circle reached there tends to `½`: the circle has signed
curvature `|r|⁻¹` and `circleMap c r` has speed `|r|` (a negative `r` traverses the circle of radius
`|r|` counterclockwise too, only from the antipodal parameter), so `½ k |Λ̇| = ½`. This is the value
the roadmap's smooth crossing (opening angle `π`) carries, computed from
`tendsto_realWindingIntegrand_at_crossing_of_contDiffAt` rather than assumed. -/
theorem tendsto_realWindingIntegrand_circleMap_crossing {c : ℂ} {r : ℝ} (hr : r ≠ 0) (t₀ : ℝ) :
    Tendsto (fun t ↦ realWindingIntegrand (circleMap c r t - circleMap c r t₀)
        (deriv (circleMap c r) t)) (𝓝[≠] t₀) (𝓝 (1 / 2)) := by
  have hsecond : deriv (deriv (circleMap c r)) t₀ = -circleMap 0 r t₀ := by
    have hfun : deriv (circleMap c r) = fun θ ↦ circleMap 0 r θ * Complex.I :=
      funext (deriv_circleMap c r)
    rw [hfun, deriv_mul_const ((differentiable_circleMap 0 r) t₀), deriv_circleMap, mul_assoc,
      Complex.I_mul_I, mul_neg_one]
  have key := tendsto_realWindingIntegrand_at_crossing_of_contDiffAt (γ := circleMap c r) (t₀ := t₀)
    (z₀ := circleMap c r t₀) (contDiff_circleMap c r).contDiffAt rfl (deriv_circleMap_ne_zero hr)
  rw [hsecond] at key
  convert key using 2
  -- The velocity is `z * i` and the acceleration is `-z` for `z = circleMap 0 r t₀`, so the
  -- quotient is `‖z‖² / (2‖z‖²) = ½`.
  rw [deriv_circleMap]
  set z : ℂ := circleMap 0 r t₀ with hz
  have hsq : z.re ^ 2 + z.im ^ 2 = r ^ 2 := by
    have h1 : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq _
    rw [hz, norm_circleMap_zero, sq_abs] at h1
    rw [← h1, Complex.normSq_apply]; ring
  have hne : z.re ^ 2 + z.im ^ 2 ≠ 0 := by rw [hsq]; exact pow_ne_zero 2 hr
  have hnum : (z * Complex.I).re * (-z).im - (z * Complex.I).im * (-z).re
      = z.re ^ 2 + z.im ^ 2 := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_re,
      Complex.neg_im]
    ring
  have hden : (2 : ℝ) * ((z * Complex.I).re ^ 2 + (z * Complex.I).im ^ 2)
      = 2 * (z.re ^ 2 + z.im ^ 2) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  rw [hnum, hden, eq_div_iff (mul_ne_zero two_ne_zero hne)]
  ring

end TauCeti.Contour

end
