/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.PwC1ImmersionOn
public import TauCeti.Analysis.Contour.RegularityConditions
import TauCeti.Analysis.Contour.Crossing.Finiteness
public import TauCeti.Analysis.Contour.Winding.Number.Circle
public import TauCeti.Analysis.Contour.Winding.Number.Concat
public import TauCeti.Analysis.Contour.Winding.Number.Reparam
public import TauCeti.Analysis.Contour.Winding.Number.Segment

/-!
# The half-disc boundary contour

For `0 < R`, the boundary of the upper half-disc of radius `R` about the origin, traversed
counterclockwise on `[-R, R + π]`: the diameter along the real axis from `-R` to `R`, followed by
the semicircular arc from `R` back to `-R`, the arc carrying its angle in `t - R`.

Its distinguishing feature is that it passes **through** the origin rather than detouring around
it, so the origin is an on-curve point and the generalized winding number there is `½` — the value
strictly between the exterior `0` and the interior `1`:

* the diameter contributes `0`: the index integrand `1 / t` is odd, so its principal value over
  the symmetric interval vanishes (`windingNumber_eq_zero_segment`);
* the arc contributes `½`: it is a half-circle about its own centre, so its winding is its angular
  extent `π / 2π` (`windingNumber_circleMap_center_eq_half`).

That `½` is exactly the hypothesis of the Hungerbühler–Wasem half-residue theorem
`hasCauchyPV_half_residue`, which is why this contour is the one HW's motivating example uses: a
Cauchy principal value along the real axis with a simple pole at the origin, where the classical
residue theorem does not apply because the pole lies *on* the contour.

## Main results

* `TauCeti.Contour.halfDiscBoundary` — the contour, with `halfDiscBoundary_of_le` and
  `halfDiscBoundary_of_lt` evaluating its two branches and `halfDiscBoundary_left`,
  `halfDiscBoundary_right` its endpoints (equal, so the contour is closed).
* `TauCeti.Contour.continuous_halfDiscBoundary` — the two branches agree at the junction, so the
  contour is continuous.
* `TauCeti.Contour.isPwC1ImmersionOn_halfDiscBoundary` — it is a piecewise-`C¹` immersion, with
  the single breakpoint `R`; this is the regularity hypothesis of the Hungerbühler–Wasem theorems.
* `TauCeti.Contour.windingNumber_halfDiscBoundary` — its generalized winding number about the
  origin is `½`.
* `TauCeti.Contour.halfDiscBoundary_eq_zero_iff` — the contour meets the origin exactly once,
  at `t = 0`.
* `TauCeti.Contour.deriv_halfDiscBoundary_of_lt_radius` and
  `TauCeti.Contour.deriv_halfDiscBoundary_of_lt` — before the junction the derivative is the real
  inclusion's, beyond it the circle map's at the shifted parameter.
* `TauCeti.Contour.integral_halfDiscBoundary_arc` — the `[R, R + π]` piece of the contour integral
  is the `circleMap 0 R` integral over `[0, π]`; for `0 < R` that is the upper semicircle, the
  form Jordan's lemma bounds.
* `TauCeti.Contour.flatOfOrder_halfDiscBoundary` — both one-sided branches at the origin lie on
  the real line, so the contour is flat there to every order.
* `TauCeti.Contour.conditionAprime_halfDiscBoundary` — Hungerbühler–Wasem condition (A′) at the
  origin, for any integrand.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997, Thm 3.3.
-/

public section

noncomputable section

open Complex Set

namespace TauCeti.Contour

variable {R : ℝ}

/-- **The half-disc boundary contour.** On `[-R, R + π]`: the diameter `t ↦ t` for `t ≤ R`, then
the semicircular arc `t ↦ R e^{i(t-R)}` from `R` back to `-R`. -/
def halfDiscBoundary (R : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ R then (t : ℂ) else circleMap 0 R (t - R)

@[simp]
theorem halfDiscBoundary_of_le {t : ℝ} (h : t ≤ R) : halfDiscBoundary R t = (t : ℂ) :=
  if_pos h

@[simp]
theorem halfDiscBoundary_of_lt {t : ℝ} (h : R < t) :
    halfDiscBoundary R t = circleMap 0 R (t - R) :=
  if_neg (not_le.mpr h)

/-- The contour starts at `-R`. -/
-- Not `@[simp]`: with `halfDiscBoundary_of_le` in the simp set, `simp` already proves this
-- (`neg_le_self_iff` discharges `-R ≤ R`), and `simpNF` rejects the redundant annotation.
theorem halfDiscBoundary_left (hR : 0 ≤ R) : halfDiscBoundary R (-R) = (-R : ℝ) :=
  halfDiscBoundary_of_le (by linarith)

/-- The contour ends at `-R`, so it is closed. -/
@[simp]
theorem halfDiscBoundary_right (R : ℝ) :
    halfDiscBoundary R (R + Real.pi) = (-R : ℝ) := by
  rw [halfDiscBoundary_of_lt (by linarith [Real.pi_pos])]
  simp [circleMap, Complex.exp_pi_mul_I]

/-- On the diameter's parameter interval the contour is the real segment. -/
theorem eqOn_halfDiscBoundary_segment (hR : 0 ≤ R) :
    EqOn (fun t : ℝ => (1 : ℂ) * (t : ℂ) + 0) (halfDiscBoundary R) (uIoo (-R) R) := by
  intro t ht
  have h2 : t < max (-R) R := (Set.mem_Ioo.mp ht).2
  rw [max_eq_right (by linarith : (-R : ℝ) ≤ R)] at h2
  simp [halfDiscBoundary_of_le h2.le]

/-- **The derivative on the open diameter.** Strictly before the junction the half-disc boundary
is the real inclusion on a whole neighbourhood, so the two derivatives agree. -/
@[simp]
theorem deriv_halfDiscBoundary_of_lt_radius {R t : ℝ} (h : t < R) :
    deriv (halfDiscBoundary R) t = deriv (fun s : ℝ => (s : ℂ)) t := by
  have hev : halfDiscBoundary R =ᶠ[nhds t] fun s : ℝ => (s : ℂ) := by
    filter_upwards [Iio_mem_nhds h] with s hs
    exact halfDiscBoundary_of_le hs.le
  exact hev.deriv_eq

/-- **The derivative on the open arc.** Strictly beyond the junction the half-disc boundary
coincides with the shifted circle map on a whole neighbourhood, so its derivative is the circle
map's, evaluated at the shifted parameter. (At the junction `t = R` itself the contour has a
corner, and no such identity is claimed.) -/
@[simp]
theorem deriv_halfDiscBoundary_of_lt {R t : ℝ} (h : R < t) :
    deriv (halfDiscBoundary R) t = deriv (circleMap 0 R) (t - R) := by
  have hev : halfDiscBoundary R =ᶠ[nhds t] (circleMap 0 R ∘ fun s : ℝ => s - R) := by
    filter_upwards [Ioi_mem_nhds h] with s hs
    exact halfDiscBoundary_of_lt hs
  rw [hev.deriv_eq]
  have hsub : HasDerivAt (fun s : ℝ => s - R) 1 t := by
    simpa using (hasDerivAt_id t).sub_const R
  have hd : HasDerivAt (circleMap 0 R ∘ fun s : ℝ => s - R)
      (deriv (circleMap 0 R) (t - R)) t := by
    simpa [deriv_circleMap] using (hasDerivAt_circleMap 0 R (t - R)).scomp t hsub
  exact hd.deriv

/-- **The arc piece of the contour integral is the circle-map integral.** Beyond the junction the
half-disc boundary is the circle map shifted by `R`, so translating the parameter identifies the
`[R, R + π]` piece of `∮_γ f` with the integral of `circleMap 0 R` over `[0, π]`. The junction
`t = R` itself, where the contour has a corner, is a single point and does not affect the integral.

The identity holds for every `R`. For `0 < R` the right-hand side is the *upper* semicircle
traversed counterclockwise — the form Jordan's lemma bounds; for `R < 0` the same parametrization
traces the lower semicircle instead, and `R = 0` is degenerate, `circleMap 0 0` being the constant
path at the origin. -/
theorem integral_halfDiscBoundary_arc (f : ℂ → ℂ) (R : ℝ) :
    (∫ t in R..(R + Real.pi), f (halfDiscBoundary R t) * deriv (halfDiscBoundary R) t)
      = ∫ θ in (0 : ℝ)..Real.pi, f (circleMap 0 R θ) * deriv (circleMap 0 R) θ := by
  have hshift : (∫ t in R..(R + Real.pi),
      f (circleMap 0 R (t - R)) * deriv (circleMap 0 R) (t - R))
      = ∫ θ in (0 : ℝ)..Real.pi, f (circleMap 0 R θ) * deriv (circleMap 0 R) θ := by
    have h := intervalIntegral.integral_comp_sub_right
      (fun θ => f (circleMap 0 R θ) * deriv (circleMap 0 R) θ) (a := R) (b := R + Real.pi) R
    simpa using h
  rw [← hshift]
  refine intervalIntegral.integral_congr_ae' (Filter.Eventually.of_forall fun t ht => ?_)
    (Filter.Eventually.of_forall fun t ht => ?_)
  · rw [halfDiscBoundary_of_lt ht.1, deriv_halfDiscBoundary_of_lt ht.1]
  · exact absurd (ht.1.trans_le ht.2) (by simp [Real.pi_pos.le])

/-- On the arc's parameter interval — including both endpoints, where the two agree — the contour
is the circle reparametrized by `t ↦ t - R`. -/
theorem eqOn_halfDiscBoundary_arc (R : ℝ) :
    EqOn (circleMap 0 R ∘ fun s : ℝ => s - R) (halfDiscBoundary R) (uIcc R (R + Real.pi)) := by
  intro t ht
  rw [uIcc_of_le (by linarith [Real.pi_pos] : R ≤ R + Real.pi)] at ht
  rcases eq_or_lt_of_le (mem_Icc.mp ht).1 with h | h
  · rw [← h, halfDiscBoundary_of_le le_rfl]
    simp [circleMap]
  · rw [halfDiscBoundary_of_lt h]
    rfl

/-- **The half-disc boundary is continuous**, the two branches agreeing at the junction `t = R`
(where `circleMap 0 R 0 = R`). -/
theorem continuous_halfDiscBoundary (R : ℝ) : Continuous (halfDiscBoundary R) := by
  refine Continuous.if_le (by fun_prop)
    ((continuous_circleMap 0 R).comp (continuous_id.sub continuous_const))
    continuous_id continuous_const (fun x hx => ?_)
  simp [hx, circleMap]

/-- On a subinterval left of the junction the contour is the real inclusion. -/
private theorem eqOn_left_piece {c d : ℝ} (hd : d ≤ R) :
    EqOn (halfDiscBoundary R) (fun t : ℝ => (t : ℂ)) (Icc c d) :=
  fun _ ht => halfDiscBoundary_of_le ((mem_Icc.mp ht).2.trans hd)

/-- On a subinterval right of the junction the contour is the shifted circle. -/
private theorem eqOn_right_piece {c d : ℝ} (hc : R ≤ c) :
    EqOn (halfDiscBoundary R) (circleMap 0 R ∘ fun s : ℝ => s - R) (Icc c d) := by
  intro t ht
  rcases eq_or_lt_of_le (hc.trans (mem_Icc.mp ht).1) with h | h
  · rw [← h, halfDiscBoundary_of_le le_rfl]
    simp [circleMap]
  · rw [halfDiscBoundary_of_lt h]
    rfl

/-- **The half-disc boundary is a piecewise-`C¹` immersion**, with the single breakpoint `R` where
the diameter meets the arc. Off that breakpoint each piece is one of the two smooth branches: the
real inclusion, of derivative `1`, or the shifted circle, of derivative `R e^{i(t-R)} · i`; both
are nonzero for `0 < R`, so the tangent never vanishes. -/
theorem isPwC1ImmersionOn_halfDiscBoundary (hR : 0 < R) :
    IsPwC1ImmersionOn (halfDiscBoundary R) (-R) (R + Real.pi) := by
  have hpi := Real.pi_pos
  refine IsPwC1ImmersionOn.of_breakpoints (continuous_halfDiscBoundary R).continuousOn {R}
    (by
      rw [min_eq_left (by linarith : (-R : ℝ) ≤ R + Real.pi),
        max_eq_right (by linarith : (-R : ℝ) ≤ R + Real.pi)]
      simpa using ⟨by linarith, by linarith⟩)
    fun c d hcd hsub hdisj => ?_
  have huniq : UniqueDiffOn ℝ (Icc c d) := uniqueDiffOn_Icc hcd
  -- Disjointness from the breakpoint puts the piece entirely on one side of `R`.
  have hside : d ≤ R ∨ R ≤ c := by
    by_contra hcon
    push Not at hcon
    exact Set.disjoint_left.mp hdisj (by simp) (mem_Ioo.mpr ⟨hcon.2, hcon.1⟩)
  rcases hside with hd | hc
  · refine ⟨(?_ : ContDiffOn ℝ 1 (fun t : ℝ => (t : ℂ)) (Icc c d)).congr
      (eqOn_left_piece hd), fun t ht => ?_⟩
    · exact (Complex.ofRealCLM.contDiff (n := 1)).contDiffOn
    · have hd1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
        simpa using (hasDerivAt_id' (x := t)).ofReal_comp
      rw [derivWithin_congr (eqOn_left_piece hd) (eqOn_left_piece hd ht),
        hd1.hasDerivWithinAt.derivWithin (huniq t ht)]
      norm_num
  · refine ⟨(?_ : ContDiffOn ℝ 1 (circleMap 0 R ∘ fun s : ℝ => s - R) (Icc c d)).congr
      (eqOn_right_piece hc), fun t ht => ?_⟩
    · exact ((contDiff_circleMap 0 R).comp (contDiff_id.sub contDiff_const)).contDiffOn
    · have hd2 : HasDerivAt (circleMap 0 R ∘ fun s : ℝ => s - R)
          (circleMap 0 R (t - R) * Complex.I) t := by
        simpa using (hasDerivAt_circleMap 0 R (t - R)).scomp t
          ((hasDerivAt_id' (x := t)).sub_const R)
      rw [derivWithin_congr (eqOn_right_piece hc) (eqOn_right_piece hc ht),
        hd2.hasDerivWithinAt.derivWithin (huniq t ht)]
      exact mul_ne_zero (circleMap_ne_center (c := 0) (θ := t - R) hR.ne') Complex.I_ne_zero

/-- The index principal value of the reparametrized arc about the origin exists: for `R ≠ 0` the
arc misses the origin, so the truncation is vacuous and the ordinary index integral converges;
at `R = 0` the arc is constant at the origin and every truncated integrand vanishes. Either way no
positivity hypothesis is needed. -/
private theorem cauchyPVExistsAt_arc :
    CauchyPVExistsAt (circleMap 0 R ∘ fun s : ℝ => s - R) R (R + Real.pi)
      (fun z => (z - 0)⁻¹) 0 := by
  have h : (fun s : ℝ => s - R) = fun s : ℝ => 1 * s + (-R) := by funext s; ring
  rw [h]
  exact cauchyPVExistsAt_circleMap_comp_affine 1 (-R) R (R + Real.pi)

/-- The reparametrized arc in the `r · t + s` shape `windingNumber_comp_mul_add` expects. -/
private theorem arc_eq_comp_mul_add (R : ℝ) :
    (circleMap 0 R ∘ fun s : ℝ => s - R) = circleMap 0 R ∘ fun s : ℝ => 1 * s + (-R) := by
  congr 1
  funext s
  ring

/-- The arc contributes `½`: it is a half-circle about its own centre. -/
private theorem windingNumber_arc (hR : 0 < R) :
    windingNumber (circleMap 0 R ∘ fun s : ℝ => s - R) R (R + Real.pi) 0 = 1 / 2 := by
  rw [arc_eq_comp_mul_add, windingNumber_comp_mul_add
    (fun u _ => (differentiable_circleMap 0 R) u)
    (by
      have h : deriv (circleMap 0 R) = fun θ => circleMap 0 R θ * Complex.I :=
        funext (deriv_circleMap 0 R)
      rw [h]
      exact ((continuous_circleMap 0 R).mul continuous_const).continuousOn)
    (fun u _ => circleMap_ne_center hR.ne')]
  simpa using windingNumber_circleMap_center_eq_half (c := 0) hR.ne'

/-- **The half-disc boundary has winding number `½` about the origin.** The diameter through the
origin contributes `0` and the semicircular arc about it contributes `½`. -/
theorem windingNumber_halfDiscBoundary (hR : 0 < R) :
    windingNumber (halfDiscBoundary R) (-R) (R + Real.pi) 0 = 1 / 2 := by
  have hpv_seg : CauchyPVExistsAt (halfDiscBoundary R) (-R) R (fun z => (z - 0)⁻¹) 0 :=
    (cauchyPVExistsAt_inv_sub_segment 1 0 R).congr_curve (eqOn_halfDiscBoundary_segment hR.le)
  have hpv_arc : CauchyPVExistsAt (halfDiscBoundary R) R (R + Real.pi) (fun z => (z - 0)⁻¹) 0 :=
    cauchyPVExistsAt_arc.congr_curve
      ((eqOn_halfDiscBoundary_arc R).mono (uIoo_subset_uIcc_self))
  have hseg : windingNumber (halfDiscBoundary R) (-R) R 0 = 0 := by
    rw [← windingNumber_congr_curve (eqOn_halfDiscBoundary_segment hR.le)]
    exact windingNumber_eq_zero_segment 1 0 R
  have harc : windingNumber (halfDiscBoundary R) R (R + Real.pi) 0 = 1 / 2 := by
    rw [← windingNumber_congr_curve
      ((eqOn_halfDiscBoundary_arc R).mono uIoo_subset_uIcc_self)]
    exact windingNumber_arc hR
  rw [windingNumber_concat hpv_seg hpv_arc, hseg, harc, zero_add]

/-- **The half-disc boundary meets the origin exactly once**, at `t = 0`: on the diameter
`γ t = t` vanishes only there, and the arc stays at distance `|R|` from the origin. -/
@[simp]
theorem halfDiscBoundary_eq_zero_iff (hR : 0 < R) {t : ℝ} :
    halfDiscBoundary R t = 0 ↔ t = 0 := by
  constructor
  · intro h
    by_cases hle : t ≤ R
    · rw [halfDiscBoundary_of_le hle] at h
      exact_mod_cast h
    · rw [halfDiscBoundary_of_lt (not_le.mp hle)] at h
      exact absurd h (circleMap_ne_center hR.ne')
  · rintro rfl
    simpa using halfDiscBoundary_of_le hR.le

/-- **The half-disc boundary is flat to every order at the origin.** With tangent direction
`v = 1` the perpendicular deviation `|Im (γ t - γ 0)|` vanishes *identically* near `t = 0`, which
is `o` of anything. For `R > 0` that is because the contour is locally the real diameter; for the
degenerate radius `R = 0` the arc collapses to the origin, so both one-sided branches still lie on
the real line. -/
theorem flatOfOrder_halfDiscBoundary (hR : 0 ≤ R) (n : ℕ) :
    FlatOfOrder (halfDiscBoundary R) 0 n := by
  have hzero : ∀ t : ℝ, t ≤ R →
      ((halfDiscBoundary R t - halfDiscBoundary R 0) * star (1 : ℂ)).im = 0 := by
    intro t ht
    rw [halfDiscBoundary_of_le ht, halfDiscBoundary_of_le hR]
    simp
  rcases eq_or_lt_of_le hR with rfl | hR'
  · -- Degenerate radius: the arc collapses to the origin, so the deviation vanishes everywhere.
    have hall : ∀ t : ℝ, ((halfDiscBoundary 0 t - halfDiscBoundary 0 0) * star (1 : ℂ)).im = 0 := by
      intro t
      rcases le_or_gt t 0 with h | h
      · exact hzero t h
      · rw [halfDiscBoundary_of_lt h, halfDiscBoundary_of_le le_rfl]
        simp [circleMap]
    exact flatOfOrder_of_eventually_collinear one_ne_zero one_ne_zero n
      (Filter.Eventually.of_forall hall) (Filter.Eventually.of_forall hall)
  · refine flatOfOrder_of_eventually_collinear one_ne_zero one_ne_zero n ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT hR'] with t ht
      exact hzero t (mem_Ioo.mp ht).2.le
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact hzero t (le_trans (le_of_lt ht) hR)

/-- **Condition (A′) holds for the half-disc boundary at the origin**, for any integrand. The
origin is met exactly once, the contour is flat there to every order (it is locally the real
diameter), and the basepoint `γ(-R) = -R` is not the origin, so that clause is vacuous. -/
theorem conditionAprime_halfDiscBoundary (hR : 0 < R) (f : ℂ → ℂ) :
    ConditionAprime (halfDiscBoundary R) (-R) (R + Real.pi) f {0} := by
  have hpi := Real.pi_pos
  have hmin : min (-R) (R + Real.pi) = -R := min_eq_left (by linarith)
  refine ⟨fun s hs => ?_, fun t₀ _ hmem n _ _ => ?_, fun hbase => ?_⟩
  · rw [Finset.mem_singleton.mp hs]
    exact (isPwC1ImmersionOn_halfDiscBoundary hR).finite_crossings
  · have ht₀ : t₀ = 0 := (halfDiscBoundary_eq_zero_iff hR).mp (by simpa using hmem)
    subst ht₀
    exact flatOfOrder_halfDiscBoundary hR.le n
  · exfalso
    rw [hmin, halfDiscBoundary_of_le (by linarith : (-R : ℝ) ≤ R)] at hbase
    have : (-R : ℝ) = 0 := by
      exact_mod_cast Complex.ofReal_eq_zero.mp (by simpa using hbase)
    linarith

end TauCeti.Contour

end

end
