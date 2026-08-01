/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Curve.Reparam
public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The generalized winding number of a circle: `1` at the centre, `0` outside

For the counterclockwise circle `circleMap c R` traversed over `[0, 2π]`, this file evaluates the
generalized winding number `TauCeti.Contour.windingNumber` (Hungerbühler–Wasem Def 2.1) at two kinds
of points:

* at every **interior** point `w` — one with `dist w c < R` — the winding number is `1`
  (`windingNumber_circleMap_eq_one_of_dist_lt`), in particular at the **centre** `c`
  (`windingNumber_circleMap_center_eq_one`), and
* at every **exterior** point `w` — one with `R < dist w c` — it is `0`
  (`windingNumber_circleMap_eq_zero_of_lt_dist`).

Together these are the roadmap's `n_c(circle) = 1` normalization and its companion "`n` is `0`
outside" (`ContourIntegration/README.md`, the worked examples). They upgrade the raw-index-integral
raw index-integral value `windingNumber_circle` to statements about the `windingNumber`
*definition*, connecting the principal-value packaging to the elementary circle computation and to
Mathlib's disc Cauchy theory.

The exterior value rests on a fact Mathlib records as missing: the Cauchy-kernel integral
`∮_{C(c,R)} dz/(z − w)` for `w` *outside* the closed disc is not among the explicit
`circleIntegral.integral_sub_*` formulas (its docstring notes the case `|w − c| > R` is deferred to
Cauchy's theorem). We supply it here as `circleIntegral_sub_inv_eq_zero_of_lt_dist`, obtained from
`DiffContOnCl.circleIntegral_eq_zero`: for `w` off the closed disc, `z ↦ (z − w)⁻¹` is holomorphic
across the whole disc, so its circle integral vanishes.

## Main results

* `TauCeti.Contour.circleIntegral_sub_inv_eq_zero_of_lt_dist` — the exterior Cauchy-kernel circle
  integral `∮_{C(c,R)} (z − w)⁻¹ = 0` for `R < dist w c`.
* `TauCeti.Contour.windingNumber_circleMap_eq_circleIntegral` — off the circle, the generalized
  winding number is `(2πi)⁻¹` times the ordinary Cauchy-kernel circle integral.
* `TauCeti.Contour.windingNumber_circleMap_eq_one_of_dist_lt` — `n_w(circle) = 1` for any `w` inside
  the disc.
* `TauCeti.Contour.indexIntegral_arc_interval` and `TauCeti.Contour.indexIntegral_arc` — the
  normalized index integral of a circular arc about its centre, `(b − a) / 2π` and `α / 2π`, with
  the specialization `windingNumber_circle` (the full circle, `1`). The two values the valence
  formula names by their points, `windingNumber_at_i` and `windingNumber_at_rho`, are in
  `ModelSector/Winding.lean`.
* `TauCeti.Contour.cauchyPVExistsAt_circleMap_comp_affine` — the index principal value of an
  affinely reparametrised circle exists.
* `TauCeti.Contour.windingNumber_circleMap_center` — an arc about its own centre has winding
  `(b − a) / 2π`, its angular extent, with the two specializations
  `TauCeti.Contour.windingNumber_circleMap_center_eq_one` (`n_c(circle) = 1`, over `[0, 2π]`) and
  `TauCeti.Contour.windingNumber_circleMap_center_eq_half` (`n_c(semicircle) = ½`, over `[0, π]`).
* `TauCeti.Contour.windingNumber_circleMap_eq_zero_of_lt_dist` — `n_w(circle) = 0` for `w` outside
  the disc.

This is a Layer-1 acceptance criterion of the Hungerbühler–Wasem generalized residue theorem
(HW Thm 3.3).

## Provenance

The arc index-integral material (`indexIntegral_arc_interval`, `indexIntegral_arc` and their
specialization `windingNumber_circle`) was
migrated and adapted from the AINTLIB `LeanModularForms` project
(`ForMathlib/HungerbuhlerWasem/Crossing.lean`), specialised to the raw-function
(`γ : ℝ → ℂ` on `[a, b]`) design of the contour-integration roadmap.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Complex Metric

namespace TauCeti.Contour

/-- **The circular-arc index integral** (Hungerbühler–Wasem (2.4)), on an arbitrary angular
interval. For the circular arc `γ θ = z₀ + r·e^{iθ}` about its centre `z₀`, traversed over `[a, b]`,
the normalized index integral is the signed angular extent over `2π`:
`(2πi)⁻¹ ∫_a^b (γ̇ / (γ − z₀)) dθ = (b − a) / 2π`. The centre is off the arc, so the integrand
`γ̇ / (γ − z₀)` is constantly `i` and the value is elementary. This is the general
arbitrary-interval statement; `indexIntegral_arc` (`a = 0`) and `windingNumber_circle` are
derived from it. -/
theorem indexIntegral_arc_interval {z₀ : ℂ} {r : ℝ} (hr : r ≠ 0) (a b : ℝ) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ in a..b, deriv (circleMap z₀ r) θ / (circleMap z₀ r θ - z₀)
      = ((b - a : ℝ) : ℂ) / (2 * (Real.pi : ℂ)) := by
  have hint : ∀ θ : ℝ, deriv (circleMap z₀ r) θ / (circleMap z₀ r θ - z₀) = Complex.I := by
    intro θ
    have hne : circleMap (0 : ℂ) r θ ≠ 0 := circleMap_ne_center hr
    rw [deriv_circleMap, circleMap_sub_center, mul_comm (circleMap 0 r θ) Complex.I,
      mul_div_assoc, div_self hne, mul_one]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp_rw [hint]
  rw [intervalIntegral.integral_const, Complex.real_smul]
  field_simp

@[deprecated (since := "2026-07-29")]
alias windingNumber_modelSector_interval := indexIntegral_arc_interval

/-- **The normalized index integral of a circular arc** (Hungerbühler–Wasem (2.4)). The arc
`γ θ = z₀ + r·e^{iθ}` about its centre `z₀`, traversed over `[0, α]`, has normalized index integral
`(2πi)⁻¹ ∫_0^α (γ̇ / (γ − z₀)) dθ = α / 2π`: an arc of *signed* angular extent `α` contributes
generalized winding number `α/2π`. For `0 ≤ α` the traversal is counterclockwise; for `α < 0`
the interval `[0, α]` is reversed, the arc runs clockwise, and the contribution is negative.

The `α = 2π` specialization is `windingNumber_circle`; the `α = π` and `α = π/3` values the valence
formula names by their points are `windingNumber_at_i` and `windingNumber_at_rho`, in
`ModelSector/Winding.lean`.

`ContourIntegration/Suggested.lean` lists this statement as `windingNumber_modelSector`, which is
retained below as a deprecated alias. The closed model-sector curve — a different statement — is
`TauCeti.Contour.windingNumber_closedModelSector` in `ModelSector/Closed.lean`. -/
theorem indexIntegral_arc {z₀ : ℂ} {r : ℝ} (hr : r ≠ 0) (α : ℝ) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ in (0 : ℝ)..α, deriv (circleMap z₀ r) θ / (circleMap z₀ r θ - z₀)
      = (α : ℂ) / (2 * (Real.pi : ℂ)) := by
  rw [indexIntegral_arc_interval hr]
  push_cast
  ring

@[deprecated (since := "2026-07-29")]
alias windingNumber_modelSector := indexIntegral_arc

/-- **A full circle (`[0, 2π]`) has winding number `1`** — the closed-curve normalization, the
`[0, 2π]` specialization of `indexIntegral_arc` (`2π / 2π = 1`). Its value also follows from
Mathlib's `circleIntegral.integral_sub_center_inv`; this is the raw-index-integral form of that
normalization used as a Layer-1 target. -/
theorem windingNumber_circle {c : ℂ} {r : ℝ} (hr : r ≠ 0) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (circleMap c r) θ / (circleMap c r θ - c)
      = 1 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [indexIntegral_arc hr]
  push_cast
  field_simp


/-- **The exterior Cauchy-kernel circle integral vanishes.** For a point `w` strictly outside the
closed disc of radius `R ≥ 0` about `c` (`R < dist w c`), the integral of the Cauchy kernel
`(z − w)⁻¹` around the circle is `0`. On the closed disc the kernel is holomorphic (its only
singularity `w` lies outside), so `DiffContOnCl.circleIntegral_eq_zero` applies. Mathlib's
`circleIntegral.integral_sub_inv_of_mem_ball` covers the *interior* case (value `2πi`) but leaves
this exterior case to Cauchy's theorem, which is exactly this argument. -/
theorem circleIntegral_sub_inv_eq_zero_of_lt_dist {c w : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hw : R < dist w c) : (∮ z in C(c, R), (z - w)⁻¹) = 0 := by
  have hdiff : DifferentiableOn ℂ (fun z => (z - w)⁻¹) ({w}ᶜ) := by
    intro z hz
    have hzw : z ≠ w := by simpa using hz
    exact ((differentiableAt_id.sub_const w).inv (sub_ne_zero.mpr hzw)).differentiableWithinAt
  have hsub : closedBall c R ⊆ ({w}ᶜ) := by
    intro z hz
    have hzc : dist z c ≤ R := mem_closedBall.mp hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    exact absurd hzc (not_le.mpr hw)
  exact (hdiff.diffContOnCl_ball hsub).circleIntegral_eq_zero hR

/-- Off the circle, the generalized winding number of `circleMap c R` over `[0, 2π]` about `w` is
the ordinary Cauchy-kernel circle integral, normalized by `(2πi)⁻¹`. The avoidance hypothesis
(`circleMap c R θ ≠ w` for all `θ`) collapses the principal value in `windingNumber` to the ordinary
integral, which is `∮_{C(c,R)} (z − w)⁻¹` up to the commutativity of the integrand's product. -/
theorem windingNumber_circleMap_eq_circleIntegral {c w : ℂ} {R : ℝ}
    (havoid : ∀ θ, circleMap c R θ ≠ w) :
    windingNumber (circleMap c R) 0 (2 * Real.pi) w
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∮ z in C(c, R), (z - w)⁻¹ := by
  have hcont : ContinuousOn (circleMap c R) (Set.uIcc 0 (2 * Real.pi)) :=
    (continuous_circleMap c R).continuousOn
  have hderiv : Continuous (fun θ => deriv (circleMap c R) θ) := by
    simp only [deriv_circleMap]
    exact (continuous_circleMap 0 R).mul continuous_const
  have hint : IntervalIntegrable
      (fun t => (circleMap c R t - w)⁻¹ * deriv (circleMap c R) t) MeasureTheory.volume
      0 (2 * Real.pi) :=
    intervalIntegrable_inv_sub_mul_deriv hcont (fun t _ => havoid t)
      (hderiv.intervalIntegrable _ _)
  rw [windingNumber_eq_integral_of_avoidance hcont (fun t _ => havoid t) hint]
  congr 1
  simp only [circleIntegral, smul_eq_mul]
  exact intervalIntegral.integral_congr fun θ _ => mul_comm _ _

/-- **`n_w(circle) = 1` inside the disc** — the interior value at an arbitrary point. For a point
`w` strictly inside the disc (`dist w c < R`, so `0 < R`), the generalized winding number of the
counterclockwise circle `circleMap c R` over `[0, 2π]` about `w` is `1`: the kernel integral
`∮_{C(c,R)} (z − w)⁻¹` is `2πi` by `circleIntegral.integral_sub_inv_of_mem_ball`, and the `(2πi)⁻¹`
normalization of `windingNumber_circleMap_eq_circleIntegral` cancels it to `1`. -/
theorem windingNumber_circleMap_eq_one_of_dist_lt {c w : ℂ} {R : ℝ} (hw : dist w c < R) :
    windingNumber (circleMap c R) 0 (2 * Real.pi) w = 1 := by
  have havoid : ∀ θ, circleMap c R θ ≠ w := fun θ => circleMap_ne_mem_ball (mem_ball.mpr hw) θ
  rw [windingNumber_circleMap_eq_circleIntegral havoid,
    circleIntegral.integral_sub_inv_of_mem_ball (mem_ball.mpr hw)]
  exact inv_mul_cancel₀ Complex.two_pi_I_ne_zero

/-- **The index principal value of an affinely reparametrised circle exists.** The curve
`t ↦ circleMap c R (m t + s)` stays at distance `|R|` from `c`, so for `R ≠ 0` the principal value
about `c` is the ordinary integral. At `R = 0` the curve is constant at `c`, every truncated
integrand is identically zero, and the principal value exists (and is `0`) for that reason
instead. This is the shared construction behind the arc pieces of the model sector and of the
half-disc worked example. -/
theorem cauchyPVExistsAt_circleMap_comp_affine {c : ℂ} {R : ℝ} (m s a b : ℝ) :
    CauchyPVExistsAt (circleMap c R ∘ fun t : ℝ => m * t + s) a b (fun z => (z - c)⁻¹) c := by
  rcases eq_or_ne R 0 with rfl | hR
  · -- The curve never leaves `c`, so `‖γ t - c‖ > ε` fails for every `ε > 0`.
    refine CauchyPVExistsAt.intro (L := 0) (hasCauchyPVAt_iff.mpr ⟨?_, ?_⟩)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hεpos : (0 : ℝ) < ε := Set.mem_Ioi.mp hε
      simp [not_lt.mpr hεpos.le]
    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hεpos : (0 : ℝ) < ε := Set.mem_Ioi.mp hε
      simp [not_lt.mpr hεpos.le]
  have havoid : ∀ t ∈ Set.uIcc a b, (circleMap c R ∘ fun t : ℝ => m * t + s) t ≠ c :=
    fun _ _ => circleMap_ne_center hR
  have hcont : ContinuousOn (circleMap c R ∘ fun t : ℝ => m * t + s) (Set.uIcc a b) :=
    ((continuous_circleMap c R).comp (by fun_prop)).continuousOn
  have hderiv_circle : ContinuousOn (deriv (circleMap c R))
      ((fun t : ℝ => m * t + s) '' Set.uIcc a b) := by
    have h : deriv (circleMap c R) = fun θ => circleMap 0 R θ * Complex.I :=
      funext (deriv_circleMap c R)
    rw [h]
    exact ((continuous_circleMap 0 R).mul continuous_const).continuousOn
  have hderiv : ContinuousOn (deriv (circleMap c R ∘ fun t : ℝ => m * t + s)) (Set.uIcc a b) :=
    continuousOn_deriv_comp_reparam (φ' := fun _ => m)
      (fun t _ => by
        simpa using (_root_.HasDerivAt.const_mul m (hasDerivAt_id t)).add_const s)
      continuousOn_const (fun u _ => differentiable_circleMap c R u) hderiv_circle
  exact cauchyPVExistsAt_of_avoidance hcont havoid
    (intervalIntegrable_inv_sub_mul_deriv hcont havoid hderiv.intervalIntegrable)

/-- **The winding number of a circular arc about its own centre is its angular extent over `2π`.**
For `R ≠ 0`, the generalized winding number of `circleMap c R` over `[a, b]` about `c` is
`(b - a) / 2π`. The curve misses its centre (`circleMap_ne_center`), so the principal value in
`windingNumber` collapses to the ordinary index integral, which is
`indexIntegral_arc_interval`. This is the `windingNumber`-definition form of that raw
index-integral computation. -/
@[simp]
theorem windingNumber_circleMap_center {c : ℂ} {R : ℝ} (hR : R ≠ 0) (a b : ℝ) :
    windingNumber (circleMap c R) a b c = ((b - a : ℝ) : ℂ) / (2 * (Real.pi : ℂ)) := by
  have hcont : ContinuousOn (circleMap c R) (Set.uIcc a b) :=
    (continuous_circleMap c R).continuousOn
  have hderiv : Continuous (fun θ => deriv (circleMap c R) θ) := by
    simp only [deriv_circleMap]
    exact (continuous_circleMap 0 R).mul continuous_const
  have havoid : ∀ θ, circleMap c R θ ≠ c := fun _ => circleMap_ne_center hR
  have hint : IntervalIntegrable
      (fun t => (circleMap c R t - c)⁻¹ * deriv (circleMap c R) t) MeasureTheory.volume a b :=
    intervalIntegrable_inv_sub_mul_deriv hcont (fun t _ => havoid t)
      (hderiv.intervalIntegrable _ _)
  rw [windingNumber_eq_integral_of_avoidance hcont (fun t _ => havoid t) hint,
    ← indexIntegral_arc_interval (z₀ := c) hR a b]
  congr 1
  exact intervalIntegral.integral_congr fun θ _ => inv_mul_eq_div _ _

/-- **`n_c(circle) = 1`** — the closed-curve normalization at the centre. The generalized winding
number of the counterclockwise circle `circleMap c R` (`R ≠ 0`) over `[0, 2π]` about its centre `c`
is `1`, the interior value. This is the `[0, 2π]` specialization of `windingNumber_circleMap_center`
(`2π / 2π = 1`); it reconciles with `circleIntegral.integral_sub_center_inv`. Unlike
`windingNumber_circleMap_eq_one_of_dist_lt`, this covers a negative radius `R` as well. -/
theorem windingNumber_circleMap_center_eq_one {c : ℂ} {R : ℝ} (hR : R ≠ 0) :
    windingNumber (circleMap c R) 0 (2 * Real.pi) c = 1 := by
  rw [windingNumber_circleMap_center hR]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  rw [sub_zero]
  field_simp
/-- **`n_c(semicircle) = ½` at the centre**, the `[0, π]` specialization of
`windingNumber_circleMap_center`.

This is one of the two ingredients of a half-disc contour computation: the arc about the point
supplies `½`, and `windingNumber_eq_zero_segment` supplies `0` for a diameter *through* it. The
combined contour, and the additivity argument assembling the two, are not established here. -/
theorem windingNumber_circleMap_center_eq_half {c : ℂ} {R : ℝ} (hR : R ≠ 0) :
    windingNumber (circleMap c R) 0 Real.pi c = 1 / 2 := by
  rw [windingNumber_circleMap_center hR]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  rw [sub_zero]
  field_simp

/-- **`n_w(circle) = 0` outside the disc** — the roadmap's "`n` is `0` outside" companion to the
centre normalization. For a point `w` strictly outside the closed disc (`R < dist w c`, with
`R ≥ 0`), the generalized winding number of `circleMap c R` over `[0, 2π]` about `w` vanishes: the
kernel is holomorphic across the disc, so the Cauchy-kernel circle integral is `0`. -/
theorem windingNumber_circleMap_eq_zero_of_lt_dist {c w : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hw : R < dist w c) : windingNumber (circleMap c R) 0 (2 * Real.pi) w = 0 := by
  have havoid : ∀ θ, circleMap c R θ ≠ w := fun θ =>
    ne_of_mem_of_not_mem (circleMap_mem_closedBall c hR θ)
      (fun h => absurd (mem_closedBall.mp h) (not_le.mpr hw))
  rw [windingNumber_circleMap_eq_circleIntegral havoid,
    circleIntegral_sub_inv_eq_zero_of_lt_dist hR hw, mul_zero]

end TauCeti.Contour

end
