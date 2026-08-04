/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Order.LeftRightNhds

/-!
# The lower integral of a weight over a circle, and the length–area inequality

For a weight `g : ℂ → ℝ≥0∞` this file introduces `TauCeti.circleLIntegral g ζ ρ`, the lower
integral of `g` over the circle of centre `ζ` and radius `ρ` with respect to arc length, computed
through Mathlib's parametrisation `circleMap ζ ρ`, which for `ρ > 0` runs once around that circle
at the constant speed `ρ`:

`circleLIntegral g ζ ρ = ENNReal.ofReal ρ * ∫⁻ θ in Ioo (-π) π, g (circleMap ζ ρ θ)`.

For `ρ ≤ 0` the factor `ENNReal.ofReal ρ` makes the value `0`, a convention rather than a reading
of the parametrisation; the arc-length statements below are therefore statements about `ρ > 0`.

Two facts about it are proved, and they are the two halves of the classical **length–area method**.

The first is **polar Fubini**: integrating the circle integrals over all radii recovers the plane
integral,

`∫⁻ ρ in Ioi 0, circleLIntegral g ζ ρ = ∫⁻ z, g z`

(`TauCeti.lintegral_circleLIntegral_eq_lintegral`), for every measurable `g` and every centre `ζ`.
This is Mathlib's `Complex.lintegral_comp_polarCoord_symm` recentred at `ζ` and unfolded into an
iterated integral, the factor `ENNReal.ofReal ρ` in the definition being exactly the Jacobian
`ρ dρ dθ` of polar coordinates.

The second is **Cauchy–Schwarz on the circle**: the square of the circle integral of `g` is at most
`2 π ρ` — for `ρ > 0` the length of the circle — times the circle integral of `g ^ 2`
(`TauCeti.circleLIntegral_sq_le`). Dividing by `ρ` and integrating in `ρ`, polar Fubini reassembles
the right-hand side into the plane integral of `g ^ 2` and gives the **length–area inequality**

`∫⁻ ρ in Ioi 0, circleLIntegral g ζ ρ ^ 2 / ρ ≤ 2 π ∫⁻ z, g z ^ 2`

(`TauCeti.lintegral_circleLIntegral_sq_div_le_lintegral_sq`). Since the logarithmic measure
`∫⁻ ρ in Ioo r R, ρ⁻¹ = log (R / r)` of an annulus diverges as `r → 0`, a finite right-hand side
cannot keep `circleLIntegral g ζ ρ ^ 2` above a positive constant throughout a long annulus:
**Wolff's lemma** `TauCeti.exists_circleLIntegral_sq_lt` produces a radius `ρ` between `r` and `R`
with `circleLIntegral g ζ ρ ^ 2 < c` as soon as `2 π ∫⁻ z, g z ^ 2 < c * log (R / r)`.

The threshold `2 π ∫⁻ z, g z ^ 2 / log (R / r)` that lemma asks to be beaten falls to `0` as the
annulus is made longer, so for a weight of *finite* square integral it is beaten by every positive
`c` once the annulus is long enough. Shrinking the annulus onto the centre — take the outer radius
`R` as given and the inner one `R * exp (-L)` with `L` large — that is
`TauCeti.exists_circleLIntegral_lt_of_lintegral_sq_ne_top`: below every bound `R` there is a radius
`ρ` with `circleLIntegral g ζ ρ` smaller than any prescribed `c ≠ 0`. Equivalently, and sharply,
the circle integral has **lower limit zero at the centre**,
`TauCeti.liminf_circleLIntegral_nhdsGT_eq_zero`. Only a *lower* limit is available, and that is not
a defect of the proof: the weight `‖z - ζ‖⁻¹ / (2 π)` cut down to a sequence of thin annuli
`Ioo aₙ (aₙ * (1 + εₙ))` with `∑ εₙ` finite has finite square integral yet circle integral `1` at
every radius in those annuli, so `circleLIntegral g ζ ρ` need not tend to `0` as `ρ → 0`.

Nothing here is analytic: `g` is an arbitrary measurable weight, and the two inputs are the
polar-coordinate change of variables and Hölder's inequality. The analytic use is
`TauCeti/Analysis/Complex/Conformal/LengthArea.lean`, which takes `g` to be `‖deriv f‖ₑ` cut off
outside a set `s`, so that `circleLIntegral g ζ ρ` becomes the arc length of the image of a circular
arc under a holomorphic `f` and `∫⁻ z, g z ^ 2` its Dirichlet integral, hence the area of the image;
that file is the layer **L5** input of `TauCetiRoadmap/ConformalMapping/README.md`. Stating the
estimates for a weight keeps them available to any other length-versus-area argument — the plane
integral on the right need not be an area and the circle integral on the left need not be a length.

## Main definitions and results

* `TauCeti.circleLIntegral` — the lower integral of a weight over a circle with respect to arc
  length, through the parametrisation `circleMap`.
* `TauCeti.circleLIntegral_eq_lintegral_Ioc` — the angular integral may be taken over any period,
  so the branch cut at `±π` fixed in the definition is immaterial.
* `TauCeti.lintegral_circleLIntegral_eq_lintegral` — **polar Fubini**: the circle integrals about
  any centre integrate over the radii to the plane integral.
* `TauCeti.circleLIntegral_sq_le` — **Cauchy–Schwarz on the circle**: the square of the circle
  integral of `g` is at most the circumference times the circle integral of `g ^ 2`.
* `TauCeti.lintegral_circleLIntegral_sq_div_le_lintegral_sq` — the **length–area inequality**.
* `TauCeti.exists_circleLIntegral_sq_lt` — **Wolff's lemma**: a radius with small circle integral
  exists in every annulus whose logarithmic measure is large enough.
* `TauCeti.exists_circleLIntegral_lt_of_lintegral_sq_ne_top` — its limiting form for a weight of
  finite square integral: below every positive bound there is a radius at which the circle integral
  is smaller than any prescribed `c ≠ 0`.
* `TauCeti.liminf_circleLIntegral_nhdsGT_eq_zero` — the same statement as a lower limit: the circle
  integrals of a weight of finite square integral have lower limit `0` at the centre.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2 (the length–area method).
* P. L. Duren, *Univalent Functions*, Ch. 3.
-/

public section

namespace TauCeti

open MeasureTheory Set Topology
open scoped ENNReal Real

variable {g : ℂ → ℝ≥0∞} {ζ : ℂ} {ρ : ℝ}

/-! ### The circle integral of a weight -/

/-- The **lower integral of the weight `g` over the circle** of centre `ζ` and radius `ρ`, taken
with respect to arc length: for `ρ > 0`, the angular integral of `g ∘ circleMap ζ ρ` scaled by the
speed `ρ` of that parametrisation.

Nothing is assumed of `g`, so this is a lower integral of a possibly non-measurable integrand. The
angle runs over `Ioo (-π) π`, one full period of `circleMap ζ ρ`; by
`TauCeti.circleLIntegral_eq_lintegral_Ioc` any other period gives the same value. A nonpositive
radius gives the value `0`, by the factor `ENNReal.ofReal ρ`: that is a deliberate convention, not
a property of the parametrisation, since for `ρ < 0` the map `circleMap ζ ρ` still runs once around
the circle of radius `|ρ|`, at speed `|ρ|` and in the same direction, only rotated by `π`. -/
noncomputable def circleLIntegral (g : ℂ → ℝ≥0∞) (ζ : ℂ) (ρ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ρ * ∫⁻ θ in Ioo (-π) π, g (circleMap ζ ρ θ)

/-- The defining angular integral. The body of `TauCeti.circleLIntegral` is not `@[expose]`d, so
this is the form in which other modules reach the definition. -/
theorem circleLIntegral_def (g : ℂ → ℝ≥0∞) (ζ : ℂ) (ρ : ℝ) :
    circleLIntegral g ζ ρ = ENNReal.ofReal ρ * ∫⁻ θ in Ioo (-π) π, g (circleMap ζ ρ θ) := by
  rw [circleLIntegral]

/-- Increasing the weight on the circle increases its circle integral: only the values on
`Metric.sphere ζ ρ`, the circle the integral is taken over, matter.

The comparison is asked for only at a positive radius, since at a nonpositive one both sides are
`0` and nothing about `g` and `h` is needed. -/
theorem circleLIntegral_mono_on {h : ℂ → ℝ≥0∞} (ζ : ℂ) (ρ : ℝ)
    (hgh : 0 < ρ → ∀ z ∈ Metric.sphere ζ ρ, g z ≤ h z) :
    circleLIntegral g ζ ρ ≤ circleLIntegral h ζ ρ := by
  rcases le_or_gt ρ 0 with hρ | hρ
  · rw [circleLIntegral_def, circleLIntegral_def, ENNReal.ofReal_of_nonpos hρ, zero_mul, zero_mul]
  rw [circleLIntegral_def, circleLIntegral_def]
  gcongr with θ
  exact hgh hρ _ (circleMap_mem_sphere ζ hρ.le θ)

/-- Weights agreeing on the circle have the same circle integral; as in
`TauCeti.circleLIntegral_mono_on`, agreement is asked for only at a positive radius. -/
theorem circleLIntegral_congr {h : ℂ → ℝ≥0∞} (ζ : ℂ) (ρ : ℝ)
    (hgh : 0 < ρ → EqOn g h (Metric.sphere ζ ρ)) :
    circleLIntegral g ζ ρ = circleLIntegral h ζ ρ :=
  le_antisymm (circleLIntegral_mono_on ζ ρ fun hρ _ hz => (hgh hρ hz).le)
    (circleLIntegral_mono_on ζ ρ fun hρ _ hz => (hgh hρ hz).ge)

/-- The circle integral of a constant weight is `2 π ρ` — for `ρ > 0` the circumference of the
circle — times that constant; for `ρ ≤ 0` both sides are `0`. -/
@[simp]
theorem circleLIntegral_const (a : ℝ≥0∞) (ζ : ℂ) (ρ : ℝ) :
    circleLIntegral (fun _ => a) ζ ρ = ENNReal.ofReal (2 * π * ρ) * a := by
  rcases le_or_gt ρ 0 with hρ | _
  · rw [circleLIntegral_def, ENNReal.ofReal_of_nonpos hρ, zero_mul,
      ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) hρ), zero_mul]
  · have hπ : π - -π = 2 * π := by ring
    rw [circleLIntegral_def, setLIntegral_const, Real.volume_Ioo, hπ,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * π)]
    ring

/-- The circle integral vanishes at a nonpositive radius, by the factor `ENNReal.ofReal ρ` in the
definition of `TauCeti.circleLIntegral`. This is that convention, not a geometric statement: for
`ρ < 0` the parametrisation `circleMap ζ ρ` still runs once around the circle of radius `|ρ|`. -/
@[simp]
theorem circleLIntegral_of_nonpos (g : ℂ → ℝ≥0∞) (ζ : ℂ) (hρ : ρ ≤ 0) :
    circleLIntegral g ζ ρ = 0 := by
  rw [circleLIntegral_def, ENNReal.ofReal_of_nonpos hρ, zero_mul]

/-- The zero weight has zero circle integral. -/
@[simp]
theorem circleLIntegral_zero (ζ : ℂ) (ρ : ℝ) : circleLIntegral 0 ζ ρ = 0 := by
  simp [circleLIntegral_def]

/-- **The circle integral is additive in the weight**, as soon as one summand has an a.e.
measurable angular trace along the circle at hand; as in `TauCeti.circleLIntegral_sq_le`, nothing
is assumed of either weight off that circle. Some such hypothesis is needed, a lower integral being
only superadditive in general. It is the hypothesis of `MeasureTheory.lintegral_add_left'`, which
is why — like that lemma, and unlike its `Measurable` counterpart — this is not a `simp` lemma. -/
theorem circleLIntegral_add {h : ℂ → ℝ≥0∞} (ζ : ℂ) (ρ : ℝ)
    (hg : AEMeasurable (fun θ => g (circleMap ζ ρ θ)) (volume.restrict (Ioo (-π) π))) :
    circleLIntegral (fun z => g z + h z) ζ ρ =
      circleLIntegral g ζ ρ + circleLIntegral h ζ ρ := by
  rw [circleLIntegral_def, circleLIntegral_def, circleLIntegral_def, lintegral_add_left' hg,
    mul_add]

/-- **A finite constant comes out of the circle integral.** This is
`MeasureTheory.lintegral_const_mul'`, whose finiteness hypothesis on the constant is what lets the
weight stay arbitrary; as there, no measurability is needed. -/
theorem circleLIntegral_const_mul (a : ℝ≥0∞) (g : ℂ → ℝ≥0∞) (ζ : ℂ) (ρ : ℝ) (ha : a ≠ ∞) :
    circleLIntegral (fun z => a * g z) ζ ρ = a * circleLIntegral g ζ ρ := by
  rw [circleLIntegral_def, circleLIntegral_def, lintegral_const_mul' _ _ ha]
  ring

/-- The angular integrand has period `2 * π`, because `circleMap ζ ρ` does. -/
private theorem periodic_comp_circleMap (g : ℂ → ℝ≥0∞) (ζ : ℂ) (ρ : ℝ) :
    Function.Periodic (fun θ => g (circleMap ζ ρ θ)) (2 * π) := fun θ =>
  congrArg g (periodic_circleMap ζ ρ θ)

/-- One period of the angular integral is as good as any other: `Ioc t (t + 2 * π)` is a
fundamental domain for the translations by `2 * π`, which the integrand is invariant under. -/
private theorem lintegral_Ioc_comp_circleMap (g : ℂ → ℝ≥0∞) (ζ : ℂ) (ρ : ℝ) (t u : ℝ) :
    ∫⁻ θ in Ioc t (t + 2 * π), g (circleMap ζ ρ θ) =
      ∫⁻ θ in Ioc u (u + 2 * π), g (circleMap ζ ρ θ) :=
  (isAddFundamentalDomain_Ioc Real.two_pi_pos t).setLIntegral_eq
    (isAddFundamentalDomain_Ioc Real.two_pi_pos u) _
    fun v θ => (periodic_comp_circleMap g ζ ρ).map_vadd_zmultiples v θ

/-- **The angular integral may be taken over any period.** The interval `Ioo (-π) π` fixed in the
definition of `TauCeti.circleLIntegral` can be replaced by any `Ioc t (t + 2 * π)`, so nothing about
the quantity depends on the branch cut at `±π`; in particular an arc of the circle that crosses the
seam is handled by choosing `t` beyond its far endpoint. -/
theorem circleLIntegral_eq_lintegral_Ioc (g : ℂ → ℝ≥0∞) (ζ : ℂ) (ρ : ℝ) (t : ℝ) :
    circleLIntegral g ζ ρ =
      ENNReal.ofReal ρ * ∫⁻ θ in Ioc t (t + 2 * π), g (circleMap ζ ρ θ) := by
  have hπ : -π + 2 * π = π := by ring
  rw [circleLIntegral_def, ← lintegral_Ioc_comp_circleMap g ζ ρ (-π) t, hπ]
  exact congrArg _ (setLIntegral_congr Ioo_ae_eq_Ioc)

/-! ### Polar Fubini -/

/-- The polar-coordinate parametrisation of `ℂ` centred at `ζ` is `circleMap ζ`. -/
private theorem add_polarCoord_symm_eq_circleMap (ζ : ℂ) (p : ℝ × ℝ) :
    ζ + Complex.polarCoord.symm p = circleMap ζ p.1 p.2 := by
  simp [circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private theorem continuous_circleMap_uncurry (ζ : ℂ) :
    Continuous fun p : ℝ × ℝ => circleMap ζ p.1 p.2 := by
  simp only [circleMap]
  fun_prop

/-- **Polar Fubini for the lower integral.** Integrating the circle integrals of a measurable
weight over all radii recovers its plane integral, whatever centre the circles are taken about.

This is the polar-coordinate change of variables `Complex.lintegral_comp_polarCoord_symm`,
recentred at `ζ` by translation invariance of the plane measure and unfolded into an iterated
integral over the radius and the angle; the factor `ENNReal.ofReal ρ` built into
`TauCeti.circleLIntegral` is the Jacobian. -/
theorem lintegral_circleLIntegral_eq_lintegral (hg : Measurable g) (ζ : ℂ) :
    ∫⁻ ρ in Ioi (0 : ℝ), circleLIntegral g ζ ρ = ∫⁻ z, g z := by
  have hjoint : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * g (circleMap ζ p.1 p.2) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul
      (hg.comp (continuous_circleMap_uncurry ζ).measurable)
  calc ∫⁻ ρ in Ioi (0 : ℝ), circleLIntegral g ζ ρ
      = ∫⁻ ρ in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal ρ * g (circleMap ζ ρ θ) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun ρ _ => ?_
        rw [circleLIntegral_def, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal p.1 * g (circleMap ζ p.1 p.2) := by
        rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ hjoint.aemeasurable]
    _ = ∫⁻ z, g (ζ + z) := by
        rw [← Complex.lintegral_comp_polarCoord_symm fun z => g (ζ + z), _root_.polarCoord_target]
        simp_rw [smul_eq_mul, add_polarCoord_symm_eq_circleMap]
    _ = ∫⁻ z, g z := lintegral_add_left_eq_self g ζ

/-! ### Cauchy–Schwarz on a circle, and the length–area inequality -/

/-- **Cauchy–Schwarz.** The square of the integral of a function is at most the mass of the measure
times the integral of its square. -/
private theorem sq_lintegral_le_measure_univ_mul {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {u : α → ℝ≥0∞} (hu : AEMeasurable u μ) :
    (∫⁻ x, u x ∂μ) ^ 2 ≤ μ Set.univ * ∫⁻ x, u x ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hu
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at h
  have hrp : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast (x ^ (1 / 2 : ℝ)) 2, ← ENNReal.rpow_mul]
    norm_num
  calc (∫⁻ x, u x ∂μ) ^ 2
      ≤ ((∫⁻ x, u x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) * (μ Set.univ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left' h 2
    _ = (∫⁻ x, u x ^ (2 : ℝ) ∂μ) * μ Set.univ := by rw [mul_pow, hrp, hrp]
    _ = μ Set.univ * ∫⁻ x, u x ^ 2 ∂μ := by
        rw [mul_comm]
        exact congrArg _ (lintegral_congr fun x => ENNReal.rpow_natCast (u x) 2)

/-- Cauchy–Schwarz in the angular variable: the square of the angular integral is at most `2 π`,
the length of the angular interval, times the angular integral of the square. -/
private theorem sq_lintegral_angle_le
    (hg : AEMeasurable (fun θ => g (circleMap ζ ρ θ)) (volume.restrict (Ioo (-π) π))) :
    (∫⁻ θ in Ioo (-π) π, g (circleMap ζ ρ θ)) ^ 2 ≤
      ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π, g (circleMap ζ ρ θ) ^ 2 := by
  have hvol : (volume.restrict (Ioo (-π) π)) Set.univ = ENNReal.ofReal (2 * π) := by
    rw [Measure.restrict_apply_univ, Real.volume_Ioo]
    ring_nf
  simpa [hvol] using sq_lintegral_le_measure_univ_mul (volume.restrict (Ioo (-π) π)) hg

/-- **Cauchy–Schwarz on a circle.** The square of the circle integral of `g` is at most
`2 π ρ` — for `ρ > 0` the circumference of the circle — times the circle integral of `g ^ 2`.

Only the angular trace of `g` along the circle at hand need be measurable; nothing is assumed of
`g` off that circle. Both sides vanish for a nonpositive radius, so no positivity is assumed. -/
theorem circleLIntegral_sq_le (ζ : ℂ) (ρ : ℝ)
    (hg : AEMeasurable (fun θ => g (circleMap ζ ρ θ)) (volume.restrict (Ioo (-π) π))) :
    circleLIntegral g ζ ρ ^ 2 ≤
      ENNReal.ofReal (2 * π * ρ) * circleLIntegral (fun z => g z ^ 2) ζ ρ := by
  rcases le_or_gt ρ 0 with hρ | hρ
  · simp [circleLIntegral_of_nonpos _ _ hρ]
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  rw [circleLIntegral_def, circleLIntegral_def, mul_pow, ENNReal.ofReal_mul h2π]
  calc ENNReal.ofReal ρ ^ 2 * (∫⁻ θ in Ioo (-π) π, g (circleMap ζ ρ θ)) ^ 2
      ≤ ENNReal.ofReal ρ ^ 2 *
          (ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π, g (circleMap ζ ρ θ) ^ 2) := by
        gcongr
        exact sq_lintegral_angle_le hg
    _ = ENNReal.ofReal (2 * π) * ENNReal.ofReal ρ *
          (ENNReal.ofReal ρ * ∫⁻ θ in Ioo (-π) π, g (circleMap ζ ρ θ) ^ 2) := by ring

/-- **The length–area inequality.** For a measurable weight `g` and any centre `ζ`, the integral
over all radii of `circleLIntegral g ζ ρ ^ 2 / ρ` is at most `2 π` times the plane integral of
`g ^ 2`.

This is Cauchy–Schwarz on each circle (`TauCeti.circleLIntegral_sq_le`) — the source of the factor
`2 π` — followed by polar Fubini (`TauCeti.lintegral_circleLIntegral_eq_lintegral`) applied to the
weight `g ^ 2`, which reassembles the circle integrals of `g ^ 2` into its plane integral. -/
theorem lintegral_circleLIntegral_sq_div_le_lintegral_sq (hg : Measurable g) (ζ : ℂ) :
    ∫⁻ ρ in Ioi (0 : ℝ), circleLIntegral g ζ ρ ^ 2 / ENNReal.ofReal ρ ≤
      ENNReal.ofReal (2 * π) * ∫⁻ z, g z ^ 2 := by
  have hstep : ∀ ρ ∈ Ioi (0 : ℝ), circleLIntegral g ζ ρ ^ 2 / ENNReal.ofReal ρ ≤
      ENNReal.ofReal (2 * π) * circleLIntegral (fun z => g z ^ 2) ζ ρ := by
    intro ρ hρ
    have hρpos : (0 : ℝ) < ρ := hρ
    have hρ0 : ENNReal.ofReal ρ ≠ 0 := (ENNReal.ofReal_pos.mpr hρpos).ne'
    rw [ENNReal.div_le_iff hρ0 ENNReal.ofReal_ne_top]
    refine (circleLIntegral_sq_le ζ ρ
      (hg.comp (measurable_circleMap ζ ρ)).aemeasurable).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * π)]
    ring
  calc ∫⁻ ρ in Ioi (0 : ℝ), circleLIntegral g ζ ρ ^ 2 / ENNReal.ofReal ρ
      ≤ ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (2 * π) * circleLIntegral (fun z => g z ^ 2) ζ ρ :=
        setLIntegral_mono' measurableSet_Ioi hstep
    _ = ENNReal.ofReal (2 * π) * ∫⁻ z, g z ^ 2 := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_circleLIntegral_eq_lintegral (hg.pow_const 2) ζ]

/-- The logarithmic measure of an annulus: `∫⁻ ρ in Ioo r R, ρ⁻¹ = log (R / r)`. It is the
divergence of this integral as `r → 0` that gives the length–area method its force. -/
private theorem lintegral_inv_ofReal_Ioo {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∫⁻ ρ in Ioo r R, (ENNReal.ofReal ρ)⁻¹ = ENNReal.ofReal (Real.log (R / r)) := by
  have hR : 0 < R := hr.trans hrR
  have hcont : ContinuousOn (fun x : ℝ => x⁻¹) (Set.uIcc r R) := by
    refine ContinuousOn.inv₀ continuousOn_id fun x hx => ?_
    rw [Set.uIcc_of_le hrR.le] at hx
    exact ne_of_gt (lt_of_lt_of_le hr hx.1)
  have hint : IntegrableOn (fun x : ℝ => x⁻¹) (Ioo r R) :=
    (hcont.intervalIntegrable).1.mono_set Set.Ioo_subset_Ioc_self
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioo r R)] fun x : ℝ => x⁻¹ := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    exact le_of_lt (inv_pos.mpr (hr.trans hx.1))
  have hval : ∫ x in Ioo r R, x⁻¹ = Real.log (R / r) := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hrR.le]
    exact integral_inv_of_pos hr hR
  rw [← hval, MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn]
  refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  rw [ENNReal.ofReal_inv_of_pos (hr.trans hx.1)]

/-- **Wolff's lemma.** If `2 π` times the plane integral of `g ^ 2` is smaller than
`c * log (R / r)`, then some circle of radius `ρ` strictly between `r` and `R` has
`circleLIntegral g ζ ρ ^ 2 < c`.

Since `log (R / r)` grows without bound as the annulus is made longer while the plane integral
stays fixed, this makes the circle integral arbitrarily small at arbitrarily small radii: a weight
of finite square integral cannot have a large circle integral on every circle about `ζ`. -/
theorem exists_circleLIntegral_sq_lt (hg : Measurable g) (ζ : ℂ) {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) {c : ℝ≥0∞}
    (hc : ENNReal.ofReal (2 * π) * (∫⁻ z, g z ^ 2) < c * ENNReal.ofReal (Real.log (R / r))) :
    ∃ ρ ∈ Ioo r R, circleLIntegral g ζ ρ ^ 2 < c := by
  by_contra hcon
  have hle : ∀ ρ ∈ Ioo r R, c ≤ circleLIntegral g ζ ρ ^ 2 := fun ρ hρ =>
    not_lt.mp fun h => hcon ⟨ρ, hρ, h⟩
  have hconst : ∫⁻ ρ in Ioo r R, c * (ENNReal.ofReal ρ)⁻¹ =
      c * ENNReal.ofReal (Real.log (R / r)) := by
    rw [lintegral_const_mul'' (f := fun ρ : ℝ => (ENNReal.ofReal ρ)⁻¹) c
      ENNReal.measurable_ofReal.inv.aemeasurable, lintegral_inv_ofReal_Ioo hr hrR]
  have hmono : ∫⁻ ρ in Ioo r R, c * (ENNReal.ofReal ρ)⁻¹ ≤
      ∫⁻ ρ in Ioo r R, circleLIntegral g ζ ρ ^ 2 / ENNReal.ofReal ρ := by
    refine setLIntegral_mono' measurableSet_Ioo fun ρ hρ => ?_
    rw [div_eq_mul_inv]
    gcongr
    exact hle ρ hρ
  have hsub : ∫⁻ ρ in Ioo r R, circleLIntegral g ζ ρ ^ 2 / ENNReal.ofReal ρ ≤
      ∫⁻ ρ in Ioi (0 : ℝ), circleLIntegral g ζ ρ ^ 2 / ENNReal.ofReal ρ :=
    lintegral_mono_set fun x hx => hr.trans hx.1
  refine absurd (hc.trans_le ?_) (lt_irrefl _)
  calc c * ENNReal.ofReal (Real.log (R / r))
      = ∫⁻ ρ in Ioo r R, c * (ENNReal.ofReal ρ)⁻¹ := hconst.symm
    _ ≤ ENNReal.ofReal (2 * π) * ∫⁻ z, g z ^ 2 :=
        (hmono.trans hsub).trans (lintegral_circleLIntegral_sq_div_le_lintegral_sq hg ζ)

/-! ### Small circle integrals at arbitrarily small radii -/

/-- **An annulus of prescribed logarithmic length inside a prescribed disc.** Shrinking the inner
radius of the annulus `Ioo r R` towards `0` sends `Real.log (R / r)` to `+∞`, so every target
length `L` is met by the inner radius `R * Real.exp (-L)`, which for `0 < L` is smaller than `R`.
This is how the outer radius is kept below a prescribed bound while Wolff's lemma is given as long
an annulus as it needs. -/
private theorem log_div_mul_exp_neg {R : ℝ} (hR : 0 < R) (L : ℝ) :
    Real.log (R / (R * Real.exp (-L))) = L := by
  have h : R / (R * Real.exp (-L)) = Real.exp L := by
    rw [Real.exp_neg]
    field_simp
  rw [h, Real.log_exp]

/-- **Wolff's lemma in the limit: a weight of finite square integral has small circle integrals at
arbitrarily small radii.** If `∫⁻ z, g z ^ 2` is finite then for every threshold `c ≠ 0` and every
bound `R > 0` there is a radius `ρ` below `R` with `circleLIntegral g ζ ρ < c`.

The threshold that `TauCeti.exists_circleLIntegral_sq_lt` asks to be beaten is
`2 π ∫⁻ z, g z ^ 2 / log (R / r)`, which for a finite square integral falls to `0` as the annulus
`Ioo r R` is made logarithmically longer; here the outer radius is the prescribed bound `R` and the
inner one `R * exp (-L)` is pushed towards `0`, which is what confines the radius produced to
`Ioo 0 R`. The reduction to a finite threshold is the passage to `min c 1`, and the square is undone
by monotonicity of squaring on `ℝ≥0∞`.

There is no companion statement for a *fixed* small radius: see
`TauCeti.liminf_circleLIntegral_nhdsGT_eq_zero` for the sharp form, a lower limit rather than a
limit. -/
theorem exists_circleLIntegral_lt_of_lintegral_sq_ne_top (hg : Measurable g)
    (hfin : (∫⁻ z, g z ^ 2) ≠ ∞) (ζ : ℂ) {c : ℝ≥0∞} (hc : c ≠ 0) {R : ℝ} (hR : 0 < R) :
    ∃ ρ ∈ Ioo 0 R, circleLIntegral g ζ ρ < c := by
  -- it is enough to treat a finite threshold, since `min c 1` is one and is at most `c`
  suffices h : ∀ b : ℝ≥0∞, b ≠ 0 → b ≠ ∞ → ∃ ρ ∈ Ioo 0 R, circleLIntegral g ζ ρ < b by
    obtain ⟨ρ, hρ, hlt⟩ := h (min c 1) (by simp [hc]) (by simp)
    exact ⟨ρ, hρ, hlt.trans_le (min_le_left c 1)⟩
  intro b hb0 hbtop
  -- `A` is `2 π` times the square integral, a finite real number, and `br` is the threshold
  have hAtop : ENNReal.ofReal (2 * π) * ∫⁻ z, g z ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  set A : ℝ := (ENNReal.ofReal (2 * π) * ∫⁻ z, g z ^ 2).toReal
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  set br : ℝ := b.toReal
  have hbr0 : 0 < br := ENNReal.toReal_pos hb0 hbtop
  -- the annulus `Ioo r R`, chosen of logarithmic length `L` so that `br ^ 2 * L` beats `A`
  set L : ℝ := (A + 1) / br ^ 2 with hL
  have hLpos : 0 < L := div_pos (by linarith) (by positivity)
  have hbrL : br ^ 2 * L = A + 1 := by rw [hL]; field_simp
  set r : ℝ := R * Real.exp (-L) with hr
  have hrpos : 0 < r := mul_pos hR (Real.exp_pos _)
  have hrR : r < R := by
    have hexp : Real.exp (-L) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    nlinarith
  have hlog : Real.log (R / r) = L := by rw [hr, log_div_mul_exp_neg hR]
  -- Wolff's lemma on that annulus, at the squared threshold
  have hlt : ENNReal.ofReal (2 * π) * ∫⁻ z, g z ^ 2 <
      b ^ 2 * ENNReal.ofReal (Real.log (R / r)) := by
    have hAeq : ENNReal.ofReal (2 * π) * ∫⁻ z, g z ^ 2 = ENNReal.ofReal A :=
      (ENNReal.ofReal_toReal hAtop).symm
    have hbeq : b = ENNReal.ofReal br := (ENNReal.ofReal_toReal hbtop).symm
    rw [hAeq, hbeq, hlog, ← ENNReal.ofReal_pow hbr0.le,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ br ^ 2), hbrL]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  obtain ⟨ρ, hρmem, hρlt⟩ := exists_circleLIntegral_sq_lt hg ζ hrpos hrR hlt
  refine ⟨ρ, ⟨hrpos.trans hρmem.1, hρmem.2⟩, ?_⟩
  by_contra hcon
  exact absurd (pow_le_pow_left' (not_lt.mp hcon) 2) (not_le.mpr hρlt)

/-- **The circle integrals of a weight of finite square integral have lower limit `0` at the
centre.** This is the sharp form of `TauCeti.exists_circleLIntegral_lt_of_lintegral_sq_ne_top`,
which says exactly that every positive threshold is undercut on every interval `Ioo 0 R` of radii,
and those intervals are a basis of `𝓝[>] 0`.

The limit itself does not exist in general: the circle integral is only *frequently* small, as the
thin-annulus weight described in the module docstring shows. -/
theorem liminf_circleLIntegral_nhdsGT_eq_zero (hg : Measurable g) (hfin : (∫⁻ z, g z ^ 2) ≠ ∞)
    (ζ : ℂ) : Filter.liminf (fun ρ => circleLIntegral g ζ ρ) (𝓝[>] (0 : ℝ)) = 0 := by
  refine le_antisymm ?_ zero_le
  by_contra hcon
  obtain ⟨b, hb0, hbl⟩ := exists_between (not_le.mp hcon)
  refine absurd (Filter.liminf_le_of_frequently_le' ?_) (not_le.mpr hbl)
  refine (nhdsGT_basis (0 : ℝ)).frequently_iff.mpr fun R hR => ?_
  obtain ⟨ρ, hρ, hlt⟩ := exists_circleLIntegral_lt_of_lintegral_sq_ne_top hg hfin ζ hb0.ne' hR
  exact ⟨ρ, hρ, hlt.le⟩

end TauCeti
