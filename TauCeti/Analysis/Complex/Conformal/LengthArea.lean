/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import TauCeti.Analysis.Complex.Conformal.Area
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import TauCeti.Analysis.Contour.ArcFTC

/-!
# The length–area inequality

The **length–area method** converts the finiteness of the Dirichlet integral
`∫⁻ z in s, ‖deriv f z‖ₑ ^ 2` — which `TauCeti/Analysis/Complex/Conformal/Area.lean` identifies
with the area of `f '' s` — into a statement about *lengths*: among the circles `‖z - ζ‖ = ρ`
with `r < ρ < R`, at least one has a short image. Quantitatively, writing `ℓ ρ` for the
derivative-weighted angular integral `TauCeti.circleImageLength f s ζ ρ` — the length of the image
under `f` of the part of that circle lying in `s`, whenever `f` is holomorphic there —
Cauchy–Schwarz in the angular variable gives `ℓ ρ ^ 2 ≤ 2 π ρ ∫ ‖f'‖ ^ 2 ρ dθ`, and integrating
`ℓ ρ ^ 2 / ρ` in `ρ` reassembles the right-hand side, in polar coordinates centred at `ζ`, into the
whole Dirichlet integral:

`∫⁻ ρ in Ioi 0, ℓ ρ ^ 2 / ρ ≤ 2 π ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2`.

Since `∫⁻ ρ in Ioo r R, ρ⁻¹ = log (R / r)` diverges as `r → 0`, a finite Dirichlet integral cannot
keep `ℓ` away from `0`: on every annulus there is a radius with
`ℓ ρ < (2 π A / log (R / r)) ^ (1 / 2)`, an estimate that improves without bound as the annulus is
made longer — and for a holomorphic `f` that is a bound on the length of the image arc. That is
Wolff's lemma, and it is the analytic engine of layer **L5** of the
conformal-mapping roadmap (`ConformalMapping/README.md`), Carathéodory's boundary correspondence:
applied to a Riemann map at a boundary point `ζ` it produces crosscuts of arbitrarily small
diameter, which is what forces the boundary cluster set at `ζ` to degenerate to a point.

## Main results

* `TauCeti.circleImageLength` — the derivative-weighted angular integral
  `∫⁻ θ in Ioo (-π) π, ρ * ‖deriv f (circleMap ζ ρ θ)‖ₑ` cut off outside `s`; where `f` is
  holomorphic this is the length of the image under `f` of the part inside `s` of the circle of
  centre `ζ` and radius `ρ`.
* `TauCeti.ofReal_dist_le_circleImageLength` — the chord bound justifying the name: a sub-arc of
  angular width at most `2 * π` that stays in the domain of holomorphy has the distance between
  the images of its endpoints bounded by that quantity.
* `TauCeti.circleImageLength_eq_lintegral_Ioc` — the angular integral may be taken over any period
  `Ioc t (t + 2 * π)`, so the branch cut chosen in the definition is immaterial.
* `TauCeti.lintegral_circleImageLength_sq_div_le_lintegral_enorm_deriv_sq` — the **length–area
  inequality**, and `TauCeti.lintegral_circleImageLength_sq_div_le_volume_image` its form with the
  area of `f '' s` on the right, through the area formula of `Conformal/Area.lean`.
* `TauCeti.exists_circleImageLength_sq_lt` and
  `TauCeti.exists_circleImageLength_sq_lt_of_volume_image` — **Wolff's lemma**: a radius with
  `ℓ ρ ^ 2 < c` exists in every annulus `r < ρ < R` on which `2 π A < c * log (R / r)`.

The length–area inequality itself needs no holomorphy: it is Cauchy–Schwarz followed by the
polar-coordinate change of variables, and holds for the measurable function `deriv f` whatever it
is. Holomorphy enters only through `Conformal/Area.lean`, to replace the Dirichlet integral by the
area of the image, and in the chord bound, where the fundamental theorem of calculus along the arc
is applied — and it is that chord bound, not the definition, that makes `ℓ` a length.

The angular variable runs over `Ioo (-π) π`, one full period of Mathlib's `circleMap`
parametrisation and the angular factor of `Complex.polarCoord.target`, which is what makes the
polar-coordinate step a rewrite rather than a periodicity argument. Since the integrand is
`2 * π`-periodic the choice of period is immaterial, and
`TauCeti.circleImageLength_eq_lintegral_Ioc` moves it, so no statement here depends on the seam
at `±π`.

## Coordination with upstream Mathlib

Layer L5 is absent from [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505),
the in-progress human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem
itself, and the pinned Mathlib has no length–area estimate; so this file is new Lean formalization
rather than a temporary shim. Its Mathlib inputs — the polar-coordinate change of variables
`Complex.lintegral_comp_polarCoord_symm`, Hölder's inequality
`ENNReal.lintegral_mul_le_Lp_mul_Lq`, and the fundamental theorem of calculus along an arc through
`TauCeti.Contour.integral_comp_mul_eq_sub_of_hasDerivAt` — are consumed, not restated.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2 (the length–area method and
  Wolff's lemma).
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX.
-/

public section

namespace TauCeti

open Complex MeasureTheory Metric Set
open scoped ENNReal Real

variable {U s t : Set ℂ} {f : ℂ → ℂ} {ζ : ℂ}

/-- The **length of the image of a circle**: the integral over the circle of centre `ζ` and radius
`ρ` of the area distortion `‖deriv f‖`, with the part of the circle outside `s` discarded by an
indicator.

Where `f` is holomorphic this is the arc-length integral of `f ∘ circleMap ζ ρ`, whose speed at
angle `θ` is `ρ * ‖deriv f (circleMap ζ ρ θ)‖`, so it is the length of the image under `f` of the
part of the circle lying in `s` — in general a union of open arcs rather than a single one — and
the name is justified by `TauCeti.ofReal_dist_le_circleImageLength`, which bounds the chords of
those image arcs by this quantity. For a map with no complex derivative the geometric reading
fails, since `deriv` is then the junk value `0`: for `f = conj` the quantity is `0` while the image
circle still has length `2 π ρ`.

The angle runs over `Ioo (-π) π`, one full period of `circleMap ζ ρ`; by
`TauCeti.circleImageLength_eq_lintegral_Ioc` any other period gives the same value. A negative
radius, for which `circleMap` traverses the same circle backwards, gives the value `0`. -/
noncomputable def circleImageLength (f : ℂ → ℂ) (s : Set ℂ) (ζ : ℂ) (ρ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ρ * ∫⁻ θ in Ioo (-π) π, s.indicator (fun z => ‖deriv f z‖ₑ) (circleMap ζ ρ θ)

/-- The defining formula for `TauCeti.circleImageLength`, for use outside this module. -/
theorem circleImageLength_def (f : ℂ → ℂ) (s : Set ℂ) (ζ : ℂ) (ρ : ℝ) :
    circleImageLength f s ζ ρ =
      ENNReal.ofReal ρ *
        ∫⁻ θ in Ioo (-π) π, s.indicator (fun z => ‖deriv f z‖ₑ) (circleMap ζ ρ θ) := by
  rw [circleImageLength]

/-- Enlarging the domain can only lengthen the image of the circle inside it. -/
theorem circleImageLength_mono (f : ℂ → ℂ) (ζ : ℂ) (ρ : ℝ) (hst : s ⊆ t) :
    circleImageLength f s ζ ρ ≤ circleImageLength f t ζ ρ := by
  rw [circleImageLength_def, circleImageLength_def]
  gcongr with θ

/-- A circle of nonpositive radius contributes no length. -/
theorem circleImageLength_of_nonpos (f : ℂ → ℂ) (s : Set ℂ) (ζ : ℂ) {ρ : ℝ} (hρ : ρ ≤ 0) :
    circleImageLength f s ζ ρ = 0 := by
  rw [circleImageLength_def, ENNReal.ofReal_of_nonpos hρ, zero_mul]

/-- The angular integrand has period `2 * π`, because `circleMap ζ ρ` does. -/
private theorem periodic_indicator_circleMap (f : ℂ → ℂ) (s : Set ℂ) (ζ : ℂ) (ρ : ℝ) :
    Function.Periodic
      (fun θ => s.indicator (fun z => ‖deriv f z‖ₑ) (circleMap ζ ρ θ)) (2 * π) := fun θ =>
  congrArg (s.indicator fun z => ‖deriv f z‖ₑ) (periodic_circleMap ζ ρ θ)

/-- One period of the angular integral is as good as any other: `Ioc t (t + 2 * π)` is a
fundamental domain for the translations by `2 * π`, which the integrand is invariant under. -/
private theorem lintegral_Ioc_indicator_circleMap (f : ℂ → ℂ) (s : Set ℂ) (ζ : ℂ) (ρ : ℝ)
    (t u : ℝ) :
    ∫⁻ θ in Ioc t (t + 2 * π), s.indicator (fun z => ‖deriv f z‖ₑ) (circleMap ζ ρ θ) =
      ∫⁻ θ in Ioc u (u + 2 * π), s.indicator (fun z => ‖deriv f z‖ₑ) (circleMap ζ ρ θ) :=
  (isAddFundamentalDomain_Ioc Real.two_pi_pos t).setLIntegral_eq
    (isAddFundamentalDomain_Ioc Real.two_pi_pos u) _
    fun g θ => (periodic_indicator_circleMap f s ζ ρ).map_vadd_zmultiples g θ

/-- **The angular integral may be taken over any period.** The interval `Ioo (-π) π` fixed in the
definition of `TauCeti.circleImageLength` can be replaced by any `Ioc t (t + 2 * π)`, so nothing
about the quantity depends on the branch cut at `±π`; in particular an arc of the circle that
crosses the seam is handled by choosing `t` beyond its far endpoint. -/
theorem circleImageLength_eq_lintegral_Ioc (f : ℂ → ℂ) (s : Set ℂ) (ζ : ℂ) (ρ : ℝ) (t : ℝ) :
    circleImageLength f s ζ ρ =
      ENNReal.ofReal ρ *
        ∫⁻ θ in Ioc t (t + 2 * π), s.indicator (fun z => ‖deriv f z‖ₑ) (circleMap ζ ρ θ) := by
  have hπ : -π + 2 * π = π := by ring
  rw [circleImageLength_def, ← lintegral_Ioc_indicator_circleMap f s ζ ρ (-π) t, hπ]
  exact congrArg _ (setLIntegral_congr Ioo_ae_eq_Ioc)

/-- The area distortion of `f`, cut off outside `s`. This is the integrand on both sides of the
length–area inequality: of the Dirichlet integral directly, and of the length after the change to
polar coordinates. -/
private noncomputable def enormDerivIndicator (f : ℂ → ℂ) (s : Set ℂ) : ℂ → ℝ≥0∞ :=
  s.indicator fun z => ‖deriv f z‖ₑ

private theorem measurable_enormDerivIndicator (f : ℂ → ℂ) (hs : MeasurableSet s) :
    Measurable (enormDerivIndicator f s) := by
  rw [enormDerivIndicator]
  exact (measurable_deriv f).enorm.indicator hs

private theorem circleImageLength_eq (f : ℂ → ℂ) (s : Set ℂ) (ζ : ℂ) (ρ : ℝ) :
    circleImageLength f s ζ ρ =
      ENNReal.ofReal ρ * ∫⁻ θ in Ioo (-π) π, enormDerivIndicator f s (circleMap ζ ρ θ) := by
  rw [circleImageLength_def, enormDerivIndicator]

private theorem enormDerivIndicator_sq (f : ℂ → ℂ) (s : Set ℂ) (z : ℂ) :
    enormDerivIndicator f s z ^ 2 = s.indicator (fun z => ‖deriv f z‖ₑ ^ 2) z := by
  rw [enormDerivIndicator]
  by_cases hz : z ∈ s <;> simp [hz]

/-- The polar-coordinate parametrisation of `ℂ` centred at `ζ` is `circleMap ζ`. -/
private theorem add_polarCoord_symm_eq_circleMap (ζ : ℂ) (p : ℝ × ℝ) :
    ζ + Complex.polarCoord.symm p = circleMap ζ p.1 p.2 := by
  simp [circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private theorem continuous_circleMap_uncurry (ζ : ℂ) :
    Continuous fun p : ℝ × ℝ => circleMap ζ p.1 p.2 := by
  simp only [circleMap]
  fun_prop

/-- **The Dirichlet integral in polar coordinates centred at `ζ`.** -/
private theorem lintegral_enorm_deriv_sq_eq_polar (f : ℂ → ℂ) (hs : MeasurableSet s) (ζ : ℂ) :
    ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2 =
      ∫⁻ ρ in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π,
        ENNReal.ofReal ρ * enormDerivIndicator f s (circleMap ζ ρ θ) ^ 2 := by
  have hm : Measurable (enormDerivIndicator f s) := measurable_enormDerivIndicator f hs
  have hjoint : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * enormDerivIndicator f s (circleMap ζ p.1 p.2) ^ 2 :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul
      ((hm.comp (continuous_circleMap_uncurry ζ).measurable).pow_const 2)
  calc ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2
      = ∫⁻ z, enormDerivIndicator f s z ^ 2 := by
        rw [← lintegral_indicator hs]
        exact lintegral_congr fun z => (enormDerivIndicator_sq f s z).symm
    _ = ∫⁻ z, enormDerivIndicator f s (ζ + z) ^ 2 :=
        (lintegral_add_left_eq_self (fun z => enormDerivIndicator f s z ^ 2) ζ).symm
    _ = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
          ENNReal.ofReal p.1 * enormDerivIndicator f s (circleMap ζ p.1 p.2) ^ 2 := by
        rw [← Complex.lintegral_comp_polarCoord_symm
          (fun z => enormDerivIndicator f s (ζ + z) ^ 2), _root_.polarCoord_target]
        simp_rw [smul_eq_mul, add_polarCoord_symm_eq_circleMap]
    _ = _ := by
        rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ hjoint.aemeasurable]

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

/-- Cauchy–Schwarz in the angular variable: the square of the angular integral of the area
distortion is at most `2 π` times the angular integral of its square. -/
private theorem sq_lintegral_angle_le (f : ℂ → ℂ) (hs : MeasurableSet s) (ζ : ℂ) (ρ : ℝ) :
    (∫⁻ θ in Ioo (-π) π, enormDerivIndicator f s (circleMap ζ ρ θ)) ^ 2 ≤
      ENNReal.ofReal (2 * π) *
        ∫⁻ θ in Ioo (-π) π, enormDerivIndicator f s (circleMap ζ ρ θ) ^ 2 := by
  have hvol : (volume.restrict (Ioo (-π) π)) Set.univ = ENNReal.ofReal (2 * π) := by
    rw [Measure.restrict_apply_univ, Real.volume_Ioo]
    ring_nf
  have hum : AEMeasurable (fun θ => enormDerivIndicator f s (circleMap ζ ρ θ))
      (volume.restrict (Ioo (-π) π)) :=
    ((measurable_enormDerivIndicator f hs).comp (measurable_circleMap ζ ρ)).aemeasurable
  simpa [hvol] using sq_lintegral_le_measure_univ_mul (volume.restrict (Ioo (-π) π)) hum

/-- **The length–area inequality.** The integral of `ℓ ρ ^ 2 / ρ` over all radii, where `ℓ ρ` is
`TauCeti.circleImageLength f s ζ ρ` — the length of the image of the circle of radius `ρ` about `ζ`
inside `s`, when `f` is holomorphic there — is at most `2 π` times the Dirichlet integral of `f`
over `s`.

This is Cauchy–Schwarz in the angular variable — the source of the factor `2 π`, the length of the
angular interval — followed by the polar-coordinate change of variables, which reassembles the
angular integrals of `‖deriv f‖ₑ ^ 2` into the plane integral. Nothing is assumed of `f`; the
holomorphic content of the method is the identification of the right-hand side with the area of
`f '' s` in `TauCeti.lintegral_circleImageLength_sq_div_le_volume_image`. -/
theorem lintegral_circleImageLength_sq_div_le_lintegral_enorm_deriv_sq (f : ℂ → ℂ)
    (hs : MeasurableSet s) (ζ : ℂ) :
    ∫⁻ ρ in Ioi (0 : ℝ), circleImageLength f s ζ ρ ^ 2 / ENNReal.ofReal ρ ≤
      ENNReal.ofReal (2 * π) * ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2 := by
  rw [lintegral_enorm_deriv_sq_eq_polar f hs ζ, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioi fun ρ hρ => ?_
  have hρpos : (0 : ℝ) < ρ := hρ
  have hρ0 : ENNReal.ofReal ρ ≠ 0 := (ENNReal.ofReal_pos.mpr hρpos).ne'
  rw [circleImageLength_eq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ENNReal.div_le_iff hρ0 ENNReal.ofReal_ne_top, mul_pow]
  calc ENNReal.ofReal ρ ^ 2 *
        (∫⁻ θ in Ioo (-π) π, enormDerivIndicator f s (circleMap ζ ρ θ)) ^ 2
      ≤ ENNReal.ofReal ρ ^ 2 * (ENNReal.ofReal (2 * π) *
          ∫⁻ θ in Ioo (-π) π, enormDerivIndicator f s (circleMap ζ ρ θ) ^ 2) := by
        gcongr
        exact sq_lintegral_angle_le f hs ζ ρ
    _ = ENNReal.ofReal (2 * π) *
          (ENNReal.ofReal ρ * ∫⁻ θ in Ioo (-π) π,
            enormDerivIndicator f s (circleMap ζ ρ θ) ^ 2) * ENNReal.ofReal ρ := by ring

/-- **The length–area inequality, area form.** On a measurable subset `s` of the domain of
holomorphy on which `f` is injective the Dirichlet integral is the area of `f '' s`, so the total
weighted length `∫⁻ ρ, ℓ ρ ^ 2 / ρ` is at most `2 π` times that area. -/
theorem lintegral_circleImageLength_sq_div_le_volume_image (hUo : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hs : MeasurableSet s) (hsU : s ⊆ U) (hinj : Set.InjOn f s)
    (ζ : ℂ) :
    ∫⁻ ρ in Ioi (0 : ℝ), circleImageLength f s ζ ρ ^ 2 / ENNReal.ofReal ρ ≤
      ENNReal.ofReal (2 * π) * volume (f '' s) := by
  rw [volume_image_eq_lintegral_enorm_deriv_sq hUo hf hs.nullMeasurableSet hsU hinj]
  exact lintegral_circleImageLength_sq_div_le_lintegral_enorm_deriv_sq f hs ζ

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

/-- **Wolff's lemma.** If `2 π` times the Dirichlet integral of `f` over `s` is smaller than
`c * log (R / r)`, then some circle of radius `ρ` between `r` and `R` has `ℓ ρ ^ 2 < c`.

Since `log (R / r)` grows without bound as the annulus is made longer while the Dirichlet integral
stays fixed, this makes `ℓ` arbitrarily small at arbitrarily small radii; for a holomorphic `f`
that is the geometric statement that a map of finite Dirichlet integral cannot keep every circular
arc about `ζ` long. -/
theorem exists_circleImageLength_sq_lt (f : ℂ → ℂ) (hs : MeasurableSet s) (ζ : ℂ) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) {c : ℝ≥0∞}
    (hc : ENNReal.ofReal (2 * π) * (∫⁻ z in s, ‖deriv f z‖ₑ ^ 2) <
      c * ENNReal.ofReal (Real.log (R / r))) :
    ∃ ρ ∈ Ioo r R, circleImageLength f s ζ ρ ^ 2 < c := by
  by_contra hcon
  have hle : ∀ ρ ∈ Ioo r R, c ≤ circleImageLength f s ζ ρ ^ 2 := fun ρ hρ =>
    not_lt.mp fun h => hcon ⟨ρ, hρ, h⟩
  have hconst : ∫⁻ ρ in Ioo r R, c * (ENNReal.ofReal ρ)⁻¹ =
      c * ENNReal.ofReal (Real.log (R / r)) := by
    rw [lintegral_const_mul'' (f := fun ρ : ℝ => (ENNReal.ofReal ρ)⁻¹) c
      ENNReal.measurable_ofReal.inv.aemeasurable, lintegral_inv_ofReal_Ioo hr hrR]
  have hmono : ∫⁻ ρ in Ioo r R, c * (ENNReal.ofReal ρ)⁻¹ ≤
      ∫⁻ ρ in Ioo r R, circleImageLength f s ζ ρ ^ 2 / ENNReal.ofReal ρ := by
    refine setLIntegral_mono' measurableSet_Ioo fun ρ hρ => ?_
    rw [div_eq_mul_inv]
    gcongr
    exact hle ρ hρ
  have hsub : ∫⁻ ρ in Ioo r R, circleImageLength f s ζ ρ ^ 2 / ENNReal.ofReal ρ ≤
      ∫⁻ ρ in Ioi (0 : ℝ), circleImageLength f s ζ ρ ^ 2 / ENNReal.ofReal ρ :=
    lintegral_mono_set fun x hx => hr.trans hx.1
  refine absurd (hc.trans_le ?_) (lt_irrefl _)
  calc c * ENNReal.ofReal (Real.log (R / r))
      = ∫⁻ ρ in Ioo r R, c * (ENNReal.ofReal ρ)⁻¹ := hconst.symm
    _ ≤ ENNReal.ofReal (2 * π) * ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2 :=
        (hmono.trans hsub).trans
          (lintegral_circleImageLength_sq_div_le_lintegral_enorm_deriv_sq f hs ζ)

/-- **Wolff's lemma, area form.** On a measurable subset `s` of the domain of holomorphy on which
`f` is injective the Dirichlet integral is the area of `f '' s`, so a radius with `ℓ ρ ^ 2 < c`
exists as soon as `2 π * area (f '' s) < c * log (R / r)`. -/
theorem exists_circleImageLength_sq_lt_of_volume_image (hUo : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hs : MeasurableSet s) (hsU : s ⊆ U) (hinj : Set.InjOn f s)
    (ζ : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) {c : ℝ≥0∞}
    (hc : ENNReal.ofReal (2 * π) * volume (f '' s) < c * ENNReal.ofReal (Real.log (R / r))) :
    ∃ ρ ∈ Ioo r R, circleImageLength f s ζ ρ ^ 2 < c := by
  refine exists_circleImageLength_sq_lt f hs ζ hr hrR ?_
  rwa [volume_image_eq_lintegral_enorm_deriv_sq hUo hf hs.nullMeasurableSet hsU hinj] at hc

/-- **The chord bound.** If the closed arc of angles `Icc a b` has angular width at most `2 * π`
and the corresponding piece of the circle of radius `ρ` lies in the open set `U` on which `f` is
holomorphic, then the distance between the images of its endpoints is at most the length
`TauCeti.circleImageLength` of the image of the whole circle inside `U`.

The arc is unrestricted apart from its width: it may start anywhere and cross the branch cut at
`±π` fixed in the definition, since by `TauCeti.circleImageLength_eq_lintegral_Ioc` the period of
integration can be moved to `Ioc a (a + 2 * π)`.

This is what makes `TauCeti.circleImageLength` a length rather than an abstract integral, and it is
the form in which Wolff's lemma is used: a short image arc has small chords, and hence — applied to
the crosscut of a domain at a boundary point — a small diameter. -/
theorem ofReal_dist_le_circleImageLength (hUo : IsOpen U) (hf : DifferentiableOn ℂ f U) (ζ : ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) {a b : ℝ} (hab : a ≤ b) (hb : b ≤ a + 2 * π)
    (hmem : ∀ θ ∈ Icc a b, circleMap ζ ρ θ ∈ U) :
    ENNReal.ofReal (dist (f (circleMap ζ ρ a)) (f (circleMap ζ ρ b))) ≤
      circleImageLength f U ζ ρ := by
  have hderivCont : ContinuousOn (deriv f) U := ((hf.analyticOnNhd hUo).deriv).continuousOn
  have hcompCont : ContinuousOn (fun θ => deriv f (circleMap ζ ρ θ)) (Icc a b) :=
    hderivCont.comp (continuous_circleMap ζ ρ).continuousOn hmem
  -- the fundamental theorem of calculus along the arc
  have hFTC : ∫ θ in a..b, deriv f (circleMap ζ ρ θ) * (circleMap 0 ρ θ * I) =
      f (circleMap ζ ρ b) - f (circleMap ζ ρ a) := by
    refine Contour.integral_comp_mul_eq_sub_of_hasDerivAt ?_
      (fun θ _ => hasDerivAt_circleMap ζ ρ θ) (fun θ hθ => ?_) ?_
    · rw [Set.uIcc_of_le hab]
      exact hf.continuousOn.comp (continuous_circleMap ζ ρ).continuousOn hmem
    · have hθ' : θ ∈ Icc a b := by
        rw [min_eq_left hab, max_eq_right hab] at hθ
        exact Set.Ioo_subset_Icc_self hθ
      exact ((hf _ (hmem θ hθ')).differentiableAt (hUo.mem_nhds (hmem θ hθ'))).hasDerivAt
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      refine (ContinuousOn.integrableOn_compact isCompact_Icc ?_).mono_set Set.Ioc_subset_Icc_self
      exact hcompCont.mul ((continuous_circleMap 0 ρ).continuousOn.mul continuousOn_const)
  -- the speed of the parametrisation is `ρ * ‖deriv f‖`
  have hspeed : ∀ θ : ℝ, ‖deriv f (circleMap ζ ρ θ) * (circleMap 0 ρ θ * I)‖ =
      ρ * ‖deriv f (circleMap ζ ρ θ)‖ := by
    intro θ
    rw [norm_mul, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one, abs_of_pos hρ, mul_comm]
  have hnorm : ‖f (circleMap ζ ρ b) - f (circleMap ζ ρ a)‖ ≤
      ∫ θ in a..b, ρ * ‖deriv f (circleMap ζ ρ θ)‖ := by
    rw [← hFTC]
    refine (intervalIntegral.norm_integral_le_integral_norm hab).trans_eq ?_
    exact intervalIntegral.integral_congr fun θ _ => hspeed θ
  have hintOn : IntegrableOn (fun θ => ρ * ‖deriv f (circleMap ζ ρ θ)‖) (Ioc a b) :=
    (ContinuousOn.integrableOn_compact isCompact_Icc
      (continuousOn_const.mul hcompCont.norm)).mono_set Set.Ioc_subset_Icc_self
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioc a b)]
      fun θ => ρ * ‖deriv f (circleMap ζ ρ θ)‖ := by
    filter_upwards with θ
    simp only [Pi.zero_apply]
    positivity
  calc ENNReal.ofReal (dist (f (circleMap ζ ρ a)) (f (circleMap ζ ρ b)))
      ≤ ENNReal.ofReal (∫ θ in a..b, ρ * ‖deriv f (circleMap ζ ρ θ)‖) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [dist_eq_norm, ← norm_neg, neg_sub]
        exact hnorm
    _ = ∫⁻ θ in Ioc a b, ENNReal.ofReal (ρ * ‖deriv f (circleMap ζ ρ θ)‖) := by
        rw [intervalIntegral.integral_of_le hab,
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintOn hnn]
    _ = ∫⁻ θ in Ioc a b,
          ENNReal.ofReal ρ * U.indicator (fun z => ‖deriv f z‖ₑ) (circleMap ζ ρ θ) := by
        refine setLIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
        rw [ENNReal.ofReal_mul hρ.le, ofReal_norm,
          Set.indicator_of_mem (hmem θ (Set.Ioc_subset_Icc_self hθ))]
    _ ≤ ∫⁻ θ in Ioc a (a + 2 * π),
          ENNReal.ofReal ρ * U.indicator (fun z => ‖deriv f z‖ₑ) (circleMap ζ ρ θ) :=
        lintegral_mono_set (Set.Ioc_subset_Ioc_right hb)
    _ = circleImageLength f U ζ ρ := by
        rw [circleImageLength_eq_lintegral_Ioc f U ζ ρ a,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end TauCeti
