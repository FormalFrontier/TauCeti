/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.Dirichlet
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Dirichlet integral `∫₀^∞ sin x / x dx = π / 2`

`WorkedExamples/HalfDisc/Dirichlet.lean` evaluates the Hungerbühler--Wasem motivating example in
its complex form: the Cauchy principal values of `e^{iaz}/z` along the real segment `[-R, R]`
converge to `π i` as `R → ∞`, the pole at the origin sitting *on* the contour and contributing
only half its residue. This file cashes that in for the classical real statement it exists to
prove — the **Dirichlet integral**

`lim_{R → ∞} ∫_0^R sin (a x) / x dx = π / 2` for every frequency `a > 0`,

and in particular `lim_{R → ∞} ∫_0^R sin x / x dx = π / 2`. The limit is genuinely improper:
`x ↦ sin x / x` is not Lebesgue integrable on `[0, ∞)`, so there is no Bochner integral over
`Ioi 0` to state this about, and the result is a statement about the truncated integrals.

The bridge is a second, independent evaluation of the *same* principal value. Along the real axis
the Dirichlet integrand splits as

`e^{i a t} / t = cos (a t) / t + i · sin (a t) / t`,

and the symmetric `ε`-excision at the origin treats the two parts completely differently:

* the real part `cos (a t) / t` is **odd**, so each excised integral over `[-R, R]` vanishes
  identically — this is exactly why the principal value exists at all, the divergence of
  `∫ dt / t` cancelling between the two sides;
* the imaginary part `sin (a t) / t` is **bounded** (by `|a|`, since `|sin u| ≤ |u|`), so its
  excised integrals converge to the ordinary integral over `[-R, R]` by dominated convergence —
  no principal value is needed there.

So the principal value equals `i · ∫_{-R}^{R} sin (a t) / t dt`, and comparing with the half-disc
evaluation of `Dirichlet.lean` through uniqueness of the principal value (`HasCauchyPV.unique`)
turns the complex identity into a real one. Jordan's lemma disposes of the arc as `R → ∞`, and
evenness of `t ↦ sin (a t) / t` halves the symmetric integral.

The frequency `a` is arbitrary in the principal-value identity — neither the cancellation nor the
bound above needs anything of it — and only the passage to the limit `R → ∞` requires `a > 0`,
since that is where Jordan's lemma enters.

## Main results

* `TauCeti.Contour.hasCauchyPVAt_dirichletIntegrand_realSegment` — the principal value of
  `e^{iat}/t` along `[-R, R]` is `i · ∫_{-R}^{R} sin (a t) / t dt`, for every frequency.
* `TauCeti.Contour.integral_sin_mul_div_symm_eq` — comparing the two evaluations of that
  principal value: the symmetric integral is `π` minus the arc contribution.
* `TauCeti.Contour.tendsto_integral_sin_mul_div_symm_atTop` — the symmetric integrals
  `∫_{-R}^{R} sin (a t) / t dt` converge to `π` for `a > 0`.
* `TauCeti.Contour.tendsto_integral_sin_mul_div_atTop` — **the Dirichlet integral**:
  `∫_0^R sin (a x) / x dx → π / 2` for `a > 0`.
* `TauCeti.Contour.tendsto_integral_sin_div_atTop` and
  `TauCeti.Contour.tendsto_integral_sinc_atTop` — the unit-frequency case, in the `sin x / x` and
  the `Real.sinc` spellings.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), Thm 3.3 and the improper-integral application motivating it.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set Topology

namespace TauCeti.Contour

variable {a R ε : ℝ}

/-! ### The Dirichlet integrand along the real axis -/

/-- The derivative of the real segment `t ↦ t`, viewed as a curve in `ℂ`, is `1`. -/
private theorem deriv_ofReal_id (t : ℝ) : deriv (fun t : ℝ => (t : ℂ)) t = 1 := by
  simpa using ((hasDerivAt_id t).ofReal_comp).deriv

/-- **The real and imaginary parts of the Dirichlet integrand along the real axis.** For real `t`,
`e^{iat}/t = cos (a t)/t + i · sin (a t)/t`. Both sides are `0` at `t = 0` under the
division-by-zero convention, so no hypothesis on `t` is needed. -/
theorem dirichletIntegrand_ofReal (a t : ℝ) :
    dirichletIntegrand a (t : ℂ) =
      ((Real.cos (a * t) / t : ℝ) : ℂ) + ((Real.sin (a * t) / t : ℝ) : ℂ) * Complex.I := by
  have hexp : Complex.exp (Complex.I * (a : ℂ) * (t : ℂ))
      = ((Real.cos (a * t) : ℝ) : ℂ) + ((Real.sin (a * t) : ℝ) : ℂ) * Complex.I := by
    rw [show Complex.I * (a : ℂ) * (t : ℂ) = ((a * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [dirichletIntegrand_eq, hexp, Complex.ofReal_div, Complex.ofReal_div]
  ring

/-- The imaginary part of the Dirichlet integrand along the real axis is bounded by the frequency:
`|sin (a t) / t| ≤ |a|`, since `|sin u| ≤ |u|`. This is what keeps the imaginary part an ordinary
integral rather than a principal value. -/
theorem abs_sin_mul_div_le (a t : ℝ) : |Real.sin (a * t) / t| ≤ |a| := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · rw [abs_div, div_le_iff₀ (abs_pos.mpr ht)]
    calc |Real.sin (a * t)| ≤ |a * t| := Real.abs_sin_le_abs
      _ = |a| * |t| := abs_mul a t

/-- Off the excised `ε`-ball the real part is bounded by `ε⁻¹`, since `|cos| ≤ 1`. -/
private theorem abs_truncated_cos_mul_div_le (hε : 0 < ε) (a t : ℝ) :
    |if ε < |t| then Real.cos (a * t) / t else 0| ≤ ε⁻¹ := by
  split
  · rename_i ht
    have ht0 : (0 : ℝ) < |t| := hε.trans ht
    rw [abs_div]
    calc |Real.cos (a * t)| / |t| ≤ 1 / |t| := by gcongr; exact Real.abs_cos_le_one _
      _ ≤ 1 / ε := one_div_le_one_div_of_le hε ht.le
      _ = ε⁻¹ := one_div ε
  · simpa using (inv_pos.mpr hε).le

/-- The excision window `{t | ε < |t|}` is measurable. -/
private theorem measurableSet_excision (ε : ℝ) : MeasurableSet {t : ℝ | ε < |t|} :=
  measurableSet_lt measurable_const (by fun_prop)

/-! ### Integrability of the excised real parts -/

/-- A bounded measurable real function is interval-integrable: it is dominated by a constant, and
constants are interval-integrable for the (locally finite) Lebesgue measure. -/
private theorem intervalIntegrable_of_measurable_of_abs_le {g : ℝ → ℝ} {C x y : ℝ}
    (hg : Measurable g) (hb : ∀ t, |g t| ≤ C) :
    IntervalIntegrable g volume x y :=
  (intervalIntegrable_const (c := C)).mono_fun hg.aestronglyMeasurable
    (.of_forall fun t => by simpa [Real.norm_eq_abs] using (hb t).trans (le_abs_self C))

/-- Interval integrability transfers along the inclusion `ℝ → ℂ`. -/
private theorem intervalIntegrable_ofReal {g : ℝ → ℝ} {x y : ℝ}
    (h : IntervalIntegrable g volume x y) :
    IntervalIntegrable (fun t => ((g t : ℝ) : ℂ)) volume x y :=
  ⟨h.1.ofReal, h.2.ofReal⟩

/-- `t ↦ sin (a t) / t` is interval-integrable: measurable and bounded by `|a|`. -/
theorem intervalIntegrable_sin_mul_div (a x y : ℝ) :
    IntervalIntegrable (fun t => Real.sin (a * t) / t) volume x y :=
  intervalIntegrable_of_measurable_of_abs_le (by fun_prop) (abs_sin_mul_div_le a)

private theorem intervalIntegrable_truncated_sin (a ε x y : ℝ) :
    IntervalIntegrable (fun t => if ε < |t| then Real.sin (a * t) / t else 0) volume x y := by
  refine intervalIntegrable_of_measurable_of_abs_le (C := |a|)
    (Measurable.ite (measurableSet_excision ε) (by fun_prop) measurable_const) fun t => ?_
  split
  · exact abs_sin_mul_div_le a t
  · simp

private theorem intervalIntegrable_truncated_cos (a x y : ℝ) (hε : 0 < ε) :
    IntervalIntegrable (fun t => if ε < |t| then Real.cos (a * t) / t else 0) volume x y :=
  intervalIntegrable_of_measurable_of_abs_le (C := ε⁻¹)
    (Measurable.ite (measurableSet_excision ε) (by fun_prop) measurable_const)
    (abs_truncated_cos_mul_div_le hε a)

/-! ### The two halves of the excised integral -/

/-- Off the excised `ε`-ball the real part of the Dirichlet integrand is **odd**, so it integrates
to `0` over the symmetric interval `[-R, R]` — for every `ε` and every `R`. This exact
cancellation is what makes the principal value exist even though `∫ dt / t` diverges at the
origin. -/
theorem integral_truncated_cos_mul_div_eq_zero (a ε R : ℝ) :
    (∫ t in -R..R, if ε < |t| then Real.cos (a * t) / t else 0) = 0 := by
  set g : ℝ → ℝ := fun t => if ε < |t| then Real.cos (a * t) / t else 0 with hg
  have hodd : ∀ t : ℝ, g (-t) = -g t := by
    intro t
    simp only [hg, abs_neg, mul_neg, Real.cos_neg, div_neg]
    split <;> simp
  have hneg : (∫ t in -R..R, g (-t)) = ∫ t in -R..R, g t := by simp
  rw [show (∫ t in -R..R, g (-t)) = ∫ t in -R..R, -g t from by simp only [hodd],
    intervalIntegral.integral_neg] at hneg
  linarith

/-- The imaginary part needs **no** excision in the limit: `sin (a t) / t` is bounded by `|a|`, so
dominated convergence lets the excised integrals converge to the ordinary integral as `ε → 0⁺`. -/
theorem tendsto_integral_truncated_sin_mul_div (a : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun ε : ℝ => ∫ t in -R..R, if ε < |t| then Real.sin (a * t) / t else 0)
      (𝓝[>] 0) (𝓝 (∫ t in -R..R, Real.sin (a * t) / t)) := by
  have hle : (-R : ℝ) ≤ R := by linarith
  simp only [intervalIntegral.integral_of_le hle]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => |a|) ?_ ?_ ?_ ?_
  · filter_upwards with ε
    exact (Measurable.ite (measurableSet_excision ε) (by fun_prop)
      measurable_const).aestronglyMeasurable
  · filter_upwards with ε
    filter_upwards with t
    rw [Real.norm_eq_abs]
    split
    · exact abs_sin_mul_div_le a t
    · simp
  · exact (intervalIntegrable_const (a := -R) (b := R) (c := |a|)).1
  · -- the excision is eventually inert at every `t ≠ 0`, and `{0}` is null
    filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton (0 : ℝ)))] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds (abs_pos.mpr ht0))] with ε hε
    exact (ite_eq_left hε).symm

/-! ### The principal value along the real segment, evaluated twice -/

/-- The `ε`-excised Dirichlet integrand along the real segment, split into its two real parts. -/
private theorem truncated_dirichletIntegrand_ofReal (a ε t : ℝ) :
    (if ‖(t : ℂ) - 0‖ > ε then dirichletIntegrand a (t : ℂ) *
        deriv (fun t : ℝ => (t : ℂ)) t else 0)
      = ((if ε < |t| then Real.cos (a * t) / t else 0 : ℝ) : ℂ)
        + ((if ε < |t| then Real.sin (a * t) / t else 0 : ℝ) : ℂ) * Complex.I := by
  rw [sub_zero, Complex.norm_real, Real.norm_eq_abs, deriv_ofReal_id, mul_one]
  split
  · exact dirichletIntegrand_ofReal a t
  · simp

private theorem intervalIntegrable_truncated_dirichlet (a R : ℝ) (hε : 0 < ε) :
    IntervalIntegrable (fun t : ℝ => if ‖(t : ℂ) - 0‖ > ε then
      dirichletIntegrand a (t : ℂ) * deriv (fun t : ℝ => (t : ℂ)) t else 0) volume (-R) R := by
  simp only [truncated_dirichletIntegrand_ofReal]
  exact (intervalIntegrable_ofReal (intervalIntegrable_truncated_cos a (-R) R hε)).add
    ((intervalIntegrable_ofReal (intervalIntegrable_truncated_sin a ε (-R) R)).mul_const _)

/-- The excised integral along the real segment is `i` times the excised integral of
`sin (a t) / t`: the real part drops out by oddness. -/
private theorem integral_truncated_dirichletIntegrand_ofReal (a R : ℝ) (hε : 0 < ε) :
    (∫ t in -R..R, if ‖(t : ℂ) - 0‖ > ε then dirichletIntegrand a (t : ℂ) *
        deriv (fun t : ℝ => (t : ℂ)) t else 0)
      = ((∫ t in -R..R, if ε < |t| then Real.sin (a * t) / t else 0 : ℝ) : ℂ) * Complex.I := by
  calc (∫ t in -R..R, if ‖(t : ℂ) - 0‖ > ε then dirichletIntegrand a (t : ℂ) *
          deriv (fun t : ℝ => (t : ℂ)) t else 0)
      = ∫ t in -R..R, (((if ε < |t| then Real.cos (a * t) / t else 0 : ℝ) : ℂ)
          + ((if ε < |t| then Real.sin (a * t) / t else 0 : ℝ) : ℂ) * Complex.I) := by
        simp only [truncated_dirichletIntegrand_ofReal]
    _ = (∫ t in -R..R, ((if ε < |t| then Real.cos (a * t) / t else 0 : ℝ) : ℂ))
          + ∫ t in -R..R, ((if ε < |t| then Real.sin (a * t) / t else 0 : ℝ) : ℂ) * Complex.I :=
        intervalIntegral.integral_add
          (intervalIntegrable_ofReal (intervalIntegrable_truncated_cos a (-R) R hε))
          ((intervalIntegrable_ofReal (intervalIntegrable_truncated_sin a ε (-R) R)).mul_const _)
    _ = ((∫ t in -R..R, if ε < |t| then Real.sin (a * t) / t else 0 : ℝ) : ℂ) * Complex.I := by
        rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_ofReal, integral_truncated_cos_mul_div_eq_zero]
        simp

/-- **The principal value along the real segment, evaluated directly.** For every frequency `a`
and every radius `R ≥ 0`, the Cauchy principal value of `e^{iat}/t` along `[-R, R]`, excising the
origin symmetrically, is `i` times the ordinary integral of `sin (a t) / t`.

Both defining clauses come from the split of the integrand into `cos (a t)/t + i · sin (a t)/t`:
the excised real part integrates to `0` by oddness for every `ε`, while the imaginary part is
bounded and its excised integrals converge by dominated convergence. No positivity of `a` is
needed. -/
theorem hasCauchyPVAt_dirichletIntegrand_realSegment (a : ℝ) (hR : 0 ≤ R) :
    HasCauchyPVAt (fun t : ℝ => (t : ℂ)) (-R) R (dirichletIntegrand a) 0
      (((∫ t in -R..R, Real.sin (a * t) / t : ℝ) : ℂ) * Complex.I) := by
  refine HasCauchyPVAt.intro ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact intervalIntegrable_truncated_dirichlet a R hε
  · refine Tendsto.congr' ?_ (((Complex.continuous_ofReal.tendsto _).comp
      (tendsto_integral_truncated_sin_mul_div a hR)).mul_const Complex.I)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (integral_truncated_dirichletIntegrand_ofReal a R hε).symm

/-- **The two evaluations agree.** Comparing the direct evaluation above with the half-disc
evaluation of `Dirichlet.lean` through uniqueness of the principal value turns the complex
identity into a real one: for each radius, `i · ∫_{-R}^{R} sin (a t)/t dt` is `π i` minus the arc
contribution. -/
theorem integral_sin_mul_div_symm_eq (a : ℝ) (hR : 0 < R) :
    ((∫ t in -R..R, Real.sin (a * t) / t : ℝ) : ℂ) * Complex.I
      = (Real.pi : ℂ) * Complex.I
        - ∫ θ in (0 : ℝ)..Real.pi,
            dirichletIntegrand a (circleMap 0 R θ) * deriv (circleMap 0 R) θ :=
  HasCauchyPV.unique (hasCauchyPVAt_dirichletIntegrand_realSegment a hR.le).hasCauchyPV
    (hasCauchyPV_realSegment_dirichlet a hR)

/-! ### The improper integral -/

/-- **The symmetric Dirichlet integral.** For a positive frequency the integrals over `[-R, R]`
converge to `π`: Jordan's lemma kills the arc contribution of `integral_sin_mul_div_symm_eq`. -/
theorem tendsto_integral_sin_mul_div_symm_atTop (ha : 0 < a) :
    Tendsto (fun R : ℝ => ∫ t in -R..R, Real.sin (a * t) / t) atTop (𝓝 Real.pi) := by
  have harc : Tendsto (fun R : ℝ => (Real.pi : ℂ) * Complex.I -
      ∫ θ in (0 : ℝ)..Real.pi,
        dirichletIntegrand a (circleMap 0 R θ) * deriv (circleMap 0 R) θ)
      atTop (𝓝 ((Real.pi : ℂ) * Complex.I)) := by
    simpa using tendsto_const_nhds.sub (tendsto_integral_arc_dirichlet_atTop ha)
  have hmul : Tendsto
      (fun R : ℝ => ((∫ t in -R..R, Real.sin (a * t) / t : ℝ) : ℂ) * Complex.I)
      atTop (𝓝 ((Real.pi : ℂ) * Complex.I)) := by
    refine harc.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact (integral_sin_mul_div_symm_eq a hR).symm
  have hcast : Tendsto (fun R : ℝ => ((∫ t in -R..R, Real.sin (a * t) / t : ℝ) : ℂ))
      atTop (𝓝 ((Real.pi : ℝ) : ℂ)) := by
    have h := hmul.mul_const (-Complex.I)
    simpa [mul_assoc, Complex.I_mul_I] using h
  simpa [Function.comp_def] using (Complex.continuous_re.tendsto ((Real.pi : ℝ) : ℂ)).comp hcast

/-- The integrand `t ↦ sin (a t) / t` is even, so the symmetric integral is twice the integral
over `[0, R]`. -/
private theorem integral_sin_mul_div_symm_eq_two_mul (a R : ℝ) :
    (∫ t in -R..R, Real.sin (a * t) / t) = 2 * ∫ t in (0 : ℝ)..R, Real.sin (a * t) / t := by
  have heven : ∀ t : ℝ, Real.sin (a * -t) / -t = Real.sin (a * t) / t := by
    intro t
    rw [mul_neg, Real.sin_neg, neg_div_neg_eq]
  have hhalf : (∫ t in (-R : ℝ)..0, Real.sin (a * t) / t)
      = ∫ t in (0 : ℝ)..R, Real.sin (a * t) / t := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := R)
      fun t => Real.sin (a * t) / t
    simp only [heven, neg_zero] at h
    exact h.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_sin_mul_div a (-R) 0) (intervalIntegrable_sin_mul_div a 0 R), hhalf]
  ring

/-- **The Dirichlet integral, for an arbitrary positive frequency.**
`∫_0^R sin (a x) / x dx → π / 2` as `R → ∞`, for every `a > 0` — the value is independent of the
frequency. This is the Hungerbühler--Wasem motivating application: the pole of `e^{iaz}/z` sits
*on* the contour of integration, so the classical residue theorem does not reach this integral,
and the generalized theorem weights the residue by the winding number `½` of a point on a smooth
arc.

The limit is genuinely improper: `x ↦ sin (a x) / x` is not Lebesgue integrable on `[0, ∞)`, so
this is a statement about the truncated integrals and not about an integral over `Ioi 0`. -/
theorem tendsto_integral_sin_mul_div_atTop (ha : 0 < a) :
    Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, Real.sin (a * x) / x) atTop (𝓝 (Real.pi / 2)) := by
  have h := tendsto_integral_sin_mul_div_symm_atTop ha
  simp only [integral_sin_mul_div_symm_eq_two_mul] at h
  have h2 := h.const_mul (2⁻¹ : ℝ)
  have hfun : ∀ R : ℝ, (2 : ℝ)⁻¹ * (2 * ∫ x in (0 : ℝ)..R, Real.sin (a * x) / x)
      = ∫ x in (0 : ℝ)..R, Real.sin (a * x) / x := fun R => by ring
  simp only [hfun] at h2
  rwa [show Real.pi / 2 = 2⁻¹ * Real.pi from by ring]

/-- **The Dirichlet integral**: `∫_0^R sin x / x dx → π / 2` as `R → ∞`. -/
theorem tendsto_integral_sin_div_atTop :
    Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, Real.sin x / x) atTop (𝓝 (Real.pi / 2)) := by
  simpa using tendsto_integral_sin_mul_div_atTop one_pos

/-- **The Dirichlet integral in Mathlib's `Real.sinc` spelling.** The two integrands differ only
at the single point `0`, so the integrals agree. -/
theorem tendsto_integral_sinc_atTop :
    Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, Real.sinc x) atTop (𝓝 (Real.pi / 2)) := by
  refine tendsto_integral_sin_div_atTop.congr fun R => ?_
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with x hx _
  exact (Real.sinc_of_ne_zero (by simpa using hx)).symm

end TauCeti.Contour

end

end
