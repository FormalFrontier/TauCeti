/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex, The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
import TauCeti.Probability.Distributions.PDFInstances
import TauCeti.MeasureTheory.Integral.ExpDecay

/-!
# Elementary theory of the exponential distribution

This file completes the elementary moment, transform, and tail API for Mathlib's exponential
measure, parametrized by its rate. For a positive rate `r`, it evaluates all moments, identifies
the exact exponential-moment domain, computes the moment- and cumulant-generating functions and the
characteristic function, and deduces the mean and variance. It also establishes the memoryless
property and computes the law of the minimum of independent exponentials.

**Moments come from one formula.** `integral_pow_expMeasure` computes every moment,
`∫ x ^ n ∂(expMeasure r) = n ! / r ^ n`, and the mean and second moment are its `n = 1` and `n = 2`
specializations.

**The engine is `TauCeti.MeasureTheory.Integral.ExpDecay`.** `integral_pow_mul_exp_neg_mul_Ioi`
evaluates `∫ t in Ioi 0, t ^ n * exp (-(a * t))` as `n ! / a ^ (n + 1)`,
`integrableOn_pow_mul_exp_neg_mul_Ioi` supplies the matching integrability, and
`integrableOn_exp_mul_Ioi_iff` identifies the exact exponential-integrability domain.

## Main results

* `integrable_pow_expMeasure` — every moment is integrable, for `0 < r`;
* `integral_pow_expMeasure` — the `n`-th moment, `n ! / r ^ n`, for `0 < r`;
* `integral_id_expMeasure`, `integral_sq_expMeasure` — the mean and the second moment;
* `variance_id_expMeasure` — the variance `(r ^ 2)⁻¹`;
* `integrable_exp_mul_expMeasure_iff` — exact exponential integrability threshold `t < r`;
* `integrableExpSet_id_expMeasure`, `integrableExpSet_fun_id_expMeasure` — exact domain `(-∞, r)`;
* `mgf_id_expMeasure`, `mgf_fun_id_expMeasure` — moment-generating function `r / (r - t)`;
* `cgf_id_expMeasure` — cumulant-generating function `log (r / (r - t))`;
* `charFun_expMeasure` — characteristic function `(r : ℂ) / (r - I * t)`;
* `measureReal_Ioi_expMeasure`, `measure_Ioi_expMeasure` — tail probabilities;
* `memoryless_expMeasure` — the conditional tail is unchanged by elapsed time;
* `hasLaw_min_expMeasure_of_indepFun` — minimum of independent exponentials.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 1, exponential.
* [mathlib4#35504](https://github.com/leanprover-community/mathlib4/pull/35504) by Joakim
  Björnander (Apache 2.0), the upstream exponential mgf, moments and memorylessness work that the
  roadmap names as the source for this material. It has not landed at Tau Ceti's current Mathlib
  pin, so the names, the theorem shapes, and the real-integral proof pattern of the mgf, moment
  and memorylessness results below are adapted from it, and they should be dropped once the pin
  provides them.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal Topology

namespace TauCeti

namespace Probability

variable {a r s t : ℝ} {n : ℕ}

/-- The exponential density in closed form. Kept private: it only unfolds Mathlib's definition
through `gammaPDFReal 1`, so it is a proof convenience rather than API. -/
private theorem exponentialPDFReal_apply (x : ℝ) :
    exponentialPDFReal r x = if 0 ≤ x then r * exp (-(r * x)) else 0 := by
  rw [exponentialPDFReal, gammaPDFReal]
  split_ifs with hx
  · rw [Real.rpow_one, Real.Gamma_one, sub_self, Real.rpow_zero]
    ring
  · rfl

/-- The `ℝ≥0∞` density at rate `r`, read as a real number, is `exponentialPDFReal`. -/
private theorem toReal_gammaPDF_one (hr : 0 < r) (x : ℝ) :
    (gammaPDF 1 r x).toReal = exponentialPDFReal r x := by
  unfold gammaPDF exponentialPDFReal
  rw [ENNReal.toReal_ofReal (gammaPDFReal_nonneg one_pos hr x)]

/-- `expMeasure r` is the Lebesgue measure weighted by the Gamma density of shape `1`.

`rfl` closes this because both steps it crosses are definitional unfoldings: `expMeasure r` is
`gammaMeasure 1 r`, which is `volume.withDensity (gammaPDF 1 r)`. The density is left in its
`gammaPDF` spelling, the one `measurable_gammaPDF` and `toReal_gammaPDF_one` are stated in. -/
private lemma expMeasure_eq_withDensity (r : ℝ) :
    expMeasure r = volume.withDensity (gammaPDF 1 r) := rfl

/-- The density weight against `exp (t * x)`. This one identity is the integrand algebra behind
both the moment-generating function and the exact integrability domain below. -/
private lemma density_mul_exp (r t x : ℝ) :
    r * exp (-(r * x)) * exp (t * x) = r * exp ((t - r) * x) := by
  rw [mul_assoc, ← exp_add, show -(r * x) + t * x = (t - r) * x from by ring]

/-- Every integral against `expMeasure r` is the half-line integral of the integrand weighted by
the exponential density. This is the single reduction used by the moment and transform
computations below. -/
private lemma integral_expMeasure_Ioi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hr : 0 < r) (f : ℝ → E) :
    ∫ x, f x ∂(expMeasure r) = ∫ x in Ioi 0, (r * exp (-(r * x))) • f x := by
  rw [expMeasure_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul (measurable_gammaPDF 1 r)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hIci :
      ∫ x, (gammaPDF 1 r x).toReal • f x =
        ∫ x in Ici 0, (gammaPDF 1 r x).toReal • f x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [toReal_gammaPDF_one hr, exponentialPDFReal_apply,
        ite_eq_right (by simpa [mem_Ici] using hx), zero_smul]).symm
  have hdens :
      ∫ x in Ici 0, (gammaPDF 1 r x).toReal • f x =
        ∫ x in Ici 0, (r * exp (-(r * x))) • f x :=
    setIntegral_congr_fun measurableSet_Ici fun x hx => by
      rw [toReal_gammaPDF_one hr, exponentialPDFReal_apply, ite_eq_left (mem_Ici.mp hx)]
  rw [hIci, hdens, integral_Ici_eq_integral_Ioi]

/-- The moment integrand is the Gamma integrand supported on `Ioi 0`. This needs `n ≠ 0`: at
`n = 0` the left side is the density itself, which does not vanish at the origin. -/
private theorem integrand_eq_indicator (hn : n ≠ 0) :
    (fun x => exponentialPDFReal r x * x ^ n)
      = (Ioi (0:ℝ)).indicator (fun x => r * (x ^ n * exp (-(r * x)))) := by
  funext x
  by_cases hx : (0:ℝ) < x
  · rw [Set.indicator_of_mem (mem_Ioi.mpr hx), exponentialPDFReal_apply]
    split_ifs with h
    · ring
    · exact absurd hx.le h
  · rw [Set.indicator_of_notMem (by simpa using hx), exponentialPDFReal_apply]
    have hx' : x ≤ 0 := not_lt.mp hx
    split_ifs with h
    · have hx0 : x = 0 := le_antisymm hx' h
      rw [hx0, zero_pow hn, mul_zero]
    · ring

/-- Integrability against `expMeasure` is integrability of the density product against `volume`. -/
private theorem integrable_expMeasure_iff (hr : 0 < r) (g : ℝ → ℝ) :
    Integrable g (expMeasure r)
      ↔ Integrable (fun x => exponentialPDFReal r x * g x) volume := by
  have htoReal : ∀ x : ℝ, g x * (gammaPDF 1 r x).toReal = exponentialPDFReal r x * g x := by
    intro x
    rw [toReal_gammaPDF_one hr]
    ring
  rw [expMeasure_eq_withDensity,
    integrable_withDensity_iff (measurable_gammaPDF 1 r)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    funext htoReal]

/-- **Every moment of the exponential law is integrable.** This is not implied by the moment
formula below: Lean's integral is defined for non-integrable functions too, so an integral equality
alone says nothing about finiteness. -/
@[simp]
theorem integrable_pow_expMeasure (hr : 0 < r) (n : ℕ) :
    Integrable (fun x => x ^ n) (expMeasure r) := by
  have hprob : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [integrable_expMeasure_iff hr, integrand_eq_indicator hn,
    integrable_indicator_iff measurableSet_Ioi]
  exact (integrableOn_pow_mul_exp_neg_mul_Ioi n hr).const_mul r

/-- **The moments of the exponential law.** `∫ x ^ n ∂(expMeasure r) = n ! / r ^ n`, for every `n`.

No nondegeneracy hypothesis on `n` is needed: at `n = 0` both sides are `1`. The mean and the
second moment below are the `n = 1` and `n = 2` cases. -/
@[simp]
theorem integral_pow_expMeasure (hr : 0 < r) (n : ℕ) :
    ∫ x, x ^ n ∂(expMeasure r) = (Nat.factorial n : ℝ) / r ^ n := by
  have hr0 : r ≠ 0 := hr.ne'
  have hint : ∀ x : ℝ, (r * exp (-(r * x))) • x ^ n = r * (x ^ n * exp (-(r * x))) := by
    intro x
    rw [smul_eq_mul]
    ring
  rw [integral_expMeasure_Ioi hr]
  simp only [hint]
  rw [integral_const_mul, integral_pow_mul_exp_neg_mul_Ioi n hr, pow_succ]
  field_simp

/-- **The mean of the exponential law** with rate `r` is `r⁻¹`. -/
@[simp]
theorem integral_id_expMeasure (hr : 0 < r) : ∫ x, x ∂(expMeasure r) = r⁻¹ := by
  simpa using integral_pow_expMeasure hr 1

/-- The second moment of the exponential law with rate `r` is `2 / r ^ 2`. -/
theorem integral_sq_expMeasure (hr : 0 < r) : ∫ x, x ^ 2 ∂(expMeasure r) = 2 / r ^ 2 := by
  simpa using integral_pow_expMeasure hr 2

/-- **The variance of the exponential law** with rate `r` is `(r ^ 2)⁻¹`. -/
@[simp]
theorem variance_id_expMeasure (hr : 0 < r) : Var[id; expMeasure r] = (r ^ 2)⁻¹ := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have h₂ : Integrable (fun x => id x ^ 2) (expMeasure r) :=
    integrable_pow_expMeasure hr 2
  have hLp : MemLp id 2 (expMeasure r) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 h₂
  rw [variance_eq_sub hLp]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_sq_expMeasure hr, integral_id_expMeasure hr]
  field_simp
  ring

/-- **The exact exponential-integrability threshold.** The integrand `exp (t * x)` is integrable
against an exponential law with positive rate `r` exactly when `t < r`. -/
@[simp]
lemma integrable_exp_mul_expMeasure_iff (hr : 0 < r) :
    Integrable (fun x => exp (t * x)) (expMeasure r) ↔ t < r := by
  rw [integrable_expMeasure_iff hr]
  have hfun : (fun x : ℝ => exponentialPDFReal r x * exp (t * x)) =
      (Set.Ici (0 : ℝ)).indicator (fun x => r * exp ((t - r) * x)) := by
    funext x
    rw [exponentialPDFReal_apply]
    by_cases hx : (0 : ℝ) ≤ x
    · have hxmem : x ∈ Ici 0 := hx
      rw [Set.indicator_of_mem hxmem, ite_eq_left hx, density_mul_exp]
    · have hxmem : x ∉ Ici 0 := hx
      rw [Set.indicator_of_notMem hxmem, ite_eq_right hx, zero_mul]
  -- `integrable_const_mul_iff` is an `Integrable` lemma; the `have` bridges it to `IntegrableOn`,
  -- which is that statement for the restricted measure, without unfolding the goal.
  have hconst : IntegrableOn (fun x : ℝ => r * exp ((t - r) * x)) (Ioi 0) ↔
      IntegrableOn (fun x : ℝ => exp ((t - r) * x)) (Ioi 0) :=
    integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hr.ne') _
  rw [hfun, integrable_indicator_iff measurableSet_Ici,
    integrableOn_Ici_iff_integrableOn_Ioi, hconst,
    TauCeti.integrableOn_exp_mul_Ioi_iff, sub_lt_zero]

/-- **The exact exponential-integrability domain** of an exponential law with positive rate is
`(-∞, r)`. This is the `fun x => x` spelling of the identity, in which the computation is done;
`integrableExpSet_id_expMeasure` is the same statement with `id`. -/
@[simp]
theorem integrableExpSet_fun_id_expMeasure (hr : 0 < r) :
    integrableExpSet (fun x : ℝ => x) (expMeasure r) = Set.Iio r := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, mem_Iio]
  exact integrable_exp_mul_expMeasure_iff (r := r) (t := t) hr

/-- **The exact exponential-integrability domain** of an exponential law with positive rate is
`(-∞, r)`. This is the `id` spelling, the form a `HasLaw` consumer meets and the one the roadmap
names; use `integrableExpSet_fun_id_expMeasure` for goals in which the identity is eta-expanded. -/
@[simp]
theorem integrableExpSet_id_expMeasure (hr : 0 < r) :
    integrableExpSet id (expMeasure r) = Set.Iio r :=
  integrableExpSet_fun_id_expMeasure hr

/-- **The moment-generating function of an exponential law** with positive rate, on its finiteness
domain `t < r`. This is the `fun x => x` spelling, in which the computation is done;
`mgf_id_expMeasure` is the same statement with `id`. -/
theorem mgf_fun_id_expMeasure (hr : 0 < r) (ht : t < r) :
    mgf (fun x : ℝ => x) (expMeasure r) t = r / (r - t) := by
  have h : ∫ x : ℝ, exp (t * x) ∂(expMeasure r) = r / (r - t) := by
    have hint : ∀ x : ℝ, (r * exp (-(r * x))) • exp (t * x) = r * exp ((t - r) * x) := by
      intro x
      rw [smul_eq_mul, density_mul_exp]
    rw [integral_expMeasure_Ioi hr]
    simp only [hint]
    rw [integral_const_mul, integral_exp_mul_Ioi (sub_neg.mpr ht) 0, mul_zero, exp_zero,
      show t - r = -(r - t) from by ring, neg_div_neg_eq, mul_one_div]
  simpa [mgf] using h

/-- **The moment-generating function of an exponential law** with positive rate, on its finiteness
domain `t < r`. This is the `id` spelling of `mgf_fun_id_expMeasure`, and is the form the `cgf`
below and a `HasLaw` consumer meet. -/
theorem mgf_id_expMeasure (hr : 0 < r) (ht : t < r) :
    mgf id (expMeasure r) t = r / (r - t) :=
  mgf_fun_id_expMeasure hr ht

/-- The cumulant-generating function of an exponential law with positive rate. -/
theorem cgf_id_expMeasure (hr : 0 < r) (ht : t < r) :
    cgf id (expMeasure r) t = log (r / (r - t)) := by
  rw [cgf, mgf_id_expMeasure hr ht]

/-- The characteristic function of an exponential law with positive rate. -/
theorem charFun_expMeasure (hr : 0 < r) (t : ℝ) :
    charFun (expMeasure r) t = (r : ℂ) / (r - Complex.I * t) := by
  have hint : ∀ x : ℝ, (r * exp (-(r * x))) • Complex.exp (t * x * Complex.I) =
      (r : ℂ) * Complex.exp ((-(r : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)) := by
    intro x
    have hexp : (-(r : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)
        = ((-(r * x) : ℝ) : ℂ) + (t : ℝ) * (x : ℝ) * Complex.I := by
      push_cast
      ring
    rw [hexp, Complex.exp_add, ← Complex.ofReal_exp, Complex.real_smul]
    push_cast
    ring
  rw [charFun_apply_real, integral_expMeasure_Ioi hr]
  simp only [hint]
  rw [integral_const_mul,
    integral_exp_mul_complex_Ioi (by simpa using neg_lt_zero.mpr hr) 0,
    Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    show (-(r : ℂ) + (t : ℂ) * Complex.I) = -((r : ℂ) - Complex.I * (t : ℂ)) from by ring,
    neg_div_neg_eq, mul_one_div]

/-- The real-valued tail probability of a positive-rate exponential law. -/
lemma measureReal_Ioi_expMeasure (hr : 0 < r) (x : ℝ) :
    (expMeasure r).real (Ioi x) = if 0 ≤ x then exp (-(r * x)) else 1 := by
  have _ : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ, ← cdf_eq_real,
    cdf_expMeasure_eq hr x]
  by_cases hx : 0 ≤ x
  · rw [ite_eq_left hx, ite_eq_left hx]
    ring
  · rw [ite_eq_right hx, ite_eq_right hx]
    ring

/-- The tail probability of a positive-rate exponential law. -/
lemma measure_Ioi_expMeasure (hr : 0 < r) (x : ℝ) :
    (expMeasure r) (Ioi x) = ENNReal.ofReal (if 0 ≤ x then exp (-(r * x)) else 1) := by
  have _ : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  rw [← measureReal_Ioi_expMeasure hr x, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The memoryless property of a positive-rate exponential law, stated with conditional
probability: after surviving for time `s`, the chance of surviving a further time `t` is the
original tail probability at `t`. -/
theorem memoryless_expMeasure (hr : 0 < r) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    cond (expMeasure r) (Ioi s) (Ioi (s + t)) = (expMeasure r) (Ioi t) := by
  have hst : Ioi s ∩ Ioi (s + t) = Ioi (s + t) := by
    rw [Set.inter_eq_right]
    intro x hx
    exact lt_of_le_of_lt (le_add_of_nonneg_right ht) hx
  rw [cond_apply measurableSet_Ioi, hst, measure_Ioi_expMeasure hr s,
    measure_Ioi_expMeasure hr (s + t), measure_Ioi_expMeasure hr t,
    ite_eq_left hs, ite_eq_left (add_nonneg hs ht), ite_eq_left ht]
  rw [← ENNReal.ofReal_inv_of_pos (exp_pos _), ← ENNReal.ofReal_mul (by positivity),
    ← Real.exp_neg, ← Real.exp_add,
    show -(-(r * s)) + -(r * (s + t)) = -(r * t) from by ring]

/-- The minimum of two independent random variables with exponential laws has an exponential law
whose rate is the sum of their rates. -/
theorem hasLaw_min_expMeasure_of_indepFun {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : Ω → ℝ} (hr : 0 < r) (hs : 0 < s)
    (hXY : IndepFun X Y P) (hX : HasLaw X (expMeasure r) P)
    (hY : HasLaw Y (expMeasure s) P) :
    HasLaw (fun ω => min (X ω) (Y ω)) (expMeasure (r + s)) P := by
  have hmin : AEMeasurable (fun ω => min (X ω) (Y ω)) P :=
    hX.aemeasurable.min hY.aemeasurable
  have _ : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have _ : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have _ : IsProbabilityMeasure (P.map fun ω => min (X ω) (Y ω)) :=
    Measure.isProbabilityMeasure_map hmin
  have _ : IsProbabilityMeasure (expMeasure (r + s)) :=
    isProbabilityMeasure_expMeasure (add_pos hr hs)
  refine ⟨hmin, ?_⟩
  apply Measure.eq_of_cdf
  ext x
  rw [cdf_eq_real, map_measureReal_apply_of_aemeasurable hmin measurableSet_Iic,
    cdf_expMeasure_eq (add_pos hr hs) x]
  have hevent : (fun ω => min (X ω) (Y ω)) ⁻¹' Iic x =
      (X ⁻¹' Ioi x ∩ Y ⁻¹' Ioi x)ᶜ := by
    ext ω
    simp only [mem_preimage, mem_Iic, mem_compl_iff, mem_inter_iff, mem_Ioi,
      not_and_or, not_lt, min_le_iff]
  rw [hevent, measureReal_compl₀
    ((hX.aemeasurable.nullMeasurableSet_preimage measurableSet_Ioi).inter
      (hY.aemeasurable.nullMeasurableSet_preimage measurableSet_Ioi)), probReal_univ]
  have hind := hXY.measure_inter_preimage_eq_mul (Ioi x) (Ioi x)
    measurableSet_Ioi measurableSet_Ioi
  have hindReal := congr_arg ENNReal.toReal hind
  simp only [ENNReal.toReal_mul, ← measureReal_def] at hindReal
  have hXtail : P.real (X ⁻¹' Ioi x) = (expMeasure r).real (Ioi x) :=
    hX.measureReal_eq measurableSet_Ioi
  have hYtail : P.real (Y ⁻¹' Ioi x) = (expMeasure s).real (Ioi x) :=
    hY.measureReal_eq measurableSet_Ioi
  rw [hindReal, hXtail, hYtail, measureReal_Ioi_expMeasure hr x,
    measureReal_Ioi_expMeasure hs x]
  by_cases hx : 0 ≤ x
  · have hexp : -(r * x) + -(s * x) = -((r + s) * x) := by ring
    rw [ite_eq_left hx, ite_eq_left hx, ite_eq_left hx, ← exp_add, hexp]
  · rw [ite_eq_right hx, ite_eq_right hx, ite_eq_right hx]
    norm_num

end Probability

end TauCeti
