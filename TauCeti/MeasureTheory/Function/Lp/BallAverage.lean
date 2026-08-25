/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
-- `Mathlib.MeasureTheory.Group.Integral` is imported privately: translation invariance of the
-- Bochner integral is used only inside the proofs below.
import Mathlib.MeasureTheory.Group.Integral
-- `Mathlib.MeasureTheory.Measure.Prod` is imported privately: Tonelli's theorem
-- appears only inside the proof of `TauCeti.eLpNorm_ballAverage_sub_le`.
import Mathlib.MeasureTheory.Measure.Prod
-- Continuity of composition by measure-preserving maps is used only to prove that ball averages
-- of `Lᵖ` functions are continuous.
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
# The ball average of an `Lᵖ` function

The **ball average** of `f` at scale `r` is

`A_r f x = ⨍ y in Metric.ball x r, f y ∂μ`,

the mean of `f` over the ball of radius `r` centred at `x`. It is the mollification of `f` by the
normalized indicator of a ball, and it is the smoothing operator behind the Fréchet--Kolmogorov
compactness criterion in `Lᵖ`, hence behind Rellich--Kondrachov, Lane A.6 of
`TauCetiRoadmap/PDE/README.md`.

Four estimates are proved here, all for `1 ≤ p < ∞` and an additive Haar measure `μ` on a proper
normed additive group. Writing `V = μ (Metric.ball 0 r)` for the volume of the ball, they are

`‖A_r f x‖ ≤ V ^ (-1/p) ‖f‖_p`,
`‖A_r f (x + e) - A_r f x‖ ≤ V ^ (-1/p) ‖f(· + e) - f‖_p`,
`‖A_r f‖_p ≤ ‖f‖_p`,
`‖A_r f - f‖_p ≤ C` whenever `‖f(· + e) - f‖_p ≤ C` for every `e` in the ball of radius `r`.

For each fixed positive `r`, these estimates send a family with uniformly small `Lᵖ` translation
increments to a uniformly bounded and uniformly equicontinuous family of ball averages. The
equicontinuity bound includes the scale-dependent factor `V ^ (-1/p)`; its remaining modulus is
the original family's uniform `Lᵖ` translation modulus. This is exactly the trade-off that the
Fréchet--Kolmogorov criterion exploits: a family of functions whose translates move little in
`Lᵖ` is uniformly close to a family of uniformly equicontinuous ones.

The first two estimates come from a single Hölder bound,
`TauCeti.enorm_setAverage_le`: the average of `g` over a set `s` of finite positive measure is at
most `μ s ^ (-1/p) ‖g‖_p`. For the first, apply it to `g = f`; for the second, apply it to
`g = f(· + e) - f`, using that the ball average commutes with translation.

The last two are Hölder again, now in the translation variable, followed by Tonelli's theorem;
they share the analytic core `lintegral_enorm_setAverage_rpow_le`. For the contraction, apply it
to `G x e = f (x + e)` and use translation invariance on each slice. For the approximation
estimate, write the deviation as an average,

`A_r f x - f x = ⨍ e in Metric.ball 0 r, (f (x + e) - f x) ∂μ`,

so that its `p`-th power is bounded by `V⁻¹ ∫⁻ e in Metric.ball 0 r, ‖f (x + e) - f x‖ₑ ^ p ∂μ`.
Integrating in `x` and exchanging the two integrations, the inner integral becomes
`‖f(· + e) - f‖_p ^ p`, uniformly at most `C ^ p`, and the factor `V⁻¹` cancels against the
measure of the ball the translation ranges over.

Both the definition and the estimates are stated for a Banach-space-valued `f`. The domain is
assumed proper, which is what makes balls have finite measure; finite-dimensional real normed
spaces are an important special case.

The averages appearing here are the ones the Hardy--Littlewood maximal function
`TauCeti.maximalFunction` takes a supremum of, so `‖A_r f x‖ ≤ M f x` for every `r > 0`. The two
are put to opposite uses: the maximal function discards `r` to get a pointwise majorant of `f`,
while `A_r f` keeps `r` as a smoothing scale and is compared with `f` itself. Nothing below needs
the maximal inequality, so the two developments are kept apart.

## Main declarations

* `TauCeti.ballAverage`: the ball average, with `TauCeti.ballAverage_congr_ae` and
  `TauCeti.ballAverage_eq_setAverage_ball_zero` as its basic interface.
* `TauCeti.ballAverage_const`: the ball average of a constant is that constant, so the
  normalization is the intended one.
* `TauCeti.enorm_setAverage_rpow_le`, `TauCeti.enorm_setAverage_le`: Hölder's bound on an average
  over a set, in `∫⁻` and in `Lᵖ` form.
* `TauCeti.enorm_ballAverage_le`: the `L^∞` bound on `A_r f`.
* `TauCeti.eLpNorm_ballAverage_le`: `A_r` is an `Lᵖ` contraction.
* `TauCeti.ballAverage_comp_add`, `TauCeti.ballAverage_sub_ballAverage`: the ball average
  commutes with translation, and its increment is the ball average of the increment.
* `TauCeti.enorm_ballAverage_add_sub_ballAverage_le`: the equicontinuity estimate, with modulus
  the `Lᵖ` modulus of continuity of `f` itself.
* `TauCeti.continuous_ballAverage`, `TauCeti.memLp_ballAverage`: a ball average at positive
  scale is continuous and remains in `Lᵖ`.
* `TauCeti.ballAverage_sub_self`, `TauCeti.eLpNorm_ballAverage_sub_le`: the deviation of `f` from
  its ball average as an average of increments, and the `Lᵖ` approximation estimate.

## References

Lane A.6 of `TauCetiRoadmap/PDE/README.md`; H. Brezis, *Functional Analysis, Sobolev Spaces and
Partial Differential Equations*, Theorem 4.26 and Lemma 4.3; H. Hanche-Olsen, H. Holden,
*The Kolmogorov--Riesz compactness theorem*, Expo. Math. 28 (2010).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set
open scoped ENNReal

section SetAverage

variable {α F : Type*} [MeasurableSpace α] {mu : Measure α} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {f : α → F} {p : ℝ≥0∞} {s : Set α}

/-- **Hölder's bound on an average**, in `∫⁻` form: the `q`-th power of the average of `f` over a
set `s` of finite positive measure is at most `(μ s)⁻¹` times the integral of `‖f‖ ^ q` over `s`.
The single factor `(μ s)⁻¹` is what survives after the `q`-th power of the normalization
`(μ s)⁻¹` cancels against the `(μ s) ^ (q - 1)` of Hölder's inequality. -/
theorem enorm_setAverage_rpow_le {q : ℝ} (hq : 1 ≤ q) (hf : AEStronglyMeasurable f mu)
    (hs0 : mu s ≠ 0) (hs : mu s ≠ ∞) :
    ‖⨍ y in s, f y ∂mu‖ₑ ^ q ≤ (mu s)⁻¹ * ∫⁻ y in s, ‖f y‖ₑ ^ q ∂mu := by
  have hq0 : (0 : ℝ) < q := one_pos.trans_le hq
  have h0 : ‖⨍ y in s, f y ∂mu‖ₑ ≤ (mu s)⁻¹ * ∫⁻ y in s, ‖f y‖ₑ ∂mu := by
    rw [setAverage_eq, enorm_smul]
    have hinv : ‖(mu.real s)⁻¹‖ₑ = (mu s)⁻¹ := by
      rw [Real.enorm_eq_ofReal (by positivity), measureReal_def, ← ENNReal.toReal_inv,
        ENNReal.ofReal_toReal (by simp [hs0])]
    rw [hinv]
    exact mul_le_mul' le_rfl (enorm_integral_le_lintegral_enorm _)
  have hholder : (∫⁻ y in s, ‖f y‖ₑ ∂mu) ^ q ≤ mu s ^ (q - 1) * ∫⁻ y in s, ‖f y‖ₑ ^ q ∂mu := by
    have := rpow_lintegral_le_measure_univ_rpow_mul (μ := mu.restrict s)
      (u := fun y => ‖f y‖ₑ) hf.restrict.enorm hq
    rwa [Measure.restrict_apply_univ] at this
  have hexp : -q + (q - 1) = (-1 : ℝ) := by ring
  calc ‖⨍ y in s, f y ∂mu‖ₑ ^ q
      ≤ ((mu s)⁻¹ * ∫⁻ y in s, ‖f y‖ₑ ∂mu) ^ q := ENNReal.rpow_le_rpow h0 hq0.le
    _ = (mu s)⁻¹ ^ q * (∫⁻ y in s, ‖f y‖ₑ ∂mu) ^ q := ENNReal.mul_rpow_of_nonneg _ _ hq0.le
    _ ≤ (mu s)⁻¹ ^ q * (mu s ^ (q - 1) * ∫⁻ y in s, ‖f y‖ₑ ^ q ∂mu) := mul_le_mul' le_rfl hholder
    _ = (mu s)⁻¹ * ∫⁻ y in s, ‖f y‖ₑ ^ q ∂mu := by
        rw [← mul_assoc, ENNReal.inv_rpow, ← ENNReal.rpow_neg, ← ENNReal.rpow_add _ _ hs0 hs,
          hexp, ENNReal.rpow_neg_one]

/-- **Hölder's bound on an average**: the average of `f` over a set `s` of finite positive
measure is at most `μ s ^ (-1/p)` times the `Lᵖ` seminorm of `f` on `s`. At `p = 1` this is the
bound by the average of `‖f‖`, and the volume factor sharpens as `p` grows because a larger
exponent controls the mass of `s` more efficiently. -/
theorem enorm_setAverage_le (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : AEStronglyMeasurable f mu)
    (hs0 : mu s ≠ 0) (hs : mu s ≠ ∞) :
    ‖⨍ y in s, f y ∂mu‖ₑ ≤ mu s ^ (-(p.toReal)⁻¹) * eLpNorm f p (mu.restrict s) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hq : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp' hp
  have hq0 : (0 : ℝ) < p.toReal := one_pos.trans_le hq
  have hroot := ENNReal.rpow_le_rpow (enorm_setAverage_rpow_le (q := p.toReal) hq hf hs0 hs)
    (inv_pos.mpr hq0).le
  rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hq0.ne', ENNReal.rpow_one] at hroot
  refine hroot.trans_eq ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.inv_rpow, ← ENNReal.rpow_neg,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp', one_div]

end SetAverage

section Defs

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {mu : Measure E} {f : E → F} {r : ℝ}

/-- The **ball average** of `f` at scale `r`: the mean of `f` over the ball of radius `r`
centred at the point. -/
def ballAverage (mu : Measure E) (r : ℝ) (f : E → F) (x : E) : F := ⨍ y in ball x r, f y ∂mu

/-- The defining equation of the ball average. -/
theorem ballAverage_apply (mu : Measure E) (r : ℝ) (f : E → F) (x : E) :
    ballAverage mu r f x = ⨍ y in ball x r, f y ∂mu := by rw [ballAverage]

/-- The ball average of the zero function is zero. -/
@[simp]
theorem ballAverage_zero (mu : Measure E) (r : ℝ) (x : E) :
    ballAverage mu r (0 : E → F) x = 0 :=
  average_zero (mu.restrict (ball x r))

/-- The ball average commutes with addition when both summands are integrable on the ball. -/
theorem ballAverage_add {g : E → F} {x : E} (hf : IntegrableOn f (ball x r) mu)
    (hg : IntegrableOn g (ball x r) mu) :
    ballAverage mu r (f + g) x = ballAverage mu r f x + ballAverage mu r g x :=
  setAverage_add hf hg

/-- The ball average commutes with subtraction when both terms are integrable on the ball. -/
theorem ballAverage_sub {g : E → F} {x : E} (hf : IntegrableOn f (ball x r) mu)
    (hg : IntegrableOn g (ball x r) mu) :
    ballAverage mu r (f - g) x = ballAverage mu r f x - ballAverage mu r g x :=
  setAverage_sub hf hg

/-- The ball average commutes with scalar multiplication. -/
theorem ballAverage_smul (c : ℝ) (x : E) :
    ballAverage mu r (c • f) x = c • ballAverage mu r f x :=
  average_const_smul (mu.restrict (ball x r)) c f

/-- The ball average depends on `f` only through its almost-everywhere class. -/
theorem ballAverage_congr_ae [OpensMeasurableSpace E] {g : E → F} (h : f =ᵐ[mu] g) :
    ballAverage mu r f = ballAverage mu r g :=
  funext fun _ => setAverage_congr_fun measurableSet_ball (h.mono fun _ hx _ => hx)

end Defs

section Translation

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {mu : Measure E} [mu.IsAddHaarMeasure] {f : E → F}
  {r : ℝ}

/-- Recentring the ball at the origin: the ball average is the average of `f` over the
translates of the point by the vectors of the ball of radius `r`. -/
theorem ballAverage_eq_setAverage_ball_zero (x : E) :
    ballAverage mu r f x = ⨍ e in ball (0 : E) r, f (x + e) ∂mu := by
  have hset : ∀ e : E, (ball (0 : E) r).indicator (fun e => f (x + e)) e =
      (ball x r).indicator f (x + e) := by
    intro e
    by_cases he : e ∈ ball (0 : E) r
    · rw [indicator_of_mem he, indicator_of_mem (by simpa [dist_eq_norm] using he)]
    · rw [indicator_of_notMem he, indicator_of_notMem (by simpa [dist_eq_norm] using he)]
  rw [ballAverage_apply, setAverage_eq, setAverage_eq, Measure.addHaar_real_ball_center,
    ← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]
  congr 1
  rw [integral_congr_ae (Filter.Eventually.of_forall hset), integral_add_left_eq_self]

/-- The ball average commutes with translation. -/
theorem ballAverage_comp_add (e x : E) :
    ballAverage mu r (fun y => f (y + e)) x = ballAverage mu r f (x + e) := by
  rw [ballAverage_eq_setAverage_ball_zero, ballAverage_eq_setAverage_ball_zero]
  exact setAverage_congr_fun measurableSet_ball
    (Filter.Eventually.of_forall fun y _ => by rw [add_right_comm])

end Translation

section Estimates

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {mu : Measure E} [mu.IsAddHaarMeasure] {f : E → F} {p : ℝ≥0∞} {r : ℝ}

omit [BorelSpace E] in
/-- The ball average of a constant is that constant: the normalization is the intended one. -/
@[simp]
theorem ballAverage_const (hr : 0 < r) (c : F) (x : E) :
    ballAverage mu r (fun _ => c) x = c :=
  setAverage_const (measure_ball_pos mu x hr).ne' measure_ball_lt_top.ne c

omit [CompleteSpace F] in
/-- The `L^∞` bound on the ball average: it is controlled by the `Lᵖ` seminorm of `f`, at the
cost of the volume factor `μ (ball 0 r) ^ (-1/p)`, which blows up as `r → 0`. -/
theorem enorm_ballAverage_le (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : AEStronglyMeasurable f mu)
    (hr : 0 < r) (x : E) :
    ‖ballAverage mu r f x‖ₑ ≤ mu (ball (0 : E) r) ^ (-(p.toReal)⁻¹) * eLpNorm f p mu := by
  have hball : mu (ball x r) = mu (ball (0 : E) r) := Measure.addHaar_ball_center mu x r
  rw [ballAverage_apply, ← hball]
  refine (enorm_setAverage_le hp hp' hf (by rw [hball]; exact (measure_ball_pos mu 0 hr).ne')
    (by rw [hball]; exact measure_ball_lt_top.ne)).trans ?_
  exact mul_le_mul' le_rfl (eLpNorm_mono_measure _ Measure.restrict_le_self)

omit [CompleteSpace F] in
/-- The increment of the ball average is the ball average of the increment. -/
theorem ballAverage_sub_ballAverage (hp : 1 ≤ p) (hf : MemLp f p mu) (e x : E) :
    ballAverage mu r f (x + e) - ballAverage mu r f x =
      ballAverage mu r (fun y => f (y + e) - f y) x := by
  have : IsFiniteMeasure (mu.restrict (ball x r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hshift : MemLp (fun y => f (y + e)) p mu :=
    hf.comp_measurePreserving (measurePreserving_add_right mu e)
  rw [← ballAverage_comp_add, ballAverage_apply, ballAverage_apply, ballAverage_apply,
    ← setAverage_sub ((hshift.restrict _).integrable hp) ((hf.restrict _).integrable hp)]
  simp [Pi.sub_apply]

omit [CompleteSpace F] in
/-- **The equicontinuity estimate**: the ball average moves by at most the `Lᵖ` modulus of
continuity of `f` itself, up to the scale-dependent volume factor
`μ (ball 0 r) ^ (-1/p)`. Thus, at each fixed positive `r`, a family whose translates move
uniformly little in `Lᵖ` has uniformly equicontinuous ball averages. -/
theorem enorm_ballAverage_add_sub_ballAverage_le (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : MemLp f p mu)
    (hr : 0 < r) (e x : E) :
    ‖ballAverage mu r f (x + e) - ballAverage mu r f x‖ₑ ≤
      mu (ball (0 : E) r) ^ (-(p.toReal)⁻¹) * eLpNorm (fun y => f (y + e) - f y) p mu := by
  have hshift : MemLp (fun y => f (y + e)) p mu :=
    hf.comp_measurePreserving (measurePreserving_add_right mu e)
  rw [ballAverage_sub_ballAverage hp hf]
  exact enorm_ballAverage_le hp hp'
    (hshift.aestronglyMeasurable.sub hf.aestronglyMeasurable) hr x

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- Translation is continuous in `Lᵖ` for every `Lᵖ` function. This private form is the input that
turns the increment estimate into continuity of the ball average. -/
private theorem tendsto_eLpNorm_comp_add_sub_of_memLp (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : MemLp f p mu) :
    Filter.Tendsto (fun e : E => eLpNorm (fun y => f (y + e) - f y) p mu) (nhds 0) (nhds 0) := by
  let _ : Fact (1 ≤ p) := ⟨hp⟩
  let T : E → C(E, E) := fun e => ⟨fun y => y + e, continuous_id.add continuous_const⟩
  have hT : Continuous T := ContinuousMap.continuous_of_continuous_uncurry T (by
    dsimp only [T, Function.uncurry_apply_pair, ContinuousMap.coe_mk]
    fun_prop)
  have hpres : ∀ e, MeasurePreserving (T e) mu mu := fun e => measurePreserving_add_right mu e
  have hcomp : Continuous (fun e => Lp.compMeasurePreserving (T e) (hpres e) (hf.toLp f)) :=
    continuous_const.compMeasurePreservingLp hT hpres hp'
  have hcompzero : Lp.compMeasurePreserving (T 0) (hpres 0) (hf.toLp f) = hf.toLp f := by
    apply Lp.ext
    exact (Lp.coeFn_compMeasurePreserving (hf.toLp f) (hpres 0)).mono fun y hy => by
      simpa only [T, ContinuousMap.coe_mk, Function.comp_apply, add_zero] using hy
  have hLp : Filter.Tendsto
      (fun e => Lp.compMeasurePreserving (T e) (hpres e) (hf.toLp f)) (nhds 0)
      (nhds (hf.toLp f)) := by
    simpa only [hcompzero] using hcomp.tendsto 0
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hLp
  apply hLp.congr'
  filter_upwards with e
  apply eLpNorm_congr_ae
  exact ((Lp.coeFn_compMeasurePreserving (hf.toLp f) (hpres e)).trans
    ((hpres e).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp)).sub hf.coeFn_toLp

omit [CompleteSpace F] in
/-- At every positive scale, the ball average of an `Lᵖ` function is continuous. -/
theorem continuous_ballAverage (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : MemLp f p mu)
    (hr : 0 < r) : Continuous (ballAverage mu r f) := by
  rw [continuous_iff_continuousAt]
  intro x
  -- `tendsto_iff_edist_tendsto_0` is stated for `Tendsto`, so unfold `ContinuousAt` here.
  change Filter.Tendsto (ballAverage mu r f) (nhds x) (nhds (ballAverage mu r f x))
  rw [tendsto_iff_edist_tendsto_0]
  have hsub0 : Filter.Tendsto (fun y : E => y - x) (nhds x) (nhds (x - x)) :=
    (continuous_id.sub (continuous_const : Continuous (fun _ : E => x))).tendsto x
  have hsub : Filter.Tendsto (fun y : E => y - x) (nhds x) (nhds 0) := by
    simpa only [sub_self] using hsub0
  have htrans := (tendsto_eLpNorm_comp_add_sub_of_memLp hp hp' hf).comp hsub
  have hfactor : mu (ball (0 : E) r) ^ (-(p.toReal)⁻¹) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero (measure_ball_pos mu 0 hr).ne' measure_ball_lt_top.ne
  have hupper := ENNReal.Tendsto.const_mul htrans (Or.inr hfactor)
  have hupper_zero : Filter.Tendsto
      (fun y => mu (ball (0 : E) r) ^ (-(p.toReal)⁻¹) *
        eLpNorm (fun z => f (z + (y - x)) - f z) p mu) (nhds x) (nhds 0) := by
    simpa only [Function.comp_apply, mul_zero] using hupper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper_zero
    (fun _ => bot_le) fun y => ?_
  rw [edist_eq_enorm_sub]
  have hbound := enorm_ballAverage_add_sub_ballAverage_le hp hp' hf hr (y - x) x
  have hxy : x + (y - x) = y := by abel
  rwa [hxy] at hbound

/-- Writing the deviation of `f` from its ball average as an average of increments. -/
theorem ballAverage_sub_self (hp : 1 ≤ p) (hf : MemLp f p mu) (hr : 0 < r) (x : E) :
    ballAverage mu r f x - f x = ⨍ e in ball (0 : E) r, (f (x + e) - f x) ∂mu := by
  have : IsFiniteMeasure (mu.restrict (ball (0 : E) r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hshift : MemLp (fun e => f (x + e)) p mu :=
    hf.comp_measurePreserving (measurePreserving_add_left mu x)
  rw [ballAverage_eq_setAverage_ball_zero]
  calc
    (⨍ e in ball (0 : E) r, f (x + e) ∂mu) - f x =
        (⨍ e in ball (0 : E) r, f (x + e) ∂mu) -
          ⨍ _e in ball (0 : E) r, f x ∂mu := by
      rw [setAverage_const (measure_ball_pos mu 0 hr).ne' measure_ball_lt_top.ne]
    _ = ⨍ e in ball (0 : E) r, (f (x + e) - f x) ∂mu := by
      simpa only [Pi.sub_apply] using
        (setAverage_sub ((hshift.restrict _).integrable hp)
          (integrableOn_const measure_ball_lt_top.ne)).symm

omit [BorelSpace E] [CompleteSpace F] in
/-- The analytic core shared by the two `Lᵖ` estimates below: after Hölder's inequality in the
translation variable and Tonelli's theorem, an integral of averages over the ball of radius `r`
becomes an average, over the translations of size less than `r`, of integrals. -/
private theorem lintegral_enorm_setAverage_rpow_le {q : ℝ} (hq : 1 ≤ q) {G : E → E → F}
    (hG : StronglyMeasurable (Function.uncurry G)) (hr : 0 < r) :
    ∫⁻ x, ‖⨍ e in ball (0 : E) r, G x e ∂mu‖ₑ ^ q ∂mu ≤
      (mu (ball (0 : E) r))⁻¹ * ∫⁻ e in ball (0 : E) r, ∫⁻ x, ‖G x e‖ₑ ^ q ∂mu ∂mu := by
  have hV0 : mu (ball (0 : E) r) ≠ 0 := (measure_ball_pos mu 0 hr).ne'
  have hjoint : Measurable fun z : E × E => ‖G z.1 z.2‖ₑ ^ q :=
    ENNReal.continuous_rpow_const.measurable.comp hG.enorm
  calc ∫⁻ x, ‖⨍ e in ball (0 : E) r, G x e ∂mu‖ₑ ^ q ∂mu
      ≤ ∫⁻ x, (mu (ball (0 : E) r))⁻¹ * ∫⁻ e in ball (0 : E) r, ‖G x e‖ₑ ^ q ∂mu ∂mu :=
        lintegral_mono fun x => enorm_setAverage_rpow_le hq
          (hG.comp_measurable measurable_prodMk_left).aestronglyMeasurable hV0
          measure_ball_lt_top.ne
    _ = (mu (ball (0 : E) r))⁻¹ *
          ∫⁻ x, ∫⁻ e in ball (0 : E) r, ‖G x e‖ₑ ^ q ∂mu ∂mu :=
        lintegral_const_mul' _ _ (by finiteness)
    _ = (mu (ball (0 : E) r))⁻¹ *
          ∫⁻ e in ball (0 : E) r, ∫⁻ x, ‖G x e‖ₑ ^ q ∂mu ∂mu := by
        rw [lintegral_lintegral_swap hjoint.aemeasurable]

omit [CompleteSpace F] in
/-- **The ball average is an `Lᵖ` contraction**, for `1 ≤ p < ∞`. This is Minkowski's integral
inequality for the normalized indicator of a ball; it is the reason the smoothing operator does
not have to be undone quantitatively. -/
theorem eLpNorm_ballAverage_le (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : AEStronglyMeasurable f mu)
    (hr : 0 < r) : eLpNorm (ballAverage mu r f) p mu ≤ eLpNorm f p mu := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hq : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp' hp
  have hq0 : (0 : ℝ) < p.toReal := one_pos.trans_le hq
  have hV0 : mu (ball (0 : E) r) ≠ 0 := (measure_ball_pos mu 0 hr).ne'
  have hVt : mu (ball (0 : E) r) ≠ ∞ := measure_ball_lt_top.ne
  rw [ballAverage_congr_ae hf.ae_eq_mk, eLpNorm_congr_ae hf.ae_eq_mk]
  set g := hf.mk f with hg
  have hgm : StronglyMeasurable g := hf.stronglyMeasurable_mk
  have hcore := lintegral_enorm_setAverage_rpow_le (mu := mu) (q := p.toReal) hq
    (G := fun x e => g (x + e)) (hgm.comp_measurable (measurable_fst.add measurable_snd)) hr
  simp only [← ballAverage_eq_setAverage_ball_zero] at hcore
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp',
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp']
  refine ENNReal.rpow_le_rpow (hcore.trans_eq ?_) (by positivity)
  have hslice : ∀ e : E, ∫⁻ x, ‖g (x + e)‖ₑ ^ p.toReal ∂mu = ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂mu :=
    fun e => lintegral_add_right_eq_self (fun y => ‖g y‖ₑ ^ p.toReal) e
  rw [setLIntegral_congr_fun measurableSet_ball fun e _ => hslice e, setLIntegral_const,
    ← mul_assoc, mul_comm (mu (ball (0 : E) r))⁻¹, mul_assoc, ENNReal.inv_mul_cancel hV0 hVt,
    mul_one]

omit [CompleteSpace F] in
/-- At every positive scale, taking the ball average preserves membership in `Lᵖ`. -/
theorem memLp_ballAverage (hf : MemLp f p mu) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hr : 0 < r) : MemLp (ballAverage mu r f) p mu :=
  ⟨(continuous_ballAverage hp hp' hf hr).aestronglyMeasurable,
    lt_of_le_of_lt (eLpNorm_ballAverage_le hp hp' hf.aestronglyMeasurable hr)
      hf.eLpNorm_lt_top⟩

/-- The `Lᵖ` approximation estimate for a strongly measurable representative. -/
private theorem eLpNorm_ballAverage_sub_le_of_stronglyMeasurable (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hfm : StronglyMeasurable f) (hf : MemLp f p mu) (hr : 0 < r) {C : ℝ≥0∞}
    (hC : ∀ e ∈ ball (0 : E) r, eLpNorm (fun y => f (y + e) - f y) p mu ≤ C) :
    eLpNorm (fun x => ballAverage mu r f x - f x) p mu ≤ C := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hq : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp' hp
  have hq0 : (0 : ℝ) < p.toReal := one_pos.trans_le hq
  have hV0 : mu (ball (0 : E) r) ≠ 0 := (measure_ball_pos mu 0 hr).ne'
  have hVt : mu (ball (0 : E) r) ≠ ∞ := measure_ball_lt_top.ne
  have hcore := lintegral_enorm_setAverage_rpow_le (mu := mu) (q := p.toReal) hq
    (G := fun x e => f (x + e) - f x)
    ((hfm.comp_measurable (measurable_fst.add measurable_snd)).sub
      (hfm.comp_measurable measurable_fst)) hr
  simp only [← ballAverage_sub_self hp hf hr] at hcore
  -- Each slice of the exchanged integral is a translation increment of `f`.
  have hinner : ∀ e ∈ ball (0 : E) r,
      ∫⁻ x, ‖f (x + e) - f x‖ₑ ^ p.toReal ∂mu ≤ C ^ p.toReal := by
    intro e he
    have h := ENNReal.rpow_le_rpow (hC e he) hq0.le
    rwa [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp', ← ENNReal.rpow_mul,
      one_div_mul_cancel hq0.ne', ENNReal.rpow_one] at h
  have hmain : ∫⁻ x, ‖ballAverage mu r f x - f x‖ₑ ^ p.toReal ∂mu ≤ C ^ p.toReal := by
    refine hcore.trans ?_
    calc (mu (ball (0 : E) r))⁻¹ *
            ∫⁻ e in ball (0 : E) r, ∫⁻ x, ‖f (x + e) - f x‖ₑ ^ p.toReal ∂mu ∂mu
        ≤ (mu (ball (0 : E) r))⁻¹ * ∫⁻ _e in ball (0 : E) r, C ^ p.toReal ∂mu :=
          mul_le_mul' le_rfl
            (lintegral_mono_ae ((ae_restrict_mem measurableSet_ball).mono hinner))
      _ = C ^ p.toReal := by
          rw [setLIntegral_const, ← mul_assoc, mul_comm (mu (ball (0 : E) r))⁻¹,
            mul_assoc, ENNReal.inv_mul_cancel hV0 hVt, mul_one]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp']
  calc (∫⁻ x, ‖ballAverage mu r f x - f x‖ₑ ^ p.toReal ∂mu) ^ (1 / p.toReal)
      ≤ (C ^ p.toReal) ^ (1 / p.toReal) := ENNReal.rpow_le_rpow hmain (by positivity)
    _ = C := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]

/-- **The `Lᵖ` approximation estimate**: `f` is close to its ball average at scale `r` by no more
than the largest `Lᵖ` translation increment of `f` over translations of size less than `r`. This
is the half of the Fréchet--Kolmogorov criterion that pays for the smoothing: a family whose
translates move uniformly little in `Lᵖ` is uniformly close to the family of its ball
averages. -/
theorem eLpNorm_ballAverage_sub_le (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : MemLp f p mu) (hr : 0 < r)
    {C : ℝ≥0∞} (hC : ∀ e ∈ ball (0 : E) r, eLpNorm (fun y => f (y + e) - f y) p mu ≤ C) :
    eLpNorm (fun x => ballAverage mu r f x - f x) p mu ≤ C := by
  have hff' : f =ᵐ[mu] hf.aestronglyMeasurable.mk f := hf.aestronglyMeasurable.ae_eq_mk
  have hC' : ∀ e ∈ ball (0 : E) r, eLpNorm (fun y => hf.aestronglyMeasurable.mk f (y + e) -
      hf.aestronglyMeasurable.mk f y) p mu ≤ C := by
    intro e he
    have hae : (fun y => f (y + e) - f y) =ᵐ[mu]
        fun y => hf.aestronglyMeasurable.mk f (y + e) - hf.aestronglyMeasurable.mk f y :=
      Filter.EventuallyEq.sub
        ((measurePreserving_add_right mu e).quasiMeasurePreserving.ae_eq_comp hff') hff'
    rw [← eLpNorm_congr_ae hae]
    exact hC e he
  have hball : ballAverage mu r f = ballAverage mu r (hf.aestronglyMeasurable.mk f) :=
    ballAverage_congr_ae hff'
  have hgoal : (fun x => ballAverage mu r f x - f x) =ᵐ[mu]
      fun x => ballAverage mu r (hf.aestronglyMeasurable.mk f) x -
        hf.aestronglyMeasurable.mk f x := hff'.mono fun x hx => by simp only [hball, hx]
  rw [eLpNorm_congr_ae hgoal]
  exact eLpNorm_ballAverage_sub_le_of_stronglyMeasurable hp hp'
    hf.aestronglyMeasurable.stronglyMeasurable_mk (hf.ae_eq hff') hr hC'

end Estimates

end TauCeti
