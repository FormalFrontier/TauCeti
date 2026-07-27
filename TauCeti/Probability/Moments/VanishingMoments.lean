module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import TauCeti.Probability.Moments.Determinacy
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Vanishing moments force a function to be zero

Roadmap milestone **B1** of the `OrthogonalL2Bases` roadmap, in both the forms the completeness
step uses.  `TauCeti.Probability.Moments.Determinacy` pins down a *measure* from its moments; this
file transfers that to *functions*.

Both forms assume exponential control at a single positive rate; they differ in what carries it.

* `TauCeti.ae_eq_zero_of_forall_moment_eq_zero` (function level) assumes the *product*
  `e^{a|x|} · g` is integrable for some `a > 0`, and concludes for a real `g`.
* `TauCeti.ae_eq_zero_of_forall_moment_eq_zero_of_exists_integrable_exp` (measure level) assumes
  it of the *weight* alone -- `e^{a|x|} ∈ L¹(ν)` for some `a > 0` -- and of `g` only that it lies
  in `L²(ν)`, for scalars in any `RCLike` field.  Cauchy-Schwarz bridges the two.

The measure-level form is the usable one: `hexp` becomes a statement about the weight alone
(Gaussian decay, or automatic for a *finite* compactly supported measure), independent of `g`.
Compact support alone does not suffice: on a compactly supported measure of infinite mass even the
constant `1` fails to be integrable.  Finiteness of `ν` is not a separate hypothesis in either
form, since `e^{a|x|} ≥ 1` dominates the constant `1` and so `hexp` already forces it.
-/

public section

namespace TauCeti

open MeasureTheory ProbabilityTheory Complex Filter

open scoped Topology

variable {ν : Measure ℝ}

/-! ## Vanishing moments at the level of functions -/

/-- The positive part `max t 0` never exceeds `t` in absolute value.

This is what lets a single bound on `g` serve both truncated densities `g⁺` and `g⁻` below. -/
private theorem abs_max_zero_le_abs (t : ℝ) : |max t 0| ≤ |t| := by
  rcases le_total t 0 with h | h
  · simp [max_eq_right h]
  · simp [max_eq_left h, abs_of_nonneg h]

/-- Polynomial growth is dominated by exponential growth at any positive rate:
`|x|ⁿ ≤ (n! / aⁿ) · e^{a|x|}`. -/
private theorem pow_abs_le_factorial_div_pow_mul_exp {a : ℝ} (ha : 0 < a) (n : ℕ) (x : ℝ) :
    |x| ^ n ≤ (Nat.factorial n : ℝ) / a ^ n * Real.exp (a * |x|) := by
  have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have han : (0 : ℝ) < a ^ n := by positivity
  have h := Real.pow_div_factorial_le_exp (a * |x|) (by positivity) n
  rw [div_le_iff₀ hfac, mul_pow] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ han]
  nlinarith [h, Real.exp_pos (a * |x|), pow_nonneg (abs_nonneg x) n]

section Densities

variable {a : ℝ} {g f : ℝ → ℝ}

/-- Shared step for the positive and negative parts. If the truncation `f⁺` is pointwise dominated
by `|g|` and `e^{a|x|}·g` is integrable, every polynomial moment of the density `ofReal ∘ f` is
integrable. Applied below to `f = g` and `f = -g`. -/
private theorem integrable_toReal_ofReal_smul_pow (ha : 0 < a)
    (hexp : Integrable (fun x : ℝ => Real.exp (a * |x|) * g x) ν)
    (hfm : AEMeasurable (fun x : ℝ => ENNReal.ofReal (f x)) ν)
    (hle : ∀ x, |max (f x) 0| ≤ |g x|) (n : ℕ) :
    Integrable (fun x : ℝ => (ENNReal.ofReal (f x)).toReal • x ^ n) ν := by
  have hc : (0 : ℝ) < (Nat.factorial n : ℝ) / a ^ n := by
    have : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    positivity
  refine (hexp.const_mul ((Nat.factorial n : ℝ) / a ^ n)).mono ?_ ?_
  · exact hfm.ennreal_toReal.aestronglyMeasurable.smul (continuous_pow n).aestronglyMeasurable
  · filter_upwards with x
    have hE : (0 : ℝ) < Real.exp (a * |x|) := Real.exp_pos _
    simp only [smul_eq_mul, ENNReal.toReal_ofReal', Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos hE, abs_of_pos hc]
    nlinarith [hle x, pow_abs_le_factorial_div_pow_mul_exp ha n x, abs_nonneg (g x),
      abs_nonneg (max (f x) 0), pow_nonneg (abs_nonneg x) n, hE.le, hc.le]

/-- Shared step: the density measure `(ofReal ∘ f) · ν` inherits the finite exponential moment. -/
private theorem integrable_exp_withDensity_ofReal
    (hexp : Integrable (fun x : ℝ => Real.exp (a * |x|) * g x) ν)
    (hfm : AEMeasurable (fun x : ℝ => ENNReal.ofReal (f x)) ν)
    (hlt : ∀ᵐ x ∂ν, ENNReal.ofReal (f x) < ⊤)
    (hle : ∀ x, |max (f x) 0| ≤ |g x|) :
    Integrable (fun x : ℝ => Real.exp (a * |x|))
      (ν.withDensity fun x => ENNReal.ofReal (f x)) := by
  rw [integrable_withDensity_iff_integrable_smul₀' hfm hlt]
  refine hexp.mono ?_ ?_
  · fun_prop
  · filter_upwards with x
    have hE : (0 : ℝ) < Real.exp (a * |x|) := Real.exp_pos _
    simp only [smul_eq_mul, ENNReal.toReal_ofReal', Real.norm_eq_abs, abs_mul,
      abs_of_pos hE]
    nlinarith [hle x, abs_nonneg (g x), hE.le]

end Densities

/-- **Roadmap B1 (function level).** A real function on `ℝ` whose exponentially-weighted product
`e^{a|x|} · g` is integrable for some `a > 0`, and all of whose polynomial moments `∫ xⁿ g` vanish,
is a.e. zero.

This is the internal transfer step, not the form the completeness step consumes — that is the
measure-level `ae_eq_zero_of_forall_moment_eq_zero_of_exists_integrable_exp` below, which wraps this
one. `Measure.ext_of_forall_integral_pow_eq_of_exists_integrable_exp` in
`TauCeti.Probability.Moments.Determinacy` pins down a *measure* from its moments, and this transfers
that to a *function* by applying it to the positive and negative parts of `g` as densities
against `ν`.

The exponential hypothesis is the existential `∃ a > 0`, matching the engine's convention; a caller
holding a bound at every rate supplies it at any single one.

The reference measure is arbitrary, not just `volume`, and carries no σ-finiteness hypothesis: the
argument splits `g` into `g⁺`/`g⁻` as densities, and integrability of `g` already bounds the
positive density's lintegral, which is what lets equality of the two `withDensity` measures be read
back as equality of the densities. That generality is what lets weighted orthogonal families against
a measure other than Lebesgue (Hermite against a Gaussian, Chebyshev against `(1-x²)^{-1/2}` on
`[-1,1]`) reach the completeness step, through the measure-level form below. -/
theorem ae_eq_zero_of_forall_moment_eq_zero (g : ℝ → ℝ)
    (hexp : ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => Real.exp (a * |x|) * g x) ν)
    (hmom : ∀ n : ℕ, ∫ x : ℝ, x ^ n * g x ∂ν = 0) :
    g =ᵐ[ν] 0 := by
  obtain ⟨a, ha, hexpa⟩ := hexp
  -- `g` is measurable: it is `e^{-a|x|}` times the weighted product.
  have hgm0 : AEStronglyMeasurable g ν := by
    have hrw : g = fun x => Real.exp (-(a * |x|)) * (Real.exp (a * |x|) * g x) := by
      funext x
      rw [← mul_assoc, ← Real.exp_add]
      simp
    rw [hrw]
    exact (Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul
      hexpa.aestronglyMeasurable
  -- `e^{a|x|} ≥ 1`, so the weighted integrability already gives `g ∈ L¹`.
  have hg : Integrable g ν := by
    refine hexpa.mono hgm0 ?_
    filter_upwards with x
    have h1 : (1 : ℝ) ≤ Real.exp (a * |x|) := Real.one_le_exp (by positivity)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    nlinarith [abs_nonneg (g x)]
  have hgm : AEMeasurable g ν := hg.aestronglyMeasurable.aemeasurable
  have hmeasp : AEMeasurable (fun x => ENNReal.ofReal (g x)) ν :=
    ENNReal.measurable_ofReal.comp_aemeasurable hgm
  have hmeasn : AEMeasurable (fun x => ENNReal.ofReal (-g x)) ν :=
    ENNReal.measurable_ofReal.comp_aemeasurable hgm.neg
  have hltp : ∀ᵐ x ∂ν, ENNReal.ofReal (g x) < ⊤ := by
    filter_upwards with x using ENNReal.ofReal_lt_top
  have hltn : ∀ᵐ x ∂ν, ENNReal.ofReal (-g x) < ⊤ := by
    filter_upwards with x using ENNReal.ofReal_lt_top
  -- `ENNReal.ofReal` already truncates at zero, so these densities are exactly `g⁺` and `g⁻`.
  have hlep : ∀ x, |max (g x) 0| ≤ |g x| := fun x => abs_max_zero_le_abs (g x)
  have hlen : ∀ x, |max (-g x) 0| ≤ |g x| := fun x =>
    (abs_max_zero_le_abs (-g x)).trans_eq (abs_neg (g x))
  haveI hmpfin : IsFiniteMeasure (ν.withDensity fun x => ENNReal.ofReal (g x)) :=
    isFiniteMeasure_withDensity_ofReal hg.2
  haveI hmnfin : IsFiniteMeasure (ν.withDensity fun x => ENNReal.ofReal (-g x)) :=
    isFiniteMeasure_withDensity_ofReal hg.neg.2
  have hintp := fun n => integrable_toReal_ofReal_smul_pow ha hexpa hmeasp hlep n
  have hintn := fun n => integrable_toReal_ofReal_smul_pow ha hexpa hmeasn hlen n
  -- `g⁺ - g⁻ = g` pointwise, so the two moment sequences differ by `∫ xⁿ g = 0`.
  have hmoments : ∀ n : ℕ, ∫ x, x ^ n ∂(ν.withDensity fun x => ENNReal.ofReal (g x))
      = ∫ x, x ^ n ∂(ν.withDensity fun x => ENNReal.ofReal (-g x)) := by
    intro n
    rw [integral_withDensity_eq_integral_toReal_smul₀ hmeasp hltp,
      integral_withDensity_eq_integral_toReal_smul₀ hmeasn hltn]
    have hsplit : (fun x : ℝ => (ENNReal.ofReal (g x)).toReal • x ^ n
        - (ENNReal.ofReal (-g x)).toReal • x ^ n) = fun x : ℝ => x ^ n * g x := by
      funext x
      rw [smul_eq_mul, smul_eq_mul, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
      rcases le_total (g x) 0 with h | h
      · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
      · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
    have hz : ∫ x : ℝ, ((ENNReal.ofReal (g x)).toReal • x ^ n
        - (ENNReal.ofReal (-g x)).toReal • x ^ n) ∂ν = 0 := by
      rw [hsplit]; exact hmom n
    rw [integral_sub (hintp n) (hintn n)] at hz
    linarith
  -- Determinacy forces the two parts to be the same measure ...
  have hEq : (ν.withDensity fun x => ENNReal.ofReal (g x))
      = ν.withDensity fun x => ENNReal.ofReal (-g x) :=
    Measure.ext_of_forall_integral_pow_eq_of_exists_integrable_exp
      ⟨a, ha, integrable_exp_withDensity_ofReal hexpa hmeasp hltp hlep⟩
      ⟨a, ha, integrable_exp_withDensity_ofReal hexpa hmeasn hltn hlen⟩ hmoments
  -- ... hence the densities agree a.e., hence `g⁺ = g⁻` a.e., hence `g = 0` a.e.
  -- Integrability of `g` bounds the positive density's lintegral, which is what replaces
  -- σ-finiteness of `ν` in reading the density equality back off the measure equality.
  have hfin : ∫⁻ x, ENNReal.ofReal (g x) ∂ν ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae ?_) hg.hasFiniteIntegral)
    filter_upwards with x
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  rw [withDensity_eq_iff hmeasp hmeasn hfin] at hEq
  filter_upwards [hEq] with x hx
  have h := congrArg ENNReal.toReal hx
  rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal'] at h
  rcases le_total (g x) 0 with hle | hle
  · rw [max_eq_right hle, max_eq_left (neg_nonneg.mpr hle)] at h
    simpa using h.symm
  · rw [max_eq_left hle, max_eq_right (neg_nonpos.mpr hle)] at h
    simpa using h

/-! ## Vanishing moments at the level of measures -/

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Roadmap B1, measure level.** A measure `ν` on `ℝ` carrying one finite exponential moment is
moment-determinate, so a `g ∈ L²(ν)` orthogonal to every monomial is a.e. `0`.

The rate is existential, matching the convention of the engine this wraps and of the function-level
form above; a caller holding a bound at every rate supplies it at any single one.  Requiring it at
*every* rate would exclude exponentially-tailed weights such as `e^{-|x|}`, for which
`∫ e^{a|x|} dν` is finite only for `a < 1`, even though they are moment-determinate all the same.

Finiteness of `ν` is not a separate hypothesis: `e^{a|x|} ≥ 1`. -/
theorem ae_eq_zero_of_forall_moment_eq_zero_of_exists_integrable_exp
    (hexp : ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => Real.exp (a * |x|)) ν)
    {g : ℝ → 𝕜} (hg : MemLp g 2 ν)
    (hmom : ∀ n : ℕ, ∫ x, (algebraMap ℝ 𝕜 x) ^ n * g x ∂ν = 0) :
    g =ᵐ[ν] 0 := by
  obtain ⟨a, ha, hexpa⟩ := hexp
  set b := a / 2 with hb
  have hbpos : (0 : ℝ) < b := by positivity
  have hexpmeas : ∀ c : ℝ, AEStronglyMeasurable (fun x : ℝ => Real.exp (c * |x|)) ν :=
    fun c => (Real.continuous_exp.comp
      (continuous_const.mul continuous_abs)).aestronglyMeasurable
  -- `e^{a|x|} ≥ 1` dominates the constant function, so `ν` is finite.
  haveI hnu : IsFiniteMeasure ν := by
    have hone : Integrable (fun _ : ℝ => (1 : ℝ)) ν := by
      refine hexpa.mono' aestronglyMeasurable_const (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_one]
      exact Real.one_le_exp (by positivity)
    exact (integrable_const_iff.mp hone).resolve_left one_ne_zero
  -- Half the rate is square-integrable, its square being the full-rate weight.
  have hexp2 : MemLp (fun x : ℝ => Real.exp (b * |x|)) 2 ν := by
    refine (memLp_two_iff_integrable_sq (hexpmeas b)).2 ?_
    have hfun : (fun x : ℝ => Real.exp (a * |x|))
        = fun x : ℝ => Real.exp (b * |x|) ^ 2 := by
      funext x
      rw [sq, ← Real.exp_add, hb]
      ring_nf
    exact hfun ▸ hexpa
  -- Cauchy-Schwarz: an `L²` function against the `L²` weight is integrable.
  have key : ∀ f : ℝ → ℝ, MemLp f 2 ν →
      Integrable (fun x : ℝ => Real.exp (b * |x|) * f x) ν := by
    intro f hf
    simpa only [Pi.mul_def] using hexp2.integrable_mul hf
  -- Monomials are square-integrable: `|x|ⁿ ≤ (n!/bⁿ)·e^{b|x|}` and the right side is in `L²`.
  have hpolyL2 : ∀ n : ℕ, MemLp (fun x : ℝ => (algebraMap ℝ 𝕜 x) ^ n) 2 ν := by
    intro n
    have hK : (0 : ℝ) < (Nat.factorial n : ℝ) / b ^ n := by
      have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
      positivity
    refine MemLp.of_le (hexp2.const_mul ((Nat.factorial n : ℝ) / b ^ n)) ?_ ?_
    · exact ((RCLike.continuous_ofReal.comp continuous_id).pow n).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      have h := pow_abs_le_factorial_div_pow_mul_exp hbpos n x
      have hE : (0 : ℝ) < Real.exp (b * |x|) := Real.exp_pos _
      rw [RCLike.algebraMap_eq_ofReal, norm_pow, RCLike.norm_ofReal, Real.norm_eq_abs,
        abs_mul, abs_of_pos hK, abs_of_pos hE]
      linarith
  -- Hence each monomial moment integrand is integrable, so `re`/`im` pass through the integral.
  have hint : ∀ n : ℕ, Integrable (fun x : ℝ => (algebraMap ℝ 𝕜 x) ^ n * g x) ν :=
    fun n => by simpa only [Pi.mul_def] using (hpolyL2 n).integrable_mul hg
  have hsplit : ∀ (x : ℝ) (n : ℕ),
      (algebraMap ℝ 𝕜 x) ^ n * g x = ((x ^ n : ℝ) : 𝕜) * g x := by
    intro x n
    rw [RCLike.algebraMap_eq_ofReal, RCLike.ofReal_pow]
  -- Monomials are real, so real and imaginary parts each inherit vanishing moments.
  have hre : ∀ n : ℕ, ∫ x, x ^ n * RCLike.re (g x) ∂ν = 0 := by
    intro n
    have h0 : RCLike.re (∫ x, (algebraMap ℝ 𝕜 x) ^ n * g x ∂ν) = 0 := by
      rw [hmom n]; simp
    rw [← integral_re (hint n)] at h0
    have hfun : (fun x : ℝ => x ^ n * RCLike.re (g x))
        = fun x : ℝ => RCLike.re ((algebraMap ℝ 𝕜 x) ^ n * g x) := by
      funext x
      rw [hsplit x n, RCLike.re_ofReal_mul]
    rw [hfun]
    exact h0
  have him : ∀ n : ℕ, ∫ x, x ^ n * RCLike.im (g x) ∂ν = 0 := by
    intro n
    have h0 : RCLike.im (∫ x, (algebraMap ℝ 𝕜 x) ^ n * g x ∂ν) = 0 := by
      rw [hmom n]; simp
    rw [← integral_im (hint n)] at h0
    have hfun : (fun x : ℝ => x ^ n * RCLike.im (g x))
        = fun x : ℝ => RCLike.im ((algebraMap ℝ 𝕜 x) ^ n * g x) := by
      funext x
      rw [hsplit x n, RCLike.im_ofReal_mul]
    rw [hfun]
    exact h0
  -- Apply the function-level form to the real and imaginary parts separately.
  have hzre := ae_eq_zero_of_forall_moment_eq_zero (ν := ν) _ ⟨b, hbpos, key _ hg.re⟩ hre
  have hzim := ae_eq_zero_of_forall_moment_eq_zero (ν := ν) _ ⟨b, hbpos, key _ hg.im⟩ him
  filter_upwards [hzre, hzim] with x hx1 hx2
  simp only [Pi.zero_apply] at hx1 hx2 ⊢
  exact RCLike.ext (by simp [hx1]) (by simp [hx2])

end TauCeti
