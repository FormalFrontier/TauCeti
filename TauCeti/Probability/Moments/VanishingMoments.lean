/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Function.PolynomialMemLp
public import TauCeti.Probability.Moments.Determinacy
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul

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
  in `L²(ν)`, for scalars in any `RCLike` field.  Cauchy-Schwarz bridges the two.  The roadmap name
  `ae_eq_zero_of_forall_moment_eq_zero_of_finite_expMoments`, taking the stronger *all-rates*
  hypothesis its name implies, is provided as a public wrapper.

The measure-level form is the usable one: `hexp` becomes a statement about the weight alone
(Gaussian decay, or automatic for a *finite* compactly supported measure), independent of `g`.
Compact support alone does not suffice: on a compactly supported measure of infinite mass even the
constant `1` fails to be integrable.  In the measure-level form finiteness of `ν` is not a separate
hypothesis: there `hexp` integrates the weight `e^{a|x|} ≥ 1` itself, which dominates the constant
`1`.  The function-level form carries no such implication -- its `hexp` integrates the *product*
`e^{a|x|} · g`, which `g = 0` satisfies over any measure, finite or infinite.

The same exponential-moment hypothesis also makes every polynomial moment finite, so the result
that records this -- `TauCeti.integrable_pow_of_exp_moment`, a symmetric-moment adaptation of
`ProbabilityTheory.integrable_pow_of_integrable_exp_mul` -- lives here with it rather than with
any one consumer.
-/

public section

namespace TauCeti

open MeasureTheory ProbabilityTheory Complex Filter

open scoped Topology

variable {ν : Measure ℝ}

/-! ## Exponential moments control polynomial moments -/

/-- **One finite exponential moment makes every polynomial moment finite.**

The two-sided moment hypothesis of `ProbabilityTheory.integrable_pow_of_integrable_exp_mul` is
what a *single* symmetric moment `e^{a|x|} ∈ L¹(ν)` supplies: `±x ≤ |x|` makes `e^{a|x|}`
dominate both `e^{ax}` and `e^{-ax}`.

This is the bridge to the family-agnostic polynomial interface of
`TauCeti.MeasureTheory.Function.PolynomialMemLp`, whose hypothesis is exactly "every polynomial
moment is finite"; the `MemLp` statements of
`TauCeti.Analysis.InnerProductSpace.PolynomialCompleteness` are that interface applied through
this. -/
theorem integrable_pow_of_exp_moment
    (hexp : ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => Real.exp (a * |x|)) ν) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) ν := by
  obtain ⟨a, ha, hexpa⟩ := hexp
  have hdom : ∀ c : ℝ, (∀ x : ℝ, c * x ≤ a * |x|) →
      Integrable (fun x : ℝ => Real.exp (c * x)) ν := fun c hc =>
    hexpa.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (hc x))
  exact integrable_pow_of_integrable_exp_mul ha.ne'
    (hdom a fun x => mul_le_mul_of_nonneg_left (le_abs_self x) ha.le)
    (hdom (-a) fun x => by
      rw [neg_mul, ← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_le_abs x) ha.le) k

/-! ## Vanishing moments at the level of functions -/

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
  have hc : (0 : ℝ) < ((n : ℝ) / a) ^ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact pow_pos (div_pos (Nat.cast_pos.mpr hn) ha) _
  have hdom : ∀ x : ℝ, |x| ^ n ≤ ((n : ℝ) / a) ^ n * Real.exp (a * |x|) := by
    intro x
    have h := rpow_abs_le_mul_exp_abs x (p := (n : ℝ)) (t := a) (Nat.cast_nonneg n) (ne_of_gt ha)
    rwa [abs_of_pos ha, Real.rpow_natCast, Real.rpow_natCast] at h
  refine (hexp.const_mul (((n : ℝ) / a) ^ n)).mono ?_ ?_
  · exact hfm.ennreal_toReal.aestronglyMeasurable.smul (continuous_pow n).aestronglyMeasurable
  · filter_upwards with x
    have hE : (0 : ℝ) < Real.exp (a * |x|) := Real.exp_pos _
    simp only [smul_eq_mul, ENNReal.toReal_ofReal', Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos hE, abs_of_pos hc]
    nlinarith [hle x, hdom x, abs_nonneg (g x),
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

/-- An exponentially-weighted product bounds the function itself: since `e^{a|x|} ≥ 1` for
`a ≥ 0`, integrability of `e^{a|x|} · g` already gives integrability of `g`. -/
private theorem integrable_of_integrable_exp_mul_abs_mul (ha : 0 ≤ a)
    (hexp : Integrable (fun x : ℝ => Real.exp (a * |x|) * g x) ν) : Integrable g ν := by
  have hgm : AEStronglyMeasurable g ν := by
    have hrw : g = fun x => Real.exp (-(a * |x|)) * (Real.exp (a * |x|) * g x) := by
      funext x
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    rw [hrw]
    exact (Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul
      hexp.aestronglyMeasurable
  refine hexp.mono hgm ?_
  filter_upwards with x
  have h1 : (1 : ℝ) ≤ Real.exp (a * |x|) := Real.one_le_exp (mul_nonneg ha (abs_nonneg x))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  nlinarith [abs_nonneg (g x)]

/-- If `∫ xⁿ g` vanishes then the two truncations `g⁺` and `g⁻`, taken as densities against `ν`,
have the same `n`-th moment: their difference is `g` pointwise. -/
private theorem integral_pow_withDensity_ofReal_eq {n : ℕ}
    (hmeasp : AEMeasurable (fun x : ℝ => ENNReal.ofReal (g x)) ν)
    (hmeasn : AEMeasurable (fun x : ℝ => ENNReal.ofReal (-g x)) ν)
    (hintp : Integrable (fun x : ℝ => (ENNReal.ofReal (g x)).toReal • x ^ n) ν)
    (hintn : Integrable (fun x : ℝ => (ENNReal.ofReal (-g x)).toReal • x ^ n) ν)
    (hmom : ∫ x : ℝ, x ^ n * g x ∂ν = 0) :
    ∫ x, x ^ n ∂(ν.withDensity fun x => ENNReal.ofReal (g x))
      = ∫ x, x ^ n ∂(ν.withDensity fun x => ENNReal.ofReal (-g x)) := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hmeasp (ae_of_all _ fun _ =>
      ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul₀ hmeasn (ae_of_all _ fun _ =>
      ENNReal.ofReal_lt_top)]
  have hsplit : (fun x : ℝ => (ENNReal.ofReal (g x)).toReal • x ^ n
      - (ENNReal.ofReal (-g x)).toReal • x ^ n) = fun x : ℝ => x ^ n * g x := by
    funext x
    rw [smul_eq_mul, smul_eq_mul, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal',
      ← sub_mul, max_zero_sub_max_neg_zero_eq_self]
    ring
  have hz : ∫ x : ℝ, ((ENNReal.ofReal (g x)).toReal • x ^ n
      - (ENNReal.ofReal (-g x)).toReal • x ^ n) ∂ν = 0 := by
    rw [hsplit]; exact hmom
  rw [integral_sub hintp hintn] at hz
  linarith

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
  have hg : Integrable g ν := integrable_of_integrable_exp_mul_abs_mul ha.le hexpa
  have hgm : AEMeasurable g ν := hg.aestronglyMeasurable.aemeasurable
  have hmeasp : AEMeasurable (fun x => ENNReal.ofReal (g x)) ν :=
    ENNReal.measurable_ofReal.comp_aemeasurable hgm
  have hmeasn : AEMeasurable (fun x => ENNReal.ofReal (-g x)) ν :=
    ENNReal.measurable_ofReal.comp_aemeasurable hgm.neg
  have hltp : ∀ᵐ x ∂ν, ENNReal.ofReal (g x) < ⊤ := ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hltn : ∀ᵐ x ∂ν, ENNReal.ofReal (-g x) < ⊤ := ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  -- `ENNReal.ofReal` already truncates at zero, so these densities are exactly `g⁺` and `g⁻`.
  -- `|max t 0| ≤ |t|` is Mathlib's `abs_max_sub_max_le_abs` at `b = c = 0`.
  have hlep : ∀ x, |max (g x) 0| ≤ |g x| := fun x => by
    simpa using abs_max_sub_max_le_abs (g x) 0 0
  have hlen : ∀ x, |max (-g x) 0| ≤ |g x| := fun x => by
    simpa using abs_max_sub_max_le_abs (-g x) 0 0
  haveI hmpfin : IsFiniteMeasure (ν.withDensity fun x => ENNReal.ofReal (g x)) :=
    isFiniteMeasure_withDensity_ofReal hg.2
  haveI hmnfin : IsFiniteMeasure (ν.withDensity fun x => ENNReal.ofReal (-g x)) :=
    isFiniteMeasure_withDensity_ofReal hg.neg.2
  have hintp := fun n => integrable_toReal_ofReal_smul_pow ha hexpa hmeasp hlep n
  have hintn := fun n => integrable_toReal_ofReal_smul_pow ha hexpa hmeasn hlen n
  -- `g⁺ - g⁻ = g` pointwise, so the two moment sequences differ by `∫ xⁿ g = 0`.
  have hmoments := fun n => integral_pow_withDensity_ofReal_eq hmeasp hmeasn (hintp n) (hintn n)
    (hmom n)
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
  exact (max_zero_sub_max_neg_zero_eq_self (g x)).symm.trans (sub_eq_zero.mpr h)

/-! ## Vanishing moments at the level of measures -/

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A measure carrying an integrable weight `e^{a|x|}` at a rate `a ≥ 0` is finite: that weight
dominates the constant `1`. -/
private theorem isFiniteMeasure_of_integrable_exp_mul_abs {a : ℝ} (ha : 0 ≤ a)
    (hexp : Integrable (fun x : ℝ => Real.exp (a * |x|)) ν) : IsFiniteMeasure ν := by
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) ν := by
    refine hexp.mono' aestronglyMeasurable_const (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_one]
    exact Real.one_le_exp (mul_nonneg ha (abs_nonneg x))
  exact (integrable_const_iff.mp hone).resolve_left one_ne_zero

/-- Every monomial, cast into `𝕜`, is square-integrable against a measure carrying an integrable
weight `e^{b|x|}` at a positive rate: that weight dominates `e^{±bx}`, which makes every polynomial
moment finite. -/
private theorem memLp_two_algebraMap_pow_of_integrable_exp_mul_abs {b : ℝ} (hb : 0 < b)
    (hexp : Integrable (fun x : ℝ => Real.exp (b * |x|)) ν) (n : ℕ) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜 x) ^ n) 2 ν := by
  have hmeas : ∀ c : ℝ, AEStronglyMeasurable (fun x : ℝ => Real.exp (c * x)) ν :=
    fun c => (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  have hpos : Integrable (fun x : ℝ => Real.exp (b * x)) ν := by
    refine hexp.mono' (hmeas b) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.abs_exp]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self x) hb.le)
  have hneg : Integrable (fun x : ℝ => Real.exp (-b * x)) ν := by
    refine hexp.mono' (hmeas (-b)) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.abs_exp]
    exact Real.exp_le_exp.mpr (by nlinarith [hb, neg_le_abs x])
  have hpow : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) ν := fun k =>
    integrable_pow_of_integrable_exp_mul (ne_of_gt hb) hpos hneg k
  simpa only [Polynomial.eval_pow, Polynomial.eval_X, map_pow] using
    memLp_two_algebraMap_eval_of_forall_integrable_pow (𝕜 := 𝕜) hpow (Polynomial.X ^ n)

/-- A real-linear functional passes through a vanishing monomial moment.  The monomial `xⁿ` is
real, so `L` commutes with multiplication by it, and `∫ xⁿ · L(g)` is `L` applied to the moment. -/
private theorem integral_pow_mul_clm_eq_zero (L : 𝕜 →L[ℝ] ℝ) {g : ℝ → 𝕜} {n : ℕ}
    (hint : Integrable (fun x : ℝ => (algebraMap ℝ 𝕜 x) ^ n * g x) ν)
    (hmom : ∫ x, (algebraMap ℝ 𝕜 x) ^ n * g x ∂ν = 0) :
    ∫ x : ℝ, x ^ n * L (g x) ∂ν = 0 := by
  have hfun : (fun x : ℝ => x ^ n * L (g x))
      = fun x : ℝ => L ((algebraMap ℝ 𝕜 x) ^ n * g x) := by
    funext x
    rw [RCLike.algebraMap_eq_ofReal, ← RCLike.ofReal_pow, ← RCLike.real_smul_eq_coe_mul,
      L.map_smul, smul_eq_mul]
  rw [hfun, L.integral_comp_comm hint, hmom, map_zero]

/-- **Roadmap B1, measure level.** A measure `ν` on `ℝ` carrying one finite exponential moment is
moment-determinate, so a `g ∈ L²(ν)` orthogonal to every monomial is a.e. `0`.

The rate is existential, matching the convention of the engine this wraps and of the function-level
form above; a caller holding a bound at every rate supplies it at any single one.  Requiring it at
*every* rate would exclude exponentially-tailed weights such as `e^{-|x|}`, for which
`∫ e^{a|x|} dν` is finite only for `a < 1`, even though they are moment-determinate all the same.
The `_of_exists_integrable_exp` suffix names the hypothesis exactly — *existence* of one positive
rate with `e^{a|x|}` integrable — and matches the adjacent determinacy API
(`Measure.ext_of_forall_integral_pow_eq_of_exists_integrable_exp`).  The roadmap name
`_of_finite_expMoments`, with the matching *all-rates* hypothesis, wraps this one immediately below.

Finiteness of `ν` is not a separate hypothesis: `e^{a|x|} ≥ 1`. -/
theorem ae_eq_zero_of_forall_moment_eq_zero_of_exists_integrable_exp
    (hexp : ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => Real.exp (a * |x|)) ν)
    {g : ℝ → 𝕜} (hg : MemLp g 2 ν)
    (hmom : ∀ n : ℕ, ∫ x, (algebraMap ℝ 𝕜 x) ^ n * g x ∂ν = 0) :
    g =ᵐ[ν] 0 := by
  obtain ⟨a, ha, hexpa⟩ := hexp
  set b := a / 2 with hb
  have hbpos : (0 : ℝ) < b := by positivity
  have : IsFiniteMeasure ν := isFiniteMeasure_of_integrable_exp_mul_abs ha.le hexpa
  -- Half the rate is square-integrable, its square being the full-rate weight.
  have hexp2 : MemLp (fun x : ℝ => Real.exp (b * |x|)) 2 ν := by
    refine (memLp_two_iff_integrable_sq (Real.continuous_exp.comp
      (continuous_const.mul continuous_abs)).aestronglyMeasurable).2 ?_
    have hfun : (fun x : ℝ => Real.exp (a * |x|))
        = fun x : ℝ => Real.exp (b * |x|) ^ 2 := by
      funext x
      rw [sq, ← Real.exp_add, hb]
      ring_nf
    exact hfun ▸ hexpa
  -- Cauchy-Schwarz: an `L²` function against the `L²` weight is integrable.
  have key : ∀ f : ℝ → ℝ, MemLp f 2 ν →
      Integrable (fun x : ℝ => Real.exp (b * |x|) * f x) ν :=
    fun f hf => by simpa only [Pi.mul_def] using hexp2.integrable_mul hf
  -- Monomials are square-integrable, so each monomial moment integrand is integrable and the
  -- real and imaginary parts each pass through the integral.
  have hint : ∀ n : ℕ, Integrable (fun x : ℝ => (algebraMap ℝ 𝕜 x) ^ n * g x) ν := fun n => by
    simpa only [Pi.mul_def] using (memLp_two_algebraMap_pow_of_integrable_exp_mul_abs hbpos
      (hexp2.integrable (show (1 : ENNReal) ≤ 2 by norm_num)) n).integrable_mul hg
  have hre : ∀ n : ℕ, ∫ x, x ^ n * RCLike.re (g x) ∂ν = 0 := fun n => by
    simpa only [RCLike.reCLM_apply] using
      integral_pow_mul_clm_eq_zero RCLike.reCLM (hint n) (hmom n)
  have him : ∀ n : ℕ, ∫ x, x ^ n * RCLike.im (g x) ∂ν = 0 := fun n => by
    simpa only [RCLike.imCLM_apply] using
      integral_pow_mul_clm_eq_zero RCLike.imCLM (hint n) (hmom n)
  -- Apply the function-level form to the real and imaginary parts separately.
  have hzre := ae_eq_zero_of_forall_moment_eq_zero (ν := ν) _ ⟨b, hbpos, key _ hg.re⟩ hre
  have hzim := ae_eq_zero_of_forall_moment_eq_zero (ν := ν) _ ⟨b, hbpos, key _ hg.im⟩ him
  filter_upwards [hzre, hzim] with x hx1 hx2
  simp only [Pi.zero_apply] at hx1 hx2 ⊢
  exact RCLike.ext (by simp [hx1]) (by simp [hx2])

/-- **Roadmap B1, measure level** (roadmap-specified API name).  The name `_of_finite_expMoments`
is accurate here: the hypothesis is that *every* exponential moment is finite -- `e^{a|x|}` is
integrable at every rate `a ≥ 0` -- which is the roadmap signature.  This is strictly stronger than
the primary `_of_exists_integrable_exp`, and follows from it immediately by using the moment at any
single positive rate. -/
theorem ae_eq_zero_of_forall_moment_eq_zero_of_finite_expMoments
    (hexp : ∀ a : ℝ, 0 ≤ a → Integrable (fun x : ℝ => Real.exp (a * |x|)) ν)
    {g : ℝ → 𝕜} (hg : MemLp g 2 ν)
    (hmom : ∀ n : ℕ, ∫ x, (algebraMap ℝ 𝕜 x) ^ n * g x ∂ν = 0) :
    g =ᵐ[ν] 0 :=
  ae_eq_zero_of_forall_moment_eq_zero_of_exists_integrable_exp
    ⟨1, one_pos, hexp 1 zero_le_one⟩ hg hmom

end TauCeti
