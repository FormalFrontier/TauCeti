module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Analysis.Analytic.Order

/-!
# Moment determinacy of finite measures with finite exponential moments

A finite measure on `ℝ` whose exponential moments are finite in a neighbourhood of the origin is
determined by its sequence of polynomial moments `∫ xⁿ dμ`.  This is the analytic engine behind the
completeness step (**B1**) of the `OrthogonalL2Bases` roadmap
(`TauCetiRoadmap/OrthogonalL2Bases/README.md`, *Part B1 — Completeness toolkit (moment
determinacy)*): the roadmap's `ae_eq_zero_of_forall_moment_eq_zero`-style lemmas rest on the fact
that "vanishing moments" pins a distribution down, which for finite measures is exactly the
determinacy result proved here.

The mechanism is the one the roadmap describes — the (complex) moment-generating function is
analytic on a strip around the imaginary axis, and its Taylor coefficients at `0` are the moments,
so matching moments force the two functions to agree, hence the characteristic functions agree and
the measures coincide.  The proof stays inside Mathlib's `ProbabilityTheory.complexMGF` /
`MeasureTheory.charFun` API:

* `ProbabilityTheory.analyticAt_complexMGF` and `analyticOnNhd_complexMGF` supply the analyticity
  on the strip `{z | z.re ∈ interior (integrableExpSet id μ)}`;
* `ProbabilityTheory.iteratedDeriv_complexMGF` identifies the `n`-th derivative at `0` with the
  `n`-th complex moment;
* the identity principle (`analyticOrderAt_eq_top`,
  `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) propagates equality from `0` to the whole
  strip, in particular to the imaginary axis;
* `ProbabilityTheory.complexMGF_id_mul_I` turns the imaginary-axis values into `charFun`, and
  `MeasureTheory.Measure.ext_of_charFun` concludes.

The strip-propagation core of `charFun_eq_of_forall_integral_pow_eq` adapts Mathlib's
`ProbabilityTheory.eqOn_complexMGF_of_mgf'` (`Mathlib/Probability/Moments/ComplexMGF.lean`): it
reuses the same analyticity strip and the same
`convex_integrableExpSet.interior.…linear_preimage Complex.reLm |>.isPreconnected`
identity-principle idiom.  That file's `## TODO` note ("once we know that equal `mgf` implies equal
distributions …")
records the determinacy fact as an open gap in Mathlib; the results here complete it for finite
measures via the polynomial-moment route.

## Main declarations

* `TauCeti.charFun_eq_of_forall_integral_pow_eq`: matching moments (and finite exponential moments
  near `0`) give equal characteristic functions.
* `TauCeti.Measure.ext_of_forall_integral_pow_eq`: matching moments determine a finite measure on
  `ℝ`.
* `TauCeti.Measure.ext_of_forall_integral_pow_eq_of_exists_integrable_exp`: the same conclusion from
  the roadmap's exponential-moment hypothesis `∃ a > 0, Integrable (fun x => exp (a * |x|)) μ`,
  which already puts `0` in the interior of the integrability strip.  This is the form the
  completeness argument consumes: the hypothesis holds for Gaussian decay and automatically for
  compactly supported measures.
-/

public section

namespace TauCeti

open MeasureTheory ProbabilityTheory Complex Filter
open scoped Topology

variable {μ ν : Measure ℝ}

/-- The `n`-th derivative at `0` of the complex moment-generating function of `μ` is the `n`-th
complex moment `↑(∫ xⁿ dμ)`.  Immediate from `iteratedDeriv_complexMGF` at `z = 0`, where the
exponential factor is `1`. -/
private lemma iteratedDeriv_complexMGF_id_zero
    (hμ : (0 : ℝ) ∈ interior (integrableExpSet id μ)) (n : ℕ) :
    iteratedDeriv n (complexMGF id μ) 0 = ((∫ x, x ^ n ∂μ : ℝ) : ℂ) := by
  have hz : (0 : ℂ).re ∈ interior (integrableExpSet id μ) := by simpa using hμ
  rw [iteratedDeriv_complexMGF (z := 0) hz n]
  have hpow : ∀ x : ℝ, ((x : ℂ)) ^ n * Complex.exp (0 * (x : ℂ)) = (((x ^ n : ℝ)) : ℂ) := by
    intro x
    rw [zero_mul, Complex.exp_zero, mul_one]
    push_cast
    ring
  simp only [id_eq, hpow]
  exact integral_ofReal

/-- **Moment determinacy at the level of characteristic functions.** If two measures on `ℝ` have
finite exponential moments near `0` (so their complex moment-generating functions are analytic on a
strip about the imaginary axis) and agree on every polynomial moment `∫ xⁿ`, then their
characteristic functions coincide. -/
theorem charFun_eq_of_forall_integral_pow_eq
    (hμ : (0 : ℝ) ∈ interior (integrableExpSet id μ))
    (hν : (0 : ℝ) ∈ interior (integrableExpSet id ν))
    (hmom : ∀ n, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂ν) :
    charFun μ = charFun ν := by
  have hμ0 : (0 : ℂ).re ∈ interior (integrableExpSet id μ) := by simpa using hμ
  have hν0 : (0 : ℂ).re ∈ interior (integrableExpSet id ν) := by simpa using hν
  have hAμ : AnalyticAt ℂ (complexMGF id μ) 0 := analyticAt_complexMGF hμ0
  have hAν : AnalyticAt ℂ (complexMGF id ν) 0 := analyticAt_complexMGF hν0
  -- The difference of the two moment-generating functions has all derivatives zero at `0`.
  have hiter : ∀ i, iteratedDeriv i (fun z => complexMGF id μ z - complexMGF id ν z) 0 = 0 := by
    intro i
    rw [iteratedDeriv_fun_sub hAμ.contDiffAt hAν.contDiffAt,
      iteratedDeriv_complexMGF_id_zero hμ i, iteratedDeriv_complexMGF_id_zero hν i, hmom i,
      sub_self]
  have hsub : AnalyticAt ℂ (fun z => complexMGF id μ z - complexMGF id ν z) 0 := hAμ.sub hAν
  have hord : analyticOrderAt (fun z => complexMGF id μ z - complexMGF id ν z) 0 = ⊤ :=
    ENat.eq_top_iff_forall_ge.mpr fun m =>
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hsub).mpr fun i _ => hiter i
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ), complexMGF id μ z - complexMGF id ν z = 0 :=
    analyticOrderAt_eq_top.mp hord
  have hEqNear : complexMGF id μ =ᶠ[𝓝 0] complexMGF id ν := by
    filter_upwards [hnear] with z hz using sub_eq_zero.mp hz
  -- Propagate the equality across the common analyticity strip by the identity principle.
  set U : Set ℂ :=
    Complex.reLm ⁻¹' (interior (integrableExpSet id μ) ∩ interior (integrableExpSet id ν))
    with hUdef
  have hUconn : IsPreconnected U :=
    ((convex_integrableExpSet.interior.inter
      convex_integrableExpSet.interior).linear_preimage Complex.reLm).isPreconnected
  have hsubμ : U ⊆ {z | z.re ∈ interior (integrableExpSet id μ)} := fun z hz => hz.1
  have hsubν : U ⊆ {z | z.re ∈ interior (integrableExpSet id ν)} := fun z hz => hz.2
  have hAμU : AnalyticOnNhd ℂ (complexMGF id μ) U := analyticOnNhd_complexMGF.mono hsubμ
  have hAνU : AnalyticOnNhd ℂ (complexMGF id ν) U := analyticOnNhd_complexMGF.mono hsubν
  have h0U : (0 : ℂ) ∈ U := ⟨hμ0, hν0⟩
  have hEqU : Set.EqOn (complexMGF id μ) (complexMGF id ν) U :=
    hAμU.eqOn_of_preconnected_of_eventuallyEq hAνU hUconn h0U hEqNear
  -- The imaginary axis lies in the strip, and there the values are the characteristic functions.
  ext t
  have htU : ((t : ℂ) * I) ∈ U := by
    have ht0 : reLm ((t : ℂ) * I) = 0 := by rw [Complex.reLm_coe]; simp
    simp only [hUdef, Set.mem_preimage, Set.mem_inter_iff, ht0]
    exact ⟨hμ, hν⟩
  have := hEqU htU
  rwa [complexMGF_id_mul_I, complexMGF_id_mul_I] at this

/-- **Moment determinacy for finite measures on `ℝ`.** A finite measure on `ℝ` with finite
exponential moments near `0` is determined by its polynomial moments `∫ xⁿ`.  Combines
`charFun_eq_of_forall_integral_pow_eq` with `MeasureTheory.Measure.ext_of_charFun`. -/
theorem Measure.ext_of_forall_integral_pow_eq [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : (0 : ℝ) ∈ interior (integrableExpSet id μ))
    (hν : (0 : ℝ) ∈ interior (integrableExpSet id ν))
    (hmom : ∀ n, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂ν) :
    μ = ν :=
  Measure.ext_of_charFun (charFun_eq_of_forall_integral_pow_eq hμ hν hmom)

/-- If `∫ e^{a|x|} dμ` is finite for a single `a > 0`, then `0` lies in the interior of the
integrability set `integrableExpSet id μ`: for `|t| ≤ a` the exponential `e^{tx}` is dominated by
`e^{a|x|}`, so the open interval `(-a, a)` is contained in `integrableExpSet id μ`. -/
private lemma zero_mem_interior_integrableExpSet_id_of_exists_integrable_exp
    (h : ∃ a : ℝ, 0 < a ∧ Integrable (fun x => Real.exp (a * |x|)) μ) :
    (0 : ℝ) ∈ interior (integrableExpSet id μ) := by
  obtain ⟨a, ha, hint⟩ := h
  refine mem_interior.mpr ⟨Set.Ioo (-a) a, ?_, isOpen_Ioo, Set.mem_Ioo.mpr ⟨neg_lt_zero.mpr ha, ha⟩⟩
  intro t ht
  simp only [integrableExpSet, Set.mem_setOf_eq, id_eq]
  refine hint.mono'
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ?_
  calc t * x ≤ |t * x| := le_abs_self _
    _ = |t| * |x| := abs_mul t x
    _ ≤ a * |x| := mul_le_mul_of_nonneg_right (abs_lt.mpr ht).le (abs_nonneg x)

/-- **Moment determinacy, exponential-moment form (the roadmap's B1 hypothesis).** A finite measure
on `ℝ` for which some exponential moment `∫ e^{a|x|} dμ` with `a > 0` is finite is determined by its
polynomial moments.  This is the form the completeness argument consumes: the hypothesis holds for
Gaussian decay and automatically for compactly supported measures. -/
theorem Measure.ext_of_forall_integral_pow_eq_of_exists_integrable_exp
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∃ a : ℝ, 0 < a ∧ Integrable (fun x => Real.exp (a * |x|)) μ)
    (hν : ∃ a : ℝ, 0 < a ∧ Integrable (fun x => Real.exp (a * |x|)) ν)
    (hmom : ∀ n, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂ν) :
    μ = ν :=
  Measure.ext_of_forall_integral_pow_eq
    (zero_mem_interior_integrableExpSet_id_of_exists_integrable_exp hμ)
    (zero_mem_interior_integrableExpSet_id_of_exists_integrable_exp hν) hmom

/-! ## Vanishing moments at the level of functions -/

/-- **Roadmap B1 (function level).** A real function on `ℝ` whose exponentially-weighted products
`e^{a|x|} · g` are all integrable, and all of whose polynomial moments `∫ xⁿ g` vanish, is a.e.
zero.

This is the instance the completeness step consumes:
`Measure.ext_of_forall_integral_pow_eq_of_exists_integrable_exp`
above pins down a *measure* from its moments, and this transfers that to a *function* by applying it
to the positive and negative parts of `g` as densities against `volume`. -/
theorem ae_eq_zero_of_forall_moment_eq_zero (g : ℝ → ℝ)
    (hexp : ∀ a : ℝ, 0 ≤ a → Integrable (fun x : ℝ => Real.exp (a * |x|) * g x) volume)
    (hmom : ∀ n : ℕ, ∫ x : ℝ, x ^ n * g x = 0) :
    g =ᵐ[volume] 0 := by
  -- `a = 0` gives plain integrability of `g`.
  have hg : Integrable g volume := by simpa using hexp 0 le_rfl
  have hgm : AEMeasurable g volume := hg.aestronglyMeasurable.aemeasurable
  have hmeasp : AEMeasurable (fun x => ENNReal.ofReal (g x)) volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable hgm
  have hmeasn : AEMeasurable (fun x => ENNReal.ofReal (-g x)) volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable hgm.neg
  have hltp : ∀ᵐ x ∂volume, ENNReal.ofReal (g x) < ⊤ := by
    filter_upwards with x using ENNReal.ofReal_lt_top
  have hltn : ∀ᵐ x ∂volume, ENNReal.ofReal (-g x) < ⊤ := by
    filter_upwards with x using ENNReal.ofReal_lt_top
  -- Split `g` into its positive and negative parts as densities against `volume`.
  -- `ENNReal.ofReal` already truncates at zero, so these are exactly `g⁺` and `g⁻`.
  set mp : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (g x)) with hmp
  set mn : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (-g x)) with hmn
  haveI hmpfin : IsFiniteMeasure mp := isFiniteMeasure_withDensity_ofReal hg.2
  haveI hmnfin : IsFiniteMeasure mn := isFiniteMeasure_withDensity_ofReal hg.neg.2
  -- Vanishing moments of `g` say exactly that `g⁺` and `g⁻` have the same moments.
  -- `xⁿ · g` is integrable: `|x|ⁿ ≤ n! · e^{|x|}`, so `hexp 1` dominates every polynomial moment.
  have hdom : ∀ n : ℕ,
      Integrable (fun x : ℝ => (Nat.factorial n : ℝ) * (Real.exp (1 * |x|) * g x)) volume :=
    fun n => (hexp 1 zero_le_one).const_mul _
  have hpowbd : ∀ (n : ℕ) (x : ℝ), |x| ^ n ≤ (Nat.factorial n : ℝ) * Real.exp (1 * |x|) := by
    intro n x
    have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) n
    have hfac : (0:ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast (Nat.factorial_pos n)
    rw [one_mul]
    rw [div_le_iff₀ hfac] at h
    linarith
  have hintp : ∀ n : ℕ,
      Integrable (fun x : ℝ => (ENNReal.ofReal (g x)).toReal • x ^ n) volume := by
    intro n
    have hfacpos : (0:ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    refine (hdom n).mono ?_ ?_
    · exact (hmeasp.ennreal_toReal.aestronglyMeasurable).smul
        ((continuous_pow n).aestronglyMeasurable)
    · filter_upwards with x
      have h1 : |max (g x) 0| ≤ |g x| := by
        rcases le_total (g x) 0 with h | h
        · simp [max_eq_right h]
        · simp [max_eq_left h, abs_of_nonneg h]
      have h2 := hpowbd n x
      have hE : (0:ℝ) < Real.exp (1 * |x|) := Real.exp_pos _
      rw [smul_eq_mul, ENNReal.toReal_ofReal', Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos hE, abs_of_pos hfacpos]
      nlinarith [abs_nonneg (g x), abs_nonneg (max (g x) 0), pow_nonneg (abs_nonneg x) n]
  have hintn : ∀ n : ℕ,
      Integrable (fun x : ℝ => (ENNReal.ofReal (-g x)).toReal • x ^ n) volume := by
    intro n
    have hfacpos : (0:ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    refine (hdom n).mono ?_ ?_
    · exact (hmeasn.ennreal_toReal.aestronglyMeasurable).smul
        ((continuous_pow n).aestronglyMeasurable)
    · filter_upwards with x
      have h1 : |max (-g x) 0| ≤ |g x| := by
        rcases le_total (-g x) 0 with h | h
        · simp [max_eq_right h]
        · rw [max_eq_left h, abs_of_nonneg h]
          exact neg_le_abs (g x)
      have h2 := hpowbd n x
      have hE : (0:ℝ) < Real.exp (1 * |x|) := Real.exp_pos _
      rw [smul_eq_mul, ENNReal.toReal_ofReal', Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos hE, abs_of_pos hfacpos]
      nlinarith [abs_nonneg (g x), abs_nonneg (max (-g x) 0), pow_nonneg (abs_nonneg x) n]
  -- `g⁺ - g⁻ = g` pointwise, so the two moment sequences differ by `∫ xⁿ g = 0`.
  have hmoments : ∀ n : ℕ, ∫ x, x ^ n ∂mp = ∫ x, x ^ n ∂mn := by
    intro n
    rw [hmp, hmn, integral_withDensity_eq_integral_toReal_smul₀ hmeasp hltp,
      integral_withDensity_eq_integral_toReal_smul₀ hmeasn hltn]
    have hsplit : (fun x : ℝ => (ENNReal.ofReal (g x)).toReal • x ^ n
        - (ENNReal.ofReal (-g x)).toReal • x ^ n) = fun x : ℝ => x ^ n * g x := by
      funext x
      rw [smul_eq_mul, smul_eq_mul, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
      rcases le_total (g x) 0 with h | h
      · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
      · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
    have hz : ∫ x : ℝ, ((ENNReal.ofReal (g x)).toReal • x ^ n
        - (ENNReal.ofReal (-g x)).toReal • x ^ n) = 0 := by
      rw [hsplit]; exact hmom n
    rw [integral_sub (hintp n) (hintn n)] at hz
    linarith
  have hexpp : ∃ a : ℝ, 0 < a ∧ Integrable (fun x => Real.exp (a * |x|)) mp := by
    refine ⟨1, one_pos, ?_⟩
    rw [hmp, integrable_withDensity_iff_integrable_smul₀' hmeasp hltp]
    refine (hexp 1 zero_le_one).mono ?_ ?_
    · fun_prop
    · filter_upwards with x
      have hpos : (0:ℝ) < Real.exp (1 * |x|) := Real.exp_pos _
      rw [smul_eq_mul, ENNReal.toReal_ofReal', Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, abs_mul, abs_of_pos hpos]
      have hle : |max (g x) 0| ≤ |g x| := by
        rcases le_total (g x) 0 with h | h
        · simp [max_eq_right h]
        · simp [max_eq_left h, abs_of_nonneg h]
      nlinarith [abs_nonneg (g x), hpos.le, hle]
  have hexpn : ∃ a : ℝ, 0 < a ∧ Integrable (fun x => Real.exp (a * |x|)) mn := by
    refine ⟨1, one_pos, ?_⟩
    rw [hmn, integrable_withDensity_iff_integrable_smul₀' hmeasn hltn]
    refine (hexp 1 zero_le_one).mono ?_ ?_
    · fun_prop
    · filter_upwards with x
      have hpos : (0:ℝ) < Real.exp (1 * |x|) := Real.exp_pos _
      rw [smul_eq_mul, ENNReal.toReal_ofReal', Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, abs_mul, abs_of_pos hpos]
      have hle : |max (-g x) 0| ≤ |g x| := by
        rcases le_total (-g x) 0 with h | h
        · simp [max_eq_right h]
        · simp [max_eq_left h, abs_of_nonneg h, abs_neg (g x) ▸ le_abs_self (-g x)]
      nlinarith [abs_nonneg (g x), hpos.le, hle]
  -- Determinacy forces the two parts to be the same measure ...
  have hEq : mp = mn :=
    Measure.ext_of_forall_integral_pow_eq_of_exists_integrable_exp hexpp hexpn hmoments
  -- ... hence the densities agree a.e., hence `g⁺ = g⁻` a.e., hence `g = 0` a.e.
  rw [hmp, hmn, withDensity_eq_iff_of_sigmaFinite hmeasp hmeasn] at hEq
  filter_upwards [hEq] with x hx
  have h := congrArg ENNReal.toReal hx
  rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal'] at h
  rcases le_total (g x) 0 with hle | hle
  · rw [max_eq_right hle, max_eq_left (neg_nonneg.mpr hle)] at h
    simpa using h.symm
  · rw [max_eq_left hle, max_eq_right (neg_nonpos.mpr hle)] at h
    simpa using h

end TauCeti
