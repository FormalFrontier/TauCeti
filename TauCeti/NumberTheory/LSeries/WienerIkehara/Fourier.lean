/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.NumberTheory.LSeries.Convergence

/-!
# Fourier identities for Wiener--Ikehara

The Fourier proof of Wiener--Ikehara starts by testing a Dirichlet series against an integrable
function on a vertical line. This file records the two exact identities used in that step. The
first exchanges the Dirichlet series with the integral. The second computes the contribution of
the simple pole at `s = 1`. Their combination expresses the difference through the continuous
boundary remainder.

## Main results

* `TauCeti.LSeries.tsum_term_mul_fourierIntegral_eq_integral` is the Fourier identity for a
  convergent Dirichlet series.
* `TauCeti.LSeries.integral_exp_mul_fourierIntegral_eq` computes the pole term.
* `TauCeti.LSeries.tsum_term_mul_fourierIntegral_sub_pole` combines the two when a named function
  agrees with the boundary remainder.

These identities are the opening analytic step in Layer 9.1 of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`. They do not assert a Tauberian conclusion:
the later argument still has to take the boundary limit, derive the Chebyshev bound, and remove
the smoothing.

## Provenance

The proofs are adapted from `PrimeNumberTheoremAnd/Wiener.lean` in the Apache-2.0
`AxiomMath/PrimeNumberTheoremAnd` repository, revision
`2667e414c38e5a5dc9aa1946f16f13001e5cd3ed`. The source declarations are `first_fourier`,
`second_fourier`, and `limiting_fourier_aux`. The statements here use Mathlib's
`LSeriesSummable` directly, remove the source project's local `nterm` wrapper, and require only
Mathlib imports.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
-/

public section

namespace TauCeti.LSeries

open Complex Filter FourierTransform MeasureTheory Real Set
open scoped ComplexConjugate Real Topology

variable {a : ℕ → ℂ} {psi : ℝ → ℂ} {x sigma t : ℝ}

private instance : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)

private instance : BorelSpace Circle :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)

private lemma fourierIntegrand_aemeasurable (hpsi : AEStronglyMeasurable psi)
    (x : ℝ) (n : ℕ) :
    AEMeasurable fun u : ℝ ↦
      (‖fourierChar (-(u * (1 / (2 * π) * Real.log (n / x)))) • psi u‖ₑ : ENNReal) := by
  fun_prop

private lemma two_pi_mul_neg_log_scale (y x : ℝ) (n : ℕ) :
    (2 : ℂ) * π * -(y * (1 / (2 * π) * Real.log (n / x))) =
      -(y * Real.log (n / x)) := by
  calc
    _ = -(y * (((2 : ℂ) * π) / (2 * π) * Real.log (n / x))) := by ring
    _ = _ := by rw [div_self (by norm_num), one_mul]

private lemma term_mul_fourierChar (hx : 0 < x) (a : ℕ → ℂ) (n : ℕ) (y sigma : ℝ) :
    _root_.LSeries.term a sigma n *
        fourierChar (-(y * (1 / (2 * π) * Real.log (n / x)))) • psi y =
      _root_.LSeries.term a (sigma + y * I) n • (psi y * x ^ (y * I)) := by
  by_cases hn : n = 0
  · simp [_root_.LSeries.term, hn]
  simp only [_root_.LSeries.term, hn, ite_false]
  calc
    _ = (a n * (cexp ((2 * π * -(y * (1 / (2 * π) * Real.log (n / x)))) * I) /
        ↑((n : ℝ) ^ sigma))) • psi y := by
      rw [Circle.smul_def, fourierChar_apply, ofReal_cpow (by positivity)]
      simp only [one_div, mul_inv_rev, mul_neg, ofReal_neg, ofReal_mul, ofReal_ofNat,
        ofReal_inv, neg_mul, smul_eq_mul, ofReal_natCast]
      ring
    _ = (a n * (x ^ (y * I) / n ^ (sigma + y * I))) • psi y := by
      congr 2
      have hnpos : 0 < (n : ℝ) := by positivity
      have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      rw [Real.rpow_def_of_pos hnpos, Complex.cpow_def_of_ne_zero hx0,
        Complex.cpow_def_of_ne_zero hn0]
      push_cast
      rw [two_pi_mul_neg_log_scale, Real.log_div hnpos.ne' hx.ne']
      push_cast
      rw [Complex.ofReal_log hx.le]
      conv_rhs => rw [← Complex.exp_sub]
      conv_lhs => rw [div_eq_mul_inv, ← Complex.exp_neg, ← Complex.exp_add]
      congr 1
      ring
    _ = _ := by simp; ring

private lemma summable_enorm_term_ne_top (hsigma : LSeriesSummable a (sigma : ℂ)) :
    ∑' n, (‖_root_.LSeries.term a sigma n‖₊ : ENNReal) ≠ ⊤ := by
  simp_rw [ENNReal.tsum_coe_ne_top_iff_summable_coe, ← norm_toNNReal]
  norm_cast
  exact Summable.toNNReal (summable_norm_iff.mpr hsigma)

/-- Testing an absolutely convergent Dirichlet series against an integrable function on the
vertical line `Re s = sigma` can be done term by term. The Fourier transform is evaluated at the
logarithmic scale `(2π)⁻¹ log (n / x)` dictated by the factor `x ^ (it)`. -/
theorem tsum_term_mul_fourierIntegral_eq_integral (hpsi : Integrable psi) (hx : 0 < x)
    (hsigma : LSeriesSummable a (sigma : ℂ)) :
    ∑' n : ℕ, _root_.LSeries.term a sigma n *
        FourierTransform.fourier psi (1 / (2 * π) * Real.log (n / x)) =
      ∫ t : ℝ, LSeries a (sigma + t * I) * psi t * x ^ (t * I) := by
  calc
    _ = ∑' n : ℕ, _root_.LSeries.term a sigma n *
        ∫ u : ℝ, fourierChar (-(u * (1 / (2 * π) * Real.log (n / x)))) • psi u := by
      simp only [Real.fourier_eq, one_div, mul_inv_rev, RCLike.inner_apply', conj_trivial]
    _ = ∑' n : ℕ, ∫ u : ℝ,
        _root_.LSeries.term a sigma n *
          fourierChar (-(u * (1 / (2 * π) * Real.log (n / x)))) • psi u := by
      simp only [integral_const_mul]
    _ = ∫ u : ℝ, ∑' n : ℕ,
        _root_.LSeries.term a sigma n *
          fourierChar (-(u * (1 / (2 * π) * Real.log (n / x)))) • psi u := by
      refine (integral_tsum (fun _ ↦ ?_) ?_).symm
      · apply AEMeasurable.aestronglyMeasurable
        apply AEMeasurable.mul
        · exact aemeasurable_const
        · exact (by fun_prop : Measurable fun u : ℝ ↦
            fourierChar (-(u * (1 / (2 * π) * Real.log (_ / x))))).aemeasurable.smul
              hpsi.aemeasurable
      · simp only [enorm_mul]
        simp_rw [lintegral_const_mul'' _ (fourierIntegrand_aemeasurable hpsi.aestronglyMeasurable
          x _)]
        calc
          _ = (∑' n : ℕ, ‖_root_.LSeries.term a sigma n‖ₑ) *
              ∫⁻ u : ℝ, ‖psi u‖ₑ := by
            simp [ENNReal.tsum_mul_right, enorm_eq_nnnorm]
          _ ≠ ⊤ := ENNReal.mul_ne_top (summable_enorm_term_ne_top hsigma)
            (ne_top_of_lt hpsi.2)
    _ = _ := by
      congr 1
      ext y
      simp_rw [mul_assoc (LSeries a _), ← smul_eq_mul (a := LSeries a _), _root_.LSeries]
      rw [← Summable.tsum_smul_const]
      · simp_rw [term_mul_fourierChar hx]
      · exact hsigma.of_re_le_re (by simp)

/-! ### The simple-pole term -/

private lemma exp_mul_integrableOn_Ici (hsigma : 1 < sigma) (x : ℝ) :
    IntegrableOn (fun u : ℝ ↦ cexp (-(u * (sigma - 1)))) (Ici (-Real.log x)) := by
  norm_cast
  suffices IntegrableOn (fun u : ℝ ↦ Real.exp (-(u * (sigma - 1))))
      (Ici (-Real.log x)) _ from this.ofReal
  simp_rw [show ∀ u : ℝ, -(u * (sigma - 1)) = -(sigma - 1) * u by intro; ring]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_exp_mul_Ioi (a := -(sigma - 1)) (by linarith) _

private lemma poleFubiniIntegrable (hpsiM : Measurable psi) (hpsi : Integrable psi)
    (hsigma : 1 < sigma) (x : ℝ) :
    let nu : Measure (ℝ × ℝ) := (volume.restrict (Ici (-Real.log x))).prod volume
    Integrable (Function.uncurry fun (u v : ℝ) ↦
      (Real.exp (-u * (sigma - 1)) : ℂ) •
        (fourierChar (Multiplicative.ofAdd (-(v * (u / (2 * π))))) : ℂ) • psi v) nu := by
  intro nu
  constructor
  · apply Measurable.aestronglyMeasurable
    change Measurable (Function.uncurry fun (u v : ℝ) ↦
      (Real.exp (-u * (sigma - 1)) : ℂ) • fourierChar (-(v * (u / (2 * π)))) • psi v)
    simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one,
      smul_eq_mul]
    fun_prop
  · let f₁ : ℝ → ENNReal := fun u ↦ ‖cexp (-(u * (sigma - 1)))‖ₑ
    let f₂ : ℝ → ENNReal := fun v ↦ ‖psi v‖ₑ
    suffices ∫⁻ p : ℝ × ℝ, f₁ p.1 * f₂ p.2 ∂nu < ⊤ by
      simpa [hasFiniteIntegral_iff_enorm, enorm_eq_nnnorm, Function.uncurry,
        Complex.norm_exp]
    refine (lintegral_prod_mul ?_ ?_).trans_lt ?_ <;> try fun_prop
    exact ENNReal.mul_lt_top (exp_mul_integrableOn_Ici hsigma x).2 hpsi.2

private lemma exp_complex_integrableOn_Ioi (hsigma : 1 < sigma) (x t : ℝ) :
    IntegrableOn (fun u : ℝ ↦ cexp ((1 - sigma - t * I) * u)) (Ioi (-Real.log x)) :=
  integrableOn_exp_mul_complex_Ioi (by simp; linarith) _

private lemma polePrimitive_at_lowerEndpoint (hx : 0 < x) (t sigma : ℝ) :
    -(cexp (-((1 - sigma - t * I) * Real.log x)) / (1 - sigma - t * I)) =
      (x ^ (sigma - 1) : ℝ) * (sigma + t * I - 1)⁻¹ * x ^ (t * I) := by
  calc
    _ = cexp (Real.log x * ((sigma - 1) + t * I)) * (sigma + t * I - 1)⁻¹ := by
      rw [← div_neg]
      ring_nf
    _ = x ^ ((sigma - 1) + t * I) * (sigma + t * I - 1)⁻¹ := by
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), Complex.ofReal_log hx.le]
    _ = x ^ ((sigma : ℂ) - 1) * x ^ (t * I) * (sigma + t * I - 1)⁻¹ := by
      rw [Complex.cpow_add _ _ (ofReal_ne_zero.mpr hx.ne')]
    _ = _ := by rw [ofReal_cpow hx.le]; push_cast; ring

/-- The Fourier integral of the simple pole `1 / (s - 1)` on the line `Re s = sigma` equals a
one-sided Laplace transform of the Fourier transform. This is the pole term subtracted in the
Wiener--Ikehara boundary argument. -/
theorem integral_exp_mul_fourierIntegral_eq (hpsiM : Measurable psi) (hpsi : Integrable psi)
    (hx : 0 < x) (hsigma : 1 < sigma) :
    ∫ u in Ici (-Real.log x), Real.exp (-u * (sigma - 1)) *
        FourierTransform.fourier psi (u / (2 * π)) =
      (x ^ (sigma - 1) : ℝ) *
        ∫ t : ℝ, (1 / (sigma + t * I - 1)) * psi t * x ^ (t * I) := by
  conv in (Real.exp _ : ℂ) * _ =>
    rw [Real.fourier_real_eq, ← smul_eq_mul, ← integral_smul]
  rw [MeasureTheory.integral_integral_swap]
  swap
  · exact poleFubiniIntegrable hpsiM hpsi hsigma x
  rw [← integral_const_mul]
  congr 1
  ext t
  rw [show ∀ b c d : ℂ, b * (c * psi t * d) = (b * c * d) * psi t by
    intro b c d; ring]
  conv =>
    lhs
    enter [2]
    ext u
    rw [Circle.smul_def, fourierChar_apply]
  push_cast
  simp_rw [smul_eq_mul]
  simp_rw [← mul_assoc]
  simp_rw [← Complex.exp_add]
  rw [integral_mul_const]
  congr 1
  have hexp (u : ℝ) :
      -u * (sigma - 1) + 2 * π * -(t * (u / (2 * π))) * I =
        (1 - sigma - t * I) * u := by
    calc
      _ = -u * (sigma - 1) + (2 * π) / (2 * π) * -(t * u) * I := by ring
      _ = -u * (sigma - 1) + 1 * -(t * u) * I := by rw [div_self (by norm_num)]
      _ = _ := by ring
  simp_rw [hexp]
  let c : ℂ := 1 - sigma - t * I
  have hc : c ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [c] at hre
    linarith
  let p : ℝ → ℂ := fun u ↦ cexp (c * u) / c
  have hpderiv : ∀ u ∈ Ici (-Real.log x), HasDerivAt p (cexp (c * u)) u := by
    intro u _
    rw [show cexp (c * u) = cexp (c * u) * (c * 1) / c by field_simp]
    exact (hasDerivAt_id' u).ofReal_comp.const_mul c |>.cexp.div_const c
  have hpzero : Tendsto p atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    suffices Tendsto (fun u : ℝ ↦ ‖cexp (c * u)‖ / ‖c‖) atTop (𝓝 (0 / ‖c‖)) by
      simpa [p] using this
    apply Filter.Tendsto.div_const
    suffices Tendsto (fun u : ℝ ↦ u * (1 - sigma)) atTop atBot by
      simpa [Complex.norm_exp, mul_comm (1 - sigma), c] using this
    exact Tendsto.atTop_mul_const_of_neg (by linarith) fun ⦃s⦄ h ↦ h
  rw [integral_Ici_eq_integral_Ioi,
    integral_Ioi_of_hasDerivAt_of_tendsto' hpderiv (exp_complex_integrableOn_Ioi hsigma x t)
      hpzero]
  simpa [p, c] using polePrimitive_at_lowerEndpoint hx t sigma

/-! ### Subtracting the pole -/

private lemma continuous_LSeries_vertical (hsigma : LSeriesSummable a (sigma : ℂ)) :
    Continuous fun t : ℝ ↦ LSeries a (sigma + t * I) := by
  have hterm n : Continuous fun t : ℝ ↦ _root_.LSeries.term a (sigma + t * I) n := by
    by_cases hn : n = 0
    · simpa [_root_.LSeries.term, hn] using continuous_const
    · simp only [_root_.LSeries.term, hn, ite_false]
      exact continuous_const.div₀ (continuous_const.cpow (by fun_prop) (by simp [hn]))
        (fun t ↦ by simp [hn])
  have hnorm n (t : ℝ) :
      ‖_root_.LSeries.term a (sigma + t * I) n‖ =
        ‖_root_.LSeries.term a sigma n‖ := by
    simp only [_root_.LSeries.norm_term_eq]
    simp
  exact continuous_tsum hterm (summable_norm_iff.mpr hsigma)
    (fun n t ↦ le_of_eq (hnorm n t))

/-- Subtracting the simple-pole Fourier identity from the Dirichlet-series identity leaves exactly
the integral of the boundary remainder. This is the form used before sending `sigma` to `1` in
the Wiener--Ikehara argument. Compact support supplies the integrability needed to combine the two
integrals; no boundary continuity is needed for this algebraic step. -/
theorem tsum_term_mul_fourierIntegral_sub_pole {G : ℂ → ℂ} {A : ℂ}
    (hG : Set.EqOn G (fun s ↦ LSeries a s - A / (s - 1)) {s : ℂ | 1 < s.re})
    (hpsiC : Continuous psi) (hpsiK : HasCompactSupport psi) (hx : 0 < x)
    (hsigma : 1 < sigma) (hsigmaSum : LSeriesSummable a (sigma : ℂ)) :
    (∑' n : ℕ, _root_.LSeries.term a sigma n *
        FourierTransform.fourier psi (1 / (2 * π) * Real.log (n / x))) -
      A * (x ^ (1 - sigma) : ℝ) *
        ∫ u in Ici (-Real.log x), Real.exp (-u * (sigma - 1)) *
          FourierTransform.fourier psi (u / (2 * π)) =
      ∫ t : ℝ, G (sigma + t * I) * psi t * x ^ (t * I) := by
  have hpsi : Integrable psi := hpsiC.integrable_of_hasCompactSupport hpsiK
  have hseries := tsum_term_mul_fourierIntegral_eq_integral hpsi hx hsigmaSum
  have hpole := integral_exp_mul_fourierIntegral_eq hpsiC.measurable hpsi hx hsigma
  have hxpow : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [hx])
  have hseriesC : Continuous fun t : ℝ ↦
      LSeries a (sigma + t * I) * psi t * x ^ (t * I) :=
    ((continuous_LSeries_vertical hsigmaSum).mul hpsiC).mul hxpow
  have hseriesI : Integrable fun t : ℝ ↦
      LSeries a (sigma + t * I) * psi t * x ^ (t * I) :=
    hseriesC.integrable_of_hasCompactSupport hpsiK.mul_left.mul_right
  have hdenom (t : ℝ) : sigma + t * I - 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hpoleC : Continuous fun t : ℝ ↦
      A * (x ^ (1 - sigma) : ℝ) *
        ((x ^ (sigma - 1) : ℝ) * ((1 / (sigma + t * I - 1)) * psi t * x ^ (t * I))) := by
    simp only [one_div, ← mul_assoc]
    refine ((continuous_const.mul (Continuous.inv₀ ?_ hdenom)).mul hpsiC).mul hxpow
    fun_prop
  have hpoleI : Integrable fun t : ℝ ↦
      A * (x ^ (1 - sigma) : ℝ) *
        ((x ^ (sigma - 1) : ℝ) * ((1 / (sigma + t * I - 1)) * psi t * x ^ (t * I))) :=
    hpoleC.integrable_of_hasCompactSupport hpsiK.mul_left.mul_right.mul_left.mul_left
  have hpoleConst :
      A * (x ^ (1 - sigma) : ℝ) *
          ((x ^ (sigma - 1) : ℝ) *
            ∫ t : ℝ, (1 / (sigma + t * I - 1)) * psi t * x ^ (t * I)) =
        ∫ t : ℝ, A * (x ^ (1 - sigma) : ℝ) *
          ((x ^ (sigma - 1) : ℝ) *
            ((1 / (sigma + t * I - 1)) * psi t * x ^ (t * I))) := by
    rw [integral_const_mul, integral_const_mul]
  rw [hseries, hpole, hpoleConst, ← integral_sub hseriesI hpoleI]
  apply integral_congr_ae
  filter_upwards [] with t
  have ht : 1 < ((sigma : ℂ) + t * I).re := by simpa using hsigma
  rw [hG ht, sub_mul]
  have hxpowOne :
      ((x ^ (1 - sigma) : ℝ) : ℂ) * ((x ^ (sigma - 1) : ℝ) : ℂ) = 1 := by
    norm_cast
    rw [← Real.rpow_add hx]
    simp
  calc
    _ = LSeries a (sigma + t * I) * psi t * x ^ (t * I) -
        A * (((x ^ (1 - sigma) : ℝ) : ℂ) * ((x ^ (sigma - 1) : ℝ) : ℂ)) *
          ((sigma + t * I - 1)⁻¹ * psi t * x ^ (t * I)) := by ring
    _ = _ := by rw [hxpowOne]; ring

end TauCeti.LSeries
