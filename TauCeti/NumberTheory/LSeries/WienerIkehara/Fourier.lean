/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import TauCeti.NumberTheory.LSeries.Continuity

/-!
# Fourier identities for Wiener--Ikehara

The Fourier proof of Wiener--Ikehara starts by testing a Dirichlet series against an integrable
function on a vertical line. This file records the two exact identities used in that step. The
first exchanges the Dirichlet series with the integral. The second computes the contribution of
the simple pole at `s = 1`. Their combination expresses the difference as the integral of the
pole-subtracted remainder, a function agreeing with `LSeries a - A / (s - 1)` on the open
vertical line `Re s = sigma`; nothing about its boundary behaviour is asserted or used here.

## Main results

* `TauCeti.LSeries.tsum_term_mul_fourier_eq_integral` is the Fourier identity for a
  convergent Dirichlet series.
* `TauCeti.LSeries.integral_exp_mul_fourier_eq` computes the pole term.
* `TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral` combines the two when a named
  function agrees with the pole-subtracted remainder on the vertical line.

## Provenance

The proofs are adapted from `PrimeNumberTheoremAnd/Wiener.lean` in the Apache-2.0
`AxiomMath/PrimeNumberTheoremAnd` repository, revision
`2667e414c38e5a5dc9aa1946f16f13001e5cd3ed`. The source declarations are `first_fourier`,
`second_fourier`, and `limiting_fourier_aux`. The statements here use Mathlib's
`LSeriesSummable` directly, remove the source project's local `nterm` wrapper, and rely on
Mathlib's APIs together with the local vertical-line continuity theorem
`TauCeti.LSeries.continuous_LSeries_vertical`.

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
theorem tsum_term_mul_fourier_eq_integral (hpsi : Integrable psi) (hx : 0 < x)
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
  have harg (u : ℝ) : (1 - (sigma : ℂ)) * u = -(u * (sigma - 1)) := by ring
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact (integrableOn_exp_mul_complex_Ioi (a := 1 - (sigma : ℂ)) (by simp; linarith)
    _).congr_fun (fun u _ ↦ by simp only [harg]) measurableSet_Ioi

private lemma poleFubiniIntegrable (hpsi : Integrable psi) (hsigma : 1 < sigma) (x : ℝ) :
    Integrable (Function.uncurry fun (u v : ℝ) ↦
        (Real.exp (-u * (sigma - 1)) : ℂ) *
          ((fourierChar (-(v * (u / (2 * π)))) : ℂ) * psi v))
      ((volume.restrict (Ici (-Real.log x))).prod volume) := by
  constructor
  · exact AEStronglyMeasurable.mul (Measurable.aestronglyMeasurable (by fun_prop))
      (AEStronglyMeasurable.mul (Measurable.aestronglyMeasurable (by fun_prop))
        hpsi.aestronglyMeasurable.comp_snd)
  · let f₁ : ℝ → ENNReal := fun u ↦ ‖cexp (-(u * (sigma - 1)))‖ₑ
    let f₂ : ℝ → ENNReal := fun v ↦ ‖psi v‖ₑ
    suffices ∫⁻ p : ℝ × ℝ, f₁ p.1 * f₂ p.2
        ∂((volume.restrict (Ici (-Real.log x))).prod volume) < ⊤ by
      simpa [hasFiniteIntegral_iff_enorm, enorm_eq_nnnorm, Function.uncurry,
        Complex.norm_exp]
    refine (lintegral_prod_mul ?_ ?_).trans_lt ?_ <;> try fun_prop
    exact ENNReal.mul_lt_top (exp_mul_integrableOn_Ici hsigma x).2 hpsi.2

private lemma polePrimitive_at_lowerEndpoint (hx : 0 < x) (t sigma : ℝ) :
    -cexp ((1 - sigma - t * I) * ((-Real.log x : ℝ) : ℂ)) / (1 - sigma - t * I) =
      (x ^ (sigma - 1) : ℝ) * (1 / (sigma + t * I - 1)) * x ^ (t * I) := by
  have harg : (1 - (sigma : ℂ) - t * I) * ((-Real.log x : ℝ) : ℂ) =
      Real.log x * ((sigma - 1) + t * I) := by
    push_cast
    ring
  have hflip : (1 - (sigma : ℂ) - t * I) = -((sigma : ℂ) + t * I - 1) := by ring
  calc
    _ = cexp (Real.log x * ((sigma - 1) + t * I)) * (sigma + t * I - 1)⁻¹ := by
      rw [harg, hflip, div_neg, neg_div, neg_neg, div_eq_mul_inv]
    _ = x ^ ((sigma - 1) + t * I) * (sigma + t * I - 1)⁻¹ := by
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), Complex.ofReal_log hx.le]
    _ = x ^ ((sigma : ℂ) - 1) * x ^ (t * I) * (sigma + t * I - 1)⁻¹ := by
      rw [Complex.cpow_add _ _ (ofReal_ne_zero.mpr hx.ne')]
    _ = _ := by rw [ofReal_cpow hx.le]; push_cast; ring

/-- The one-sided Laplace transform `∫ u in Ici (-log x), exp (-u * (sigma - 1)) * 𝓕 psi (u / 2π)`
equals `x ^ (sigma - 1)` times the Fourier integral of the simple pole `1 / (s - 1)` on the line
`Re s = sigma`. This is the pole term subtracted in the Wiener--Ikehara boundary argument, and the
factor `x ^ (sigma - 1)` is the normalization that makes it match the Dirichlet-series identity. -/
theorem integral_exp_mul_fourier_eq (hpsi : Integrable psi) (hx : 0 < x) (hsigma : 1 < sigma) :
    ∫ u in Ici (-Real.log x), Real.exp (-u * (sigma - 1)) *
        FourierTransform.fourier psi (u / (2 * π)) =
      (x ^ (sigma - 1) : ℝ) *
        ∫ t : ℝ, (1 / (sigma + t * I - 1)) * psi t * x ^ (t * I) := by
  conv in (Real.exp _ : ℂ) * _ =>
    rw [Real.fourier_real_eq, ← smul_eq_mul, ← integral_smul]
  rw [MeasureTheory.integral_integral_swap]
  swap
  · exact poleFubiniIntegrable hpsi hsigma x
  rw [← integral_const_mul]
  congr 1
  ext t
  have hpull (b c d : ℂ) : b * (c * psi t * d) = b * c * d * psi t := by ring
  rw [hpull]
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
  rw [integral_Ici_eq_integral_Ioi,
    integral_exp_mul_complex_Ioi (by simp; linarith) (-Real.log x)]
  exact polePrimitive_at_lowerEndpoint hx t sigma

/-! ### Subtracting the pole -/

/-- Subtracting the simple-pole Fourier identity from the Dirichlet-series identity leaves exactly
the integral of the pole-subtracted remainder `G`. Only the values of `G` on the vertical line
`Re s = sigma` enter, so no continuity or limiting behaviour of `G` on the boundary line is
assumed here. This is the form used before sending `sigma` to `1` in the Wiener--Ikehara
argument. -/
theorem tsum_term_mul_fourier_sub_pole_eq_integral {G : ℂ → ℂ} {A : ℂ}
    (hG : ∀ t : ℝ, G (sigma + t * I) = LSeries a (sigma + t * I) -
      A / (sigma + t * I - 1))
    (hpsi : Integrable psi) (hx : 0 < x)
    (hsigma : 1 < sigma) (hsigmaSum : LSeriesSummable a (sigma : ℂ)) :
    (∑' n : ℕ, _root_.LSeries.term a sigma n *
        FourierTransform.fourier psi (1 / (2 * π) * Real.log (n / x))) -
      A * (x ^ (1 - sigma) : ℝ) *
        ∫ u in Ici (-Real.log x), Real.exp (-u * (sigma - 1)) *
          FourierTransform.fourier psi (u / (2 * π)) =
      ∫ t : ℝ, G (sigma + t * I) * psi t * x ^ (t * I) := by
  have hseries := tsum_term_mul_fourier_eq_integral hpsi hx hsigmaSum
  have hpole := integral_exp_mul_fourier_eq hpsi hx hsigma
  have hxpow : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [hx])
  have hxnorm (t : ℝ) : ‖(x : ℂ) ^ (t * I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp
  have hdenom (t : ℝ) : (sigma : ℂ) + t * I - 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  -- The two integrands are bounded multiples of `psi`, so `Integrable psi` suffices.
  have hLbound (t : ℝ) : ‖LSeries a ((sigma : ℂ) + t * I) * (x : ℂ) ^ (t * I)‖ ≤
      ∑' n : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) n‖ := by
    rw [norm_mul, hxnorm, mul_one]
    calc
      ‖LSeries a ((sigma : ℂ) + t * I)‖
          ≤ ∑' n : ℕ, ‖_root_.LSeries.term a ((sigma : ℂ) + t * I) n‖ :=
        norm_tsum_le_tsum_norm (summable_norm_iff.mpr (hsigmaSum.of_re_le_re (by simp)))
      _ = _ := by
        refine tsum_congr fun n ↦ ?_
        simp only [_root_.LSeries.norm_term_eq]
        simp
  have hpolebound (t : ℝ) :
      ‖1 / ((sigma : ℂ) + t * I - 1) * (x : ℂ) ^ (t * I)‖ ≤ (sigma - 1)⁻¹ := by
    rw [norm_mul, hxnorm, mul_one, norm_div, norm_one, one_div]
    refine inv_anti₀ (by linarith) ?_
    calc
      sigma - 1 = ((sigma : ℂ) + t * I - 1).re := by simp
      _ ≤ _ := re_le_norm _
  have hseriesI : Integrable fun t : ℝ ↦
      LSeries a (sigma + t * I) * psi t * x ^ (t * I) := by
    exact (hpsi.bdd_mul (f := fun t : ℝ ↦ LSeries a ((sigma : ℂ) + t * I) * (x : ℂ) ^ (t * I))
      ((continuous_LSeries_vertical hsigmaSum).mul hxpow).aestronglyMeasurable
      (.of_forall hLbound)).congr (.of_forall fun t ↦ by ring)
  have hpoleI : Integrable fun t : ℝ ↦
      A * (x ^ (1 - sigma) : ℝ) *
        ((x ^ (sigma - 1) : ℝ) * ((1 / (sigma + t * I - 1)) * psi t * x ^ (t * I))) := by
    have hbdd : Integrable fun t : ℝ ↦
        1 / ((sigma : ℂ) + t * I - 1) * (x : ℂ) ^ (t * I) * psi t := by
      refine hpsi.bdd_mul (f := fun t : ℝ ↦ 1 / ((sigma : ℂ) + t * I - 1) * (x : ℂ) ^ (t * I))
        ?_ (.of_forall hpolebound)
      exact ((continuous_const.div (by fun_prop) hdenom).mul hxpow).aestronglyMeasurable
    exact (hbdd.const_mul (A * (x ^ (1 - sigma) : ℝ) * (x ^ (sigma - 1) : ℝ))).congr
      (.of_forall fun t ↦ by ring)
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
  rw [hG t, sub_mul]
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
