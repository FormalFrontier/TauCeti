/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.LSeries.Convolution
public import Mathlib.NumberTheory.LSeries.Deriv
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.VonMangoldt

/-!
# The logarithmic derivative of the Dirichlet series of an ideal weight

For a completely multiplicative ideal arithmetic function `χ` — a multiplicative ideal weight, for
instance — the von Mangoldt transform `χ Λ` is the coefficient system of the logarithmic derivative
of the Dirichlet series of `χ`: on the half-plane where the ideal-indexed series of `χ` converges
absolutely, `(∑_A χ(A) Λ(A) N(A)^{-s}) L(s) = -L'(s)`, hence
`∑_A χ(A) Λ(A) N(A)^{-s} = -L'(s) / L(s)` at every point of that half-plane at which `L(s) ≠ 0`.
The nonvanishing is an explicit hypothesis of the quotient forms below: it is not proved here,
since for the Dedekind zeta function it is the Euler product of Layer 3.

The proof is purely algebraic apart from one convergence estimate. The divisor sum
`TauCeti.IdealArithmeticFunction.convolution_vonMangoldt_one` identifies `Λ ⋆ 1` with the ideal
logarithm, complete multiplicativity twists that identity into
`(χ Λ) ⋆ χ = (log N) χ`, regrouping by absolute norm turns the ideal convolution into Mathlib's
Dirichlet convolution, and the absolute norm is constant on a norm fibre, so the regrouped
`(log N) χ` is exactly Mathlib's `LSeries.logMul` of the regrouped `χ`. No Euler product is
needed.  Nothing beyond complete multiplicativity is used, so none of this asks for the finiteness
condition carried by `TauCeti.MultiplicativeIdealWeight`.

## Main results

* `TauCeti.normCoeff_log_mul`: regrouping `(log N) f` by absolute norm is `LSeries.logMul` of the
  regrouping of `f`.
* `TauCeti.summable_idealTerm_vonMangoldtTransform`: the ideal-indexed series of the von Mangoldt
  transform of `f` converges absolutely wherever that of `f` does.
* `TauCeti.IdealArithmeticFunction.convolution_vonMangoldtTransform`: the convolution identity
  `(χ Λ) ⋆ χ = (log N) χ` for a completely multiplicative `χ`.
* `TauCeti.LSeries_normCoeff_vonMangoldtTransform_mul_eq_neg_deriv`: the identity in product form,
  on the whole half-plane and with no nonvanishing hypothesis.
* `TauCeti.LSeries_normCoeff_vonMangoldtTransform_eq_neg_logDeriv`: the logarithmic derivative
  identity, assuming `L(s) ≠ 0`.
* `TauCeti.LSeries_normCoeff_vonMangoldt_eq_neg_logDeriv_dedekindZeta`: its instance at the
  constant-one weight, `-ζ_K'(s) / ζ_K(s) = ∑_A Λ(A) N(A)^{-s}` for `Re s > 1` with `ζ_K(s) ≠ 0`.

## Roadmap role

This completes Layer **2.3** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, whose target
asks for "the exact coefficient identity for the logarithmic derivative of an Euler product on its
absolute-convergence half-plane". Layer 10.1 consumes the trivial-weight instance as the exact
nonnegative von Mangoldt coefficient system on `Re s > 1`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters I.2 and II.
* Mathlib's `ArithmeticFunction.vonMangoldt_mul_zeta` is the rational-prime analogue of the divisor
  sum used here, and Mathlib's `LSeries_deriv` supplies the analytic half of the identity.
-/

public section

namespace TauCeti

open NumberField LSeries
open scoped nonZeroDivisors NumberField ComplexOrder

variable {K : Type*} [Field K] [NumberField K]

/-! ### Regrouping the ideal logarithm -/

/-- Regrouping the pointwise product of the ideal logarithm with `f` multiplies the `n`-th
coefficient by `log n`: the absolute norm is constant on a norm fibre, so the logarithm factors out
of the fibre sum. This identifies it with Mathlib's `LSeries.logMul`. -/
theorem normCoeff_log_mul (f : IdealArithmeticFunction K) :
    (normCoeff K (IdealArithmeticFunction.log * f) : ℕ → ℂ) =
      LSeries.logMul (normCoeff K f) := by
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [normCoeff_eq_sum_normFiber, LSeries.logMul, normCoeff_eq_sum_normFiber, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I hI ↦ ?_
  rw [Pi.mul_apply, IdealArithmeticFunction.log_apply, (mem_normFiber K).mp hI,
    Complex.natCast_log]

/-! ### Absolute convergence of the twisted series -/

/-- **The ideal logarithm does not increase the abscissa.** The ideal-indexed Dirichlet series of
`(log N) f` converges absolutely wherever that of `f` does, because `log t` is dominated by every
positive power of `t`. This is the ideal-indexed analogue of Mathlib's
`LSeries.abscissaOfAbsConv_logMul`. -/
theorem summable_idealTerm_log_mul {f : IdealArithmeticFunction K} {s : ℂ}
    (hs : idealAbscissaOfAbsConv K f < s.re) :
    Summable (idealTerm K (IdealArithmeticFunction.log * f) s) := by
  obtain ⟨x, hx, hxs⟩ := exists_summable_idealTerm_lt_re K hs
  have hδ : 0 < s.re - x := by linarith
  rw [← summable_norm_iff] at hx ⊢
  refine (hx.mul_left (s.re - x)⁻¹).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun I ↦ ?_
  have hN1 : (1 : ℝ) ≤ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I
  have hN0 : (0 : ℝ) < (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) := by linarith
  have hsplit : (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s.re =
      (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (s.re - x) *
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ x := by
    rw [← Real.rpow_add hN0]; ring_nf
  rw [norm_idealTerm, norm_idealTerm, Complex.ofReal_re, Pi.mul_apply, norm_mul,
    IdealArithmeticFunction.log_apply, Complex.norm_real,
    Real.norm_of_nonneg (Real.log_nonneg hN1), hsplit, div_mul_eq_div_div, ← mul_div_assoc]
  gcongr
  calc Real.log (Ideal.absNorm (I : Ideal (𝓞 K))) * ‖f I‖ /
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (s.re - x)
      = Real.log (Ideal.absNorm (I : Ideal (𝓞 K))) /
          (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (s.re - x) * ‖f I‖ := by ring
    _ ≤ (s.re - x)⁻¹ * ‖f I‖ := by
        gcongr
        rw [div_le_iff₀ (Real.rpow_pos_of_pos hN0 _), inv_mul_eq_div]
        exact Real.log_le_rpow_div hN0.le hδ

/-- The ideal-indexed Dirichlet series of the von Mangoldt transform of `f` converges absolutely
wherever that of `f` does, because `Λ (A) ≤ log N(A)`. -/
theorem summable_idealTerm_vonMangoldtTransform {f : IdealArithmeticFunction K} {s : ℂ}
    (hs : idealAbscissaOfAbsConv K f < s.re) :
    Summable (idealTerm K f.vonMangoldtTransform s) := by
  rw [← summable_norm_iff]
  refine (summable_norm_iff.mpr (summable_idealTerm_log_mul hs)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun I ↦ ?_
  rw [norm_idealTerm, norm_idealTerm]
  gcongr
  rw [IdealArithmeticFunction.vonMangoldtTransform_apply, Pi.mul_apply, norm_mul, norm_mul,
    mul_comm]
  gcongr
  exact IdealArithmeticFunction.norm_vonMangoldt_le_norm_log I

/-! ### The logarithmic derivative -/

namespace IdealArithmeticFunction

/-- **The convolution identity behind the logarithmic derivative.** For a completely
multiplicative ideal arithmetic function `f`, convolving the von Mangoldt transform `f Λ` with `f`
gives the pointwise product of the ideal logarithm with `f`. It is the divisor sum `Λ ⋆ 1 = log N`,
twisted by `f`.

Only complete multiplicativity enters, so the hypothesis is stated for a bare ideal arithmetic
function; a `TauCeti.MultiplicativeIdealWeight` supplies it through its multiplicativity. -/
theorem convolution_vonMangoldtTransform {f : IdealArithmeticFunction K}
    (hf : ∀ A B : (Ideal (𝓞 K))⁰, f (A * B) = f A * f B) :
    convolution f.vonMangoldtTransform f = log * f := by
  funext A
  rw [Pi.mul_apply, ← convolution_vonMangoldt_one, convolution_apply, convolution_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hA : A = p.1 * p.2 := (Ideal.mem_divisorsAntidiagonal.mp hp).symm
  simp only [vonMangoldtTransform_apply, Pi.one_apply, hA, hf]
  ring

end IdealArithmeticFunction

/-- Regrouping the convolution identity by absolute norm identifies the Dirichlet-convolution
product of the two regrouped coefficient systems with `LSeries.logMul` of the regrouping of `f`. -/
theorem normCoeff_vonMangoldtTransform_mul {f : IdealArithmeticFunction K}
    (hf : ∀ A B : (Ideal (𝓞 K))⁰, f (A * B) = f A * f B) :
    ((normCoeff K f.vonMangoldtTransform * normCoeff K f : ArithmeticFunction ℂ) : ℕ → ℂ) =
      LSeries.logMul (normCoeff K f) := by
  rw [← normCoeff_convolution, IdealArithmeticFunction.convolution_vonMangoldtTransform hf,
    normCoeff_log_mul]

/-- **The von Mangoldt transform is the coefficient system of the logarithmic derivative**, in
product form: on the half-plane of absolute convergence of the ideal-indexed series of a completely
multiplicative `f`, the `LSeries` of the regrouped `f Λ` times the `LSeries` of the regrouped `f`
is `-L'`. -/
theorem LSeries_normCoeff_vonMangoldtTransform_mul_eq_neg_deriv {f : IdealArithmeticFunction K}
    (hf : ∀ A B : (Ideal (𝓞 K))⁰, f (A * B) = f A * f B) {s : ℂ}
    (hs : idealAbscissaOfAbsConv K f < s.re) :
    LSeries (normCoeff K f.vonMangoldtTransform) s * LSeries (normCoeff K f) s =
      -deriv (LSeries (normCoeff K f)) s := by
  have habs : LSeries.abscissaOfAbsConv (normCoeff K f) < s.re :=
    lt_of_le_of_lt (abscissaOfAbsConv_normCoeff_le K _) hs
  rw [← ArithmeticFunction.LSeries_mul'
      (LSeriesSummable_normCoeff K (summable_idealTerm_vonMangoldtTransform hs))
      (LSeriesSummable_normCoeff K (summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re K hs)),
    normCoeff_vonMangoldtTransform_mul hf, LSeries_deriv habs, neg_neg]

/-- **The exact coefficient identity for the logarithmic derivative.** On the half-plane of
absolute convergence of the ideal-indexed series of a completely multiplicative ideal arithmetic
function `f`, and away from the zeros of its `LSeries`, the `LSeries` of the regrouped von Mangoldt
transform `f Λ` is the negative of the logarithmic derivative.

Every prime power carries a coefficient here; removing the higher prime powers is a later
estimate, not a simplification of this identity. -/
theorem LSeries_normCoeff_vonMangoldtTransform_eq_neg_logDeriv {f : IdealArithmeticFunction K}
    (hf : ∀ A B : (Ideal (𝓞 K))⁰, f (A * B) = f A * f B) {s : ℂ}
    (hs : idealAbscissaOfAbsConv K f < s.re) (hL : LSeries (normCoeff K f) s ≠ 0) :
    LSeries (normCoeff K f.vonMangoldtTransform) s =
      -logDeriv (LSeries (normCoeff K f)) s := by
  rw [logDeriv_apply, ← neg_div, eq_div_iff hL]
  exact LSeries_normCoeff_vonMangoldtTransform_mul_eq_neg_deriv hf hs

/-! ### The Dedekind zeta function -/

/-- **The logarithmic derivative of the Dedekind zeta function**: for `Re s > 1` and away from the
zeros of `ζ_K`, the Dirichlet series with the ideal von Mangoldt coefficients is `-ζ_K'/ζ_K`.

This is the constant-one instance of
`TauCeti.LSeries_normCoeff_vonMangoldtTransform_eq_neg_logDeriv`, whose absolute-convergence
hypothesis is `1 < Re s` here by `TauCeti.idealAbscissaOfAbsConv_one`. The nonvanishing hypothesis
is genuinely assumed: `ζ_K` has no zero on `Re s > 1`, but that is the Euler product of Layer 3 and
is not available yet. -/
theorem LSeries_normCoeff_vonMangoldt_eq_neg_logDeriv_dedekindZeta {s : ℂ} (hs : 1 < s.re)
    (hζ : NumberField.dedekindZeta K s ≠ 0) :
    LSeries (normCoeff K (IdealArithmeticFunction.vonMangoldt : IdealArithmeticFunction K)) s =
      -logDeriv (NumberField.dedekindZeta K) s := by
  have hzeta : NumberField.dedekindZeta K = LSeries (normCoeff K (1 : IdealArithmeticFunction K)) :=
    funext (dedekindZeta_eq_LSeries_normCoeff_one K)
  have hs' : idealAbscissaOfAbsConv K (1 : IdealArithmeticFunction K) < s.re := by
    rw [idealAbscissaOfAbsConv_one]
    exact_mod_cast hs
  have := LSeries_normCoeff_vonMangoldtTransform_eq_neg_logDeriv
    (f := (1 : IdealArithmeticFunction K)) (fun A B ↦ by simp) hs' (by rwa [← hzeta])
  rwa [IdealArithmeticFunction.vonMangoldtTransform_one, ← hzeta] at this

end TauCeti
