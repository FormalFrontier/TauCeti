/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.NumberTheory.LSeries.Convolution
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Data

/-!
# The analytic Euler product of an ideal arithmetic function

`TauCeti.EulerProductData.normCoeff_eq_eulerProduct` identifies the norm coefficients of bundled
Euler-product data with a formal Euler product, coefficient by coefficient. This file supplies the
analytic statement it does not: where the Dirichlet series indexed by the nonzero ideals converges
absolutely, the infinite product of the local Euler factors converges, in the unrestricted sense
of `HasProd` over the height-one primes, to the `LSeries` of the norm coefficients.

The local factor at a height-one prime `P` is the `LSeries` of the canonical local arithmetic
factor, equivalently the prime-power Dirichlet series `∑' e, f (P ^ e) / N(P ^ e) ^ s`. For a
completely multiplicative weight that series is geometric, and the factor takes the familiar
closed form `(1 - χ(P) N(P) ^ (-s))⁻¹`; specializing to the trivial weight gives the Euler
product of the Dedekind zeta function.

## Main definitions

* `TauCeti.EulerProductData.eulerFactor`: the local Euler factor at a height-one prime.

## Main results

* `TauCeti.EulerProductData.hasProd_eulerFactor`: the **analytic Euler product**, when the
  ideal-indexed Dirichlet series converges absolutely at `s`.
* `TauCeti.MultiplicativeIdealWeight.hasProd_eulerFactor`: the same product, with the local factors
  in the closed geometric form available for a completely multiplicative weight.
* `TauCeti.dedekindZeta_eulerProduct_hasProd`: the **Euler product of the Dedekind zeta
  function**, valid on `Re s > 1`.

No nonvanishing statement is made here. An unconditionally convergent product of nonzero factors
may still vanish, so nonvanishing requires additional hypotheses such as convergence of the
reciprocal product.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `EulerProduct` API, whose `Nat.Primes`-indexed statements this file mirrors for the
  height-one primes of a number field.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors NumberField ComplexOrder
open IsDedekindDomain (HeightOneSpectrum)

variable {K : Type*} [Field K] [NumberField K]

namespace EulerProductData

open IdealArithmeticFunction

variable (D : EulerProductData K) {s : ℂ}

/-! ### The local Euler factor -/

/-- The **local Euler factor** of `D` at a height-one prime `P`, evaluated at `s`. -/
noncomputable def eulerFactor (D : EulerProductData K) (P : HeightOneSpectrum (𝓞 K)) (s : ℂ) : ℂ :=
  LSeries (D.localArithmeticFactor P) s

/-- The local Euler factor is the `LSeries` of the canonical local arithmetic factor. -/
theorem eulerFactor_def (D : EulerProductData K) (P : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    D.eulerFactor P s = LSeries (D.localArithmeticFactor P) s := by
  rw [eulerFactor]

/-- The local Euler factor is the Dirichlet series over the powers of `P`. -/
theorem eulerFactor_eq_tsum (D : EulerProductData K) (P : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    D.eulerFactor P s =
      ∑' e : ℕ, idealTerm K D.toIdealArithmeticFunction s
        (P.primeIdealPow e) := by
  have hsupp : Function.support
      (fun n : ℕ ↦ (D.localArithmeticFactor P n : ℂ) / (n : ℂ) ^ s) ⊆
      Set.range fun e : ℕ ↦ Ideal.absNorm P.asIdeal ^ e := by
    intro n hn
    simp only [Function.mem_support, ne_eq, div_eq_zero_iff, not_or] at hn
    by_contra hpow
    exact hn.1 (D.localArithmeticFactor_apply_eq_zero_of_not_exists_pow_eq P hpow)
  rw [eulerFactor_def, LSeries_def₀ (by simp),
    ← (Nat.pow_right_injective
      (NumberField.HeightOneSpectrum.one_lt_absNorm P)).tsum_eq hsupp]
  refine tsum_congr fun e ↦ ?_
  rw [localArithmeticFactor_apply_pow, idealTerm_def,
    P.absNorm_primeIdealPow]

end EulerProductData

namespace IdealArithmeticFunction

variable {f : IdealArithmeticFunction K} {s : ℂ}

/-! ### Restriction to a set of primes, analytically -/

/-- The ideal terms of a restriction of `f` are the ideal terms of `f`, cut off outside the ideals
supported on the prescribed set of primes. -/
theorem idealTerm_supportedPart (f : IdealArithmeticFunction K)
    (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℂ) :
    idealTerm K (supportedPart f S) s =
      Set.indicator {I : (Ideal (𝓞 K))⁰ | Ideal.IsPrimeTo (I : Ideal (𝓞 K)) Sᶜ}
        (idealTerm K f s) := by
  funext I
  by_cases hI : I ∈ {I : (Ideal (𝓞 K))⁰ | Ideal.IsPrimeTo (I : Ideal (𝓞 K)) Sᶜ}
  · rw [Set.indicator_of_mem hI, idealTerm_def, idealTerm_def,
      supportedPart_apply_of_isPrimeTo_compl hI]
  · rw [Set.indicator_of_notMem hI, idealTerm_def,
      supportedPart_apply_of_not_isPrimeTo_compl hI, zero_div]

/-- Restricting to a set of primes never increases an ideal term. -/
theorem norm_idealTerm_supportedPart_le (f : IdealArithmeticFunction K)
    (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    ‖idealTerm K (supportedPart f S) s I‖ ≤ ‖idealTerm K f s I‖ := by
  rw [idealTerm_supportedPart]
  exact norm_indicator_le_norm_self _ _

/-- Absolute convergence of the ideal-indexed Dirichlet series is inherited by every restriction
to a set of primes. -/
theorem summable_idealTerm_supportedPart (hs : Summable (idealTerm K f s))
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    Summable (idealTerm K (supportedPart f S) s) := by
  rw [idealTerm_supportedPart]
  exact hs.indicator _

/-- Absolute convergence of the ideal-indexed Dirichlet series makes every local Euler factor an
absolutely convergent `LSeries`. -/
theorem LSeriesSummable_localArithmeticFactor (hs : Summable (idealTerm K f s))
    (P : HeightOneSpectrum (𝓞 K)) :
    LSeriesSummable (localArithmeticFactor f P) s := by
  rw [← normCoeff_supportedPart_singleton f P]
  exact LSeriesSummable_normCoeff K (summable_idealTerm_supportedPart hs _)

/-- The norm coefficients of the restriction of `f` to no primes are Mathlib's Kronecker delta. -/
theorem coe_normCoeff_supportedPart_empty (hf : f 1 = 1) :
    ⇑(normCoeff K (supportedPart f (∅ : Set (HeightOneSpectrum (𝓞 K))))) = LSeries.delta := by
  rw [supportedPart_empty hf, normCoeff_delta]
  funext n
  simp [ArithmeticFunction.one_apply, LSeries.delta]

end IdealArithmeticFunction

namespace EulerProductData

open IdealArithmeticFunction

variable (D : EulerProductData K) {s : ℂ}

/-- Absolute convergence of the ideal-indexed Dirichlet series makes every bundled local Euler
factor an absolutely convergent `LSeries`. -/
theorem LSeriesSummable_localArithmeticFactor
    (hs : Summable (idealTerm K D.toIdealArithmeticFunction s))
    (P : HeightOneSpectrum (𝓞 K)) :
    LSeriesSummable (D.localArithmeticFactor P) s := by
  rw [D.localArithmeticFactor_eq]
  exact IdealArithmeticFunction.LSeriesSummable_localArithmeticFactor hs P

/-- **Convergence of the finite Euler product.** Where the local Euler factors over a finite set
`S` of primes are absolutely convergent `LSeries`, so are the norm coefficients of the restriction
of `D` to `S`. -/
theorem LSeriesSummable_normCoeff_supportedPart (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ P ∈ S, LSeriesSummable (D.localArithmeticFactor P) s) :
    LSeriesSummable (normCoeff K (supportedPart D.toIdealArithmeticFunction
      (S : Set (HeightOneSpectrum (𝓞 K))))) s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [Finset.coe_empty, coe_normCoeff_supportedPart_empty D.isMultiplicative.map_one]
      refine summable_of_ne_finset_zero (s := {1}) fun n hn ↦ ?_
      simp only [Finset.mem_singleton] at hn
      simp [LSeries.term_delta, hn]
  | insert P S hPS ih =>
      rw [Finset.coe_insert, supportedPart_insert D.isMultiplicative (by simpa using hPS),
        normCoeff_convolution, normCoeff_supportedPart_singleton]
      refine ArithmeticFunction.LSeriesSummable_mul
        (ih fun Q hQ ↦ hS Q (Finset.mem_insert_of_mem hQ)) ?_
      rw [← D.localArithmeticFactor_eq P]
      exact hS P (Finset.mem_insert_self P S)

/-- **The finite Euler product, analytically.** Where the local Euler factors over a finite set `S`
of primes are absolutely convergent `LSeries`, the `LSeries` of the norm coefficients of the
restriction of `D` to `S` is their finite product over `S`. -/
theorem LSeries_normCoeff_supportedPart (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ P ∈ S, LSeriesSummable (D.localArithmeticFactor P) s) :
    LSeries (normCoeff K (supportedPart D.toIdealArithmeticFunction
      (S : Set (HeightOneSpectrum (𝓞 K))))) s = ∏ P ∈ S, D.eulerFactor P s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [Finset.coe_empty, coe_normCoeff_supportedPart_empty D.isMultiplicative.map_one,
        LSeries_delta, Pi.one_apply, Finset.prod_empty]
  | insert P S hPS ih =>
      have hSsum := D.LSeriesSummable_normCoeff_supportedPart S
        fun Q hQ ↦ hS Q (Finset.mem_insert_of_mem hQ)
      have hPsum : LSeriesSummable
          (normCoeff K (supportedPart D.toIdealArithmeticFunction
            ({P} : Set (HeightOneSpectrum (𝓞 K))))) s := by
        rw [normCoeff_supportedPart_singleton, ← D.localArithmeticFactor_eq P]
        exact hS P (Finset.mem_insert_self P S)
      rw [Finset.coe_insert, supportedPart_insert D.isMultiplicative (by simpa using hPS),
        normCoeff_convolution, ArithmeticFunction.LSeries_mul' hSsum hPsum,
        ih fun Q hQ ↦ hS Q (Finset.mem_insert_of_mem hQ),
        normCoeff_supportedPart_singleton,
        Finset.prod_insert hPS, mul_comm]
      rw [eulerFactor_def, localArithmeticFactor_eq]

/-! ### The infinite Euler product -/

/-- **The analytic Euler product.** If the ideal-indexed Dirichlet series of `D` converges
absolutely at `s`, then its local Euler factors have an unrestricted
infinite product over the height-one primes, and that product is the `LSeries` of the norm
coefficients of `D`.

The hypothesis is absolute convergence of the *ideal-indexed* series, not of the regrouped one:
regrouping can only improve convergence, and the finite partial products of the local factors are
sums over ideals, not over norms. -/
theorem hasProd_eulerFactor (hs : Summable (idealTerm K D.toIdealArithmeticFunction s)) :
    HasProd (fun P ↦ D.eulerFactor P s)
      (LSeries (normCoeff K D.toIdealArithmeticFunction) s) := by
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 K)),
      ∏ P ∈ S, D.eulerFactor P s =
        ∑' I, idealTerm K (supportedPart D.toIdealArithmeticFunction
          (S : Set (HeightOneSpectrum (𝓞 K)))) s I := by
    intro S
    rw [← D.LSeries_normCoeff_supportedPart S
        fun P _ ↦ D.LSeriesSummable_localArithmeticFactor hs P,
      LSeries_normCoeff K (summable_idealTerm_supportedPart hs _)]
  rw [HasProd, SummationFilter.unconditional_filter, LSeries_normCoeff K hs]
  simp only [key]
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun I ↦ ‖idealTerm K D.toIdealArithmeticFunction s I‖)
    (summable_norm_iff.mpr hs) (fun I ↦ ?_) (Filter.Eventually.of_forall fun S I ↦ ?_)
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_isPrimeTo_compl I] with S hS
    rw [idealTerm_def, idealTerm_def, supportedPart_apply_of_isPrimeTo_compl hS]
  · exact norm_idealTerm_supportedPart_le D.toIdealArithmeticFunction _ s I

/-- The local Euler factors are multipliable wherever the ideal-indexed Dirichlet series converges
absolutely. -/
theorem multipliable_eulerFactor (hs : Summable (idealTerm K D.toIdealArithmeticFunction s)) :
    Multipliable fun P ↦ D.eulerFactor P s :=
  (D.hasProd_eulerFactor hs).multipliable

/-- The analytic Euler product, as an equality of the unrestricted product with the `LSeries`. -/
theorem tprod_eulerFactor (hs : Summable (idealTerm K D.toIdealArithmeticFunction s)) :
    ∏' P, D.eulerFactor P s = LSeries (normCoeff K D.toIdealArithmeticFunction) s :=
  (D.hasProd_eulerFactor hs).tprod_eq

end EulerProductData

/-! ### Completely multiplicative weights -/

namespace MultiplicativeIdealWeight

open IdealArithmeticFunction

variable (χ : MultiplicativeIdealWeight K) {s : ℂ}

/-- The ideal terms of a completely multiplicative weight along the powers of a prime form a
geometric progression. -/
@[simp]
theorem idealTerm_toIdealArithmeticFunction_primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (e : ℕ)
    (s : ℂ) :
    idealTerm K χ.toIdealArithmeticFunction s (P.primeIdealPow e) =
      (χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s) ^ e := by
  rw [idealTerm_def, toIdealArithmeticFunction_apply,
    P.absNorm_primeIdealPow, P.coe_primeIdealPow,
    map_pow, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
    Complex.cpow_nat_mul, div_pow]

/-- **The local ratio of a convergent weight is a contraction.** Absolute convergence of the
ideal-indexed Dirichlet series forces the geometric ratio at each prime to have modulus less than
one, because the powers of that prime already contribute a geometric subseries. -/
theorem norm_div_lt_one_of_summable_idealTerm
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s))
    (P : HeightOneSpectrum (𝓞 K)) :
    ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s‖ < 1 := by
  rw [← summable_geometric_iff_norm_lt_one]
  exact (hs.comp_injective P.primeIdealPow_injective).congr fun e ↦
    idealTerm_toIdealArithmeticFunction_primeIdealPow χ P e s

/-- The local Euler factor of a completely multiplicative weight is the geometric closed form
`(1 - χ(P) N(P)⁻ˢ)⁻¹`. -/
theorem eulerFactor_ofMultiplicativeIdealWeight
    (P : HeightOneSpectrum (𝓞 K))
    (hP : ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s‖ < 1) :
    (EulerProductData.ofMultiplicativeIdealWeight χ).eulerFactor P s =
      (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)⁻¹ := by
  rw [EulerProductData.eulerFactor_eq_tsum,
    EulerProductData.toIdealArithmeticFunction_ofMultiplicativeIdealWeight,
    tsum_congr fun e ↦ idealTerm_toIdealArithmeticFunction_primeIdealPow χ P e s]
  exact tsum_geometric_of_norm_lt_one hP

/-- **The Euler product of a completely multiplicative ideal weight.** -/
theorem hasProd_eulerFactor (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    HasProd (fun P : HeightOneSpectrum (𝓞 K) ↦
        (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)⁻¹)
      (LSeries (normCoeff K χ.toIdealArithmeticFunction) s) := by
  have hfun : (fun P : HeightOneSpectrum (𝓞 K) ↦
      (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)⁻¹) =
      fun P ↦ (EulerProductData.ofMultiplicativeIdealWeight χ).eulerFactor P s :=
    funext fun P ↦ (eulerFactor_ofMultiplicativeIdealWeight χ P
      (norm_div_lt_one_of_summable_idealTerm χ hs P)).symm
  rw [hfun]
  have hprod := (EulerProductData.ofMultiplicativeIdealWeight χ).hasProd_eulerFactor
    (s := s) (by
      simpa only [EulerProductData.toIdealArithmeticFunction_ofMultiplicativeIdealWeight] using hs)
  simpa only [EulerProductData.toIdealArithmeticFunction_ofMultiplicativeIdealWeight] using hprod

end MultiplicativeIdealWeight

/-! ### The Dedekind zeta function -/

/-- **The Euler product of the Dedekind zeta function.** For `Re s > 1` the Dedekind zeta function
of `K` is the unrestricted product over the height-one primes of `𝓞 K` of the local factors
`(1 - N(𝔭) ^ (-s))⁻¹`.

This is the ideal-theoretic counterpart of Mathlib's `riemannZeta_eulerProduct_hasProd`, and it
is not obtained from it: the product is indexed by the primes of `𝓞 K`, whose norms repeat and
whose count above a rational prime is the splitting behaviour of `K`. -/
theorem dedekindZeta_eulerProduct_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun P : HeightOneSpectrum (𝓞 K) ↦ (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹)
      (NumberField.dedekindZeta K s) := by
  have hsum : Summable (idealTerm K
      (1 : MultiplicativeIdealWeight K).toIdealArithmeticFunction s) := by
    rw [MultiplicativeIdealWeight.toIdealArithmeticFunction_one]
    exact summable_idealTerm_one_iff.mpr hs
  have hprod := MultiplicativeIdealWeight.hasProd_eulerFactor (1 : MultiplicativeIdealWeight K) hsum
  rw [MultiplicativeIdealWeight.toIdealArithmeticFunction_one,
    ← dedekindZeta_eq_LSeries_normCoeff_one K s] at hprod
  have hfun : (fun P : HeightOneSpectrum (𝓞 K) ↦
      (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹) =
      fun P : HeightOneSpectrum (𝓞 K) ↦
        (1 - (1 : MultiplicativeIdealWeight K) P.asIdeal /
          (Ideal.absNorm P.asIdeal : ℂ) ^ s)⁻¹ := by
    funext P
    rw [MultiplicativeIdealWeight.one_apply, ite_eq_right P.ne_bot, Complex.cpow_neg, one_div]
  rw [hfun]
  exact hprod

end TauCeti
