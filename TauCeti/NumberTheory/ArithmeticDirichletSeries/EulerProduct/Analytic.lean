/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.NumberTheory.LSeries.Convolution
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Regroup

/-!
# The analytic Euler product of an ideal arithmetic function

`TauCeti.IdealArithmeticFunction.normCoeff_eq_eulerProduct` identifies the norm coefficients of a
multiplicative ideal arithmetic function with a formal Euler product, coefficient by coefficient.
This file supplies the analytic statement it does not: where the Dirichlet series indexed by the
nonzero ideals converges absolutely, the infinite product of the local Euler factors converges,
in the unrestricted sense of `HasProd` over the height-one primes, to the `LSeries` of the norm
coefficients.

The local factor at a height-one prime `P` is the `LSeries` of the canonical local arithmetic
factor, equivalently the prime-power Dirichlet series `∑' e, f (P ^ e) / N(P ^ e) ^ s`. For a
completely multiplicative weight that series is geometric, and the factor takes the familiar
closed form `(1 - χ(P) N(P) ^ (-s))⁻¹`; specializing to the trivial weight gives the Euler
product of the Dedekind zeta function.

## Main definitions

* `TauCeti.primeIdealPow`: the `e`-th power of a height-one prime, as a nonzero integral ideal.
* `TauCeti.IdealArithmeticFunction.eulerFactor`: the local Euler factor at a height-one prime.

## Main results

* `TauCeti.IdealArithmeticFunction.hasProd_eulerFactor`: the **analytic Euler product**, for a
  multiplicative ideal arithmetic function whose ideal-indexed Dirichlet series converges
  absolutely at `s`.
* `TauCeti.MultiplicativeIdealWeight.hasProd_eulerFactor`: the same product, with the local factors
  in the closed geometric form available for a completely multiplicative weight.
* `TauCeti.hasProd_dedekindZeta`: the **Euler product of the Dedekind zeta function**, valid on
  `Re s > 1`.

## Implementation notes

The finite partial products are handled by regrouping, not by a second combinatorial induction:
`TauCeti.IdealArithmeticFunction.normCoeff_supportedPart` already writes the restriction of `f`
to the ideals supported on a finite prime set as a Dirichlet convolution of local factors, and
Mathlib's `LSeries_mul'` turns that convolution into a product of `LSeries` values. What remains
is the passage to the limit, and there the partial product is *literally* the ideal-indexed sum
restricted to the supported ideals, so Tannery's theorem
(`tendsto_tsum_of_dominated_convergence`) applies with the ideal terms of `f` as the dominating
bound: each individual ideal is eventually supported, by
`TauCeti.IdealArithmeticFunction.eventually_isPrimeTo_compl`.

No nonvanishing statement is made here. An unconditionally convergent product of nonzero factors
may still vanish, so nonvanishing needs the convergence of the reciprocal product and is left to
the layer that proves it.

## Roadmap role

This is Layer **3.3**, the infinite Euler product, of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.

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

/-! ### Prime powers as nonzero ideals -/

/-- The `e`-th power of a height-one prime of `𝓞 K`, as a nonzero integral ideal. This is the
index carrier of the local Euler factor at that prime. -/
def primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) : (Ideal (𝓞 K))⁰ :=
  ⟨P.asIdeal ^ e, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero e P.ne_bot)⟩

omit [NumberField K] in
/-- A prime power, as a nonzero integral ideal, has the expected underlying ideal. -/
@[simp]
theorem coe_primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    (primeIdealPow P e : Ideal (𝓞 K)) = P.asIdeal ^ e :=
  (rfl)

/-- The absolute norm is multiplicative on prime powers. -/
@[simp]
theorem absNorm_primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    Ideal.absNorm (primeIdealPow P e : Ideal (𝓞 K)) = Ideal.absNorm P.asIdeal ^ e := by
  rw [coe_primeIdealPow, map_pow]

/-- Distinct exponents give distinct prime powers: their absolute norms are distinct powers of an
integer at least two. -/
theorem primeIdealPow_injective (P : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (primeIdealPow P) := fun m n h ↦
  Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm P)
    (by simpa only [absNorm_primeIdealPow] using
      congrArg (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) h)

/-- A complex power of a natural-number power splits off the natural exponent. This is the norm
computation behind the geometric shape of a completely multiplicative local factor. -/
theorem natCast_pow_cpow (n e : ℕ) (s : ℂ) :
    ((n ^ e : ℕ) : ℂ) ^ s = ((n : ℂ) ^ s) ^ e := by
  rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

namespace IdealArithmeticFunction

variable {f : IdealArithmeticFunction K} {s : ℂ}

/-! ### The local Euler factor -/

/-- The **local Euler factor** of `f` at a height-one prime `P`, evaluated at `s`: the `LSeries`
of the canonical local arithmetic factor `TauCeti.IdealArithmeticFunction.localArithmeticFactor`.
By `TauCeti.IdealArithmeticFunction.eulerFactor_eq_tsum` this is the prime-power Dirichlet series
`∑' e, f (P ^ e) / N(P ^ e) ^ s`. -/
noncomputable def eulerFactor (f : IdealArithmeticFunction K) (P : HeightOneSpectrum (𝓞 K))
    (s : ℂ) : ℂ :=
  LSeries (localArithmeticFactor f P) s

/-- The local Euler factor is the Dirichlet series over the powers of `P`. -/
theorem eulerFactor_eq_tsum (f : IdealArithmeticFunction K) (P : HeightOneSpectrum (𝓞 K))
    (s : ℂ) :
    eulerFactor f P s = ∑' e : ℕ, idealTerm K f s (primeIdealPow P e) := by
  have hsupp : Function.support
      (fun n : ℕ ↦ (localArithmeticFactor f P n : ℂ) / (n : ℂ) ^ s) ⊆
      Set.range fun e : ℕ ↦ Ideal.absNorm P.asIdeal ^ e := by
    intro n hn
    simp only [Function.mem_support, ne_eq, div_eq_zero_iff, not_or] at hn
    exact exists_pow_eq_of_localArithmeticFactor_apply_ne_zero f P hn.1
  rw [eulerFactor, LSeries_def₀ (by simp),
    ← (Nat.pow_right_injective
      (NumberField.HeightOneSpectrum.one_lt_absNorm P)).tsum_eq hsupp]
  refine tsum_congr fun e ↦ ?_
  rw [localArithmeticFactor_apply_pow, idealTerm_def, absNorm_primeIdealPow]
  rfl

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
  by_cases hI : I ∈ {I : (Ideal (𝓞 K))⁰ | Ideal.IsPrimeTo (I : Ideal (𝓞 K)) Sᶜ}
  · rw [Set.indicator_of_mem hI]
  · rw [Set.indicator_of_notMem hI, norm_zero]
    exact norm_nonneg _

/-- Absolute convergence of the ideal-indexed Dirichlet series is inherited by every restriction
to a set of primes. -/
theorem summable_idealTerm_supportedPart (hs : Summable (idealTerm K f s))
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    Summable (idealTerm K (supportedPart f S) s) := by
  rw [← summable_norm_iff] at hs ⊢
  exact hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_idealTerm_supportedPart_le f S s)

/-- Absolute convergence of the ideal-indexed Dirichlet series makes every local Euler factor an
absolutely convergent `LSeries`. -/
theorem LSeriesSummable_localArithmeticFactor (hs : Summable (idealTerm K f s))
    (P : HeightOneSpectrum (𝓞 K)) :
    LSeriesSummable (localArithmeticFactor f P) s := by
  rw [← normCoeff_supportedPart_singleton f P]
  exact LSeriesSummable_normCoeff K (summable_idealTerm_supportedPart hs _)

/-- **The finite Euler product, analytically.** The `LSeries` of the norm coefficients of the
restriction of `f` to a finite set `S` of primes is the finite product of the local Euler factors
over `S`. -/
theorem LSeries_normCoeff_supportedPart (hf : f.IsMultiplicative)
    (hs : Summable (idealTerm K f s)) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    LSeries (normCoeff K (supportedPart f (S : Set (HeightOneSpectrum (𝓞 K))))) s =
      ∏ P ∈ S, eulerFactor f P s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [Finset.coe_empty, supportedPart_empty hf.map_one, normCoeff_delta, Finset.prod_empty]
      have hone : ⇑(1 : ArithmeticFunction ℂ) = LSeries.delta := by
        funext n
        simp [ArithmeticFunction.one_apply, LSeries.delta]
      rw [hone, LSeries_delta, Pi.one_apply]
  | insert P S hPS ih =>
      have hS := LSeriesSummable_normCoeff K (summable_idealTerm_supportedPart hs
        (S : Set (HeightOneSpectrum (𝓞 K))))
      have hP := LSeriesSummable_normCoeff K (summable_idealTerm_supportedPart hs
        ({P} : Set (HeightOneSpectrum (𝓞 K))))
      rw [Finset.coe_insert, supportedPart_insert hf (by simpa using hPS), normCoeff_convolution,
        ArithmeticFunction.LSeries_mul' hS hP, ih, normCoeff_supportedPart_singleton,
        Finset.prod_insert hPS, mul_comm]
      rfl

/-! ### The infinite Euler product -/

/-- **The analytic Euler product.** If `f` is multiplicative and its ideal-indexed Dirichlet
series converges absolutely at `s`, then the local Euler factors of `f` have an unrestricted
infinite product over the height-one primes, and that product is the `LSeries` of the norm
coefficients of `f`.

The hypothesis is absolute convergence of the *ideal-indexed* series, not of the regrouped one:
regrouping can only improve convergence, and the finite partial products of the local factors are
sums over ideals, not over norms. -/
theorem hasProd_eulerFactor (hf : f.IsMultiplicative) (hs : Summable (idealTerm K f s)) :
    HasProd (fun P ↦ eulerFactor f P s) (LSeries (normCoeff K f) s) := by
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 K)),
      ∏ P ∈ S, eulerFactor f P s =
        ∑' I, idealTerm K (supportedPart f (S : Set (HeightOneSpectrum (𝓞 K)))) s I := by
    intro S
    rw [← LSeries_normCoeff_supportedPart hf hs S,
      LSeries_normCoeff K (summable_idealTerm_supportedPart hs _)]
  rw [HasProd, SummationFilter.unconditional_filter, LSeries_normCoeff K hs]
  simp only [key]
  refine tendsto_tsum_of_dominated_convergence (bound := fun I ↦ ‖idealTerm K f s I‖)
    (summable_norm_iff.mpr hs) (fun I ↦ ?_) (Filter.Eventually.of_forall fun S I ↦ ?_)
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_isPrimeTo_compl I] with S hS
    rw [idealTerm_def, idealTerm_def, supportedPart_apply_of_isPrimeTo_compl hS]
  · exact norm_idealTerm_supportedPart_le f _ s I

/-- The local Euler factors of a multiplicative ideal arithmetic function are multipliable
wherever its ideal-indexed Dirichlet series converges absolutely. -/
theorem multipliable_eulerFactor (hf : f.IsMultiplicative) (hs : Summable (idealTerm K f s)) :
    Multipliable fun P ↦ eulerFactor f P s :=
  (hasProd_eulerFactor hf hs).multipliable

/-- The analytic Euler product, as an equality of the unrestricted product with the `LSeries`. -/
theorem tprod_eulerFactor (hf : f.IsMultiplicative) (hs : Summable (idealTerm K f s)) :
    ∏' P, eulerFactor f P s = LSeries (normCoeff K f) s :=
  (hasProd_eulerFactor hf hs).tprod_eq

end IdealArithmeticFunction

/-! ### Completely multiplicative weights -/

namespace MultiplicativeIdealWeight

open IdealArithmeticFunction

variable (χ : MultiplicativeIdealWeight K) {s : ℂ}

/-- The ideal terms of a completely multiplicative weight along the powers of a prime form a
geometric progression. -/
theorem idealTerm_toIdealArithmeticFunction_primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (e : ℕ)
    (s : ℂ) :
    idealTerm K χ.toIdealArithmeticFunction s (primeIdealPow P e) =
      (χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s) ^ e := by
  rw [idealTerm_def, toIdealArithmeticFunction_apply, absNorm_primeIdealPow, coe_primeIdealPow,
    map_pow, natCast_pow_cpow, div_pow]

/-- **The local ratio of a convergent weight is a contraction.** Absolute convergence of the
ideal-indexed Dirichlet series forces the geometric ratio at each prime to have modulus less than
one, because the powers of that prime already contribute a geometric subseries. -/
theorem norm_div_lt_one_of_summable_idealTerm
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s))
    (P : HeightOneSpectrum (𝓞 K)) :
    ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s‖ < 1 := by
  rw [← summable_geometric_iff_norm_lt_one]
  exact (hs.comp_injective (primeIdealPow_injective P)).congr fun e ↦
    idealTerm_toIdealArithmeticFunction_primeIdealPow χ P e s

/-- The local Euler factor of a completely multiplicative weight is the geometric closed form
`(1 - χ(P) N(P)⁻ˢ)⁻¹`. -/
theorem eulerFactor_toIdealArithmeticFunction
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s))
    (P : HeightOneSpectrum (𝓞 K)) :
    eulerFactor χ.toIdealArithmeticFunction P s =
      (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)⁻¹ := by
  rw [eulerFactor_eq_tsum,
    tsum_congr fun e ↦ idealTerm_toIdealArithmeticFunction_primeIdealPow χ P e s]
  exact tsum_geometric_of_norm_lt_one (norm_div_lt_one_of_summable_idealTerm χ hs P)

/-- **The Euler product of a completely multiplicative ideal weight.** -/
theorem hasProd_eulerFactor (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    HasProd (fun P : HeightOneSpectrum (𝓞 K) ↦
        (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)⁻¹)
      (LSeries (normCoeff K χ.toIdealArithmeticFunction) s) := by
  have hfun : (fun P : HeightOneSpectrum (𝓞 K) ↦
      (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)⁻¹) =
      fun P ↦ eulerFactor χ.toIdealArithmeticFunction P s :=
    funext fun P ↦ (eulerFactor_toIdealArithmeticFunction χ hs P).symm
  rw [hfun]
  exact IdealArithmeticFunction.hasProd_eulerFactor
    (isMultiplicative_toIdealArithmeticFunction χ) hs

end MultiplicativeIdealWeight

/-! ### The Dedekind zeta function -/

/-- The ideal-indexed Dirichlet series of the trivial ideal weight converges absolutely exactly on
`Re s > 1`. -/
theorem summable_idealTerm_one_iff {s : ℂ} :
    Summable (idealTerm K (1 : IdealArithmeticFunction K) s) ↔ 1 < s.re := by
  refine ⟨fun h ↦ (LSeriesSummable_normCoeff_one_iff K).mp (LSeriesSummable_normCoeff K h),
    fun h ↦ ?_⟩
  exact summable_idealTerm_of_nonneg K 1 (fun _ ↦ zero_le_one)
    ((LSeriesSummable_normCoeff_one_iff K).mpr h)

/-- **The Euler product of the Dedekind zeta function.** For `Re s > 1` the Dedekind zeta function
of `K` is the unrestricted product over the height-one primes of `𝓞 K` of the local factors
`(1 - N(𝔭) ^ (-s))⁻¹`.

This is the ideal-theoretic counterpart of Mathlib's `riemannZeta_eulerProduct_hasProd`, and it
is not obtained from it: the product is indexed by the primes of `𝓞 K`, whose norms repeat and
whose count above a rational prime is the splitting behaviour of `K`. -/
theorem hasProd_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
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
