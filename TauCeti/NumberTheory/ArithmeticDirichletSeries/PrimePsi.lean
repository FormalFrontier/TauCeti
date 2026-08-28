/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.HigherPrimePowers

/-!
# Chebyshev's `ψ` for a set of prime ideals, and the removal of the higher prime powers

For a set `S` of height-one primes of the ring of integers of a number field `K`, Chebyshev's
`ψ` weights *every* prime power `𝔭 ^ k` with `𝔭 ∈ S` and `k ≥ 1` by `log N(𝔭)`, while `ϑ` weights
only the primes themselves.  This file defines `ψ`, proves that the difference `ψ - ϑ` is exactly
the higher-prime-power sum estimated in
`TauCeti/NumberTheory/ArithmeticDirichletSeries/HigherPrimePowers.lean`, and spends that estimate
on the transfer of an asymptotic `ψ(x) = δ x + o(x)` to `ϑ(x) = δ x + o(x)`.

Prime powers with `k ≥ 2` are kept visible throughout: `ψ` is *defined* with all of them present,
and their removal is a named hypothesis, `TauCeti.HasNegligibleHigherPrimePowers`, discharged for
the standard logarithmic weight by `TauCeti.standardPrimePowerRemoval`.  A different coefficient
system does not get that hypothesis for free; what it has to supply is the domination bound of
`TauCeti.primePowerSummatory_isLittleO_of_le_higherPrimePowerWeight`.

## Main definitions

* `TauCeti.primePowerWeight` is the standard logarithmic prime-power weight, the value `log N(𝔭)`
  at `𝔭 ^ k` for every `k ≥ 1`.  It is the real form of the ideal von Mangoldt function of Layer 2
  on the prime powers.
* `TauCeti.primePsi` is its inclusive summatory function over the prime powers whose base lies in
  `S`: the number-field analogue of Chebyshev's `ψ`.
* `TauCeti.HasNegligibleHigherPrimePowers K S` says that `ψ - ϑ` is `o(x)`.
* `TauCeti.primeVonMangoldtWeight` is the same weight spread over *all* nonzero ideals, zero away
  from the prime powers with base in `S`, and `TauCeti.primeVonMangoldtCoeff` is its regrouping by
  absolute norm, an `ArithmeticFunction ℝ`.

## Main results

* `TauCeti.primePsi_sub_primeTheta` identifies `ψ - ϑ` with the higher-prime-power sum.
* `TauCeti.standardPrimePowerRemoval` proves `HasNegligibleHigherPrimePowers K S` for every `S`,
  from the Layer 5 estimate `ψ(x) - ϑ(x) = O(√x log² x)`.
* `TauCeti.primeTheta_asymptotic_of_primePsi` and
  `TauCeti.primePsi_asymptotic_of_primeTheta` transfer a linear asymptotic across that difference,
  with `TauCeti.primeTheta_isEquivalent_of_primePsi` the equivalence form for a nonzero density.
* `TauCeti.primePsi_eq_sum_range` presents `ψ(x)` as the inclusive partial sum
  `∑_{n ≤ ⌊x⌋₊} a n` of the coefficient system, whose coefficients are nonnegative
  (`TauCeti.primeVonMangoldtCoeff_nonneg`) and supported on the prime powers
  (`TauCeti.primeVonMangoldtCoeff_eq_zero_of_not_isPrimePow`).
* `TauCeti.normCoeff_vonMangoldt` identifies the coefficient system of the full prime carrier with
  the Layer 1 regrouping of the Layer 2 ideal von Mangoldt function.

## Roadmap role

This is Layer **10.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: "For the fixed
standard nonnegative logarithmic prime-power weight, use Layer 5 to prove
`standardPrimePowerRemoval : HasNegligibleHigherPrimePowers K S` and make
`primeTheta_asymptotic_of_primePsi` consume that named estimate."  It also supplies the arithmetic
half of Layer **10.1**, "Define `primePsi` with all prime powers present": the exact nonnegative
von Mangoldt coefficient system and the identity presenting `ψ` as its partial sum, which is the
shape in which a Tauberian theorem delivers its conclusion.  What remains of 10.1 — the analytic
package `PrimeBoundaryRemainder`, carrying the `LSeriesHasSum` and boundary-continuity hypotheses,
and the asymptotic `primePsi_asymptotic_of_boundary` it yields — waits on the Wiener–Ikehara
theorem of Layer 9.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 7.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.

The rational-prime case of `ψ`, `ϑ` and their difference is Mathlib's
`Mathlib/NumberTheory/Chebyshev.lean`, whose `Chebyshev.theta_le_psi` and
`Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` are the analogues of
`TauCeti.primeTheta_le_primePsi` and `TauCeti.standardPrimePowerRemoval`; nothing is transported
from there, since the estimate consumed here is proved over prime ideals in Layer 5.
-/

public section

namespace TauCeti

open Filter NumberField
open scoped Asymptotics nonZeroDivisors NumberField
open IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-! ### The standard logarithmic prime-power weight -/

/-- The **standard logarithmic prime-power weight**: the value `log N(𝔭)` at the prime power
`𝔭 ^ k`, for every `k ≥ 1`.  Unlike `TauCeti.higherPrimePowerWeight` it does not vanish on the
primes themselves, so its summatory function is Chebyshev's `ψ` rather than `ψ - ϑ`. -/
noncomputable def primePowerWeight (A : IdealPrimePower K) : ℝ :=
  Real.log (Ideal.absNorm (primePowerBase A).asIdeal)

/-- The standard logarithmic prime-power weight is the real part of the ideal von Mangoldt
function of Layer 2, restricted to the prime powers. -/
theorem primePowerWeight_eq_vonMangoldt_re (A : IdealPrimePower K) :
    primePowerWeight A = (IdealArithmeticFunction.vonMangoldt (A : (Ideal (𝓞 K))⁰)).re := by
  rw [primePowerWeight, IdealArithmeticFunction.vonMangoldt_apply_of_eq_prime_pow
    (prime_primePowerBase A) (primePowerExponent_pos A)
    (primePowerBase_pow_primePowerExponent A), Complex.ofReal_re]

/-- The standard logarithmic prime-power weight is positive. -/
theorem primePowerWeight_pos (A : IdealPrimePower K) : 0 < primePowerWeight A :=
  log_absNorm_asIdeal_pos (primePowerBase A)

/-- The standard logarithmic prime-power weight is nonnegative. -/
theorem primePowerWeight_nonneg (A : IdealPrimePower K) : 0 ≤ primePowerWeight A :=
  (primePowerWeight_pos A).le

/-- On a prime the standard weight is the logarithm of its own absolute norm. -/
@[simp]
theorem primePowerWeight_ofPrime (v : HeightOneSpectrum (𝓞 K)) :
    primePowerWeight (IdealPrimePower.ofPrime v) = Real.log (Ideal.absNorm v.asIdeal) := by
  rw [primePowerWeight, primePowerBase_ofPrime]

/-- Away from the primes the two prime-power weights agree: `TauCeti.higherPrimePowerWeight` is
the standard weight with its exponent-one part deleted. -/
theorem higherPrimePowerWeight_of_not_prime {A : IdealPrimePower K}
    (hA : ¬ Prime (A : Ideal (𝓞 K))) :
    higherPrimePowerWeight A = primePowerWeight A :=
  higherPrimePowerWeight_of_two_le_primePowerExponent (two_le_primePowerExponent hA)

/-! ### Chebyshev's `ψ` -/

variable (K) in
/-- **Chebyshev's `ψ` for a set of prime ideals**: the inclusive sum of `log N(𝔭)` over the prime
powers `𝔭 ^ k` of absolute norm at most `x` whose base `𝔭` lies in `S`, with every exponent
`k ≥ 1` present. -/
noncomputable def primePsi (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) : ℝ :=
  primePowerSummatory K
    ({A : IdealPrimePower K | primePowerBase A ∈ S}.indicator primePowerWeight) x

variable {S : Set (HeightOneSpectrum (𝓞 K))} {x δ : ℝ}

/-- Chebyshev's `ψ` as an explicit sum over the inclusive prime-power carrier. -/
theorem primePsi_apply (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primePsi K S x = ∑ A ∈ primePowersLE K x,
      {A : IdealPrimePower K | primePowerBase A ∈ S}.indicator primePowerWeight A := by
  rw [primePsi, primePowerSummatory_apply]

/-- The empty set of primes contributes nothing to `ψ`. -/
@[simp]
theorem primePsi_empty (x : ℝ) : primePsi K (∅ : Set (HeightOneSpectrum (𝓞 K))) x = 0 := by
  simp [primePsi_apply]

/-- Chebyshev's `ψ` is nonnegative. -/
theorem primePsi_nonneg (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) : 0 ≤ primePsi K S x :=
  primePowerSummatory_nonneg K _
    (fun A ↦ Set.indicator_nonneg (fun A _ ↦ primePowerWeight_nonneg A) A) x

/-- Chebyshev's `ψ` is monotone in the inclusive cutoff. -/
theorem primePsi_mono (S : Set (HeightOneSpectrum (𝓞 K))) : Monotone (primePsi K S) :=
  primePowerSummatory_mono K _
    fun A ↦ Set.indicator_nonneg (fun A _ ↦ primePowerWeight_nonneg A) A

/-- Below the cutoff `2` there is no prime power to weight. -/
theorem primePsi_eq_zero_of_lt_two (S : Set (HeightOneSpectrum (𝓞 K))) (hx : x < 2) :
    primePsi K S x = 0 := by
  rw [primePsi_apply, primePowersLE_eq_empty_of_lt_two hx, Finset.sum_empty]

/-! ### The higher prime powers as the gap between `ψ` and `ϑ` -/

/-- **The difference between `ψ` and `ϑ` is the higher-prime-power sum.**  Both sides run over the
prime powers whose base lies in `S`; the exponent-one part of `ψ` is exactly `ϑ`. -/
theorem primePsi_sub_primeTheta (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primePsi K S x - primeTheta K S x =
      primePowerSummatory K
        ({A : IdealPrimePower K | primePowerBase A ∈ S}.indicator higherPrimePowerWeight) x := by
  have hsplit : ({A : IdealPrimePower K | primePowerBase A ∈ S}.indicator primePowerWeight)
      = {A : IdealPrimePower K | primePowerBase A ∈ S}.indicator
          (primePowerWeight - higherPrimePowerWeight)
        + {A : IdealPrimePower K | primePowerBase A ∈ S}.indicator higherPrimePowerWeight := by
    rw [← Set.indicator_add', sub_add_cancel]
  have hzero : ∀ A : IdealPrimePower K, ¬ Prime (A : Ideal (𝓞 K)) →
      {A : IdealPrimePower K | primePowerBase A ∈ S}.indicator
        (primePowerWeight - higherPrimePowerWeight) A = 0 := fun A hA ↦ by
    simp [higherPrimePowerWeight_of_not_prime hA]
  have hexp : primePowerSummatory K
      ({A : IdealPrimePower K | primePowerBase A ∈ S}.indicator
        (primePowerWeight - higherPrimePowerWeight)) x = primeTheta K S x := by
    rw [primePowerSummatory_eq_primeSummatory K _ hzero, primeSummatory_apply, primeTheta_apply]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    by_cases hv : v ∈ S <;>
      simp [hv, higherPrimePowerWeight_of_prime (IdealPrimePower.prime_ofPrime v)]
  rw [primePsi, hsplit, primePowerSummatory_add, hexp, add_sub_cancel_left]

/-- Chebyshev's `ϑ` never exceeds `ψ`. -/
theorem primeTheta_le_primePsi (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeTheta K S x ≤ primePsi K S x := by
  rw [← sub_nonneg, primePsi_sub_primeTheta]
  exact primePowerSummatory_nonneg K _
    (fun A ↦ Set.indicator_nonneg (fun A _ ↦ higherPrimePowerWeight_nonneg A) A) x

/-! ### Removing the higher prime powers -/

variable (K) in
/-- **The higher prime powers of `S` are negligible**: `ψ - ϑ` is `o(x)`.  Naming the hypothesis
keeps the estimate an input to the prime-number-theorem transfer instead of a definitional
simplification of `ψ`. -/
def HasNegligibleHigherPrimePowers (S : Set (HeightOneSpectrum (𝓞 K))) : Prop :=
  (fun x ↦ primePsi K S x - primeTheta K S x) =o[atTop] fun x : ℝ ↦ x

/-- The defining little-o estimate behind `TauCeti.HasNegligibleHigherPrimePowers`. -/
theorem hasNegligibleHigherPrimePowers_iff :
    HasNegligibleHigherPrimePowers K S ↔
      (fun x ↦ primePsi K S x - primeTheta K S x) =o[atTop] fun x : ℝ ↦ x :=
  Iff.rfl

/-- **Removal of the higher prime powers** for the standard logarithmic weight.  This is the
`o(x)` corollary of the Layer 5 bound `ψ(x) - ϑ(x) ≤ [K:ℚ] / (2 log 2) · √x log² x`. -/
theorem standardPrimePowerRemoval (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) : HasNegligibleHigherPrimePowers K S := by
  rw [hasNegligibleHigherPrimePowers_iff]
  simpa only [primePsi_sub_primeTheta] using primePowerSummatory_indicator_isLittleO K S

/-- **Transfer of a linear asymptotic from `ψ` to `ϑ`.**  If the higher prime powers of `S` are
negligible and `ψ(x) = δ x + o(x)`, then `ϑ(x) = δ x + o(x)`. -/
theorem primeTheta_asymptotic_of_primePsi (h : HasNegligibleHigherPrimePowers K S)
    (hψ : (fun x ↦ primePsi K S x - δ * x) =o[atTop] fun x : ℝ ↦ x) :
    (fun x ↦ primeTheta K S x - δ * x) =o[atTop] fun x : ℝ ↦ x :=
  (hψ.sub h).congr' (Eventually.of_forall fun x ↦ by ring) EventuallyEq.rfl

/-- **Transfer of a linear asymptotic from `ϑ` to `ψ`**, the converse direction. -/
theorem primePsi_asymptotic_of_primeTheta (h : HasNegligibleHigherPrimePowers K S)
    (hϑ : (fun x ↦ primeTheta K S x - δ * x) =o[atTop] fun x : ℝ ↦ x) :
    (fun x ↦ primePsi K S x - δ * x) =o[atTop] fun x : ℝ ↦ x :=
  (hϑ.add h).congr' (Eventually.of_forall fun x ↦ by ring) EventuallyEq.rfl

/-- The asymptotic-equivalence form of `TauCeti.primeTheta_asymptotic_of_primePsi`, for a nonzero
density `δ`.  At `δ = 0` an equivalence would force `ϑ` to vanish eventually, so the `o(x)` form
above is the one that covers that case. -/
theorem primeTheta_isEquivalent_of_primePsi (hδ : δ ≠ 0) (h : HasNegligibleHigherPrimePowers K S)
    (hψ : primePsi K S ~[atTop] fun x ↦ δ * x) :
    primeTheta K S ~[atTop] fun x ↦ δ * x := by
  have hψ' : (fun x ↦ primePsi K S x - δ * x) =o[atTop] fun x : ℝ ↦ x :=
    hψ.isLittleO.of_const_mul_right
  rw [Asymptotics.IsEquivalent]
  exact ((primeTheta_asymptotic_of_primePsi h hψ').const_mul_right hδ).congr'
    (Eventually.of_forall fun x ↦ (Pi.sub_apply _ _ x).symm) EventuallyEq.rfl

/-! ### The von Mangoldt coefficient system of a set of primes -/

variable (K) in
/-- The **von Mangoldt weight of a set `S` of height-one primes**, as a real weight on the nonzero
integral ideals of `𝓞 K`: the value `log N(𝔭)` at `𝔭 ^ k` for `𝔭 ∈ S` and `k ≥ 1`, and `0` at every
other nonzero ideal.

It is the ideal von Mangoldt function of Layer 2 cut down to the prime powers whose base lies in
`S`, taken in its real form, because the Tauberian input of Layer 9 is a nonnegative *real*
coefficient system.  Cutting down by "some prime of `S` divides `A`" rather than by the prime base
of `A` avoids naming that base at ideals which are not prime powers, where the ideal von Mangoldt
function vanishes anyway. -/
noncomputable def primeVonMangoldtWeight (S : Set (HeightOneSpectrum (𝓞 K)))
    (A : (Ideal (𝓞 K))⁰) : ℝ :=
  {I : (Ideal (𝓞 K))⁰ | ∃ 𝔭 ∈ S, 𝔭.asIdeal ∣ (I : Ideal (𝓞 K))}.indicator
    (fun I ↦ (IdealArithmeticFunction.vonMangoldt I).re) A

/-- At an ideal divisible by a prime of `S`, the von Mangoldt weight of `S` is the ideal von
Mangoldt value. -/
theorem primeVonMangoldtWeight_of_exists_dvd {A : (Ideal (𝓞 K))⁰}
    (h : ∃ 𝔭 ∈ S, 𝔭.asIdeal ∣ (A : Ideal (𝓞 K))) :
    primeVonMangoldtWeight K S A = (IdealArithmeticFunction.vonMangoldt A).re :=
  Set.indicator_of_mem
    (s := {I : (Ideal (𝓞 K))⁰ | ∃ 𝔭 ∈ S, 𝔭.asIdeal ∣ (I : Ideal (𝓞 K))}) h _

/-- The von Mangoldt weight of `S` vanishes at an ideal with no prime factor in `S`. -/
theorem primeVonMangoldtWeight_of_not_exists_dvd {A : (Ideal (𝓞 K))⁰}
    (h : ¬ ∃ 𝔭 ∈ S, 𝔭.asIdeal ∣ (A : Ideal (𝓞 K))) :
    primeVonMangoldtWeight K S A = 0 :=
  Set.indicator_of_notMem
    (s := {I : (Ideal (𝓞 K))⁰ | ∃ 𝔭 ∈ S, 𝔭.asIdeal ∣ (I : Ideal (𝓞 K))}) h _

/-- The empty set of primes carries no von Mangoldt weight. -/
@[simp]
theorem primeVonMangoldtWeight_empty (A : (Ideal (𝓞 K))⁰) :
    primeVonMangoldtWeight K (∅ : Set (HeightOneSpectrum (𝓞 K))) A = 0 :=
  primeVonMangoldtWeight_of_not_exists_dvd (by simp)

/-- The von Mangoldt weight of `S` vanishes away from the prime-power ideals. -/
@[simp]
theorem primeVonMangoldtWeight_eq_zero_of_not_isPrimePow {A : (Ideal (𝓞 K))⁰}
    (hA : ¬ IsPrimePow (A : Ideal (𝓞 K))) : primeVonMangoldtWeight K S A = 0 :=
  Set.indicator_apply_eq_zero.mpr fun _ ↦ by
    rw [IdealArithmeticFunction.vonMangoldt_eq_zero_of_not_isPrimePow hA, Complex.zero_re]

/-- The von Mangoldt weight of `S` is nonnegative. -/
theorem primeVonMangoldtWeight_nonneg (S : Set (HeightOneSpectrum (𝓞 K)))
    (A : (Ideal (𝓞 K))⁰) : 0 ≤ primeVonMangoldtWeight K S A :=
  Set.indicator_nonneg (fun _ _ ↦ IdealArithmeticFunction.vonMangoldt_re_nonneg) A

/-- The von Mangoldt weight of `S` at a positive power of a prime of `S`. -/
theorem primeVonMangoldtWeight_of_pow_of_mem {𝔭 : HeightOneSpectrum (𝓞 K)} (h𝔭 : 𝔭 ∈ S) {k : ℕ}
    (hk : 0 < k) {A : (Ideal (𝓞 K))⁰} (hA : 𝔭.asIdeal ^ k = (A : Ideal (𝓞 K))) :
    primeVonMangoldtWeight K S A = Real.log (Ideal.absNorm 𝔭.asIdeal) := by
  rw [primeVonMangoldtWeight_of_exists_dvd ⟨𝔭, h𝔭, hA ▸ dvd_pow_self _ hk.ne'⟩,
    IdealArithmeticFunction.vonMangoldt_apply_of_eq_prime_pow
      (Ideal.prime_of_isPrime 𝔭.ne_bot 𝔭.isPrime) hk hA, Complex.ofReal_re]

/-- The von Mangoldt weight of `S` vanishes at a positive power of a prime outside `S`. -/
theorem primeVonMangoldtWeight_of_pow_of_notMem {𝔭 : HeightOneSpectrum (𝓞 K)} (h𝔭 : 𝔭 ∉ S) {k : ℕ}
    (hk : 0 < k) {A : (Ideal (𝓞 K))⁰} (hA : 𝔭.asIdeal ^ k = (A : Ideal (𝓞 K))) :
    primeVonMangoldtWeight K S A = 0 := by
  have hprime : Prime 𝔭.asIdeal := Ideal.prime_of_isPrime 𝔭.ne_bot 𝔭.isPrime
  refine primeVonMangoldtWeight_of_not_exists_dvd ?_
  rintro ⟨𝔮, h𝔮, hdvd⟩
  refine h𝔭 ?_
  have hbase : primePowerBase ⟨A, 𝔭.asIdeal, k, hprime, hk, hA⟩ = 𝔭 :=
    HeightOneSpectrum.ext (primePowerBase_asIdeal_eq hprime hA)
  rwa [← hbase, ← dvd_iff_eq_primePowerBase.mp hdvd]

/-- The von Mangoldt weight is monotone in the set of primes. -/
theorem primeVonMangoldtWeight_mono_set {T : Set (HeightOneSpectrum (𝓞 K))} (hST : S ⊆ T)
    (A : (Ideal (𝓞 K))⁰) :
    primeVonMangoldtWeight K S A ≤ primeVonMangoldtWeight K T A := by
  by_cases h : ∃ 𝔭 ∈ S, 𝔭.asIdeal ∣ (A : Ideal (𝓞 K))
  · obtain ⟨𝔭, h𝔭, hdvd⟩ := h
    rw [primeVonMangoldtWeight_of_exists_dvd ⟨𝔭, h𝔭, hdvd⟩,
      primeVonMangoldtWeight_of_exists_dvd ⟨𝔭, hST h𝔭, hdvd⟩]
  · rw [primeVonMangoldtWeight_of_not_exists_dvd h]
    exact primeVonMangoldtWeight_nonneg T A

/-- **The von Mangoldt weight of `S` on the prime-power carrier** is exactly the summand of
Chebyshev's `ψ`: the standard logarithmic weight at the prime powers with base in `S`, and `0`
elsewhere. -/
theorem primeVonMangoldtWeight_idealPrimePower (S : Set (HeightOneSpectrum (𝓞 K)))
    (A : IdealPrimePower K) :
    primeVonMangoldtWeight K S (A : (Ideal (𝓞 K))⁰) =
      {B : IdealPrimePower K | primePowerBase B ∈ S}.indicator primePowerWeight A := by
  by_cases h : primePowerBase A ∈ S
  · rw [primeVonMangoldtWeight_of_exists_dvd
      ⟨primePowerBase A, h, dvd_iff_eq_primePowerBase.mpr rfl⟩,
      Set.indicator_of_mem (s := {B : IdealPrimePower K | primePowerBase B ∈ S}) h,
      primePowerWeight_eq_vonMangoldt_re]
  · rw [Set.indicator_of_notMem (s := {B : IdealPrimePower K | primePowerBase B ∈ S}) h]
    refine primeVonMangoldtWeight_of_not_exists_dvd ?_
    rintro ⟨𝔭, h𝔭, hdvd⟩
    exact h (dvd_iff_eq_primePowerBase.mp hdvd ▸ h𝔭)

/-- Over *all* height-one primes the weight is the real form of the ideal von Mangoldt function of
Layer 2. -/
@[simp]
theorem primeVonMangoldtWeight_univ (A : (Ideal (𝓞 K))⁰) :
    primeVonMangoldtWeight K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) A =
      (IdealArithmeticFunction.vonMangoldt A).re := by
  by_cases hA : IsPrimePow (A : Ideal (𝓞 K))
  · exact primeVonMangoldtWeight_of_exists_dvd
      ⟨primePowerBase ⟨A, hA⟩, Set.mem_univ _, dvd_iff_eq_primePowerBase.mpr rfl⟩
  · rw [primeVonMangoldtWeight_eq_zero_of_not_isPrimePow hA,
      IdealArithmeticFunction.vonMangoldt_eq_zero_of_not_isPrimePow hA, Complex.zero_re]

variable (K) in
/-- The **von Mangoldt coefficient system of a set `S` of height-one primes**: its value at `n` is
the sum of `log N(𝔭)` over the prime powers `𝔭 ^ k` of absolute norm exactly `n` whose base `𝔭` lies
in `S`.

This is the nonnegative arithmetic function whose inclusive partial sums are Chebyshev's `ψ`, by
`TauCeti.primePsi_eq_sum_range`, and whose Dirichlet series is the one a Tauberian theorem sees. -/
noncomputable def primeVonMangoldtCoeff (S : Set (HeightOneSpectrum (𝓞 K))) :
    ArithmeticFunction ℝ where
  toFun n := ∑ I ∈ normFiber K n, primeVonMangoldtWeight K S I
  map_zero' := by rw [normFiber_zero, Finset.sum_empty]

/-- The von Mangoldt coefficient at `n` is the total weight of the absolute-norm fibre at `n`. -/
theorem primeVonMangoldtCoeff_apply (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    primeVonMangoldtCoeff K S n = ∑ I ∈ normFiber K n, primeVonMangoldtWeight K S I :=
  (rfl)

/-- The von Mangoldt coefficients are nonnegative, as the Tauberian input requires. -/
theorem primeVonMangoldtCoeff_nonneg (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    0 ≤ primeVonMangoldtCoeff K S n := by
  rw [primeVonMangoldtCoeff_apply]
  exact Finset.sum_nonneg fun I _ ↦ primeVonMangoldtWeight_nonneg S I

/-- The empty set of primes has vanishing von Mangoldt coefficients. -/
@[simp]
theorem primeVonMangoldtCoeff_empty (n : ℕ) :
    primeVonMangoldtCoeff K (∅ : Set (HeightOneSpectrum (𝓞 K))) n = 0 := by
  rw [primeVonMangoldtCoeff_apply]
  exact Finset.sum_eq_zero fun I _ ↦ primeVonMangoldtWeight_empty I

/-- The von Mangoldt coefficient at `1` vanishes: the unit ideal is the only ideal of absolute
norm one, and it is not a prime power. -/
@[simp]
theorem primeVonMangoldtCoeff_apply_one (S : Set (HeightOneSpectrum (𝓞 K))) :
    primeVonMangoldtCoeff K S 1 = 0 := by
  rw [primeVonMangoldtCoeff_apply, normFiber_one, Finset.sum_singleton]
  exact primeVonMangoldtWeight_eq_zero_of_not_isPrimePow
    (by simpa using (isUnit_one (M := Ideal (𝓞 K))).not_isPrimePow)

/-- The von Mangoldt coefficients are monotone in the set of primes. -/
theorem primeVonMangoldtCoeff_mono_set {T : Set (HeightOneSpectrum (𝓞 K))} (hST : S ⊆ T) (n : ℕ) :
    primeVonMangoldtCoeff K S n ≤ primeVonMangoldtCoeff K T n := by
  rw [primeVonMangoldtCoeff_apply, primeVonMangoldtCoeff_apply]
  exact Finset.sum_le_sum fun I _ ↦ primeVonMangoldtWeight_mono_set hST I

/-- **The support of the coefficient system**: a von Mangoldt coefficient vanishes unless its index
is a prime power, since the absolute norm of a prime-power ideal is again a prime power. -/
theorem primeVonMangoldtCoeff_eq_zero_of_not_isPrimePow (S : Set (HeightOneSpectrum (𝓞 K)))
    {n : ℕ} (hn : ¬ IsPrimePow n) : primeVonMangoldtCoeff K S n = 0 := by
  rw [primeVonMangoldtCoeff_apply]
  refine Finset.sum_eq_zero fun I hI ↦
    primeVonMangoldtWeight_eq_zero_of_not_isPrimePow fun h ↦ hn ?_
  rw [← (mem_normFiber K).mp hI]
  exact isPrimePow_absNorm ⟨I, h⟩

/-- **The coefficient system is the Layer 1 norm regrouping of the von Mangoldt weight of `S`**,
read in `ℂ`. -/
theorem normCoeff_ofReal_primeVonMangoldtWeight (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    normCoeff K (fun I ↦ ((primeVonMangoldtWeight K S I : ℝ) : ℂ)) n =
      ((primeVonMangoldtCoeff K S n : ℝ) : ℂ) := by
  rw [normCoeff_eq_sum_normFiber, primeVonMangoldtCoeff_apply, Complex.ofReal_sum]

/-- **Over all height-one primes the coefficient system regroups the ideal von Mangoldt function**
of Layer 2 by absolute norm. -/
theorem normCoeff_vonMangoldt (n : ℕ) :
    normCoeff K (IdealArithmeticFunction.vonMangoldt : IdealArithmeticFunction K) n =
      ((primeVonMangoldtCoeff K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) n : ℝ) : ℂ) := by
  rw [← normCoeff_ofReal_primeVonMangoldtWeight]
  refine congrArg (fun f ↦ normCoeff K f n) (funext fun I ↦ ?_)
  rw [primeVonMangoldtWeight_univ]
  exact (Complex.ext (by simp) (by simp [IdealArithmeticFunction.vonMangoldt_im])).symm

/-- **Chebyshev's `ψ` is the inclusive partial sum of the von Mangoldt coefficient system.**

This is what lets a Tauberian theorem stated for `x⁻¹ ∑_{n ≤ x} a n` speak about `ψ(x) / x`:
Layer 9's conclusion is about the left-hand side, and Layer 10 needs it about the right. -/
theorem primePsi_eq_sum_range (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primePsi K S x = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), primeVonMangoldtCoeff K S n := by
  rw [primePsi, ← idealSummatory_eq_primePowerSummatory K (primeVonMangoldtWeight K S) _
      (primeVonMangoldtWeight_idealPrimePower S)
      (fun _ hI ↦ primeVonMangoldtWeight_eq_zero_of_not_isPrimePow hI),
    idealSummatory_eq_sum_range_normFiber]
  exact Finset.sum_congr rfl fun n _ ↦ (primeVonMangoldtCoeff_apply S n).symm

/-- Chebyshev's `ψ` at a natural cutoff, the form in which the coefficient system is summed. -/
theorem primePsi_natCast_eq_sum_range (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    primePsi K S (n : ℝ) = ∑ m ∈ Finset.range (n + 1), primeVonMangoldtCoeff K S m := by
  rw [primePsi_eq_sum_range, Nat.floor_natCast]

end TauCeti
