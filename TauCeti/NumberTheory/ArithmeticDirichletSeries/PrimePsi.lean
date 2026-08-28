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

## Main results

* `TauCeti.primePsi_sub_primeTheta` identifies `ψ - ϑ` with the higher-prime-power sum.
* `TauCeti.standardPrimePowerRemoval` proves `HasNegligibleHigherPrimePowers K S` for every `S`,
  from the Layer 5 estimate `ψ(x) - ϑ(x) = O(√x log² x)`.
* `TauCeti.primeTheta_asymptotic_of_primePsi` and
  `TauCeti.primePsi_asymptotic_of_primeTheta` transfer a linear asymptotic across that difference,
  with `TauCeti.primeTheta_isEquivalent_of_primePsi` the equivalence form for a nonzero density.

## Roadmap role

This is Layer **10.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: "For the fixed
standard nonnegative logarithmic prime-power weight, use Layer 5 to prove
`standardPrimePowerRemoval : HasNegligibleHigherPrimePowers K S` and make
`primeTheta_asymptotic_of_primePsi` consume that named estimate."  The definition of `primePsi`
belongs to Layer 10.1, whose remaining content — the analytic package `PrimeBoundaryRemainder`
and the asymptotic for `ψ` it yields — waits on the Wiener–Ikehara theorem of Layer 9.

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

end TauCeti
