/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.LFunction
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Weight

/-!
# Local factors for ideal arithmetic functions

This file starts the Euler-product layer for arithmetic functions on nonzero ideals.  It defines
coprime multiplicativity on the ideal carrier, builds the canonical formal power series at each
height-one prime, and sends that series into Mathlib's `ArithmeticFunction.ofPowerSeries` API.

`TauCeti.EulerProductData K f` packages the coprime-multiplicativity prerequisite for these
canonical local factors.  The local factors are derived from `f`, rather than stored as
independently chosen data, so the package has no unconstrained values away from prime powers.
The equality between `normCoeff K f` and their formal Euler product is not part of the data;
Layer 3.2 derives it from finite prime-power factorization.  The delta function supplies the base
example.

## Main definitions

* `TauCeti.IdealArithmeticFunction.IsMultiplicative` is multiplicativity on relatively prime
  nonzero ideals.
* `TauCeti.IdealArithmeticFunction.localPowerSeries` has coefficient `f (P ^ n)` at `n`.
* `TauCeti.IdealArithmeticFunction.localArithmeticFactor` realizes that power series as an
  arithmetic function supported on powers of `N(P)`.
* `TauCeti.EulerProductData K f` records the multiplicativity prerequisite for the formal ideal
  Euler-product identity.

## Roadmap role

This is the canonical-local-factor and packaging part of Layer **3.1** of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.  The remaining part of that target constructs
the package for multiplicative ideal weights and proves its restriction, product, conjugation,
and trivial-weight operations.  Later Layer 3 steps pass from this formal identity to finite and
absolutely convergent analytic products.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `ArithmeticFunction.ofPowerSeries` and `ArithmeticFunction.eulerProduct` APIs.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors NumberField
open IsDedekindDomain (HeightOneSpectrum)

namespace IdealArithmeticFunction

variable {K : Type*} [Field K]

/-- An ideal arithmetic function is multiplicative when it takes the unit ideal to `1` and
respects products of relatively prime nonzero ideals.  This is weaker than the complete
multiplicativity carried by `MultiplicativeIdealWeight`. -/
def IsMultiplicative (f : IdealArithmeticFunction K) : Prop :=
  f 1 = 1 ∧ ∀ I J : (Ideal (𝓞 K))⁰,
    IsRelPrime (I : Ideal (𝓞 K)) (J : Ideal (𝓞 K)) → f (I * J) = f I * f J

/-- The unit-value part of ideal multiplicativity. -/
theorem IsMultiplicative.map_one {f : IdealArithmeticFunction K} (hf : f.IsMultiplicative) :
    f 1 = 1 :=
  hf.1

/-- The coprime-product part of ideal multiplicativity. -/
theorem IsMultiplicative.map_mul_of_isRelPrime {f : IdealArithmeticFunction K}
    (hf : f.IsMultiplicative) {I J : (Ideal (𝓞 K))⁰}
    (hIJ : IsRelPrime (I : Ideal (𝓞 K)) (J : Ideal (𝓞 K))) :
    f (I * J) = f I * f J :=
  hf.2 I J hIJ

/-- The everywhere-one ideal arithmetic function is multiplicative. -/
theorem isMultiplicative_one : IsMultiplicative (1 : IdealArithmeticFunction K) := by
  simp [IsMultiplicative]

/-- The convolution identity is multiplicative. -/
theorem isMultiplicative_delta : IsMultiplicative (delta : IdealArithmeticFunction K) := by
  refine ⟨delta_one, fun I J _ => ?_⟩
  by_cases hI : I = 1
  · subst I
    simp
  by_cases hJ : J = 1
  · subst J
    simp
  have hmul : I * J ≠ 1 := by
    intro hmul
    have hunit : IsUnit (I : Ideal (𝓞 K)) :=
      isUnit_iff_exists_inv.mpr ⟨(J : Ideal (𝓞 K)), by simpa using congrArg Subtype.val hmul⟩
    apply hI
    exact Subtype.ext ((Ideal.isUnit_iff.mp hunit).trans Ideal.one_eq_top.symm)
  rw [delta_of_ne_one hmul, delta_of_ne_one hI, delta_of_ne_one hJ, zero_mul]

/-- Pointwise products of multiplicative ideal arithmetic functions are multiplicative. -/
theorem IsMultiplicative.mul {f g : IdealArithmeticFunction K}
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) : (f * g).IsMultiplicative := by
  refine ⟨by simp [hf.map_one, hg.map_one], fun I J hIJ => ?_⟩
  rw [Pi.mul_apply, Pi.mul_apply, Pi.mul_apply, hf.map_mul_of_isRelPrime hIJ,
    hg.map_mul_of_isRelPrime hIJ]
  ring

/-- Complex conjugation preserves multiplicativity of ideal arithmetic functions. -/
theorem IsMultiplicative.star {f : IdealArithmeticFunction K} (hf : f.IsMultiplicative) :
    (star f).IsMultiplicative := by
  refine ⟨by simp [hf.map_one], fun I J hIJ => ?_⟩
  simp only [Pi.star_apply, hf.map_mul_of_isRelPrime hIJ, star_mul']

variable [NumberField K]

/-- The ideal arithmetic function underlying a completely multiplicative ideal weight is
multiplicative on relatively prime ideals. -/
theorem isMultiplicative_toIdealArithmeticFunction (χ : MultiplicativeIdealWeight K) :
    χ.toIdealArithmeticFunction.IsMultiplicative := by
  refine ⟨by simp, fun I J _ => ?_⟩
  simp

/-- The ideal arithmetic function underlying a unitary ideal weight is multiplicative on
relatively prime ideals. -/
theorem isMultiplicative_unitary_toIdealArithmeticFunction (χ : UnitaryIdealWeight K) :
    χ.toIdealArithmeticFunction.IsMultiplicative := by
  have hfun : χ.toIdealArithmeticFunction = χ.1.toIdealArithmeticFunction := by
    funext I
    rw [UnitaryIdealWeight.toIdealArithmeticFunction_apply,
      MultiplicativeIdealWeight.toIdealArithmeticFunction_apply]
  rw [hfun]
  exact isMultiplicative_toIdealArithmeticFunction χ.1

/-- The canonical local power series of `f` at a height-one prime `P`; its coefficient at `n` is
the value of `f` at the nonzero ideal `P ^ n`. -/
noncomputable def localPowerSeries (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    f ⟨P.asIdeal ^ n, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n P.ne_bot)⟩

omit [NumberField K] in
/-- Coefficients of the canonical local power series are the prime-power values of `f`. -/
@[simp]
theorem coeff_localPowerSeries (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    PowerSeries.coeff n (localPowerSeries f P) =
      f ⟨P.asIdeal ^ n, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n P.ne_bot)⟩ := by
  simp [localPowerSeries]

omit [NumberField K] in
/-- The constant coefficient of the canonical local power series is `f 1`. -/
@[simp]
theorem constantCoeff_localPowerSeries (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) :
    (localPowerSeries f P).constantCoeff = f 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  rw [coeff_localPowerSeries]
  exact congrArg f (Subtype.ext (pow_zero P.asIdeal))

/-- The canonical local arithmetic factor at `P`, obtained by substituting `N(P)⁻ˢ` into the
formal prime-power series through Mathlib's `ArithmeticFunction.ofPowerSeries`. -/
noncomputable def localArithmeticFactor (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) : ArithmeticFunction ℂ :=
  ArithmeticFunction.ofPowerSeries (Ideal.absNorm P.asIdeal) (localPowerSeries f P)

/-- At a power of `N(P)`, the local arithmetic factor is the corresponding value at `P ^ n`. -/
@[simp]
theorem localArithmeticFactor_apply_pow (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    localArithmeticFactor f P (Ideal.absNorm P.asIdeal ^ n) =
      f ⟨P.asIdeal ^ n, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n P.ne_bot)⟩ := by
  rw [localArithmeticFactor, ArithmeticFunction.ofPowerSeries_apply_pow
    (NumberField.HeightOneSpectrum.one_lt_absNorm P)]
  exact coeff_localPowerSeries f P n

/-- A local arithmetic factor vanishes away from powers of its prime-ideal norm. -/
@[simp]
theorem localArithmeticFactor_apply_eq_zero_of_not_exists (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) {m : ℕ}
    (hm : ¬ ∃ n : ℕ, Ideal.absNorm P.asIdeal ^ n = m) :
    localArithmeticFactor f P m = 0 := by
  rw [localArithmeticFactor, ArithmeticFunction.ofPowerSeries_apply
    (NumberField.HeightOneSpectrum.one_lt_absNorm P),
    Function.extend_apply' _ _ _ (by simpa using hm), Pi.zero_apply]

/-- If `f` is multiplicative, each canonical local arithmetic factor is a multiplicative
arithmetic function. -/
theorem IsMultiplicative.isMultiplicative_localArithmeticFactor
    {f : IdealArithmeticFunction K} (hf : f.IsMultiplicative)
    (P : HeightOneSpectrum (𝓞 K)) :
    (localArithmeticFactor f P).IsMultiplicative := by
  apply ArithmeticFunction.isMultiplicative_ofPowerSeries_of_isPrimePow
  · obtain ⟨p, n, hn, _hpP, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P.asIdeal
    exact ⟨p, n, hp.prime, hn, hnorm.symm⟩
  · simpa using hf.map_one

/-- The canonical local power series of the convolution identity is the constant series `1`. -/
@[simp]
theorem localPowerSeries_delta (P : HeightOneSpectrum (𝓞 K)) :
    localPowerSeries (delta : IdealArithmeticFunction K) P = 1 := by
  rw [PowerSeries.ext_iff]
  intro n
  cases n with
  | zero =>
      simp only [PowerSeries.coeff_one]
      exact (congrArg delta (Subtype.ext (by simp [Ideal.one_eq_top]))).trans delta_one
  | succ n =>
      rw [coeff_localPowerSeries, delta_of_ne_one]
      · simp
      · intro hpow
        have hunit : IsUnit P.asIdeal :=
          IsUnit.of_pow_eq_one (congrArg Subtype.val hpow) (Nat.succ_ne_zero n)
        exact P.prime.not_isUnit hunit

/-- Every canonical local arithmetic factor of the convolution identity is `1`. -/
@[simp]
theorem localArithmeticFactor_delta (P : HeightOneSpectrum (𝓞 K)) :
    localArithmeticFactor (delta : IdealArithmeticFunction K) P = 1 := by
  rw [localArithmeticFactor, localPowerSeries_delta]
  exact (ArithmeticFunction.ofPowerSeries (Ideal.absNorm P.asIdeal)).map_one

end IdealArithmeticFunction

variable (K : Type*) [Field K]

/-- Local Euler-product data for an ideal arithmetic function.

The local factors are the canonical factors derived from the prime-power values of `f`, so the
only prerequisite stored here is coprime multiplicativity.  The global equality between the
norm-regrouped coefficient and Mathlib's formal Euler product is a theorem to be derived from the
finite-factorization result in Layer 3.2, rather than an assumption in this structure. -/
structure EulerProductData (f : IdealArithmeticFunction K) : Prop where
  isMultiplicative : f.IsMultiplicative

namespace EulerProductData

variable {K : Type*} [Field K]
variable {f g : IdealArithmeticFunction K}

/-- Euler-product data are proof-irrelevant for a fixed ideal arithmetic function. -/
instance : Subsingleton (EulerProductData K f) := inferInstance

/-- Transport Euler-product data across equality of ideal arithmetic functions. -/
theorem congr (hfg : f = g) (hf : EulerProductData K f) : EulerProductData K g := by
  subst g
  exact hf

/-- The formal Euler product attached to data is multiplicative as an arithmetic function. -/
theorem isMultiplicative_eulerProduct [NumberField K] (hf : EulerProductData K f) :
    (ArithmeticFunction.eulerProduct f.localArithmeticFactor).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_eulerProduct _
    hf.isMultiplicative.isMultiplicative_localArithmeticFactor

/-- The convolution identity has the tautological Euler product whose every local factor is
`1`.  This is the base example for the package and fixes its zero-slot convention. -/
@[simp]
theorem delta : EulerProductData K IdealArithmeticFunction.delta where
  isMultiplicative := IdealArithmeticFunction.isMultiplicative_delta

end EulerProductData

end TauCeti
