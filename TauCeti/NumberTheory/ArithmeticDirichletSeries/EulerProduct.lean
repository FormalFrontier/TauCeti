/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.LFunction
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

/-!
# Local factors for ideal arithmetic functions

This file starts the Euler-product layer for arithmetic functions on nonzero ideals. It builds the
canonical formal power series at each height-one prime and sends that series into Mathlib's
`ArithmeticFunction.ofPowerSeries` API. The resulting local arithmetic factor has the prescribed
prime-power values and vanishes away from powers of the prime-ideal norm.

The richer `EulerProductData` package required by Layer 3.1 is not defined here: it must also carry
a finite bad set and the hypotheses that transport an ideal product through `normCoeff`. The
canonical factors developed here are prerequisites for that package, not a substitute for it.

## Main definitions

* `TauCeti.IdealArithmeticFunction.localPowerSeries` has coefficient `f (P ^ n)` at `n`.
* `TauCeti.IdealArithmeticFunction.localArithmeticFactor` realizes that power series as an
  arithmetic function supported on powers of `N(P)`.

## Roadmap role

This is the canonical-local-factor prerequisite for Layer **3.1** of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`; the local series is derived here rather than
stored. The remaining target defines `EulerProductData` with its finite bad set and `normCoeff`
transport hypotheses, supplies extensionality, and constructs restriction, product, conjugation,
trivial-weight, and general multiplicative-weight operations. Layer 3.2 then proves the finite
prime-power factorization and formal Euler-product identity, before later steps pass to absolutely
convergent analytic products.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `ArithmeticFunction.ofPowerSeries` and `ArithmeticFunction.eulerProduct` APIs.
* `TauCetiRoadmap/ArithmeticDirichletSeries/Suggested.lean`, whose Layer 3 local-factor target
  signatures and naming are adapted here; the full data package and `normCoeff` identity are
  deferred as described above.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors NumberField
open IsDedekindDomain (HeightOneSpectrum)

namespace IdealArithmeticFunction

variable {K : Type*} [Field K]

variable [NumberField K]

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

/-- The canonical local arithmetic factor is Mathlib's arithmetic function associated to the
local power series at `P`. -/
theorem localArithmeticFactor_def (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) :
    localArithmeticFactor f P =
      ArithmeticFunction.ofPowerSeries (Ideal.absNorm P.asIdeal) (localPowerSeries f P) := by
  rw [localArithmeticFactor]

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
theorem localArithmeticFactor_apply_eq_zero_of_not_exists_pow_eq (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) {m : ℕ}
    (hm : ¬ ∃ n : ℕ, Ideal.absNorm P.asIdeal ^ n = m) :
    localArithmeticFactor f P m = 0 := by
  rw [localArithmeticFactor, ArithmeticFunction.ofPowerSeries_apply
    (NumberField.HeightOneSpectrum.one_lt_absNorm P),
    Function.extend_apply' _ _ _ (by simpa using hm), Pi.zero_apply]

/-- A nonzero value of a local arithmetic factor is supported on a power of the prime-ideal
norm. -/
theorem exists_pow_eq_of_localArithmeticFactor_apply_ne_zero (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) {m : ℕ} (hm : localArithmeticFactor f P m ≠ 0) :
    ∃ n : ℕ, Ideal.absNorm P.asIdeal ^ n = m := by
  by_contra hpow
  exact hm (localArithmeticFactor_apply_eq_zero_of_not_exists_pow_eq f P hpow)

/-- If `f` takes the unit ideal to `1`, each canonical local arithmetic factor is a
multiplicative arithmetic function. -/
theorem isMultiplicative_localArithmeticFactor
    {f : IdealArithmeticFunction K} (hf : f 1 = 1)
    (P : HeightOneSpectrum (𝓞 K)) :
    (localArithmeticFactor f P).IsMultiplicative := by
  apply ArithmeticFunction.isMultiplicative_ofPowerSeries_of_isPrimePow
  · obtain ⟨p, n, hn, _hpP, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P.asIdeal
    exact ⟨p, n, hp.prime, hn, hnorm.symm⟩
  · simpa using hf

/-- If `f` takes the unit ideal to `1`, the formal Euler product of its canonical local factors is
multiplicative as an arithmetic function. -/
theorem isMultiplicative_eulerProduct {f : IdealArithmeticFunction K} (hf : f 1 = 1) :
    (ArithmeticFunction.eulerProduct f.localArithmeticFactor).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_eulerProduct _ (isMultiplicative_localArithmeticFactor hf)

/-- At each coefficient, finite products of the canonical local factors eventually equal their
formal Euler product. -/
theorem tendsTo_eulerProduct_localArithmeticFactor (f : IdealArithmeticFunction K)
    (hf : f 1 = 1) (n : ℕ) :
    ∀ᶠ S : Finset (HeightOneSpectrum (𝓞 K)) in Filter.atTop,
      (∏ P ∈ S, localArithmeticFactor f P) n =
        ArithmeticFunction.eulerProduct f.localArithmeticFactor n := by
  have hlocal : f.localArithmeticFactor = fun P ↦
      ArithmeticFunction.ofPowerSeries (Ideal.absNorm P.asIdeal) (localPowerSeries f P) := by
    rfl
  rw [hlocal]
  exact
    ArithmeticFunction.tendsTo_eulerProduct_ofPowerSeries
      (fun P : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm P.asIdeal)
      (fun P ↦ localPowerSeries f P)
      (fun P ↦ (constantCoeff_localPowerSeries f P).trans hf) n

/-- The canonical local power series of the convolution identity is the constant series `1`. -/
@[simp]
theorem localPowerSeries_delta (P : HeightOneSpectrum (𝓞 K)) :
    localPowerSeries (delta : IdealArithmeticFunction K) P = 1 := by
  rw [PowerSeries.ext_iff]
  intro n
  cases n with
  | zero =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_localPowerSeries, delta_one]
      simp
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

end TauCeti
