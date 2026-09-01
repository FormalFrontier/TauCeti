/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.LFunction
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution
public import TauCeti.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm

/-!
# Local factors and finite Euler products for ideal arithmetic functions

This file develops the Euler-product layer for arithmetic functions on nonzero ideals. It builds
the canonical formal power series at each height-one prime and sends that series into Mathlib's
`ArithmeticFunction.ofPowerSeries` API. The resulting local arithmetic factor has the prescribed
prime-power values and vanishes away from powers of the prime-ideal norm.

It then restricts an ideal arithmetic function to the nonzero ideals whose prime factors lie in a
prescribed set of height-one primes, and proves that for a *finite* set of primes the norm
coefficients of that restriction are exactly the product of the local factors, taken in Mathlib's
Dirichlet convolution of arithmetic functions. Everything here is a formal identity of
coefficients: no convergence hypothesis enters, and the passage to an infinite product of analytic
functions is a later step.

The richer `EulerProductData` package required by Layer 3.1 is not defined here: it must also carry
a finite bad set and bundle the coprime-multiplicativity and analytic local hypotheses. The formal
transport through `normCoeff` is proved here from multiplicativity, so the eventual package can
expose that theorem without storing an unconstrained equality field.

## Main definitions

* `TauCeti.IdealArithmeticFunction.localPowerSeries` has coefficient `f (P ^ n)` at `n`.
* `TauCeti.IdealArithmeticFunction.localArithmeticFactor` realizes that power series as an
  arithmetic function supported on powers of `N(P)`.
* `TauCeti.IdealArithmeticFunction.supportedPart f S` is `f` restricted to the nonzero ideals all
  of whose prime factors lie in `S`, and zero elsewhere.

## Main results

* `TauCeti.IdealArithmeticFunction.supportedPart_insert`: for a multiplicative `f`, adjoining one
  prime to the support convolves the restriction with the restriction to the powers of that prime.
* `TauCeti.IdealArithmeticFunction.normCoeff_supportedPart`: the **finite Euler product**
  `normCoeff (supportedPart f S) = ∏ P ∈ S, localArithmeticFactor f P` for a multiplicative `f`
  and a finite set `S` of height-one primes.
* `TauCeti.IdealArithmeticFunction.normCoeff_eq_eulerProduct`: the norm coefficients of a
  multiplicative ideal arithmetic function are Mathlib's formal Euler product of its canonical
  local factors.

## Implementation notes

"Supported on `S`" is spelled `Ideal.IsPrimeTo · Sᶜ`: no prime *outside* `S` divides the ideal.
That predicate, and the splitting `Ideal.IsPrimeTo.exists_eq_pow_mul` of an ideal into a prime
power times a cofactor together with its uniqueness `Ideal.eq_and_eq_of_pow_mul_eq_pow_mul`, live
in `TauCeti/RingTheory/DedekindDomain/Ideal.lean`, since nothing in them is specific to a number
field. Uniqueness is what makes the induction work: it is why exactly one summand of the ideal
convolution survives at each ideal. The multiplicativity of `f` over a prime-power factorization,
`TauCeti.IdealArithmeticFunction.IsMultiplicative.map_prod_pow`, likewise lives with the predicate
it elaborates, in `TauCeti/NumberTheory/ArithmeticDirichletSeries/Basic.lean`.

`TauCeti.MultiplicativeIdealWeight.restrict` is the opposite regime and is not a substitute:
it restricts *away from* a **finite** set of primes and stays inside the bundled weight carrier. A
finite Euler product needs support on a *finite* set of primes, so all but finitely many primes are
bad; such a function is never a `MultiplicativeIdealWeight`, whose zero support is finite by
definition. Hence `supportedPart` is a plain ideal arithmetic function.

## Roadmap role

This is the canonical-local-factor prerequisite for Layer **3.1** and the whole of Layer **3.2**
("Finite products first") of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`; the local series
is derived here rather than stored. The remaining Layer 3.1 target defines `EulerProductData` with
its finite bad set and `normCoeff` transport hypotheses, supplies extensionality, and constructs
restriction, product, conjugation, trivial-weight, and general multiplicative-weight operations.
The formal transport theorem `normCoeff_eq_eulerProduct` supplies the coefficient identity that
package will expose. Layer 3.3 then evaluates it on an absolute-convergence half-plane and passes
to the analytic product of the local series.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `ArithmeticFunction.ofPowerSeries` and `ArithmeticFunction.eulerProduct` APIs.
* `TauCetiRoadmap/ArithmeticDirichletSeries/Suggested.lean`, whose Layer 3 local-factor target
  signatures and naming are adapted here; the full data package is deferred as described above.
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

/-! ### Finite Euler products -/

/-- The part of `f` supported on the nonzero ideals all of whose prime factors lie in `S`: it
agrees with `f` there and vanishes on every other nonzero ideal. Being supported on `S` is
`Ideal.IsPrimeTo · Sᶜ`, that no prime outside `S` divides the ideal. Use
`supportedPart_apply_of_isPrimeTo_compl` and `supportedPart_apply_of_not_isPrimeTo_compl` rather
than unfolding. -/
noncomputable def supportedPart (f : IdealArithmeticFunction K)
    (S : Set (HeightOneSpectrum (𝓞 K))) : IdealArithmeticFunction K :=
  Set.indicator {A : (Ideal (𝓞 K))⁰ | Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ} f

variable {f : IdealArithmeticFunction K} {S : Set (HeightOneSpectrum (𝓞 K))}
  {A : (Ideal (𝓞 K))⁰}

omit [NumberField K] in
/-- On an ideal supported on `S`, the restriction of `f` to `S` is `f`. -/
@[simp]
theorem supportedPart_apply_of_isPrimeTo_compl (hA : Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ) :
    supportedPart f S A = f A :=
  Set.indicator_of_mem
    (s := {A : (Ideal (𝓞 K))⁰ | Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ}) hA f

omit [NumberField K] in
/-- On an ideal with a prime factor outside `S`, the restriction of `f` to `S` vanishes. -/
@[simp]
theorem supportedPart_apply_of_not_isPrimeTo_compl (hA : ¬ Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ) :
    supportedPart f S A = 0 :=
  Set.indicator_of_notMem
    (s := {A : (Ideal (𝓞 K))⁰ | Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ}) hA f

omit [NumberField K] in
/-- The restriction of `f` to `S` is supported on the ideals supported on `S`. -/
theorem isPrimeTo_compl_of_supportedPart_apply_ne_zero (hA : supportedPart f S A ≠ 0) :
    Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ :=
  not_not.mp fun h ↦ hA (supportedPart_apply_of_not_isPrimeTo_compl h)

/-- The unit ideal is supported on every set of primes. This is not marked `@[simp]`: `simp`
already reaches it through `supportedPart_apply_of_isPrimeTo_compl`. -/
theorem supportedPart_one (f : IdealArithmeticFunction K) (S : Set (HeightOneSpectrum (𝓞 K))) :
    supportedPart f S 1 = f 1 :=
  supportedPart_apply_of_isPrimeTo_compl (by simp [Ideal.one_eq_top])

/-- Restricting a multiplicative ideal arithmetic function to the ideals supported on `S` keeps it
multiplicative: an ideal is supported on `S` exactly when both factors of a product are. -/
theorem IsMultiplicative.supportedPart (hf : f.IsMultiplicative)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    (IdealArithmeticFunction.supportedPart f S).IsMultiplicative := by
  refine ⟨by rw [supportedPart_one, hf.map_one], fun {I J} hIJ ↦ ?_⟩
  by_cases hI : Ideal.IsPrimeTo (I : Ideal (𝓞 K)) Sᶜ
  · by_cases hJ : Ideal.IsPrimeTo (J : Ideal (𝓞 K)) Sᶜ
    · rw [supportedPart_apply_of_isPrimeTo_compl (A := I * J)
        (by rw [Submonoid.coe_mul]; exact Ideal.isPrimeTo_mul_iff.mpr ⟨hI, hJ⟩),
        supportedPart_apply_of_isPrimeTo_compl hI, supportedPart_apply_of_isPrimeTo_compl hJ,
        hf.map_mul_of_isRelPrime hIJ]
    · rw [supportedPart_apply_of_not_isPrimeTo_compl (A := I * J)
        (by rw [Submonoid.coe_mul, Ideal.isPrimeTo_mul_iff]; tauto),
        supportedPart_apply_of_not_isPrimeTo_compl hJ, mul_zero]
  · rw [supportedPart_apply_of_not_isPrimeTo_compl (A := I * J)
      (by rw [Submonoid.coe_mul, Ideal.isPrimeTo_mul_iff]; tauto),
      supportedPart_apply_of_not_isPrimeTo_compl hI, zero_mul]

omit [NumberField K] in
/-- Every nonzero ideal is supported on the set of all height-one primes. -/
@[simp]
theorem supportedPart_univ (f : IdealArithmeticFunction K) : supportedPart f Set.univ = f := by
  funext A
  refine supportedPart_apply_of_isPrimeTo_compl ?_
  rw [Set.compl_univ]
  exact Ideal.isPrimeTo_empty.mpr (by simpa using nonZeroDivisors.coe_ne_zero A)

/-- Only the unit ideal is supported on no prime at all, so the empty restriction of a function
taking the value `1` there is the convolution identity. -/
theorem supportedPart_empty (hf : f 1 = 1) : supportedPart f ∅ = delta := by
  funext A
  have hiff : Ideal.IsPrimeTo (A : Ideal (𝓞 K)) (∅ : Set (HeightOneSpectrum (𝓞 K)))ᶜ ↔ A = 1 := by
    rw [Set.compl_empty, Ideal.isPrimeTo_univ_iff, ← Ideal.one_eq_top]
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  rcases eq_or_ne A 1 with rfl | hA
  · rw [supportedPart_apply_of_isPrimeTo_compl (hiff.mpr rfl), delta_one, hf]
  · rw [supportedPart_apply_of_not_isPrimeTo_compl fun h ↦ hA (hiff.mp h), delta_of_ne_one hA]

/-- **Splitting off one prime.** For a multiplicative `f`, adjoining a prime `P ∉ S` to the support
convolves the restriction to `S` with the restriction to the powers of `P`; the factorization of an
ideal supported on `insert P S` into its `P`-part and its `S`-part is unique, so exactly one
summand of the convolution survives. -/
theorem supportedPart_insert (hf : f.IsMultiplicative) {P : HeightOneSpectrum (𝓞 K)}
    (hP : P ∉ S) :
    supportedPart f (insert P S) = convolution (supportedPart f S) (supportedPart f {P}) := by
  have hPS : P ∈ Sᶜ := Set.mem_compl hP
  have hmono : (insert P S)ᶜ ⊆ Sᶜ := Set.compl_subset_compl.mpr (Set.subset_insert P S)
  -- A nonvanishing summand pairs an ideal supported on `S` with a power of `P`.
  have key : ∀ p : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰,
      supportedPart f S p.1 * supportedPart f {P} p.2 ≠ 0 →
      Ideal.IsPrimeTo (p.1 : Ideal (𝓞 K)) Sᶜ ∧ ∃ m : ℕ, (p.2 : Ideal (𝓞 K)) = P.asIdeal ^ m := by
    intro p hp
    exact ⟨isPrimeTo_compl_of_supportedPart_apply_ne_zero (left_ne_zero_of_mul hp),
      Ideal.isPrimeTo_compl_singleton_iff.mp
        (isPrimeTo_compl_of_supportedPart_apply_ne_zero (right_ne_zero_of_mul hp))⟩
  funext A
  rw [convolution_apply]
  by_cases hA : Ideal.IsPrimeTo (A : Ideal (𝓞 K)) (insert P S)ᶜ
  · obtain ⟨n, J, hJ, hAJ⟩ := hA.exists_eq_pow_mul (𝔭 := P)
    obtain ⟨B, hBval⟩ : ∃ B : (Ideal (𝓞 K))⁰, (B : Ideal (𝓞 K)) = J :=
      ⟨⟨J, mem_nonZeroDivisors_of_ne_zero (by simpa using hJ.ne_bot)⟩, rfl⟩
    obtain ⟨C, hCval⟩ : ∃ C : (Ideal (𝓞 K))⁰, (C : Ideal (𝓞 K)) = P.asIdeal ^ n :=
      ⟨⟨_, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n P.ne_bot)⟩, rfl⟩
    have hJ' : Ideal.IsPrimeTo (B : Ideal (𝓞 K)) Sᶜ := by rw [hBval]; exact hJ
    have hCP : Ideal.IsPrimeTo (C : Ideal (𝓞 K)) ({P} : Set (HeightOneSpectrum (𝓞 K)))ᶜ := by
      rw [hCval]; exact Ideal.isPrimeTo_compl_singleton_iff.mpr ⟨n, rfl⟩
    have hBC : B * C = A :=
      Subtype.ext (by rw [Submonoid.coe_mul, hBval, hCval, mul_comm, ← hAJ])
    have hzero : ∀ p ∈ Ideal.divisorsAntidiagonal A, p ≠ (B, C) →
        supportedPart f S p.1 * supportedPart f {P} p.2 = 0 := by
      intro p hp hne
      by_contra hp0
      obtain ⟨h1, m, h2⟩ := key p hp0
      have hmul : (p.1 : Ideal (𝓞 K)) * (p.2 : Ideal (𝓞 K)) = (A : Ideal (𝓞 K)) := by
        rw [← Submonoid.coe_mul, Ideal.mem_divisorsAntidiagonal.mp hp]
      have heq : P.asIdeal ^ m * (p.1 : Ideal (𝓞 K)) = P.asIdeal ^ n * J := by
        rw [← h2, mul_comm, hmul, hAJ]
      obtain ⟨rfl, hval⟩ :=
        Ideal.eq_and_eq_of_pow_mul_eq_pow_mul P.ne_bot (h1.not_dvd hPS) (hJ.not_dvd hPS) heq
      exact hne (Prod.ext (Subtype.ext (hval.trans hBval.symm))
        (Subtype.ext (h2.trans hCval.symm)))
    rw [Finset.sum_eq_single_of_mem (B, C) (Ideal.mem_divisorsAntidiagonal.mpr hBC) hzero,
      supportedPart_apply_of_isPrimeTo_compl hA, supportedPart_apply_of_isPrimeTo_compl hJ',
      supportedPart_apply_of_isPrimeTo_compl hCP,
      ← hf.map_mul_of_isRelPrime
        ((hJ'.mono (Set.singleton_subset_iff.mpr hPS)).isRelPrime hCP), hBC]
  · rw [supportedPart_apply_of_not_isPrimeTo_compl hA]
    refine (Finset.sum_eq_zero fun p hp ↦ ?_).symm
    by_contra hp0
    obtain ⟨h1, m, h2⟩ := key p hp0
    refine hA ?_
    rw [← congrArg Subtype.val (Ideal.mem_divisorsAntidiagonal.mp hp), Submonoid.coe_mul]
    refine Ideal.isPrimeTo_mul_iff.mpr ⟨h1.mono hmono, ?_⟩
    rw [h2]
    exact (Ideal.isPrimeTo_asIdeal_iff.mpr (by simp)).pow m

/-- The norm coefficients of the restriction to the powers of a single prime `P` are exactly its
canonical local arithmetic factor. -/
@[simp]
theorem normCoeff_supportedPart_singleton (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) :
    normCoeff K (supportedPart f {P}) = localArithmeticFactor f P := by
  have h2 : 2 ≤ Ideal.absNorm P.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm P
  have hpow : ∀ I : (Ideal (𝓞 K))⁰,
      supportedPart f ({P} : Set (HeightOneSpectrum (𝓞 K))) I ≠ 0 →
      ∃ j : ℕ, (I : Ideal (𝓞 K)) = P.asIdeal ^ j := fun _ hI ↦
    Ideal.isPrimeTo_compl_singleton_iff.mp (isPrimeTo_compl_of_supportedPart_apply_ne_zero hI)
  ext n
  rw [normCoeff_eq_sum_normFiber]
  by_cases hn : ∃ k : ℕ, Ideal.absNorm P.asIdeal ^ k = n
  · obtain ⟨k, rfl⟩ := hn
    obtain ⟨C, hCval⟩ : ∃ C : (Ideal (𝓞 K))⁰, (C : Ideal (𝓞 K)) = P.asIdeal ^ k :=
      ⟨⟨_, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k P.ne_bot)⟩, rfl⟩
    have hCmem : C ∈ normFiber K (Ideal.absNorm P.asIdeal ^ k) := by
      rw [mem_normFiber, hCval, map_pow]
    have hother : ∀ I ∈ normFiber K (Ideal.absNorm P.asIdeal ^ k), I ≠ C →
        supportedPart f ({P} : Set (HeightOneSpectrum (𝓞 K))) I = 0 := by
      intro I hI hIC
      by_contra hI0
      obtain ⟨j, hj⟩ := hpow I hI0
      have hjk : Ideal.absNorm P.asIdeal ^ j = Ideal.absNorm P.asIdeal ^ k := by
        rw [← map_pow, ← hj]
        exact (mem_normFiber K).mp hI
      exact hIC (Subtype.ext (by rw [hj, hCval, Nat.pow_right_injective h2 hjk]))
    rw [Finset.sum_eq_single_of_mem C hCmem hother, supportedPart_apply_of_isPrimeTo_compl
      (by rw [hCval]; exact Ideal.isPrimeTo_compl_singleton_iff.mpr ⟨k, rfl⟩),
      localArithmeticFactor_apply_pow]
    exact congrArg f (Subtype.ext hCval)
  · rw [localArithmeticFactor_apply_eq_zero_of_not_exists_pow_eq f P hn]
    refine Finset.sum_eq_zero fun I hI ↦ ?_
    by_contra hI0
    obtain ⟨j, hj⟩ := hpow I hI0
    exact hn ⟨j, by rw [← map_pow, ← hj]; exact (mem_normFiber K).mp hI⟩

/-- **The finite Euler product.** For a multiplicative ideal arithmetic function, the norm
coefficients of its restriction to the ideals supported on a finite set `S` of height-one primes
are the product, in Mathlib's Dirichlet convolution of arithmetic functions, of the canonical
local factors at the primes of `S`. -/
theorem normCoeff_supportedPart (hf : f.IsMultiplicative)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    normCoeff K (supportedPart f (S : Set (HeightOneSpectrum (𝓞 K))))
      = ∏ P ∈ S, localArithmeticFactor f P := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [Finset.coe_empty, supportedPart_empty hf.map_one, normCoeff_delta, Finset.prod_empty]
  | insert P S hPS ih =>
      rw [Finset.coe_insert, supportedPart_insert hf (by simpa using hPS), normCoeff_convolution,
        ih, normCoeff_supportedPart_singleton, Finset.prod_insert hPS, mul_comm]

/-- At a fixed coefficient, restricting to a sufficiently large finite set of prime ideals does
not change the norm coefficient. One may take all prime ideals of norm at most `n`: every prime
divisor of an ideal of norm `n` belongs to that finite set. -/
theorem eventually_normCoeff_supportedPart_eq (f : IdealArithmeticFunction K) (n : ℕ) :
    ∀ᶠ S : Finset (HeightOneSpectrum (𝓞 K)) in Filter.atTop,
      normCoeff K (supportedPart f (S : Set (HeightOneSpectrum (𝓞 K)))) n =
        normCoeff K f n := by
  classical
  let T : Finset (HeightOneSpectrum (𝓞 K)) :=
    (Northcott.finite_le
      (h := fun P : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm P.asIdeal) n).toFinset
  filter_upwards [Filter.eventually_ge_atTop T] with S hTS
  rw [normCoeff_eq_sum_normFiber, normCoeff_eq_sum_normFiber]
  refine Finset.sum_congr rfl fun A hA ↦ supportedPart_apply_of_isPrimeTo_compl ?_
  rw [Ideal.isPrimeTo_iff]
  refine ⟨nonZeroDivisors.coe_ne_zero A, fun P hP hPdvd ↦ hP ?_⟩
  have hnormP : Ideal.absNorm P.asIdeal ≤ n := by
    have hnormdvd : Ideal.absNorm P.asIdeal ∣ Ideal.absNorm (A : Ideal (𝓞 K)) :=
      Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hPdvd)
    have hnormA : Ideal.absNorm (A : Ideal (𝓞 K)) = n := (mem_normFiber K).mp hA
    rw [hnormA] at hnormdvd
    exact Nat.le_of_dvd (hnormA ▸ Ideal.absNorm_pos_of_nonZeroDivisors A) hnormdvd
  exact hTS ((Northcott.finite_le
    (h := fun P : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm P.asIdeal) n).mem_toFinset.mpr hnormP)

/-- **The formal Euler product of norm coefficients.** The norm coefficients of a multiplicative
ideal arithmetic function are Mathlib's `ArithmeticFunction.eulerProduct` of the canonical local
arithmetic factors. This is an equality of arithmetic functions; the analytic infinite product
obtained after evaluating their `LSeries` is the separate absolute-convergence step of Layer 3.3. -/
theorem normCoeff_eq_eulerProduct (hf : f.IsMultiplicative) :
    normCoeff K f = ArithmeticFunction.eulerProduct f.localArithmeticFactor := by
  ext n
  obtain ⟨S, hcoeff, hprod⟩ := ((eventually_normCoeff_supportedPart_eq f n).and
    (tendsTo_eulerProduct_localArithmeticFactor f hf.map_one n)).exists
  rw [normCoeff_supportedPart hf S] at hcoeff
  exact hcoeff.symm.trans hprod

end IdealArithmeticFunction

end TauCeti
