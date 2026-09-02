/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Weight

/-!
# The ideal von Mangoldt function

The von Mangoldt function of a nonzero ideal `A` of the ring of integers of a number field is
`log N(P)` when `A` is a positive power of a prime ideal `P`, and zero otherwise.  This file
packages that function as an `IdealArithmeticFunction`, defines its pointwise product with an
ideal arithmetic function, and proves its divisor sum: summing it over the divisors of `A` gives
`log N(A)`.

## Main definitions

* `TauCeti.IdealArithmeticFunction.vonMangoldt` is the complex-valued ideal von Mangoldt
  function.
* `TauCeti.IdealArithmeticFunction.vonMangoldtTransform` sends `f` to the weighted function
  `A ↦ f(A) Λ(A)`.
* `TauCeti.IdealArithmeticFunction.log` is the ideal logarithm `A ↦ log N(A)`, the ideal analogue
  of Mathlib's `ArithmeticFunction.log`.

## Main results

* `TauCeti.IdealArithmeticFunction.vonMangoldt_apply_prime_pow` computes the value on a positive
  power of a prime ideal.
* `TauCeti.IdealArithmeticFunction.vonMangoldt_ne_zero_iff` says that its support is exactly the
  prime-power ideals.
* `TauCeti.IdealArithmeticFunction.vonMangoldtTransform_ne_zero_iff` identifies the support of
  the transform, and its specialization in `TauCeti.MultiplicativeIdealWeight` describes this as
  the good prime powers for a completely multiplicative weight.
* `TauCeti.IdealArithmeticFunction.sum_vonMangoldt_divisors` and
  `TauCeti.IdealArithmeticFunction.convolution_vonMangoldt_one`: the divisor sum `Λ ⋆ 1 = log N`,
  the ideal analogue of Mathlib's `ArithmeticFunction.vonMangoldt_mul_zeta`.

The definition chooses a prime base from a proof that `A` is a prime power.  Mathlib's
`eq_of_prime_pow_eq`, applied to ideals, identifies that choice with any prime base supplied by a
caller.  The public evaluation theorem therefore removes the choice from every computation.

## Implementation notes

This is the ideal analogue of Mathlib's `ArithmeticFunction.vonMangoldt`.  Here the prime base is
chosen from `IsPrimePow` rather than computed by `Nat.minFac`, its logarithmic weight is
`Ideal.absNorm P` rather than `p`, and the function is complex-valued to match
`IdealArithmeticFunction`.

## Roadmap role

This is the algebraic part of Layer **2.3** of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: the coefficient, its exact prime-power
support, and the divisor sum.  The logarithmic-derivative identity that the divisor sum feeds is
`TauCeti/NumberTheory/ArithmeticDirichletSeries/LogDeriv.lean`; it needs no Euler product, only
the Layer 2.1 convolution and the Layer 1.2 regrouping.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
-/

public section

namespace TauCeti

open NumberField
open scoped nonZeroDivisors NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The absolute norm of a prime ideal is greater than one. -/
theorem one_lt_absNorm_of_prime {P : Ideal (𝓞 K)} (hP : Prime P) :
    1 < Ideal.absNorm P := by
  rw [Nat.one_lt_iff_ne_zero_and_ne_one]
  exact ⟨Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero,
    Ideal.absNorm_eq_one_iff.not.mpr fun htop ↦
      hP.not_isUnit (Ideal.isUnit_iff.mpr htop)⟩

namespace IdealArithmeticFunction

open Classical in
/-- The **ideal von Mangoldt function**.  It takes the value `log N(P)` on every positive power of
a prime ideal `P`, and vanishes on ideals which are not prime powers.

The codomain is `ℂ`, matching `IdealArithmeticFunction`, although every value is real. -/
noncomputable def vonMangoldt : IdealArithmeticFunction K := fun A ↦
  if h : IsPrimePow (A : Ideal (𝓞 K)) then
    (Real.log (Ideal.absNorm h.choose) : ℂ)
  else 0

/-- The ideal von Mangoldt function vanishes at the unit ideal. -/
@[simp]
theorem vonMangoldt_one : (vonMangoldt : IdealArithmeticFunction K) 1 = 0 := by
  rw [vonMangoldt, Submonoid.coe_one, dite_eq_right]
  exact isUnit_one.not_isPrimePow

/-- The value of the ideal von Mangoldt function at a positive power of a prime ideal.  This is the
choice-free characterization of `vonMangoldt` on its support. -/
theorem vonMangoldt_apply_of_eq_prime_pow {A : (Ideal (𝓞 K))⁰} {P : Ideal (𝓞 K)}
    (hP : Prime P) {n : ℕ} (hn : 0 < n) (hpow : P ^ n = (A : Ideal (𝓞 K))) :
    (vonMangoldt : IdealArithmeticFunction K) A = Real.log (Ideal.absNorm P) := by
  have hA : IsPrimePow (A : Ideal (𝓞 K)) := ⟨P, n, hP, hn, hpow⟩
  have hchosen : hA.choose = P := by
    exact eq_of_prime_pow_eq hA.choose_spec.choose_spec.1 hP
      hA.choose_spec.choose_spec.2.1 (hA.choose_spec.choose_spec.2.2.trans hpow.symm)
  rw [vonMangoldt, dite_eq_left hA, hchosen]

/-- The ideal von Mangoldt function at a positive power of a prime nonzero ideal. -/
@[simp]
theorem vonMangoldt_apply_prime_pow {P : (Ideal (𝓞 K))⁰}
    (hP : Prime (P : Ideal (𝓞 K))) {n : ℕ} (hn : 0 < n) :
    (vonMangoldt : IdealArithmeticFunction K) (P ^ n) =
      Real.log (Ideal.absNorm (P : Ideal (𝓞 K))) := by
  apply vonMangoldt_apply_of_eq_prime_pow hP hn
  simp

/-- The ideal von Mangoldt function at a prime ideal. -/
@[simp]
theorem vonMangoldt_apply_prime {P : (Ideal (𝓞 K))⁰}
    (hP : Prime (P : Ideal (𝓞 K))) :
    (vonMangoldt : IdealArithmeticFunction K) P =
      Real.log (Ideal.absNorm (P : Ideal (𝓞 K))) := by
  simpa using vonMangoldt_apply_prime_pow hP (n := 1) zero_lt_one

/-- The ideal von Mangoldt function vanishes away from prime powers. -/
@[simp]
theorem vonMangoldt_eq_zero_of_not_isPrimePow {A : (Ideal (𝓞 K))⁰}
    (hA : ¬ IsPrimePow (A : Ideal (𝓞 K))) :
    (vonMangoldt : IdealArithmeticFunction K) A = 0 := by
  simp [vonMangoldt, hA]

/-- The support of the ideal von Mangoldt function is exactly the set of prime-power ideals. -/
theorem vonMangoldt_ne_zero_iff {A : (Ideal (𝓞 K))⁰} :
    (vonMangoldt : IdealArithmeticFunction K) A ≠ 0 ↔ IsPrimePow (A : Ideal (𝓞 K)) := by
  constructor
  · intro hne
    by_contra hnot
    exact hne (vonMangoldt_eq_zero_of_not_isPrimePow hnot)
  · rintro ⟨P, n, hP, hn, hpow⟩
    rw [vonMangoldt_apply_of_eq_prime_pow hP hn hpow]
    apply Complex.ofReal_ne_zero.mpr
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast Nat.zero_lt_one.trans (one_lt_absNorm_of_prime hP)
    · exact_mod_cast (one_lt_absNorm_of_prime hP).ne'

/-- The ideal von Mangoldt function vanishes exactly away from prime powers. -/
@[simp]
theorem vonMangoldt_eq_zero_iff {A : (Ideal (𝓞 K))⁰} :
    (vonMangoldt : IdealArithmeticFunction K) A = 0 ↔ ¬ IsPrimePow (A : Ideal (𝓞 K)) :=
  by simpa only [not_ne_iff] using not_congr (vonMangoldt_ne_zero_iff (K := K) (A := A))

private theorem exists_ofReal_eq_vonMangoldt (A : (Ideal (𝓞 K))⁰) :
    ∃ r : ℝ, 0 ≤ r ∧ (vonMangoldt : IdealArithmeticFunction K) A = (r : ℂ) := by
  by_cases hA : IsPrimePow (A : Ideal (𝓞 K))
  · obtain ⟨P, n, hP, hn, hpow⟩ := hA
    refine ⟨Real.log (Ideal.absNorm P), Real.log_nonneg ?_,
      vonMangoldt_apply_of_eq_prime_pow hP hn hpow⟩
    exact_mod_cast (one_lt_absNorm_of_prime hP).le
  · exact ⟨0, le_rfl, vonMangoldt_eq_zero_of_not_isPrimePow hA⟩

/-- Every value of the ideal von Mangoldt function is real. -/
theorem vonMangoldt_im {A : (Ideal (𝓞 K))⁰} :
    ((vonMangoldt : IdealArithmeticFunction K) A).im = 0 := by
  obtain ⟨r, -, hr⟩ := exists_ofReal_eq_vonMangoldt A
  rw [hr, Complex.ofReal_im]

/-- The (real) values of the ideal von Mangoldt function are nonnegative. -/
theorem vonMangoldt_re_nonneg {A : (Ideal (𝓞 K))⁰} :
    0 ≤ ((vonMangoldt : IdealArithmeticFunction K) A).re := by
  obtain ⟨r, hr, hvalue⟩ := exists_ofReal_eq_vonMangoldt A
  rw [hvalue, Complex.ofReal_re]
  exact hr

/-- The **von Mangoldt transform** of an ideal arithmetic function `f`: the pointwise product
`A ↦ f(A) Λ(A)`. -/
noncomputable def vonMangoldtTransform (f : IdealArithmeticFunction K) :
    IdealArithmeticFunction K :=
  f * vonMangoldt

/-- Evaluation of the von Mangoldt transform. -/
theorem vonMangoldtTransform_apply (f : IdealArithmeticFunction K)
    (A : (Ideal (𝓞 K))⁰) :
    f.vonMangoldtTransform A = f A * vonMangoldt A := by
  rw [vonMangoldtTransform, Pi.mul_apply]

/-- The von Mangoldt transform on a positive power of a prime ideal. -/
@[simp]
theorem vonMangoldtTransform_apply_prime_pow (f : IdealArithmeticFunction K)
    {P : (Ideal (𝓞 K))⁰} (hP : Prime (P : Ideal (𝓞 K))) {n : ℕ} (hn : 0 < n) :
    f.vonMangoldtTransform (P ^ n) =
      f (P ^ n) * Real.log (Ideal.absNorm (P : Ideal (𝓞 K))) := by
  rw [vonMangoldtTransform_apply, vonMangoldt_apply_prime_pow hP hn]

/-- The support of a von Mangoldt transform is the intersection of the support of the original
function with the prime-power ideals. -/
@[simp]
theorem vonMangoldtTransform_ne_zero_iff (f : IdealArithmeticFunction K)
    {A : (Ideal (𝓞 K))⁰} :
    f.vonMangoldtTransform A ≠ 0 ↔
      IsPrimePow (A : Ideal (𝓞 K)) ∧ f A ≠ 0 := by
  rw [vonMangoldtTransform_apply, mul_ne_zero_iff, vonMangoldt_ne_zero_iff, and_comm]

/-- The transform of the constant-one ideal arithmetic function is the ideal von Mangoldt
function. -/
@[simp]
theorem vonMangoldtTransform_one :
    (1 : IdealArithmeticFunction K).vonMangoldtTransform = vonMangoldt := by
  rw [vonMangoldtTransform, one_mul]

/-! ### The ideal logarithm and the divisor sum -/

/-- The **ideal logarithm**: the ideal arithmetic function whose value at a nonzero ideal `A` is
`log N(A)`.  Like Mathlib's `ArithmeticFunction.log`, the name refers to the bundled function on
the carrier, not to the real logarithm. -/
noncomputable def log : IdealArithmeticFunction K := fun A ↦
  (Real.log (Ideal.absNorm (A : Ideal (𝓞 K))) : ℂ)

/-- Evaluation of the ideal logarithm. -/
@[simp]
theorem log_apply (A : (Ideal (𝓞 K))⁰) :
    (log : IdealArithmeticFunction K) A = Real.log (Ideal.absNorm (A : Ideal (𝓞 K))) :=
  (rfl)

/-- The ideal logarithm vanishes at the unit ideal. -/
theorem log_one : (log : IdealArithmeticFunction K) 1 = 0 := by
  simp [Ideal.one_eq_top]

/-- The ideal logarithm is completely additive. -/
theorem log_mul (A B : (Ideal (𝓞 K))⁰) :
    (log : IdealArithmeticFunction K) (A * B) = log A + log B := by
  have hA : (Ideal.absNorm (A : Ideal (𝓞 K)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_pos_of_nonZeroDivisors A).ne'
  have hB : (Ideal.absNorm (B : Ideal (𝓞 K)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_pos_of_nonZeroDivisors B).ne'
  rw [log_apply, log_apply, log_apply, Submonoid.coe_mul, _root_.map_mul, Nat.cast_mul,
    Real.log_mul hA hB, Complex.ofReal_add]

/-- The values of the ideal logarithm are nonnegative reals. -/
theorem log_re_nonneg (A : (Ideal (𝓞 K))⁰) :
    0 ≤ ((log : IdealArithmeticFunction K) A).re := by
  rw [log_apply, Complex.ofReal_re]
  exact Real.log_nonneg (Nat.one_le_cast.mpr (Ideal.absNorm_pos_of_nonZeroDivisors A))

/-- The values of the ideal logarithm are real. -/
theorem log_im (A : (Ideal (𝓞 K))⁰) : ((log : IdealArithmeticFunction K) A).im = 0 := by
  rw [log_apply, Complex.ofReal_im]

/-- The ideal von Mangoldt function is dominated by the ideal logarithm: its value at `P ^ k` is
`log N(P)`, while the logarithm there is `k log N(P)`. -/
theorem norm_vonMangoldt_le_norm_log (A : (Ideal (𝓞 K))⁰) :
    ‖(vonMangoldt : IdealArithmeticFunction K) A‖ ≤ ‖(log : IdealArithmeticFunction K) A‖ := by
  by_cases hA : IsPrimePow (A : Ideal (𝓞 K))
  · obtain ⟨P, k, hP, hk, hpow⟩ := hA
    have hlog : 0 ≤ Real.log (Ideal.absNorm P) :=
      Real.log_nonneg (mod_cast (one_lt_absNorm_of_prime hP).le)
    rw [vonMangoldt_apply_of_eq_prime_pow hP hk hpow, log_apply, ← hpow, _root_.map_pow,
      Nat.cast_pow, Real.log_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hlog, Real.norm_of_nonneg (by positivity)]
    exact le_mul_of_one_le_left hlog (mod_cast hk)
  · rw [vonMangoldt_eq_zero_of_not_isPrimePow hA, norm_zero]
    exact norm_nonneg _

/-- The logarithm of the absolute norm of a product of nonzero ideals is the sum of the logarithms
of their absolute norms. -/
private theorem log_absNorm_multiset_prod :
    ∀ {t : Multiset (Ideal (𝓞 K))}, t.prod ≠ 0 →
      (Real.log (Ideal.absNorm t.prod) : ℂ) =
        (t.map fun P ↦ (Real.log (Ideal.absNorm P) : ℂ)).sum := by
  intro t
  induction t using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    intro ht
    have ha0 : a ≠ 0 := fun h ↦ ht <| by rw [Multiset.prod_cons, h, zero_mul]
    have hp0 : t.prod ≠ 0 := fun h ↦ ht <| by rw [Multiset.prod_cons, h, mul_zero]
    have ha : Ideal.absNorm a ≠ 0 := fun h ↦
      ha0 ((Ideal.absNorm_eq_zero_iff.mp h).trans Ideal.zero_eq_bot.symm)
    have hp : Ideal.absNorm t.prod ≠ 0 := fun h ↦
      hp0 ((Ideal.absNorm_eq_zero_iff.mp h).trans Ideal.zero_eq_bot.symm)
    rw [Multiset.prod_cons, _root_.map_mul, Multiset.map_cons, Multiset.sum_cons, ← ih hp0,
      Nat.cast_mul, Real.log_mul (mod_cast ha) (mod_cast hp), Complex.ofReal_add]

open Finset UniqueFactorizationMonoid in
/-- **The divisor sum of the ideal von Mangoldt function.** Summing `Λ` over the divisors of a
nonzero ideal `A` gives `log N(A)`.

The prime-power divisors of `A` are exactly the ideals `P ^ k` with `P` a prime factor of `A` and
`1 ≤ k ≤ v_P(A)`, and `Λ (P ^ k) = log N(P)`, so the sum is `∑ v_P(A) log N(P) = log N(A)`. -/
theorem sum_vonMangoldt_divisors (A : (Ideal (𝓞 K))⁰) :
    ∑ B ∈ Ideal.divisors A, (vonMangoldt : IdealArithmeticFunction K) B = log A := by
  classical
  have hA0 : (A : Ideal (𝓞 K)) ≠ 0 := nonZeroDivisors.coe_ne_zero A
  have hnormalize : ∀ I : Ideal (𝓞 K), normalize I = I := fun I ↦
    associated_iff_eq.mp (normalize_associated I)
  set m : Multiset (Ideal (𝓞 K)) := normalizedFactors (A : Ideal (𝓞 K)) with hm
  set S : Finset ((Ideal (𝓞 K))⁰) := {B ∈ Ideal.divisors A | Prime (B : Ideal (𝓞 K))} with hS
  set T : Finset ((Ideal (𝓞 K))⁰) :=
    {B ∈ Ideal.divisors A | IsPrimePow (B : Ideal (𝓞 K))} with hT
  set D : Finset ((_ : (Ideal (𝓞 K))⁰) × ℕ) :=
    S.sigma (fun B ↦ Finset.Icc 1 (m.count (B : Ideal (𝓞 K)))) with hD
  -- The prime divisors of `A` are the elements of `m`.
  have hmemS : ∀ B : (Ideal (𝓞 K))⁰, B ∈ S ↔ (B : Ideal (𝓞 K)) ∈ m := by
    intro B
    rw [hS, Finset.mem_filter, Ideal.mem_divisors]
    refine ⟨fun hB ↦ ?_, fun hB ↦ ⟨dvd_of_mem_normalizedFactors hB,
      prime_of_normalized_factor _ hB⟩⟩
    obtain ⟨P, hP, hassoc⟩ :=
      exists_mem_normalizedFactors_of_dvd hA0 hB.2.irreducible hB.1
    rwa [associated_iff_eq.mp hassoc]
  -- A power of a prime divisor divides `A` exactly up to its multiplicity.
  have hpow : ∀ B ∈ S, ∀ k : ℕ,
      ((B : Ideal (𝓞 K)) ^ k ∣ (A : Ideal (𝓞 K)) ↔ k ≤ m.count (B : Ideal (𝓞 K))) := by
    intro B hB k
    rw [pow_dvd_iff_le_emultiplicity, emultiplicity_eq_count_normalizedFactors
      (Finset.mem_filter.mp hB).2.irreducible hA0, hnormalize, ← hm, Nat.cast_le]
  -- Raising a prime divisor to an admissible exponent is a bijection from `D` onto `T`.
  have hinj : ∀ x ∈ D, ∀ y ∈ D, x.1 ^ x.2 = y.1 ^ y.2 → x = y := by
    rintro ⟨B, k⟩ hBk ⟨C, l⟩ hCl h
    simp only [hD, Finset.mem_sigma, Finset.mem_Icc] at hBk hCl
    obtain ⟨hBS, hk1, -⟩ := hBk
    obtain ⟨hCS, -, -⟩ := hCl
    have hB : Prime (B : Ideal (𝓞 K)) := (Finset.mem_filter.mp hBS).2
    have hC : Prime (C : Ideal (𝓞 K)) := (Finset.mem_filter.mp hCS).2
    have hcoe : (B : Ideal (𝓞 K)) ^ k = (C : Ideal (𝓞 K)) ^ l := by
      simpa using congrArg Subtype.val h
    have hBC : B = C := Subtype.ext (eq_of_prime_pow_eq hB hC (by omega) hcoe)
    subst hBC
    have hkl : k = l := Nat.pow_right_injective (one_lt_absNorm_of_prime hB) <| by
      simpa using congrArg Ideal.absNorm hcoe
    simp [hkl]
  have himage : D.image (fun x ↦ x.1 ^ x.2) = T := by
    ext B
    simp only [hT, hD, Finset.mem_filter, Ideal.mem_divisors, Finset.mem_image, Finset.mem_sigma,
      Finset.mem_Icc]
    constructor
    · rintro ⟨⟨C, k⟩, ⟨hC, hk1, hk2⟩, rfl⟩
      have hCprime : Prime (C : Ideal (𝓞 K)) := (Finset.mem_filter.mp hC).2
      refine ⟨by simpa using (hpow C hC k).mpr hk2, C, k, hCprime, hk1, by simp⟩
    · rintro ⟨hdvd, P, k, hP, hk, hPB⟩
      have hPdvd : P ∣ (A : Ideal (𝓞 K)) :=
        (dvd_pow_self P (by omega)).trans (hPB ▸ hdvd)
      have hPS : (⟨P, mem_nonZeroDivisors_of_ne_zero hP.ne_zero⟩ : (Ideal (𝓞 K))⁰) ∈ S :=
        Finset.mem_filter.mpr ⟨Ideal.mem_divisors.mpr hPdvd, hP⟩
      refine ⟨⟨⟨P, mem_nonZeroDivisors_of_ne_zero hP.ne_zero⟩, k⟩,
        ⟨hPS, hk, (hpow _ hPS k).mp (hPB ▸ hdvd)⟩, Subtype.ext ?_⟩
      simpa using hPB
  have hprod : m.prod = (A : Ideal (𝓞 K)) := associated_iff_eq.mp (prod_normalizedFactors hA0)
  calc ∑ B ∈ Ideal.divisors A, (vonMangoldt : IdealArithmeticFunction K) B
      = ∑ B ∈ T, vonMangoldt B :=
        (Finset.sum_filter_of_ne fun B _ hB ↦
          by_contra fun h ↦ hB (vonMangoldt_eq_zero_of_not_isPrimePow h)).symm
    _ = ∑ x ∈ D, (vonMangoldt : IdealArithmeticFunction K) (x.1 ^ x.2) := by
        rw [← himage, Finset.sum_image hinj]
    _ = ∑ B ∈ S, ∑ k ∈ Finset.Icc 1 (m.count (B : Ideal (𝓞 K))),
          (vonMangoldt : IdealArithmeticFunction K) (B ^ k) :=
        (Finset.sum_sigma' (f := fun (B : (Ideal (𝓞 K))⁰) (k : ℕ) ↦
          (vonMangoldt : IdealArithmeticFunction K) (B ^ k)) _ _).symm
    _ = ∑ B ∈ S, m.count (B : Ideal (𝓞 K)) • (log : IdealArithmeticFunction K) B := by
        refine Finset.sum_congr rfl fun B hB ↦ ?_
        have hB' : Prime (B : Ideal (𝓞 K)) := (Finset.mem_filter.mp hB).2
        rw [Finset.sum_congr rfl fun k hk ↦
          vonMangoldt_apply_prime_pow hB' (by simp only [Finset.mem_Icc] at hk; omega)]
        simp [Nat.card_Icc]
    _ = (m.map fun P ↦ (Real.log (Ideal.absNorm P) : ℂ)).sum := by
        refine (Finset.sum_nbij (i := fun (B : (Ideal (𝓞 K))⁰) ↦ (B : Ideal (𝓞 K)))
          (fun (B : (Ideal (𝓞 K))⁰) hB ↦ Multiset.mem_toFinset.mpr ((hmemS B).mp hB))
          (fun (B : (Ideal (𝓞 K))⁰) _ (C : (Ideal (𝓞 K))⁰) _ h ↦ Subtype.ext h)
          (fun P hP ↦ ?_) fun _ _ ↦ rfl).trans
          (Finset.sum_multiset_map_count m fun P ↦ (Real.log (Ideal.absNorm P) : ℂ)).symm
        have hP' := Multiset.mem_toFinset.mp hP
        exact ⟨⟨P, mem_nonZeroDivisors_of_ne_zero (prime_of_normalized_factor _ hP').ne_zero⟩,
          (hmemS _).mpr hP', rfl⟩
    _ = log A := by rw [log_apply, ← hprod, log_absNorm_multiset_prod (hprod ▸ hA0)]

/-- **The divisor sum of the ideal von Mangoldt function, in convolution form.** Convolving `Λ`
with the everywhere-one function on nonzero ideals gives the ideal logarithm.  This is the ideal
analogue of Mathlib's `ArithmeticFunction.vonMangoldt_mul_zeta`. -/
@[simp]
theorem convolution_vonMangoldt_one :
    convolution (vonMangoldt : IdealArithmeticFunction K) 1 = log := by
  funext A
  simpa using (Ideal.sum_divisorsAntidiagonal_fst A
    (vonMangoldt : IdealArithmeticFunction K)).trans (sum_vonMangoldt_divisors A)

end IdealArithmeticFunction

namespace MultiplicativeIdealWeight

/-- The von Mangoldt transform of a completely multiplicative weight on a positive power of a
prime ideal. -/
theorem vonMangoldtTransform_apply_prime_pow (χ : MultiplicativeIdealWeight K)
    {P : (Ideal (𝓞 K))⁰} (hP : Prime (P : Ideal (𝓞 K))) {n : ℕ} (hn : 0 < n) :
    χ.toIdealArithmeticFunction.vonMangoldtTransform (P ^ n) =
      χ P ^ n * Real.log (Ideal.absNorm (P : Ideal (𝓞 K))) := by
  rw [IdealArithmeticFunction.vonMangoldtTransform_apply_prime_pow _ hP hn,
    toIdealArithmeticFunction_apply]
  rw [SubmonoidClass.coe_pow, map_pow]

/-- The support of the von Mangoldt transform of a completely multiplicative weight consists
exactly of the prime powers on which the weight is good. -/
@[simp 1100]
theorem vonMangoldtTransform_ne_zero_iff (χ : MultiplicativeIdealWeight K)
    {A : (Ideal (𝓞 K))⁰} :
    χ.toIdealArithmeticFunction.vonMangoldtTransform A ≠ 0 ↔
      IsPrimePow (A : Ideal (𝓞 K)) ∧ χ.IsGood (A : Ideal (𝓞 K)) := by
  rw [IdealArithmeticFunction.vonMangoldtTransform_ne_zero_iff,
    toIdealArithmeticFunction_apply, χ.apply_ne_zero_iff_isGood]

end MultiplicativeIdealWeight

end TauCeti
