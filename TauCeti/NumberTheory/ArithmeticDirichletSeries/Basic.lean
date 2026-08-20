/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Arithmetic functions and multiplicative weights on the ideals of a number field

An arithmetic Dirichlet series attached to a number field `K` is built from a complex-valued
function on the integral ideals of `𝓞 K`. This file fixes the carriers that every later
construction — norm regrouping, ideal convolution, Euler products, Dirichlet density — is written
against, and separates them from each other.

The **general carrier** is a function on the *nonzero* ideals. Excluding `⊥` is not cosmetic: in
the multiplicative monoid of ideals every `J` satisfies `⊥ * J = ⊥`, so a divisor sum over the
factorizations of `⊥` is an infinite sum. The nonzero ideals are exactly the non-zero-divisors of
that monoid, which is Mathlib's `(Ideal (𝓞 K))⁰`, so the carrier is a submonoid and the
convolution to come has a domain closed under multiplication.

`zeroExtend` puts the excluded value back, always as `0`, and `restrict` restricts a function on
all ideals to the nonzero ideals. The two operations are inverse precisely on functions vanishing
at the zero ideal. The resulting existence-and-uniqueness API is recorded without exposing the
implementation of `zeroExtend`: `TauCeti.IdealArithmeticFunction.existsUnique_zeroExtend_eq`
characterizes its image, while `TauCeti.IdealArithmeticFunction.zeroExtend_injective` says that
no information is lost.

The **multiplicative carriers** are the completely multiplicative degree-one weights: an ideal
weight is a `MonoidWithZeroHom` out of the ideals of `𝓞 K`, together with a finite set of *bad*
height-one primes on which it is required to vanish. That set is data and not the exact zero
locus: `restrict` enlarges it, which is how an imprimitive weight records the local factors an
Euler product must omit. `UnitaryIdealWeight` adds the condition that
its values at the remaining height-one primes have modulus one, which is what a finite-order Hecke
character satisfies, and complete multiplicativity then propagates that to every ideal prime to
the bad set (`UnitaryIdealWeight.norm_apply_eq_one_of_isGood`, proved by induction over a
factorization into primes).

Both carriers are deliberately narrow, and three rejection theorems record where their boundaries
lie. The everywhere-one function on *all* ideals is not the zero extension of any arithmetic
function and is not an ideal weight, because `map_zero` forces the value `0` at `⊥`
(`IdealArithmeticFunction.not_exists_zeroExtend_eq_one`,
`MultiplicativeIdealWeight.not_exists_apply_eq_one`); the ideal Möbius function is not an ideal
weight, because complete multiplicativity forces `χ 𝔭 = 0` as soon as `χ (𝔭 ^ 2) = 0`
(`MultiplicativeIdealWeight.not_exists_apply_eq_neg_one_and_apply_sq_eq_zero`); and when
`z.re ≠ 0`, the twist `χ · N⁻ᶻ` has non-unit modulus at every good ideal of norm greater
than one, since its modulus there is `N(I) ^ (-Re z)`
(`UnitaryIdealWeight.norm_apply_normTwist_ne_one`). Accordingly the arbitrary norm-twist
construction lands in `MultiplicativeIdealWeight`, while `imaginaryNormTwist` stays inside
`UnitaryIdealWeight`.

The carriers are stated for the ring of integers of a number field rather than for a general
Dedekind domain, because the absolute norm that the twists and all of Layer 1 use is Mathlib's
`Ideal.absNorm`, which is the index of the ideal in a finite-rank free `ℤ`-module.

## Main definitions

* `TauCeti.IdealArithmeticFunction`: a complex-valued function on `(Ideal (𝓞 K))⁰`.
* `TauCeti.IdealArithmeticFunction.zeroExtend`: its canonical extension by `0` at `⊥`.
* `TauCeti.IdealArithmeticFunction.restrict`: restricts a function on all ideals to nonzero ideals.
* `TauCeti.MultiplicativeIdealWeight`: a completely multiplicative ideal weight with a finite set
  of bad height-one primes, together with `one`, `conj`, `pointwiseMul`, `restrict` and
  `normTwist`.
* `TauCeti.MultiplicativeIdealWeight.IsGood`: an ideal is *good* when it is nonzero and divisible
  by no bad prime.
* `TauCeti.UnitaryIdealWeight`: the ideal weights of modulus one away from the bad primes,
  together with `one`, `conj`, `pointwiseMul`, `restrict` and `imaginaryNormTwist`.

## Main results

* `TauCeti.IdealArithmeticFunction.existsUnique_zeroExtend_eq`: a function on all ideals that
  vanishes at `⊥` is the zero extension of a unique ideal arithmetic function.
* `TauCeti.UnitaryIdealWeight.norm_apply_eq_one_of_isGood`: a unitary weight has modulus one at
  every good ideal, not only at the good height-one primes.
* `TauCeti.UnitaryIdealWeight.norm_apply_normTwist_of_isGood`: the modulus of an arbitrary norm
  twist of a unitary weight at a good ideal is `N(I) ^ (-Re z)`.
* `TauCeti.IdealArithmeticFunction.not_exists_zeroExtend_eq_one`,
  `TauCeti.MultiplicativeIdealWeight.not_exists_apply_eq_one`,
  `TauCeti.MultiplicativeIdealWeight.not_exists_apply_eq_neg_one_and_apply_sq_eq_zero` and
  `TauCeti.UnitaryIdealWeight.norm_apply_normTwist_ne_one`: the rejection tests described above.

## Roadmap role

This is Layer **0** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, items 0.1 to 0.4, whose
export contract names `IdealArithmeticFunction`, `zeroExtend`, `MultiplicativeIdealWeight` and
`UnitaryIdealWeight`. Layer 1 sums an `IdealArithmeticFunction` over the ideals of a fixed
absolute norm to reach Mathlib's `LSeries`, and Layer 2 defines the convolution whose divisor sums
are the reason the carrier omits `⊥`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

public section

namespace TauCeti

open NumberField IsDedekindDomain
open scoped nonZeroDivisors NumberField

section

variable (K : Type*) [Field K]

/-- An **ideal arithmetic function** over a field `K`: a complex-valued function on the nonzero
ideals of `𝓞 K`.

The domain is `(Ideal (𝓞 K))⁰`, Mathlib's non-zero-divisor submonoid. Since the ring of integers is
a domain, its elements are exactly the ideals different from `⊥`. For number fields, keeping `⊥`
out of the carrier ensures that later divisor sums use only the nonzero-ideal factorization
theory. -/
abbrev IdealArithmeticFunction := (Ideal (𝓞 K))⁰ → ℂ

namespace IdealArithmeticFunction

variable {K}

/-- Extend an ideal arithmetic function to all integral ideals by assigning zero to `⊥`.

Use `zeroExtend_bot` and `zeroExtend_coe` to simplify its two characteristic cases, rather than
unfolding this definition. -/
noncomputable def zeroExtend (f : IdealArithmeticFunction K) : Ideal (𝓞 K) → ℂ := fun I =>
  Function.extend Subtype.val f 0 I

/-- Restrict a function on all integral ideals to the nonzero ideals. -/
def restrict (g : Ideal (𝓞 K) → ℂ) : IdealArithmeticFunction K := fun I => g I

@[simp]
theorem restrict_apply (g : Ideal (𝓞 K) → ℂ) (I : (Ideal (𝓞 K))⁰) : restrict g I = g I := by
  simp [restrict]

/-- The zero extension is zero at the zero ideal. -/
@[simp]
theorem zeroExtend_bot (f : IdealArithmeticFunction K) : f.zeroExtend ⊥ = 0 := by
  simp [zeroExtend]

/-- Away from `⊥`, the zero extension is the original ideal arithmetic function. -/
@[simp]
theorem zeroExtend_of_ne (f : IdealArithmeticFunction K) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    f.zeroExtend I = f ⟨I, by simpa using hI⟩ := by
  rw [zeroExtend]
  exact Function.extend_val_apply (by simpa using hI)

/-- The zero extension agrees with the original function on every nonzero ideal. -/
@[simp]
theorem zeroExtend_coe (f : IdealArithmeticFunction K) (I : (Ideal (𝓞 K))⁰) :
    f.zeroExtend I = f I := by
  exact Subtype.val_injective.extend_apply f 0 I

/-- Restricting a zero extension recovers the original ideal arithmetic function. -/
@[simp]
theorem restrict_zeroExtend (f : IdealArithmeticFunction K) : restrict f.zeroExtend = f := by
  funext I
  simp

/-- Extending a restriction recovers a function on all ideals exactly when it vanishes at `⊥`. -/
@[simp]
theorem zeroExtend_restrict {g : Ideal (𝓞 K) → ℂ} (hg : g ⊥ = 0) :
    (restrict g).zeroExtend = g := by
  funext I
  by_cases hI : I = ⊥
  · simpa [hI] using hg.symm
  · simp [hI]

/-- A function on all ideals is a zero extension if and only if it vanishes at `⊥`. -/
theorem exists_zeroExtend_eq_iff {g : Ideal (𝓞 K) → ℂ} :
    (∃ f : IdealArithmeticFunction K, f.zeroExtend = g) ↔ g ⊥ = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    exact zeroExtend_bot f
  · intro hg
    exact ⟨restrict g, zeroExtend_restrict hg⟩

/-- Zero extension is injective: its values on nonzero ideals retain the entire function. -/
theorem zeroExtend_injective :
    Function.Injective (zeroExtend : IdealArithmeticFunction K → Ideal (𝓞 K) → ℂ) :=
  Function.extend_injective
    (f := (Subtype.val : (Ideal (𝓞 K))⁰ → Ideal (𝓞 K))) Subtype.val_injective
      (0 : Ideal (𝓞 K) → ℂ)

/-- Two zero extensions agree exactly when the underlying ideal arithmetic functions agree. -/
@[simp]
theorem zeroExtend_eq_iff {f g : IdealArithmeticFunction K} :
    f.zeroExtend = g.zeroExtend ↔ f = g := zeroExtend_injective.eq_iff

/-- A function on all ideals that vanishes at `⊥` is the zero extension of a unique ideal
arithmetic function. -/
theorem existsUnique_zeroExtend_eq {g : Ideal (𝓞 K) → ℂ} (hg : g ⊥ = 0) :
    ∃! f : IdealArithmeticFunction K, f.zeroExtend = g := by
  refine ⟨restrict g, zeroExtend_restrict hg, fun f hf => ?_⟩
  exact zeroExtend_injective (hf.trans (zeroExtend_restrict hg).symm)

/-- The zero extension is zero exactly at `⊥` when the original function has no zero values. -/
theorem zeroExtend_eq_zero_iff (f : IdealArithmeticFunction K)
    (hf : ∀ I, f I ≠ 0) {I : Ideal (𝓞 K)} : f.zeroExtend I = 0 ↔ I = ⊥ := by
  constructor
  · intro h
    by_contra hI
    exact hf ⟨I, by simpa using hI⟩ ((zeroExtend_of_ne f hI).symm.trans h)
  · rintro rfl
    exact zeroExtend_bot f

/-- If the original function does not vanish, its zero extension is nonzero at every nonzero
ideal. -/
theorem zeroExtend_ne_zero (f : IdealArithmeticFunction K) (hf : ∀ I, f I ≠ 0)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : f.zeroExtend I ≠ 0 := by
  intro hzero
  exact hI ((zeroExtend_eq_zero_iff f hf).mp hzero)

/-! ## Compatibility with pointwise operations -/

/-- Zero extension preserves the pointwise zero function. -/
@[simp]
theorem zeroExtend_zero : zeroExtend (0 : IdealArithmeticFunction K) = 0 := by
  funext I
  by_cases hI : I = ⊥ <;> simp [hI]

/-- Zero extension preserves pointwise addition. -/
@[simp]
theorem zeroExtend_add (f g : IdealArithmeticFunction K) :
    zeroExtend (f + g) = f.zeroExtend + g.zeroExtend := by
  funext I
  by_cases hI : I = ⊥ <;> simp [hI]

/-- Zero extension preserves pointwise negation. -/
@[simp]
theorem zeroExtend_neg (f : IdealArithmeticFunction K) : zeroExtend (-f) = -f.zeroExtend := by
  funext I
  by_cases hI : I = ⊥ <;> simp [hI]

/-- Zero extension preserves pointwise subtraction. -/
@[simp]
theorem zeroExtend_sub (f g : IdealArithmeticFunction K) :
    zeroExtend (f - g) = f.zeroExtend - g.zeroExtend := by
  funext I
  by_cases hI : I = ⊥ <;> simp [hI]

/-- Zero extension preserves pointwise complex scalar multiplication. -/
@[simp]
theorem zeroExtend_smul (c : ℂ) (f : IdealArithmeticFunction K) :
    zeroExtend (c • f) = c • f.zeroExtend := by
  funext I
  by_cases hI : I = ⊥ <;> simp [hI]

/-- Zero extension preserves pointwise multiplication. -/
@[simp]
theorem zeroExtend_mul (f g : IdealArithmeticFunction K) :
    zeroExtend (f * g) = f.zeroExtend * g.zeroExtend := by
  funext I
  by_cases hI : I = ⊥ <;> simp [hI]

/-- The everywhere-one function on all ideals is not the zero extension of an ideal arithmetic
function, since its value at `⊥` is one rather than zero. This is the roadmap's zero-ideal
rejection test. -/
theorem not_exists_zeroExtend_eq_one :
    ¬ ∃ f : IdealArithmeticFunction K, f.zeroExtend = (1 : Ideal (𝓞 K) → ℂ) := by
  rw [exists_zeroExtend_eq_iff]
  exact one_ne_zero

end IdealArithmeticFunction

/-! ### Completely multiplicative ideal weights -/

/-- A **multiplicative ideal weight** on a number field `K`: a completely multiplicative
complex-valued function on the ideals of `𝓞 K`, packaged as a `MonoidWithZeroHom` so that the
value at `⊥` is `0` and the value at `⊤` is `1`, together with a finite set of *bad* height-one
primes on which the weight is required to vanish.

This is a degree-one carrier: the value at a prime power is determined by the value at the prime.
It is therefore not a carrier for the ideal Möbius function, nor for a coefficient system whose
local factors at a prime are independent polynomial data. -/
structure MultiplicativeIdealWeight extends Ideal (𝓞 K) →*₀ ℂ where
  /-- The finite set of primes at which the weight is required to vanish. -/
  bad : Set (HeightOneSpectrum (𝓞 K))
  /-- The bad set is finite. -/
  bad_finite : bad.Finite
  /-- The weight vanishes at every bad prime. -/
  map_eq_zero_of_mem_bad : ∀ 𝔭 ∈ bad, toMonoidWithZeroHom 𝔭.asIdeal = 0

namespace MultiplicativeIdealWeight

/-- A multiplicative ideal weight is a function on the ideals of `𝓞 K`. -/
instance : CoeFun (MultiplicativeIdealWeight K) fun _ ↦ Ideal (𝓞 K) → ℂ :=
  ⟨fun χ ↦ χ.toMonoidWithZeroHom⟩

variable {K} (χ : MultiplicativeIdealWeight K)

@[simp]
theorem apply_bot : χ ⊥ = 0 := by
  rw [← Ideal.zero_eq_bot]; exact map_zero _

@[simp]
theorem apply_top : χ ⊤ = 1 := by
  rw [← Ideal.one_eq_top]; exact map_one _

@[simp]
theorem apply_mul (I J : Ideal (𝓞 K)) : χ (I * J) = χ I * χ J := map_mul _ _ _

@[simp]
theorem apply_pow (I : Ideal (𝓞 K)) (n : ℕ) : χ (I ^ n) = χ I ^ n := map_pow _ _ _

theorem apply_eq_zero_of_mem_bad {𝔭 : HeightOneSpectrum (𝓞 K)} (h𝔭 : 𝔭 ∈ χ.bad) :
    χ 𝔭.asIdeal = 0 :=
  χ.map_eq_zero_of_mem_bad 𝔭 h𝔭

/-- Two multiplicative ideal weights agreeing as functions and having the same bad set are equal.
Agreement as functions alone is not enough: the bad set is data, and a weight is only *required*
to vanish on it, so a prime where the weight happens to vanish need not be declared bad. -/
@[ext]
theorem ext {χ ψ : MultiplicativeIdealWeight K} (hfun : ∀ I, χ I = ψ I) (hbad : χ.bad = ψ.bad) :
    χ = ψ := by
  obtain ⟨f, b, hbfin, hbzero⟩ := χ
  obtain ⟨g, c, hcfin, hczero⟩ := ψ
  obtain rfl : f = g := DFunLike.ext f g hfun
  obtain rfl : b = c := hbad
  rfl

/-- An ideal is **good** for a weight when it is nonzero and divisible by no bad prime. The
nonvanishing conditions that Euler products and unitarity impose are stated at good ideals; the
explicit nonzero condition is needed even when the bad set is empty. -/
def IsGood (I : Ideal (𝓞 K)) : Prop :=
  I ≠ ⊥ ∧ ∀ 𝔭 ∈ χ.bad, ¬ 𝔭.asIdeal ∣ I

variable {χ}

@[simp]
theorem isGood_iff {I : Ideal (𝓞 K)} : χ.IsGood I ↔ I ≠ ⊥ ∧ ∀ 𝔭 ∈ χ.bad, ¬ 𝔭.asIdeal ∣ I :=
  Iff.rfl

theorem IsGood.ne_bot {I : Ideal (𝓞 K)} (hI : χ.IsGood I) : I ≠ ⊥ := hI.1

theorem IsGood.not_dvd {I : Ideal (𝓞 K)} (hI : χ.IsGood I) {𝔭 : HeightOneSpectrum (𝓞 K)}
    (h𝔭 : 𝔭 ∈ χ.bad) : ¬ 𝔭.asIdeal ∣ I :=
  hI.2 𝔭 h𝔭

/-- A divisor of a good ideal is good. -/
theorem IsGood.of_dvd {I J : Ideal (𝓞 K)} (hI : χ.IsGood I) (hJ : J ∣ I) : χ.IsGood J := by
  refine ⟨fun hb ↦ hI.1 ?_, fun 𝔭 h𝔭 hd ↦ hI.2 𝔭 h𝔭 (hd.trans hJ)⟩
  rw [hb, ← Ideal.zero_eq_bot] at hJ
  rw [← Ideal.zero_eq_bot]
  exact zero_dvd_iff.1 hJ

variable (χ)

theorem isGood_top : χ.IsGood ⊤ :=
  ⟨top_ne_bot, fun 𝔭 _ hd ↦ 𝔭.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd hd))⟩

/-- A weight vanishing at a power of an ideal already vanishes at the ideal: complete
multiplicativity leaves no room for independent prime-power data. -/
theorem apply_eq_zero_of_apply_pow_eq_zero {I : Ideal (𝓞 K)} {n : ℕ} (hn : n ≠ 0)
    (h : χ (I ^ n) = 0) : χ I = 0 :=
  (pow_eq_zero_iff hn).1 (by rwa [apply_pow] at h)

variable (K) in
/-- **Zero-ideal rejection test.** The function equal to `1` on every ideal is not a multiplicative
ideal weight: `map_zero` forces the value `0` at `⊥`. -/
theorem not_exists_apply_eq_one :
    ¬ ∃ χ : MultiplicativeIdealWeight K, ∀ I : Ideal (𝓞 K), χ I = 1 := by
  rintro ⟨χ, hχ⟩
  exact zero_ne_one (χ.apply_bot.symm.trans (hχ ⊥))

/-- **Möbius rejection test.** No multiplicative ideal weight takes the values of the ideal Möbius
function at a prime and at its square, since complete multiplicativity forces the value at the
prime to vanish along with the value at the square. -/
theorem not_exists_apply_eq_neg_one_and_apply_sq_eq_zero (𝔭 : HeightOneSpectrum (𝓞 K)) :
    ¬ ∃ χ : MultiplicativeIdealWeight K, χ 𝔭.asIdeal = -1 ∧ χ (𝔭.asIdeal ^ 2) = 0 := by
  rintro ⟨χ, h₁, h₂⟩
  rw [χ.apply_eq_zero_of_apply_pow_eq_zero two_ne_zero h₂] at h₁
  norm_num at h₁

/-! #### Constructions of multiplicative ideal weights -/

variable (K)

/-- The **trivial ideal weight**, equal to `1` at every nonzero ideal and to `0` at `⊥`, with empty
bad set. It is the weight whose Dirichlet series is the Dedekind zeta function of `K`. -/
noncomputable def one : MultiplicativeIdealWeight K where
  toFun I := if I = ⊥ then 0 else 1
  map_zero' := by simp
  map_one' := by simp [Ideal.one_eq_top]
  map_mul' I J := by
    rcases eq_or_ne I ⊥ with rfl | hI
    · simp
    rcases eq_or_ne J ⊥ with rfl | hJ
    · simp
    simp [hI, hJ]
  bad := ∅
  bad_finite := Set.finite_empty
  map_eq_zero_of_mem_bad 𝔭 h𝔭 := absurd h𝔭 (Set.notMem_empty 𝔭)

/-- The trivial ideal weight is the indicator of the nonzero ideals. -/
@[simp]
theorem one_apply (I : Ideal (𝓞 K)) : one K I = if I = ⊥ then 0 else 1 := (rfl)

/-- The trivial ideal weight has no bad prime. -/
@[simp]
theorem bad_one : (one K).bad = ∅ := (rfl)

variable {K} (χ : MultiplicativeIdealWeight K)

/-- The **complex conjugate** of a multiplicative ideal weight, with the same bad set. -/
noncomputable def conj : MultiplicativeIdealWeight K where
  toFun I := starRingEnd ℂ (χ I)
  map_zero' := by simp
  map_one' := by simp
  map_mul' I J := by simp
  bad := χ.bad
  bad_finite := χ.bad_finite
  map_eq_zero_of_mem_bad 𝔭 h𝔭 := by simp [χ.apply_eq_zero_of_mem_bad h𝔭]

@[simp]
theorem conj_apply (I : Ideal (𝓞 K)) : χ.conj I = starRingEnd ℂ (χ I) := (rfl)

@[simp]
theorem bad_conj : χ.conj.bad = χ.bad := (rfl)

/-- The **pointwise product** of two multiplicative ideal weights, whose bad set is the union of
the two bad sets. This is pointwise multiplication of coefficients, and not the Dirichlet
convolution of the associated arithmetic functions. -/
noncomputable def pointwiseMul (ψ : MultiplicativeIdealWeight K) : MultiplicativeIdealWeight K where
  toFun I := χ I * ψ I
  map_zero' := by simp
  map_one' := by simp
  map_mul' I J := by simp only [apply_mul]; ring
  bad := χ.bad ∪ ψ.bad
  bad_finite := χ.bad_finite.union ψ.bad_finite
  map_eq_zero_of_mem_bad 𝔭 h𝔭 := by
    rcases h𝔭 with h | h
    · simp [χ.apply_eq_zero_of_mem_bad h]
    · simp [ψ.apply_eq_zero_of_mem_bad h]

@[simp]
theorem pointwiseMul_apply (ψ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 K)) :
    χ.pointwiseMul ψ I = χ I * ψ I := (rfl)

@[simp]
theorem bad_pointwiseMul (ψ : MultiplicativeIdealWeight K) :
    (χ.pointwiseMul ψ).bad = χ.bad ∪ ψ.bad := (rfl)

/-- The arithmetic function on the nonzero ideals underlying a multiplicative ideal weight. -/
def toIdealArithmeticFunction : IdealArithmeticFunction K := fun I ↦ χ (I : Ideal (𝓞 K))

@[simp]
theorem toIdealArithmeticFunction_apply (I : (Ideal (𝓞 K))⁰) :
    χ.toIdealArithmeticFunction I = χ (I : Ideal (𝓞 K)) := (rfl)

end MultiplicativeIdealWeight

end

section

variable (K : Type*) [Field K] [NumberField K]

/-! #### Restriction away from a finite set of primes -/

namespace MultiplicativeIdealWeight

variable {K} (χ : MultiplicativeIdealWeight K)

open Classical in
/-- The **restriction** of a multiplicative ideal weight away from a finite set `S` of height-one
primes: the value is unchanged at the ideals prime to `S` and is `0` at the ideals divisible by
some prime of `S`, and the bad set grows to `χ.bad ∪ S`. This is the operation producing the
imprimitive versions of a weight, whose Euler products omit the local factors at `S`. -/
noncomputable def restrict (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    MultiplicativeIdealWeight K where
  toFun I := if ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I then χ I else 0
  map_zero' := by split_ifs <;> simp
  map_one' :=
    (ite_eq_left fun 𝔭 _ hd ↦
      𝔭.isPrime.ne_top (Ideal.isUnit_iff.1 (isUnit_of_dvd_one hd))).trans (map_one _)
  map_mul' I J := by
    have key : (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I * J) ↔
        (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I) ∧ ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ J := by
      refine ⟨fun h ↦ ⟨fun 𝔭 h𝔭 hd ↦ h 𝔭 h𝔭 (hd.mul_right J),
        fun 𝔭 h𝔭 hd ↦ h 𝔭 h𝔭 (hd.mul_left I)⟩, ?_⟩
      rintro ⟨h₁, h₂⟩ 𝔭 h𝔭 hd
      exact (𝔭.prime.2.2 I J hd).elim (h₁ 𝔭 h𝔭) (h₂ 𝔭 h𝔭)
    by_cases hI : ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I
    · by_cases hJ : ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ J
      · rw [ite_eq_left (key.2 ⟨hI, hJ⟩), ite_eq_left hI, ite_eq_left hJ, apply_mul]
      · rw [ite_eq_right fun h ↦ hJ (key.1 h).2, ite_eq_right hJ, mul_zero]
    · rw [ite_eq_right fun h ↦ hI (key.1 h).1, ite_eq_right hI, zero_mul]
  bad := χ.bad ∪ S
  bad_finite := χ.bad_finite.union hS
  map_eq_zero_of_mem_bad 𝔭 h𝔭 := by
    rcases h𝔭 with h | h
    · by_cases hc : ∀ 𝔮 ∈ S, ¬ 𝔮.asIdeal ∣ 𝔭.asIdeal
      · exact (ite_eq_left hc).trans (χ.apply_eq_zero_of_mem_bad h)
      · exact ite_eq_right hc
    · exact ite_eq_right fun hcon ↦ hcon 𝔭 h dvd_rfl

open Classical in
@[simp]
theorem restrict_apply (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) (I : Ideal (𝓞 K)) :
    χ.restrict S hS I = if ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I then χ I else 0 := (rfl)

@[simp]
theorem bad_restrict (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    (χ.restrict S hS).bad = χ.bad ∪ S := (rfl)

/-- The restriction away from `S` agrees with the original weight at the ideals that are good for
it, since those are prime to `S`. -/
theorem restrict_apply_of_isGood {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite)
    {I : Ideal (𝓞 K)} (hI : (χ.restrict S hS).IsGood I) : χ.restrict S hS I = χ I := by
  rw [restrict_apply]
  exact ite_eq_left fun 𝔭 h𝔭 ↦ hI.not_dvd (Or.inr h𝔭)

/-! #### The norm twist -/

/-- The **norm twist** `I ↦ χ I * N(I) ^ (-z)` of a multiplicative ideal weight by an arbitrary
complex number, with the same bad set. Its codomain is the general multiplicative carrier. When
`Re z ≠ 0`, `TauCeti.UnitaryIdealWeight.norm_apply_normTwist_ne_one` shows that a twist of a
unitary weight has non-unit modulus at every good ideal of norm greater than one. -/
noncomputable def normTwist (z : ℂ) : MultiplicativeIdealWeight K where
  toFun I := χ I * (Ideal.absNorm I : ℂ) ^ (-z)
  map_zero' := by simp
  map_one' := by simp
  map_mul' I J := by
    rw [apply_mul, map_mul Ideal.absNorm, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  bad := χ.bad
  bad_finite := χ.bad_finite
  map_eq_zero_of_mem_bad 𝔭 h𝔭 := by simp [χ.apply_eq_zero_of_mem_bad h𝔭]

@[simp]
theorem normTwist_apply (z : ℂ) (I : Ideal (𝓞 K)) :
    χ.normTwist z I = χ I * (Ideal.absNorm I : ℂ) ^ (-z) := (rfl)

@[simp]
theorem bad_normTwist (z : ℂ) : (χ.normTwist z).bad = χ.bad := (rfl)

end MultiplicativeIdealWeight

end

section

variable (K : Type*) [Field K] [NumberField K]

/-! ### Unitary ideal weights -/

/-- A **unitary ideal weight**: a multiplicative ideal weight whose values at the height-one primes
outside the bad set have modulus one. A finite-order Hecke character, viewed as a weight on ideals,
lands here; purely imaginary norm twists preserve this carrier. -/
structure UnitaryIdealWeight extends MultiplicativeIdealWeight K where
  /-- Away from the bad primes the weight has modulus one. -/
  norm_apply_eq_one : ∀ 𝔭 ∉ bad, ‖toMonoidWithZeroHom 𝔭.asIdeal‖ = 1

namespace UnitaryIdealWeight

/-- A unitary ideal weight is a function on the ideals of `𝓞 K`, through the underlying
multiplicative ideal weight. -/
instance : CoeFun (UnitaryIdealWeight K) fun _ ↦ Ideal (𝓞 K) → ℂ :=
  ⟨fun χ ↦ χ.toMultiplicativeIdealWeight⟩

variable {K} (χ : UnitaryIdealWeight K)

omit [NumberField K] in
/-- Two unitary ideal weights with the same underlying multiplicative ideal weight are equal. -/
@[ext]
theorem ext {χ ψ : UnitaryIdealWeight K}
    (h : χ.toMultiplicativeIdealWeight = ψ.toMultiplicativeIdealWeight) : χ = ψ := by
  obtain ⟨χ', hχ⟩ := χ
  obtain ⟨ψ', hψ⟩ := ψ
  obtain rfl : χ' = ψ' := h
  rfl

/-- **A unitary weight has modulus one at every good ideal**, not merely at the good height-one
primes. Complete multiplicativity turns the condition at the primes into the condition at every
ideal prime to the bad set, by induction over a factorization into primes. -/
theorem norm_apply_eq_one_of_isGood {I : Ideal (𝓞 K)}
    (hI : χ.toMultiplicativeIdealWeight.IsGood I) : ‖χ I‖ = 1 := by
  revert hI
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun h ↦ absurd Ideal.zero_eq_bot h.ne_bot
  | h₂ I hI => exact fun _ ↦ by rw [Ideal.isUnit_iff.1 hI]; simp
  | h₃ J p hJ hp ih =>
      intro hgood
      have hp' : p ≠ ⊥ := by rw [← Ideal.zero_eq_bot]; exact hp.ne_zero
      have hJ' : J ≠ ⊥ := by rw [← Ideal.zero_eq_bot]; exact hJ
      have hmem : (⟨p, Ideal.isPrime_of_prime hp, hp'⟩ : HeightOneSpectrum (𝓞 K)) ∉
          χ.toMultiplicativeIdealWeight.bad := fun h ↦ hgood.not_dvd h (Dvd.intro J rfl)
      have hgoodJ : χ.toMultiplicativeIdealWeight.IsGood J :=
        ⟨hJ', fun 𝔮 h𝔮 hd ↦ hgood.not_dvd h𝔮 (hd.mul_left p)⟩
      rw [MultiplicativeIdealWeight.apply_mul, norm_mul, ih hgoodJ, mul_one]
      exact χ.norm_apply_eq_one _ hmem

/-- A unitary weight does not vanish at a good ideal. -/
theorem apply_ne_zero_of_isGood {I : Ideal (𝓞 K)}
    (hI : χ.toMultiplicativeIdealWeight.IsGood I) : χ I ≠ 0 := by
  intro h
  simpa [h] using χ.norm_apply_eq_one_of_isGood hI

variable (K)

/-- The **trivial unitary ideal weight**, the indicator of the nonzero ideals. -/
noncomputable def one : UnitaryIdealWeight K where
  toMultiplicativeIdealWeight := MultiplicativeIdealWeight.one K
  norm_apply_eq_one 𝔭 _ := by simp [𝔭.ne_bot]

omit [NumberField K] in
@[simp]
theorem toMultiplicativeIdealWeight_one :
    (one K).toMultiplicativeIdealWeight = MultiplicativeIdealWeight.one K := (rfl)

variable {K}

/-- The **complex conjugate** of a unitary ideal weight. -/
noncomputable def conj : UnitaryIdealWeight K where
  toMultiplicativeIdealWeight := χ.toMultiplicativeIdealWeight.conj
  norm_apply_eq_one 𝔭 h𝔭 := by
    rw [MultiplicativeIdealWeight.conj_apply, RCLike.norm_conj]
    exact χ.norm_apply_eq_one 𝔭 h𝔭

omit [NumberField K] in
@[simp]
theorem toMultiplicativeIdealWeight_conj :
    χ.conj.toMultiplicativeIdealWeight = χ.toMultiplicativeIdealWeight.conj := (rfl)

/-- The **pointwise product** of two unitary ideal weights, with the union of their bad sets. -/
noncomputable def pointwiseMul (ψ : UnitaryIdealWeight K) : UnitaryIdealWeight K where
  toMultiplicativeIdealWeight :=
    χ.toMultiplicativeIdealWeight.pointwiseMul ψ.toMultiplicativeIdealWeight
  norm_apply_eq_one 𝔭 h𝔭 := by
    rw [MultiplicativeIdealWeight.pointwiseMul_apply, norm_mul,
      χ.norm_apply_eq_one 𝔭 (fun h ↦ h𝔭 (Or.inl h)),
      ψ.norm_apply_eq_one 𝔭 (fun h ↦ h𝔭 (Or.inr h)), one_mul]

omit [NumberField K] in
@[simp]
theorem toMultiplicativeIdealWeight_pointwiseMul (ψ : UnitaryIdealWeight K) :
    (χ.pointwiseMul ψ).toMultiplicativeIdealWeight =
      χ.toMultiplicativeIdealWeight.pointwiseMul ψ.toMultiplicativeIdealWeight := (rfl)

/-- The **restriction** of a unitary ideal weight away from a finite set `S` of height-one primes,
which is again unitary: a height-one prime outside `χ.bad ∪ S` is prime to `S`, because a
height-one prime dividing another is equal to it. -/
noncomputable def restrict (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    UnitaryIdealWeight K where
  toMultiplicativeIdealWeight := χ.toMultiplicativeIdealWeight.restrict S hS
  norm_apply_eq_one 𝔭 h𝔭 := by
    have hne : ∀ 𝔮 ∈ S, ¬ 𝔮.asIdeal ∣ 𝔭.asIdeal := by
      intro 𝔮 h𝔮 hd
      have h𝔭𝔮 : 𝔭 = 𝔮 :=
        HeightOneSpectrum.ext (𝔭.isMaximal.eq_of_le 𝔮.isPrime.ne_top (Ideal.le_of_dvd hd))
      exact h𝔭 (Or.inr (by rw [h𝔭𝔮]; exact h𝔮))
    rw [MultiplicativeIdealWeight.restrict_apply, ite_eq_left hne]
    exact χ.norm_apply_eq_one 𝔭 fun h ↦ h𝔭 (Or.inl h)

@[simp]
theorem toMultiplicativeIdealWeight_restrict (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : S.Finite) : (χ.restrict S hS).toMultiplicativeIdealWeight =
      χ.toMultiplicativeIdealWeight.restrict S hS := (rfl)

/-- **The modulus of an arbitrary norm twist at a good ideal.** Twisting a unitary weight by
`N⁻ᶻ` gives modulus `N(I) ^ (-Re z)`. -/
theorem norm_apply_normTwist_of_isGood (z : ℂ) {I : Ideal (𝓞 K)}
    (hI : χ.toMultiplicativeIdealWeight.IsGood I) :
    ‖χ.toMultiplicativeIdealWeight.normTwist z I‖ = (Ideal.absNorm I : ℝ) ^ (-z.re) := by
  have hpos : 0 < Ideal.absNorm I :=
    Nat.pos_of_ne_zero fun h ↦ hI.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  rw [MultiplicativeIdealWeight.normTwist_apply, norm_mul, χ.norm_apply_eq_one_of_isGood hI,
    one_mul, Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]

/-- **Norm-twist rejection test.** If `z.re ≠ 0`, then at every good ideal of absolute norm
greater than one, the norm twist has modulus different from `1`. -/
theorem norm_apply_normTwist_ne_one {z : ℂ} (hz : z.re ≠ 0) {I : Ideal (𝓞 K)}
    (hI : χ.toMultiplicativeIdealWeight.IsGood I) (hnorm : 1 < Ideal.absNorm I) :
    ‖χ.toMultiplicativeIdealWeight.normTwist z I‖ ≠ 1 := by
  have hone : (1 : ℝ) < (Ideal.absNorm I : ℝ) := by exact_mod_cast hnorm
  rw [χ.norm_apply_normTwist_of_isGood z hI]
  rcases hz.lt_or_gt with h | h
  · exact ne_of_gt ((Real.one_lt_rpow_iff_of_pos (by positivity)).2
      (Or.inl ⟨hone, by simpa using h⟩))
  · exact ne_of_lt (Real.rpow_lt_one_of_one_lt_of_neg hone (by simpa using h))

/-- The **purely imaginary norm twist** `I ↦ χ I * N(I) ^ (-i t)` of a unitary ideal weight, which
is again unitary. -/
noncomputable def imaginaryNormTwist (t : ℝ) : UnitaryIdealWeight K where
  toMultiplicativeIdealWeight := χ.toMultiplicativeIdealWeight.normTwist (Complex.I * t)
  norm_apply_eq_one 𝔭 h𝔭 := by
    have hpos : 0 < Ideal.absNorm 𝔭.asIdeal :=
      Nat.pos_of_ne_zero fun h ↦ 𝔭.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    rw [MultiplicativeIdealWeight.normTwist_apply, norm_mul, χ.norm_apply_eq_one 𝔭 h𝔭, one_mul,
      Complex.norm_natCast_cpow_of_pos hpos]
    simp

@[simp]
theorem toMultiplicativeIdealWeight_imaginaryNormTwist (t : ℝ) :
    (χ.imaginaryNormTwist t).toMultiplicativeIdealWeight =
      χ.toMultiplicativeIdealWeight.normTwist (Complex.I * t) := (rfl)

end UnitaryIdealWeight

end

end TauCeti
