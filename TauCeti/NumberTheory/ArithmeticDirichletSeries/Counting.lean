/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.NormCoeff
public import TauCeti.Order.Northcott

/-!
# Counting carriers for ideals and prime ideals

Every estimate in the arithmetic-Dirichlet-series roadmap counts objects whose absolute norm does
not exceed a *real* cutoff `x`, and always inclusively: an object of norm exactly `x` is counted.
This file fixes that convention once.

The common core is Mathlib's `Northcott` property: a function `N : ι → ℕ` is Northcott when each
set `{i | N i ≤ B}` is finite.  For such an `N`:

* `TauCeti.normLE N x` is the finite set of indices with `(N i : ℝ) ≤ x`;
* `TauCeti.summatory N w x` is the inclusive sum of a weight `w` over `TauCeti.normLE N x`.

Two instances of this core carry the arithmetic content, `TauCeti.idealsLE` for the nonzero
integral ideals of `𝓞 K` and `TauCeti.primesLE` for the height-one primes, with
`TauCeti.idealSummatory`, `TauCeti.primeSummatory`, and `TauCeti.primePowerSummatory` the associated
summatory functions.  The
weighted prime counts of the roadmap are the two named specializations
`TauCeti.primeTheta`, the logarithmically weighted count, and `TauCeti.primeCount`, the
unweighted one; both are restricted to a set `S` of height-one primes through `Set.indicator`,
so no decidability hypothesis is needed on `S`.

A prime-power ideal is `𝔭 ^ k` for a unique height-one prime `𝔭` and a unique `k ≥ 1`;
`TauCeti.primePowerBase` and `TauCeti.primePowerExponent` name that pair, and
`TauCeti.idealPrimePower_eq_of_base_eq_of_exponent_eq` records that it determines the ideal.  The
exponent is `1` exactly on the primes themselves, which is `TauCeti.primePowerExponent_eq_one_iff`;
`TauCeti.IdealPrimePower.ofPrime` is the resulting inclusion of the prime carrier into the
prime-power carrier, and `TauCeti.primePowerSummatory_eq_primeSummatory` uses it to read a
prime-power sum concentrated on the exponent-one part as a sum over primes.

Two lemmas move a summatory function between the three carriers.
`TauCeti.idealSummatory_eq_primePowerSummatory` reads an ideal weight vanishing off the prime
powers as a prime-power weight, and `TauCeti.idealSummatory_eq_sum_range_normFiber` regroups an
ideal summatory function into the partial sum, over `n ≤ ⌊x⌋₊`, of the total mass on the norm
fibre at `n`.  Together they present a sum over prime powers as a partial sum of an
`ArithmeticFunction`, which is the shape a Tauberian theorem consumes.

For `0 ≤ x`, a real cutoff and its floor select the same indices, so
`TauCeti.normLE_eq_normLE_natFloor` and `TauCeti.summatory_eq_summatory_natFloor` convert between
the real and natural conventions. The small-cutoff cases are degenerate for a reason worth
recording: a nonzero ideal has absolute norm at least `1`, and a height-one prime at least `2`, so
`TauCeti.idealsLE_one` isolates the unit ideal and `TauCeti.primesLE_eq_empty_of_lt_two` empties the
prime carrier below `2`.

Modifying a weight on a finite set, or a prime set on a finite symmetric difference, changes a
summatory function by a quantity that is eventually the *constant* total discrepancy; this is
`TauCeti.eventually_summatory_sub_eq` and its two prime specializations. Layer 7 uses these to
show that finite changes do not affect a density.

## Roadmap role

This is Layer **4** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: the finite cutoff
carriers of 4.1, the generic summatory functions on ideals, primes, and prime powers of 4.2, and the
weighted prime counts `primeTheta` and `primeCount` of 4.3. Layer 5 supplies the actual size
estimates for these counts, and consumes the prime base and exponent of a prime-power ideal to
fibre those estimates over the primes.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters I--II.
* H. Davenport, *Multiplicative Number Theory*, Chapters 1 and 7.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors NumberField
open IsDedekindDomain

/-! ### Ideals and height-one primes of bounded absolute norm -/

/-- The absolute norm on nonzero ideals of a Dedekind domain finite and free over `ℤ` is Northcott,
by `Ideal.finite_setOfPred_absNorm_le₀`. Mathlib already supplies the corresponding instance on
height-one primes. -/
instance instNorthcottAbsNormNonZeroDivisors {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R] [CharZero R] :
    Northcott (fun I : (Ideal R)⁰ ↦ Ideal.absNorm (I : Ideal R)) :=
  ⟨fun B ↦ Ideal.finite_setOfPred_absNorm_le₀ B⟩

variable (K : Type*) [Field K] [NumberField K]

/-- The nonzero integral ideals of `𝓞 K` of absolute norm at most `x`. -/
noncomputable abbrev idealsLE (x : ℝ) : Finset ((Ideal (𝓞 K))⁰) :=
  normLE (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) x

/-- The height-one primes of `𝓞 K` of absolute norm at most `x`. -/
noncomputable abbrev primesLE (x : ℝ) : Finset (HeightOneSpectrum (𝓞 K)) :=
  normLE (fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal) x

/-- A nonzero integral ideal which is a positive power of a prime ideal. -/
abbrev IdealPrimePower :=
  {A : (Ideal (𝓞 K))⁰ // IsPrimePow (A : Ideal (𝓞 K))}

/-- Absolute norm is Northcott on prime-power ideals, by restriction from nonzero ideals. -/
instance instNorthcottAbsNormIdealPrimePower :
    Northcott (fun A : IdealPrimePower K ↦ Ideal.absNorm (A : Ideal (𝓞 K))) :=
  ⟨fun B ↦ (Northcott.finite_le
    (h := fun A : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (A : Ideal (𝓞 K))) B).preimage
      fun _ _ _ _ h ↦ Subtype.ext h⟩

/-- The prime-power ideals of `𝓞 K` of absolute norm at most `x`. -/
noncomputable abbrev primePowersLE (x : ℝ) : Finset (IdealPrimePower K) :=
  normLE (fun A : IdealPrimePower K ↦ Ideal.absNorm (A : Ideal (𝓞 K))) x

/-- Prime-power cutoff carriers grow monotonically with the cutoff. -/
theorem primePowersLE_mono : Monotone (primePowersLE K) :=
  normLE_mono _

variable {K}

/-- The absolute norm of a nonzero integral ideal is at least `1`, as a real number. -/
theorem one_le_absNorm_real_of_nonZeroDivisors (I : (Ideal (𝓞 K))⁰) :
    (1 : ℝ) ≤ Ideal.absNorm (I : Ideal (𝓞 K)) := by
  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I

/-- The absolute norm of a height-one prime is at least `2`, as a real number. -/
theorem two_le_absNorm_asIdeal_real (v : HeightOneSpectrum (𝓞 K)) :
    (2 : ℝ) ≤ Ideal.absNorm v.asIdeal := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

/-- The absolute norm of a prime-power ideal is at least `2`, as a real number. -/
theorem two_le_absNorm_idealPrimePower_real (A : IdealPrimePower K) :
    (2 : ℝ) ≤ Ideal.absNorm (A.1 : Ideal (𝓞 K)) := by
  have hne_zero : Ideal.absNorm (A.1 : Ideal (𝓞 K)) ≠ 0 :=
    Ideal.absNorm_ne_zero_of_nonZeroDivisors A.1
  have hne_one : Ideal.absNorm (A.1 : Ideal (𝓞 K)) ≠ 1 := fun h ↦
    A.property.not_isUnit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp h))
  have hnorm : 2 ≤ Ideal.absNorm (A.1 : Ideal (𝓞 K)) := by omega
  exact_mod_cast hnorm

/-! ### The prime base and the exponent of a prime-power ideal -/

/-- The **exponent** of a prime-power ideal `A`: the unique `k ≥ 1` with `A = 𝔭 ^ k`. -/
noncomputable def primePowerExponent (A : IdealPrimePower K) : ℕ :=
  A.2.choose_spec.choose

/-- The **prime base** of a prime-power ideal `A`: the unique height-one prime `𝔭` with
`A = 𝔭 ^ k` for some `k ≥ 1`. -/
noncomputable def primePowerBase (A : IdealPrimePower K) : HeightOneSpectrum (𝓞 K) where
  asIdeal := A.2.choose
  isPrime := Ideal.isPrime_of_prime A.2.choose_spec.choose_spec.1
  ne_bot := A.2.choose_spec.choose_spec.1.ne_zero

/-- The ideal underlying the prime base of a prime-power ideal is prime. -/
theorem prime_primePowerBase (A : IdealPrimePower K) : Prime (primePowerBase A).asIdeal :=
  A.2.choose_spec.choose_spec.1

omit [NumberField K] in
/-- The exponent of a prime-power ideal is positive. -/
theorem primePowerExponent_pos (A : IdealPrimePower K) : 0 < primePowerExponent A :=
  A.2.choose_spec.choose_spec.2.1

/-- The defining factorization of a prime-power ideal. -/
theorem primePowerBase_pow_primePowerExponent (A : IdealPrimePower K) :
    (primePowerBase A).asIdeal ^ primePowerExponent A = (A : Ideal (𝓞 K)) :=
  A.2.choose_spec.choose_spec.2.2

/-- The prime base is determined by any factorization of `A` as a power of a prime. -/
theorem primePowerBase_asIdeal_eq {A : IdealPrimePower K} {P : Ideal (𝓞 K)} (hP : Prime P)
    {k : ℕ} (hpow : P ^ k = (A : Ideal (𝓞 K))) :
    (primePowerBase A).asIdeal = P :=
  eq_of_prime_pow_eq (prime_primePowerBase A) hP (primePowerExponent_pos A)
    ((primePowerBase_pow_primePowerExponent A).trans hpow.symm)

/-- **The prime base is the only height-one prime dividing a prime-power ideal.** -/
@[simp]
theorem dvd_iff_eq_primePowerBase {v : HeightOneSpectrum (𝓞 K)} {A : IdealPrimePower K} :
    v.asIdeal ∣ (A : Ideal (𝓞 K)) ↔ v = primePowerBase A := by
  refine ⟨fun hdvd ↦ HeightOneSpectrum.ext ?_, fun hv ↦ ?_⟩
  · rw [← primePowerBase_pow_primePowerExponent A] at hdvd
    have hle : (primePowerBase A).asIdeal ≤ v.asIdeal :=
      Ideal.dvd_iff_le.mp
        ((Ideal.prime_of_isPrime v.ne_bot v.isPrime).dvd_of_dvd_pow hdvd)
    exact ((Ideal.IsPrime.isMaximal (primePowerBase A).isPrime
      (primePowerBase A).ne_bot).eq_of_le v.isPrime.ne_top hle).symm
  · rw [hv, ← primePowerBase_pow_primePowerExponent A]
    exact dvd_pow_self _ (primePowerExponent_pos A).ne'

/-- The absolute norm of a prime-power ideal is the corresponding power of the norm of its
prime base. -/
theorem absNorm_eq_absNorm_primePowerBase_pow (A : IdealPrimePower K) :
    Ideal.absNorm (A : Ideal (𝓞 K)) =
      Ideal.absNorm (primePowerBase A).asIdeal ^ primePowerExponent A := by
  rw [← primePowerBase_pow_primePowerExponent A, map_pow]

/-- The absolute norm of a prime-power ideal is a prime power: `N(𝔭 ^ k) = p ^ (f k)` for the
rational prime `p` below `𝔭` and the residue degree `f`. -/
theorem isPrimePow_absNorm (A : IdealPrimePower K) :
    IsPrimePow (Ideal.absNorm (A : Ideal (𝓞 K))) := by
  have : ((primePowerBase A).asIdeal).IsMaximal :=
    Ideal.IsPrime.isMaximal (primePowerBase A).isPrime (primePowerBase A).ne_bot
  obtain ⟨p, m, hm, -, hp, hnorm⟩ :=
    Ideal.exists_prime_and_absNorm_eq_pow (primePowerBase A).asIdeal
  refine ⟨p, m * primePowerExponent A, hp.prime, Nat.mul_pos hm (primePowerExponent_pos A), ?_⟩
  rw [pow_mul, ← hnorm, ← absNorm_eq_absNorm_primePowerBase_pow]

/-- The exponent is determined by any factorization of `A` as a power of a prime. -/
theorem primePowerExponent_eq {A : IdealPrimePower K} {P : Ideal (𝓞 K)} (hP : Prime P)
    {k : ℕ} (hpow : P ^ k = (A : Ideal (𝓞 K))) :
    primePowerExponent A = k := by
  have hbase : (primePowerBase A).asIdeal = P := primePowerBase_asIdeal_eq hP hpow
  have hnorm : Ideal.absNorm P ^ primePowerExponent A = Ideal.absNorm P ^ k := by
    rw [← map_pow, ← map_pow, hpow, ← hbase, primePowerBase_pow_primePowerExponent A]
  refine Nat.pow_right_injective ?_ hnorm
  have h2 : (2 : ℝ) ≤ Ideal.absNorm (primePowerBase A).asIdeal :=
    two_le_absNorm_asIdeal_real _
  rw [hbase] at h2
  exact_mod_cast h2

/-- A prime-power ideal is determined by its prime base and its exponent. -/
theorem idealPrimePower_eq_of_base_eq_of_exponent_eq {A B : IdealPrimePower K}
    (hbase : primePowerBase A = primePowerBase B)
    (hexp : primePowerExponent A = primePowerExponent B) : A = B := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [← primePowerBase_pow_primePowerExponent A, ← primePowerBase_pow_primePowerExponent B,
    hbase, hexp]

/-- A prime-power ideal has exponent one exactly when it is itself prime. -/
@[simp] theorem primePowerExponent_eq_one_iff (A : IdealPrimePower K) :
    primePowerExponent A = 1 ↔ Prime (A : Ideal (𝓞 K)) := by
  refine ⟨fun h ↦ ?_, fun h ↦ primePowerExponent_eq h (pow_one _)⟩
  rw [← primePowerBase_pow_primePowerExponent A, h, pow_one]
  exact prime_primePowerBase A

/-- A prime-power ideal which is not prime has exponent at least two. -/
theorem two_le_primePowerExponent {A : IdealPrimePower K} (hA : ¬ Prime (A : Ideal (𝓞 K))) :
    2 ≤ primePowerExponent A := by
  have h₁ := primePowerExponent_pos A
  have h₂ : primePowerExponent A ≠ 1 := fun h ↦ hA ((primePowerExponent_eq_one_iff A).mp h)
  omega

/-- A height-one prime, seen as the prime-power ideal of exponent one that it is. -/
def IdealPrimePower.ofPrime (v : HeightOneSpectrum (𝓞 K)) : IdealPrimePower K :=
  ⟨⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩,
    v.asIdeal, 1, Ideal.prime_of_isPrime v.ne_bot v.isPrime, one_pos, pow_one _⟩

/-- The ideal underlying `TauCeti.IdealPrimePower.ofPrime v` is the prime ideal of `v`. -/
@[simp]
theorem IdealPrimePower.coe_ofPrime (v : HeightOneSpectrum (𝓞 K)) :
    (IdealPrimePower.ofPrime v : Ideal (𝓞 K)) = v.asIdeal :=
  (rfl)

/-- The underlying ideal of a height-one prime is prime. -/
theorem IdealPrimePower.prime_ofPrime (v : HeightOneSpectrum (𝓞 K)) :
    Prime ((IdealPrimePower.ofPrime v : IdealPrimePower K) : Ideal (𝓞 K)) :=
  Ideal.prime_of_isPrime v.ne_bot v.isPrime

/-- A height-one prime is its own prime base. -/
@[simp]
theorem primePowerBase_ofPrime (v : HeightOneSpectrum (𝓞 K)) :
    primePowerBase (IdealPrimePower.ofPrime v) = v :=
  HeightOneSpectrum.ext
    (primePowerBase_asIdeal_eq (IdealPrimePower.prime_ofPrime v) (pow_one _))

/-- A height-one prime has exponent one as a prime-power ideal. -/
@[simp]
theorem primePowerExponent_ofPrime (v : HeightOneSpectrum (𝓞 K)) :
    primePowerExponent (IdealPrimePower.ofPrime v) = 1 :=
  primePowerExponent_eq (IdealPrimePower.prime_ofPrime v) (pow_one _)

/-- A prime prime-power ideal is its own prime base, seen as a prime-power ideal. -/
@[simp]
theorem IdealPrimePower.ofPrime_primePowerBase {A : IdealPrimePower K}
    (hA : Prime (A : Ideal (𝓞 K))) : IdealPrimePower.ofPrime (primePowerBase A) = A := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [IdealPrimePower.coe_ofPrime, ← primePowerBase_pow_primePowerExponent A,
    (primePowerExponent_eq_one_iff A).mpr hA, pow_one]

/-- Below a cutoff, the prime-power ideals which are themselves prime are exactly the images
under `TauCeti.IdealPrimePower.ofPrime` of the height-one primes below that cutoff. -/
private theorem primePowersLE_filter_prime (x : ℝ)
    [DecidablePred fun A : IdealPrimePower K ↦ Prime (A : Ideal (𝓞 K))] :
    (primePowersLE K x).filter (fun A : IdealPrimePower K ↦ Prime (A : Ideal (𝓞 K)))
      = (primesLE K x).image IdealPrimePower.ofPrime := by
  ext A
  simp only [Finset.mem_filter, Finset.mem_image, mem_normLE]
  refine ⟨fun ⟨hle, hA⟩ ↦ ⟨primePowerBase A, ?_, IdealPrimePower.ofPrime_primePowerBase hA⟩,
    fun ⟨v, hv, hvA⟩ ↦ ?_⟩
  · have hbase : ((IdealPrimePower.ofPrime (primePowerBase A) : IdealPrimePower K) :
        Ideal (𝓞 K)) = (A : Ideal (𝓞 K)) :=
      congrArg (fun B : IdealPrimePower K ↦ (B : Ideal (𝓞 K)))
        (IdealPrimePower.ofPrime_primePowerBase hA)
    rw [IdealPrimePower.coe_ofPrime] at hbase
    rw [hbase]
    exact hle
  · subst hvA
    exact ⟨hv, IdealPrimePower.prime_ofPrime v⟩

/-- Below the cutoff `1` there is no nonzero integral ideal to count. -/
theorem idealsLE_eq_empty_of_lt_one {x : ℝ} (hx : x < 1) : idealsLE K x = ∅ :=
  normLE_eq_empty_of_lt _ one_le_absNorm_real_of_nonZeroDivisors hx

/-- At the cutoff `1` the only nonzero integral ideal counted is the unit ideal. -/
theorem idealsLE_one : idealsLE K 1 = {1} := by
  have h : idealsLE K 1 = normFiber K 1 := by
    ext I
    rw [mem_normLE, mem_normFiber]
    exact ⟨fun hI ↦ by
      exact_mod_cast le_antisymm hI (one_le_absNorm_real_of_nonZeroDivisors I),
      fun hI ↦ by simp [hI]⟩
  rw [h, normFiber_one]

/-- Below the cutoff `2` there is no height-one prime to count. -/
theorem primesLE_eq_empty_of_lt_two {x : ℝ} (hx : x < 2) : primesLE K x = ∅ :=
  normLE_eq_empty_of_lt _ two_le_absNorm_asIdeal_real hx

/-- Below the cutoff `2` there is no prime-power ideal to count. -/
theorem primePowersLE_eq_empty_of_lt_two {x : ℝ} (hx : x < 2) :
    primePowersLE K x = ∅ :=
  normLE_eq_empty_of_lt _ two_le_absNorm_idealPrimePower_real hx

/-- Every real cutoff selects the same prime-power ideals as its natural floor. -/
theorem primePowersLE_eq_primePowersLE_natFloor (x : ℝ) :
    primePowersLE K x = primePowersLE K (⌊x⌋₊ : ℝ) := by
  by_cases hx : 0 ≤ x
  · exact normLE_eq_normLE_natFloor _ hx
  · rw [primePowersLE_eq_empty_of_lt_two (by linarith),
      Nat.floor_of_nonpos (le_of_not_ge hx), primePowersLE_eq_empty_of_lt_two (by norm_num)]

/-- There are at most as many height-one primes as nonzero ideals below any cutoff. -/
theorem card_primesLE_le_card_idealsLE (x : ℝ) : (primesLE K x).card ≤ (idealsLE K x).card := by
  refine Finset.card_le_card_of_injOn
    (fun v ↦ ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩)
    (fun v hv ↦ ?_) fun v _ w _ h ↦ ?_
  · simpa using (mem_normLE _).mp hv
  · exact HeightOneSpectrum.ext (congrArg Subtype.val h)

variable (K)

/-! ### Summatory functions over ideals and over primes -/

/-- The inclusive summatory function of a weight on the nonzero integral ideals of `𝓞 K`. -/
noncomputable abbrev idealSummatory {M : Type*} [AddCommMonoid M]
    (w : (Ideal (𝓞 K))⁰ → M) (x : ℝ) : M :=
  summatory (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) w x

/-- The inclusive summatory function of a weight on the height-one primes of `𝓞 K`. -/
noncomputable abbrev primeSummatory {M : Type*} [AddCommMonoid M]
    (w : HeightOneSpectrum (𝓞 K) → M) (x : ℝ) : M :=
  summatory (fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal) w x

/-- The inclusive summatory function of a weight on prime-power ideals of `𝓞 K`. -/
noncomputable abbrev primePowerSummatory {M : Type*} [AddCommMonoid M]
    (w : IdealPrimePower K → M) (x : ℝ) : M :=
  summatory (fun A : IdealPrimePower K ↦ Ideal.absNorm (A : Ideal (𝓞 K))) w x

/-- An ideal summatory function is the sum of its weight over the inclusive cutoff carrier. -/
theorem idealSummatory_apply {M : Type*} [AddCommMonoid M] (w : (Ideal (𝓞 K))⁰ → M) (x : ℝ) :
    idealSummatory K w x = ∑ I ∈ idealsLE K x, w I :=
  summatory_apply _ w x

/-- A prime summatory function is the sum of its weight over the inclusive cutoff carrier. -/
theorem primeSummatory_apply {M : Type*} [AddCommMonoid M]
    (w : HeightOneSpectrum (𝓞 K) → M) (x : ℝ) :
    primeSummatory K w x = ∑ v ∈ primesLE K x, w v :=
  summatory_apply _ w x

/-- A prime-power summatory function is the sum of its weight over the inclusive cutoff carrier. -/
theorem primePowerSummatory_apply {M : Type*} [AddCommMonoid M]
    (w : IdealPrimePower K → M) (x : ℝ) :
    primePowerSummatory K w x = ∑ A ∈ primePowersLE K x, w A :=
  summatory_apply _ w x

/-- A prime-power weight vanishing off the primes themselves has the same summatory function as
its restriction to the primes.  This is what separates the exponent-one part of a sum over prime
powers, such as Chebyshev's `ϑ` inside `ψ`. -/
theorem primePowerSummatory_eq_primeSummatory {M : Type*} [AddCommMonoid M]
    (w : IdealPrimePower K → M)
    (hw : ∀ A : IdealPrimePower K, ¬ Prime (A : Ideal (𝓞 K)) → w A = 0) (x : ℝ) :
    primePowerSummatory K w x =
      primeSummatory K (fun v ↦ w (IdealPrimePower.ofPrime v)) x := by
  classical
  rw [primePowerSummatory_apply, primeSummatory_apply,
    ← Finset.sum_filter_of_ne (p := fun A : IdealPrimePower K ↦ Prime (A : Ideal (𝓞 K)))
      fun A _ hne ↦ not_not.mp fun h ↦ hne (hw A h),
    primePowersLE_filter_prime]
  exact Finset.sum_image fun v _ w' _ h ↦ HeightOneSpectrum.ext
    (by simpa using congrArg (fun B : IdealPrimePower K ↦ (B : Ideal (𝓞 K))) h)

/-- Prime-power summation distributes over pointwise addition of weights. -/
theorem primePowerSummatory_add {M : Type*} [AddCommMonoid M]
    (w₁ w₂ : IdealPrimePower K → M) (x : ℝ) :
    primePowerSummatory K (w₁ + w₂) x =
      primePowerSummatory K w₁ x + primePowerSummatory K w₂ x :=
  summatory_add _ _ _ x

/-- Every real cutoff gives the same prime-power summatory value as its natural floor. -/
theorem primePowerSummatory_eq_primePowerSummatory_natFloor {M : Type*} [AddCommMonoid M]
    (w : IdealPrimePower K → M) (x : ℝ) :
    primePowerSummatory K w x = primePowerSummatory K w (⌊x⌋₊ : ℝ) := by
  rw [primePowerSummatory_apply, primePowerSummatory_apply,
    primePowersLE_eq_primePowersLE_natFloor]

/-- A pointwise nonnegative real weight has a nonnegative prime-power summatory function. -/
theorem primePowerSummatory_nonneg (w : IdealPrimePower K → ℝ) (hw : ∀ A, 0 ≤ w A) (x : ℝ) :
    0 ≤ primePowerSummatory K w x :=
  summatory_nonneg _ hw x

/-- A nonnegative real weight has a prime-power summatory function monotone in the cutoff. -/
theorem primePowerSummatory_mono (w : IdealPrimePower K → ℝ) (hw : ∀ A, 0 ≤ w A) :
    Monotone (primePowerSummatory K w) :=
  summatory_mono _ hw

/-- Changing a prime-power weight on finitely many ideals produces an eventually constant
difference of summatory functions. -/
theorem eventually_primePowerSummatory_sub_eq {M : Type*} [AddCommGroup M]
    (w₁ w₂ : IdealPrimePower K → M) (u : Finset (IdealPrimePower K))
    (h : ∀ A ∉ u, w₁ A = w₂ A) :
    ∀ᶠ x in Filter.atTop,
      primePowerSummatory K w₁ x - primePowerSummatory K w₂ x =
        ∑ A ∈ u, (w₁ A - w₂ A) :=
  eventually_summatory_sub_eq _ _ _ u h

/-- Below the cutoff `1` there is nothing to sum over the nonzero ideals. -/
theorem idealSummatory_eq_zero_of_lt_one {M : Type*} [AddCommMonoid M]
    (w : (Ideal (𝓞 K))⁰ → M) {x : ℝ} (hx : x < 1) :
    idealSummatory K w x = 0 :=
  summatory_eq_zero_of_lt _ one_le_absNorm_real_of_nonZeroDivisors hx w

/-- At the cutoff `1` only the unit ideal contributes. -/
theorem idealSummatory_one {M : Type*} [AddCommMonoid M] (w : (Ideal (𝓞 K))⁰ → M) :
    idealSummatory K w 1 = w 1 := by
  rw [idealSummatory_apply, idealsLE_one, Finset.sum_singleton]

open Classical in
/-- The ideals of absolute norm at most `x` and of absolute norm exactly `n` are the whole norm
fibre at `n`, as soon as `n` is at most `⌊x⌋₊`. -/
private theorem idealsLE_filter_absNorm_eq {n : ℕ} {x : ℝ} (hn : n ≤ ⌊x⌋₊) (hx : 0 ≤ x) :
    (idealsLE K x).filter (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K)) = n) =
      normFiber K n := by
  ext I
  simp only [Finset.mem_filter, mem_normLE, mem_normFiber]
  refine ⟨fun hI ↦ hI.2, fun hI ↦ ⟨?_, hI⟩⟩
  rw [hI]
  exact (Nat.cast_le.mpr hn).trans (Nat.floor_le hx)

/-- **Regrouping an ideal summatory function by absolute norm.** The inclusive sum of a weight over
the nonzero integral ideals of absolute norm at most `x` is the sum, over the natural numbers
`n ≤ ⌊x⌋₊`, of the total mass of the weight on the norm fibre at `n`.

This is the finite form of the Layer 1 regrouping: it reads a summatory function over ideals as a
partial sum of the `ArithmeticFunction` obtained from the same weight by `TauCeti.normCoeff`. -/
theorem idealSummatory_eq_sum_range_normFiber {M : Type*} [AddCommMonoid M]
    (w : (Ideal (𝓞 K))⁰ → M) (x : ℝ) :
    idealSummatory K w x = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), ∑ I ∈ normFiber K n, w I := by
  classical
  rcases lt_or_ge x 1 with hx | hx
  · rw [idealSummatory_eq_zero_of_lt_one K w hx, Nat.floor_eq_zero.mpr hx]
    simp
  · rw [idealSummatory_apply,
      ← Finset.sum_fiberwise_of_maps_to
        (g := fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K)))
        (t := Finset.range (⌊x⌋₊ + 1))
        (fun I hI ↦ Finset.mem_range_succ_iff.mpr (Nat.le_floor (by simpa using hI))) w]
    exact Finset.sum_congr rfl fun n hn ↦ by
      rw [idealsLE_filter_absNorm_eq K (Finset.mem_range_succ_iff.mp hn) (zero_le_one.trans hx)]

/-- **An ideal weight concentrated on the prime powers, read as a prime-power weight.** An ideal
weight vanishing off the prime-power ideals has the same summatory function as its restriction to
the prime-power carrier.  This is the ideal-level counterpart of
`TauCeti.primePowerSummatory_eq_primeSummatory`. -/
theorem idealSummatory_eq_primePowerSummatory {M : Type*} [AddCommMonoid M]
    (v : (Ideal (𝓞 K))⁰ → M) (w : IdealPrimePower K → M)
    (hvw : ∀ A : IdealPrimePower K, v (A : (Ideal (𝓞 K))⁰) = w A)
    (hv : ∀ I : (Ideal (𝓞 K))⁰, ¬ IsPrimePow (I : Ideal (𝓞 K)) → v I = 0) (x : ℝ) :
    idealSummatory K v x = primePowerSummatory K w x := by
  classical
  have hmem {I : (Ideal (𝓞 K))⁰} :
      I ∈ (primePowersLE K x).image (fun A : IdealPrimePower K ↦ (A : (Ideal (𝓞 K))⁰)) ↔
        IsPrimePow (I : Ideal (𝓞 K)) ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x := by
    simp only [Finset.mem_image, mem_normLE]
    exact ⟨fun ⟨A, hA, hAI⟩ ↦ ⟨hAI ▸ A.2, hAI ▸ hA⟩, fun ⟨h, hI⟩ ↦ ⟨⟨I, h⟩, hI, rfl⟩⟩
  rw [idealSummatory_apply, primePowerSummatory_apply]
  calc ∑ I ∈ idealsLE K x, v I
      = ∑ I ∈ (primePowersLE K x).image
          (fun A : IdealPrimePower K ↦ (A : (Ideal (𝓞 K))⁰)), v I := by
        refine (Finset.sum_subset (fun I hI ↦ by simpa using (hmem.mp hI).2)
          fun I hI hI' ↦ hv I fun h ↦ hI' (hmem.mpr ⟨h, by simpa using hI⟩)).symm
    _ = ∑ A ∈ primePowersLE K x, v (A : (Ideal (𝓞 K))⁰) :=
        Finset.sum_image fun _ _ _ _ h ↦ Subtype.ext h
    _ = ∑ A ∈ primePowersLE K x, w A := Finset.sum_congr rfl fun A _ ↦ hvw A

/-! ### The weighted prime counts -/

/-- The logarithmically weighted count of the primes of `S` of absolute norm at most `x`: the
number-field analogue of Chebyshev's `ϑ`. -/
noncomputable def primeTheta (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) : ℝ :=
  primeSummatory K (S.indicator fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ)) x

/-- The number of primes of `S` of absolute norm at most `x`, as a real number: the number-field
analogue of `π`. -/
noncomputable def primeCount (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) : ℝ :=
  primeSummatory K (S.indicator 1) x

variable {K}
variable {S T : Set (HeightOneSpectrum (𝓞 K))} {x : ℝ}

/-- The logarithmically weighted prime count as an explicit sum over the inclusive carrier. -/
theorem primeTheta_apply (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeTheta K S x =
      ∑ v ∈ primesLE K x, S.indicator (fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ)) v :=
  by rw [primeTheta, primeSummatory_apply]

/-- The unweighted prime count as an explicit sum over the inclusive carrier. -/
theorem primeCount_apply (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeCount K S x = ∑ v ∈ primesLE K x, S.indicator 1 v := by
  rw [primeCount, primeSummatory_apply]

/-- The count of `S` really is the cardinality of the set of primes of `S` below the cutoff. -/
theorem primeCount_eq_card (S : Set (HeightOneSpectrum (𝓞 K))) [DecidablePred (· ∈ S)] (x : ℝ) :
    primeCount K S x = ((primesLE K x).filter (· ∈ S)).card := by
  rw [primeCount_apply]
  simp [Set.indicator_apply, Finset.sum_boole]

@[simp]
theorem primeTheta_empty (x : ℝ) : primeTheta K (∅ : Set (HeightOneSpectrum (𝓞 K))) x = 0 := by
  simp [primeTheta_apply]

@[simp]
theorem primeCount_empty (x : ℝ) : primeCount K (∅ : Set (HeightOneSpectrum (𝓞 K))) x = 0 := by
  simp [primeCount_apply]

/-- The absolute norm of a height-one prime is positive, as a real number. -/
theorem absNorm_asIdeal_real_pos (v : HeightOneSpectrum (𝓞 K)) :
    0 < (Ideal.absNorm v.asIdeal : ℝ) :=
  lt_of_lt_of_le zero_lt_two (two_le_absNorm_asIdeal_real v)

/-- The logarithm of the absolute norm of a height-one prime is positive. -/
theorem log_absNorm_asIdeal_pos (v : HeightOneSpectrum (𝓞 K)) :
    0 < Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
  Real.log_pos (by linarith [two_le_absNorm_asIdeal_real v])

/-- The logarithm of the absolute norm of a height-one prime is nonnegative. -/
theorem log_absNorm_asIdeal_nonneg (v : HeightOneSpectrum (𝓞 K)) :
    0 ≤ Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
  (log_absNorm_asIdeal_pos v).le

/-- The logarithmically weighted prime count is nonnegative. -/
theorem primeTheta_nonneg (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) : 0 ≤ primeTheta K S x :=
  summatory_nonneg _ (fun v ↦ Set.indicator_nonneg
    (fun v _ ↦ log_absNorm_asIdeal_nonneg v) v) x

/-- The unweighted prime count is nonnegative. -/
theorem primeCount_nonneg (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) : 0 ≤ primeCount K S x :=
  summatory_nonneg _ (fun v ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) v) x

/-- The logarithmically weighted prime count is monotone in the inclusive cutoff. -/
theorem primeTheta_mono (S : Set (HeightOneSpectrum (𝓞 K))) : Monotone (primeTheta K S) :=
  summatory_mono _ fun v ↦ Set.indicator_nonneg
    (fun v _ ↦ log_absNorm_asIdeal_nonneg v) v

/-- The unweighted prime count is monotone in the inclusive cutoff. -/
theorem primeCount_mono (S : Set (HeightOneSpectrum (𝓞 K))) : Monotone (primeCount K S) :=
  summatory_mono _ fun v ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) v

/-- Enlarging the prime set can only increase the logarithmically weighted count. -/
theorem primeTheta_mono_set (hST : S ⊆ T) (x : ℝ) : primeTheta K S x ≤ primeTheta K T x :=
  summatory_le_summatory _ (fun v ↦ Set.indicator_le_indicator_of_subset hST
    log_absNorm_asIdeal_nonneg v) x

/-- Enlarging the prime set can only increase the unweighted count. -/
theorem primeCount_mono_set (hST : S ⊆ T) (x : ℝ) : primeCount K S x ≤ primeCount K T x :=
  summatory_le_summatory _
    (fun v ↦ Set.indicator_le_indicator_of_subset hST (fun _ ↦ zero_le_one) v) x

/-- Below the cutoff `2` no prime is counted. -/
theorem primeTheta_eq_zero_of_lt_two (S : Set (HeightOneSpectrum (𝓞 K))) (hx : x < 2) :
    primeTheta K S x = 0 :=
  summatory_eq_zero_of_lt _ two_le_absNorm_asIdeal_real hx _

/-- Below the cutoff `2` no prime is counted by the unweighted count. -/
theorem primeCount_eq_zero_of_lt_two (S : Set (HeightOneSpectrum (𝓞 K))) (hx : x < 2) :
    primeCount K S x = 0 :=
  summatory_eq_zero_of_lt _ two_le_absNorm_asIdeal_real hx _

/-- Every real cutoff gives the same logarithmically weighted prime count as its natural floor. -/
theorem primeTheta_eq_primeTheta_natFloor (S : Set (HeightOneSpectrum (𝓞 K))) :
    primeTheta K S x = primeTheta K S (⌊x⌋₊ : ℝ) :=
  by
    by_cases hx : 0 ≤ x
    · exact summatory_eq_summatory_natFloor _ _ hx
    · rw [primeTheta_eq_zero_of_lt_two S (by linarith),
        Nat.floor_of_nonpos (le_of_not_ge hx), primeTheta_eq_zero_of_lt_two S (by norm_num)]

/-- Every real cutoff gives the same unweighted prime count as its natural floor. -/
theorem primeCount_eq_primeCount_natFloor (S : Set (HeightOneSpectrum (𝓞 K))) :
    primeCount K S x = primeCount K S (⌊x⌋₊ : ℝ) :=
  by
    by_cases hx : 0 ≤ x
    · exact summatory_eq_summatory_natFloor _ _ hx
    · rw [primeCount_eq_zero_of_lt_two S (by linarith),
        Nat.floor_of_nonpos (le_of_not_ge hx), primeCount_eq_zero_of_lt_two S (by norm_num)]

/-- The weighted counts are additive along a disjoint union of prime sets. -/
theorem primeTheta_union (hST : Disjoint S T) (x : ℝ) :
    primeTheta K (S ∪ T) x = primeTheta K S x + primeTheta K T x := by
  rw [primeTheta, Set.indicator_union_of_disjoint hST]
  exact summatory_add _ _ _ x

/-- The unweighted count is additive along a disjoint union of prime sets. -/
theorem primeCount_union (hST : Disjoint S T) (x : ℝ) :
    primeCount K (S ∪ T) x = primeCount K S x + primeCount K T x := by
  rw [primeCount, Set.indicator_union_of_disjoint hST]
  exact summatory_add _ _ _ x

/-- Chebyshev's trivial comparison: each counted prime contributes at most `log x`. -/
theorem primeTheta_le_primeCount_mul_log (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeTheta K S x ≤ primeCount K S x * Real.log x := by
  rw [primeTheta_apply, primeCount_apply, Finset.sum_mul]
  refine Finset.sum_le_sum fun v hv ↦ ?_
  rw [mem_normLE] at hv
  by_cases hS : v ∈ S
  · rw [Set.indicator_of_mem hS, Set.indicator_of_mem hS, Pi.one_apply, one_mul]
    exact Real.log_le_log (absNorm_asIdeal_real_pos v) hv
  · rw [Set.indicator_of_notMem hS, Set.indicator_of_notMem hS, zero_mul]

/-- A finite set of primes has eventually constant count, namely its cardinality.  This is the
input to the Layer 7 statement that a finite set of primes has Dirichlet density zero. -/
theorem eventually_primeCount_eq_card (hS : S.Finite) :
    ∀ᶠ x in Filter.atTop, primeCount K S x = S.ncard := by
  filter_upwards [eventually_summatory_eq_sum
    (fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal)
    (S.indicator (1 : HeightOneSpectrum (𝓞 K) → ℝ)) hS.toFinset
    fun v hv ↦ Set.indicator_of_notMem (by simpa using hv) _] with x hx
  rw [primeCount, primeSummatory_apply]
  have hsum : (∑ v ∈ primesLE K x,
      S.indicator (1 : HeightOneSpectrum (𝓞 K) → ℝ) v) =
      ∑ v ∈ hS.toFinset, S.indicator (1 : HeightOneSpectrum (𝓞 K) → ℝ) v := by
    rw [← primeSummatory_apply]
    exact hx
  rw [hsum,
    Finset.sum_congr rfl fun v hv ↦
    Set.indicator_of_mem (hS.mem_toFinset.mp hv) _, Set.ncard_eq_toFinset_card S hS]
  simp

/-- If two prime sets have finite symmetric difference, their logarithmically weighted counts
differ eventually by the fixed total discrepancy on that symmetric difference. -/
theorem eventually_primeTheta_sub_eq (hST : (symmDiff S T).Finite) :
    ∀ᶠ x in Filter.atTop, primeTheta K S x - primeTheta K T x
      = ∑ v ∈ hST.toFinset, (S.indicator (fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ)) v
          - T.indicator (fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ)) v) :=
  eventually_summatory_indicator_sub_eq _ _ hST

/-- If two prime sets have finite symmetric difference, their unweighted counts differ eventually
by the fixed total discrepancy on that symmetric difference. -/
theorem eventually_primeCount_sub_eq (hST : (symmDiff S T).Finite) :
    ∀ᶠ x in Filter.atTop, primeCount K S x - primeCount K T x
      = ∑ v ∈ hST.toFinset, (S.indicator 1 v - T.indicator 1 v) :=
  eventually_summatory_indicator_sub_eq _ _ hST

end TauCeti
