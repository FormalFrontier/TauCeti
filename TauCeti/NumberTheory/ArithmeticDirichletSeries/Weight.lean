/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Defs

/-!
# Completely multiplicative ideal weights

The completely multiplicative specializations of `TauCeti.IdealArithmeticFunction`: the two
carriers on which every Euler product, Hecke character and character-family argument of this
development is stated.

A `TauCeti.MultiplicativeIdealWeight K` is a monoid-with-zero homomorphism
`Ideal (𝓞 K) →*₀ ℂ` killing only finitely many height-one primes, and
`TauCeti.UnitaryIdealWeight K` is the subtype of those whose values have modulus `1` away from
that finite bad set. Using Mathlib's `→*₀` vocabulary is what pins the zero-ideal law
`χ ⊥ = 0`; the finiteness condition is what bounds the bad local factors of the Euler product.

Both carriers are *degree one*: the value at `𝔭 ^ n` is forced to be `χ 𝔭 ^ n`. They are
therefore deliberately too narrow for the ideal Möbius function or for coefficient systems
whose prime-power values are independent local data; those get separate carriers.

The organising notion is `Ideal.IsPrimeTo`, an ideal of a Dedekind domain being nonzero and
divisible by no prime of a given set; it is stated for a general Dedekind domain because
nothing in it is specific to a number field. The good ideals of a weight are the ideals
prime to its bad primes, and `Ideal.IsPrimeTo.induction` factors such an ideal into
good primes; this is the engine behind both
`TauCeti.MultiplicativeIdealWeight.apply_ne_zero_iff_isGood` and
`TauCeti.UnitaryIdealWeight.norm_apply`.

## Main declarations

* `Ideal.IsPrimeTo`: an ideal is nonzero and no prime of `S` divides it, with its
  multiplicativity (`Ideal.isPrimeTo_mul_iff`) and its induction principle
  (`Ideal.IsPrimeTo.induction`);
* `IsDedekindDomain.HeightOneSpectrum.asIdeal_dvd_asIdeal_iff`: divisibility between
  height-one primes is equality;
* `TauCeti.MultiplicativeIdealWeight`: the general completely multiplicative carrier, its
  `TauCeti.MultiplicativeIdealWeight.badPrimes` and its good ideals
  (`TauCeti.MultiplicativeIdealWeight.IsGood`);
* `TauCeti.MultiplicativeIdealWeight.apply_ne_zero_iff_isGood`: a weight is nonzero exactly on
  the good ideals;
* `TauCeti.MultiplicativeIdealWeight.ofBadPrimes`, the pointwise `CommMonoid` structure (whose
  unit is the trivial weight), `TauCeti.MultiplicativeIdealWeight.restrict`,
  `TauCeti.MultiplicativeIdealWeight.conj` and
  `TauCeti.MultiplicativeIdealWeight.normTwist`: the constructors and operations;
* `TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction`: passage to the general
  carrier, inverted by `TauCeti.IdealArithmeticFunction.zeroExtend`;
* `TauCeti.UnitaryIdealWeight`: the unitary subtype, with
  `TauCeti.UnitaryIdealWeight.norm_apply` on all good ideals,
  `TauCeti.UnitaryIdealWeight.ofPowEqOne` for finite-order weights, and the operations
  `TauCeti.UnitaryIdealWeight.conj`, `TauCeti.UnitaryIdealWeight.restrict` and
  `TauCeti.UnitaryIdealWeight.normTwist` (the last for the imaginary norm twists only).

## Rejection tests

The two worked negative examples of this layer are proved here.
`TauCeti.MultiplicativeIdealWeight.coe_ne_one` says the everywhere-one function on *all*
integral ideals underlies no weight, because `→*₀` forces the value `0` at `⊥` — the
everywhere-one function on the *nonzero* ideals is the trivial weight instead
(`TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_one`).
`TauCeti.UnitaryIdealWeight.norm_normTwist_apply_ne_one` says that a norm twist with
`Re z ≠ 0` changes the modulus at every good ideal of absolute norm greater than one, so such
twists live only in the general carrier.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- Divisibility between height-one primes of a Dedekind domain is equality: the only
height-one prime dividing `𝔮` is `𝔮` itself. -/
theorem asIdeal_dvd_asIdeal_iff {𝔭 𝔮 : HeightOneSpectrum R} :
    𝔭.asIdeal ∣ 𝔮.asIdeal ↔ 𝔭 = 𝔮 :=
  ⟨fun h ↦ asIdeal_injective (associated_iff_eq.mp (𝔭.prime.associated_of_dvd 𝔮.prime h)),
    fun h ↦ h ▸ dvd_rfl⟩

end IsDedekindDomain.HeightOneSpectrum

namespace Ideal

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- An ideal of a Dedekind domain is **prime to** a set `S` of height-one primes when it is
nonzero and no prime of `S` divides it. Nonzeroness is part of the definition, so `⊥` is prime
to no set at all — not even to `∅`. -/
def IsPrimeTo (I : Ideal R) (S : Set (HeightOneSpectrum R)) : Prop :=
  I ≠ ⊥ ∧ ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I

variable {I J : Ideal R} {S T : Set (HeightOneSpectrum R)}

omit [IsDedekindDomain R] in
theorem IsPrimeTo.ne_bot (h : IsPrimeTo I S) : I ≠ ⊥ := h.1

omit [IsDedekindDomain R] in
theorem IsPrimeTo.not_dvd (h : IsPrimeTo I S) {𝔭 : HeightOneSpectrum R} (h𝔭 : 𝔭 ∈ S) :
    ¬ 𝔭.asIdeal ∣ I := h.2 𝔭 h𝔭

omit [IsDedekindDomain R] in
/-- The zero ideal is prime to no set of primes, not even to the empty set. -/
theorem not_isPrimeTo_bot : ¬ IsPrimeTo (⊥ : Ideal R) S := fun h ↦ h.ne_bot rfl

@[simp]
theorem isPrimeTo_top : IsPrimeTo (⊤ : Ideal R) S := by
  refine ⟨top_ne_bot, fun 𝔭 _ hdvd ↦ 𝔭.prime.not_isUnit ?_⟩
  exact isUnit_of_dvd_one (by simpa [Ideal.one_eq_top] using hdvd)

omit [IsDedekindDomain R] in
theorem IsPrimeTo.mono (hST : S ⊆ T) (h : IsPrimeTo I T) : IsPrimeTo I S :=
  ⟨h.ne_bot, fun _𝔭 h𝔭 ↦ h.not_dvd (hST h𝔭)⟩

@[simp]
theorem isPrimeTo_mul_iff : IsPrimeTo (I * J) S ↔ IsPrimeTo I S ∧ IsPrimeTo J S := by
  simp only [IsPrimeTo, ne_eq, Ideal.mul_eq_bot, not_or]
  refine ⟨fun ⟨h0, h⟩ ↦ ⟨⟨h0.1, fun 𝔭 h𝔭 hdvd ↦ h 𝔭 h𝔭 (hdvd.mul_right _)⟩,
    ⟨h0.2, fun 𝔭 h𝔭 hdvd ↦ h 𝔭 h𝔭 (hdvd.mul_left _)⟩⟩, fun ⟨hI, hJ⟩ ↦ ⟨⟨hI.1, hJ.1⟩, ?_⟩⟩
  intro 𝔭 h𝔭 hdvd
  rcases 𝔭.prime.dvd_mul.mp hdvd with h | h
  · exact hI.2 𝔭 h𝔭 h
  · exact hJ.2 𝔭 h𝔭 h

@[simp]
theorem isPrimeTo_asIdeal_iff {𝔭 : HeightOneSpectrum R} :
    IsPrimeTo 𝔭.asIdeal S ↔ 𝔭 ∉ S := by
  refine ⟨fun h h𝔭 ↦ h.not_dvd h𝔭 dvd_rfl, fun h𝔭 ↦ ⟨𝔭.ne_bot, fun 𝔮 h𝔮 hdvd ↦ h𝔭 ?_⟩⟩
  rwa [HeightOneSpectrum.asIdeal_dvd_asIdeal_iff.mp hdvd] at h𝔮

/-- **Induction on ideals prime to `S`.** Such an ideal is a finite product of height-one
primes outside `S`, so a property holding at `⊤` and stable under multiplication by a
height-one prime outside `S` holds for all of them. -/
@[elab_as_elim]
theorem IsPrimeTo.induction {motive : Ideal R → Prop} (h : IsPrimeTo I S)
    (top : motive ⊤)
    (mul_prime : ∀ (𝔭 : HeightOneSpectrum R) (J : Ideal R), 𝔭 ∉ S →
      IsPrimeTo J S → motive J → motive (𝔭.asIdeal * J)) :
    motive I := by
  revert h
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun h ↦ absurd rfl h.ne_bot
  | h₂ x hx => exact fun _ ↦ (Ideal.isUnit_iff.mp hx) ▸ top
  | h₃ J p _ hp ih =>
      intro hprime
      have hJ : IsPrimeTo J S := (isPrimeTo_mul_iff.mp hprime).2
      have hbad : HeightOneSpectrum.ofPrime hp ∉ S :=
        fun h ↦ hprime.2 _ h (dvd_mul_right p J)
      exact mul_prime (HeightOneSpectrum.ofPrime hp) J hbad hJ (ih hJ)

end Ideal

namespace TauCeti

open NumberField IsDedekindDomain nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-!
### The general carrier of completely multiplicative ideal weights
-/

/-- A **multiplicative ideal weight** on a number field `K`: a completely multiplicative
complex-valued function on *all* integral ideals of `𝓞 K`, packaged as a monoid-with-zero
homomorphism `Ideal (𝓞 K) →*₀ ℂ`, which kills only finitely many height-one primes.

Being a `→*₀` forces the value `0` at the zero ideal `⊥` and the value `1` at `⊤`; the
finiteness condition is what makes the associated Euler product have finitely many bad local
factors. This carrier is *degree one*: its value at a prime power `𝔭 ^ n` is forced to be
`χ 𝔭 ^ n`, so it excludes the ideal Möbius function and any coefficient system whose
prime-power values are independent local data. -/
structure MultiplicativeIdealWeight (K : Type*) [Field K] [NumberField K] where
  /-- The underlying completely multiplicative map on all integral ideals. -/
  toMonoidWithZeroHom : Ideal (𝓞 K) →*₀ ℂ
  /-- Only finitely many height-one primes are killed. -/
  finite_setOf_apply_eq_zero :
    {𝔭 : HeightOneSpectrum (𝓞 K) | toMonoidWithZeroHom 𝔭.asIdeal = 0}.Finite

namespace MultiplicativeIdealWeight

instance : FunLike (MultiplicativeIdealWeight K) (Ideal (𝓞 K)) ℂ where
  coe χ := χ.toMonoidWithZeroHom
  coe_injective χ ψ h := by
    cases χ; cases ψ
    congr 1
    exact DFunLike.coe_injective h

instance : MonoidWithZeroHomClass (MultiplicativeIdealWeight K) (Ideal (𝓞 K)) ℂ where
  map_zero χ := χ.toMonoidWithZeroHom.map_zero
  map_one χ := χ.toMonoidWithZeroHom.map_one
  map_mul χ := χ.toMonoidWithZeroHom.map_mul

@[simp]
theorem coe_toMonoidWithZeroHom (χ : MultiplicativeIdealWeight K) :
    ⇑χ.toMonoidWithZeroHom = ⇑χ := rfl

@[ext]
theorem ext {χ ψ : MultiplicativeIdealWeight K} (h : ∀ I, χ I = ψ I) : χ = ψ :=
  DFunLike.ext _ _ h

/-- **The zero-ideal law.** Every multiplicative ideal weight kills the zero ideal, so no
weight is the everywhere-one function on all ideals. -/
@[simp]
theorem apply_bot (χ : MultiplicativeIdealWeight K) : χ ⊥ = 0 := map_zero χ

@[simp]
theorem apply_top (χ : MultiplicativeIdealWeight K) : χ ⊤ = 1 := by
  simpa using map_one χ

/-- The **bad primes** of an ideal weight: the height-one primes it kills. This is a derived,
canonically determined accessor, not extra data. -/
def badPrimes (χ : MultiplicativeIdealWeight K) : Set (HeightOneSpectrum (𝓞 K)) :=
  {𝔭 | χ 𝔭.asIdeal = 0}

@[simp]
theorem mem_badPrimes {χ : MultiplicativeIdealWeight K} {𝔭 : HeightOneSpectrum (𝓞 K)} :
    𝔭 ∈ χ.badPrimes ↔ χ 𝔭.asIdeal = 0 := Iff.rfl

theorem finite_badPrimes (χ : MultiplicativeIdealWeight K) : χ.badPrimes.Finite :=
  χ.finite_setOf_apply_eq_zero

variable {χ : MultiplicativeIdealWeight K}

/-- An ideal is **good** for `χ` when it is prime to the bad primes of `χ`. In particular a
good ideal is nonzero, even when `χ` has no bad primes at all. -/
def IsGood (χ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 K)) : Prop :=
  Ideal.IsPrimeTo I χ.badPrimes

theorem isGood_iff {I : Ideal (𝓞 K)} : χ.IsGood I ↔ Ideal.IsPrimeTo I χ.badPrimes := Iff.rfl

theorem IsGood.ne_bot {I : Ideal (𝓞 K)} (h : χ.IsGood I) : I ≠ ⊥ := h.1

theorem not_isGood_bot : ¬ χ.IsGood ⊥ := Ideal.not_isPrimeTo_bot

@[simp]
theorem isGood_top : χ.IsGood ⊤ := Ideal.isPrimeTo_top

@[simp]
theorem isGood_mul_iff {I J : Ideal (𝓞 K)} :
    χ.IsGood (I * J) ↔ χ.IsGood I ∧ χ.IsGood J := Ideal.isPrimeTo_mul_iff

@[simp]
theorem isGood_asIdeal_iff {𝔭 : HeightOneSpectrum (𝓞 K)} :
    χ.IsGood 𝔭.asIdeal ↔ χ 𝔭.asIdeal ≠ 0 :=
  Ideal.isPrimeTo_asIdeal_iff

/-- **A completely multiplicative ideal weight is nonzero exactly on the good ideals.** The
easy direction is that a bad prime factor, or the zero ideal itself, forces the value `0`; the
substantial direction factors a good ideal into good primes. -/
theorem apply_ne_zero_iff_isGood (χ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 K)) :
    χ I ≠ 0 ↔ χ.IsGood I := by
  refine ⟨fun h ↦ ⟨fun hbot ↦ h (by simp [hbot]), fun 𝔭 h𝔭 ⟨J, hJ⟩ ↦ h ?_⟩, fun hI ↦ ?_⟩
  · rw [hJ, map_mul, mem_badPrimes.mp h𝔭, zero_mul]
  · refine hI.induction (by simp) fun 𝔭 J h𝔭 _ ih ↦ ?_
    exact (map_mul χ _ _).trans_ne (mul_ne_zero h𝔭 ih)

theorem apply_eq_zero_iff_not_isGood (χ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 K)) :
    χ I = 0 ↔ ¬ χ.IsGood I := by
  rw [← not_ne_iff, χ.apply_ne_zero_iff_isGood]

/-!
### Constructors and operations
-/

section Operations

variable {S : Set (HeightOneSpectrum (𝓞 K))}

open scoped Classical in
/-- The **indicator weight** of a finite set `S` of height-one primes: the value is `1` on the
ideals prime to `S` and `0` elsewhere. Its bad primes are exactly `S`, and `ofBadPrimes ∅` is
the trivial weight `1`. -/
noncomputable def ofBadPrimes (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    MultiplicativeIdealWeight K where
  toMonoidWithZeroHom :=
    { toFun I := if Ideal.IsPrimeTo I S then 1 else 0
      map_zero' := by simp [Ideal.not_isPrimeTo_bot]
      map_one' := by simp [Ideal.one_eq_top]
      map_mul' I J := by
        by_cases h : Ideal.IsPrimeTo (I * J) S
        · simp [h, (Ideal.isPrimeTo_mul_iff.mp h).1, (Ideal.isPrimeTo_mul_iff.mp h).2]
        · rcases not_and_or.mp (fun hc ↦ h (Ideal.isPrimeTo_mul_iff.mpr hc)) with h' | h' <;>
            simp [h, h'] }
  finite_setOf_apply_eq_zero := by
    convert hS using 1
    ext 𝔭
    simp

open scoped Classical in
/-- Defining equation of `TauCeti.MultiplicativeIdealWeight.ofBadPrimes`; its body is not
exposed. -/
theorem ofBadPrimes_apply (hS : S.Finite) (I : Ideal (𝓞 K)) :
    ofBadPrimes S hS I = if Ideal.IsPrimeTo I S then 1 else 0 := (rfl)

@[simp]
theorem badPrimes_ofBadPrimes (hS : S.Finite) : (ofBadPrimes S hS).badPrimes = S := by
  classical
  ext 𝔭
  simp [badPrimes, ofBadPrimes_apply]

theorem isGood_ofBadPrimes_iff (hS : S.Finite) {I : Ideal (𝓞 K)} :
    (ofBadPrimes S hS).IsGood I ↔ Ideal.IsPrimeTo I S := by
  rw [isGood_iff, badPrimes_ofBadPrimes]

/-- The pointwise product of two multiplicative ideal weights, with the trivial weight — the
indicator of the nonzero ideals — as unit. Pointwise multiplication is *not* ideal convolution;
convolution lives on `TauCeti.IdealArithmeticFunction`. -/
noncomputable instance : CommMonoid (MultiplicativeIdealWeight K) where
  one := ofBadPrimes ∅ Set.finite_empty
  mul χ ψ :=
    { toMonoidWithZeroHom :=
        { toFun I := χ I * ψ I
          map_zero' := by simp
          map_one' := by simp [Ideal.one_eq_top]
          map_mul' I J := by simp only [map_mul]; ring }
      finite_setOf_apply_eq_zero := by
        refine (χ.finite_badPrimes.union ψ.finite_badPrimes).subset fun 𝔭 h𝔭 ↦ ?_
        simpa [badPrimes, mul_eq_zero] using h𝔭 }
  mul_assoc χ ψ ω := by ext I; exact mul_assoc (χ I) (ψ I) (ω I)
  one_mul χ := by
    classical
    ext I
    change ofBadPrimes (∅ : Set (HeightOneSpectrum (𝓞 K))) Set.finite_empty I * χ I = χ I
    rcases eq_or_ne I ⊥ with rfl | hI
    · simp
    · simp [ofBadPrimes_apply, Ideal.IsPrimeTo, hI]
  mul_one χ := by
    classical
    ext I
    change χ I * ofBadPrimes (∅ : Set (HeightOneSpectrum (𝓞 K))) Set.finite_empty I = χ I
    rcases eq_or_ne I ⊥ with rfl | hI
    · simp
    · simp [ofBadPrimes_apply, Ideal.IsPrimeTo, hI]
  mul_comm χ ψ := by ext I; exact mul_comm (χ I) (ψ I)

@[simp]
theorem mul_apply (χ ψ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 K)) :
    (χ * ψ) I = χ I * ψ I := (rfl)

theorem one_eq_ofBadPrimes_empty :
    (1 : MultiplicativeIdealWeight K) = ofBadPrimes ∅ Set.finite_empty := (rfl)

@[simp]
theorem badPrimes_one : (1 : MultiplicativeIdealWeight K).badPrimes = ∅ := by
  rw [one_eq_ofBadPrimes_empty, badPrimes_ofBadPrimes]

@[simp]
theorem badPrimes_mul (χ ψ : MultiplicativeIdealWeight K) :
    (χ * ψ).badPrimes = χ.badPrimes ∪ ψ.badPrimes := by
  ext 𝔭
  simp [badPrimes, mul_eq_zero]

/-- The trivial weight is the indicator of the nonzero ideals. -/
theorem one_apply (I : Ideal (𝓞 K)) :
    (1 : MultiplicativeIdealWeight K) I = if I = ⊥ then 0 else 1 := by
  classical
  rw [one_eq_ofBadPrimes_empty, ofBadPrimes_apply]
  rcases eq_or_ne I ⊥ with rfl | hI
  · simp [Ideal.not_isPrimeTo_bot]
  · simp [Ideal.IsPrimeTo, hI]

@[simp]
theorem isGood_one_iff {I : Ideal (𝓞 K)} :
    (1 : MultiplicativeIdealWeight K).IsGood I ↔ I ≠ ⊥ := by
  simp [isGood_iff, Ideal.IsPrimeTo]

/-- **Restriction away from a finite set of primes**: `χ` is left unchanged on the ideals prime
to `S` and set to `0` on the others. -/
noncomputable def restrict (χ : MultiplicativeIdealWeight K)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) : MultiplicativeIdealWeight K :=
  χ * ofBadPrimes S hS

open scoped Classical in
theorem restrict_apply (χ : MultiplicativeIdealWeight K) (hS : S.Finite) (I : Ideal (𝓞 K)) :
    χ.restrict S hS I = if Ideal.IsPrimeTo I S then χ I else 0 := by
  by_cases h : Ideal.IsPrimeTo I S <;> simp [restrict, ofBadPrimes_apply, h]

@[simp]
theorem badPrimes_restrict (χ : MultiplicativeIdealWeight K) (hS : S.Finite) :
    (χ.restrict S hS).badPrimes = χ.badPrimes ∪ S := by
  simp [restrict]

/-- The **conjugate weight** `I ↦ conj (χ I)`. -/
def conj (χ : MultiplicativeIdealWeight K) : MultiplicativeIdealWeight K where
  toMonoidWithZeroHom := ((starRingEnd ℂ) : ℂ →+* ℂ).toMonoidWithZeroHom.comp
    χ.toMonoidWithZeroHom
  finite_setOf_apply_eq_zero := χ.finite_badPrimes.subset fun 𝔭 h𝔭 ↦ by
    have h : (starRingEnd ℂ) (χ 𝔭.asIdeal) = 0 := h𝔭
    simpa [badPrimes] using h

@[simp]
theorem conj_apply (χ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 K)) :
    χ.conj I = starRingEnd ℂ (χ I) := (rfl)

@[simp]
theorem badPrimes_conj (χ : MultiplicativeIdealWeight K) : χ.conj.badPrimes = χ.badPrimes := by
  ext 𝔭
  simp [badPrimes]

@[simp]
theorem conj_conj (χ : MultiplicativeIdealWeight K) : χ.conj.conj = χ := by
  ext I
  simp

/-- The **norm twist** `I ↦ χ I * N(I) ^ (-z)`. For general `z` this leaves the unitary
carrier; only the purely imaginary twists preserve it
(`TauCeti.UnitaryIdealWeight.normTwist`). -/
noncomputable def normTwist (z : ℂ) (χ : MultiplicativeIdealWeight K) :
    MultiplicativeIdealWeight K where
  toMonoidWithZeroHom :=
    { toFun I := χ I * (Ideal.absNorm I : ℂ) ^ (-z)
      map_zero' := by simp
      map_one' := by simp
      map_mul' I J := by
        rw [map_mul, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
        ring }
  finite_setOf_apply_eq_zero := χ.finite_badPrimes.subset fun 𝔭 h𝔭 ↦ by
    have h : ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ℂ) ≠ 0 := by
      simpa [Ideal.absNorm_eq_zero_iff] using 𝔭.ne_bot
    have h' : χ 𝔭.asIdeal * ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ℂ) ^ (-z) = 0 := h𝔭
    rcases mul_eq_zero.mp h' with h₁ | h₂
    · exact h₁
    · exact absurd ((Complex.cpow_eq_zero_iff _ _).mp h₂).1 h

@[simp]
theorem normTwist_apply (z : ℂ) (χ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 K)) :
    normTwist z χ I = χ I * (Ideal.absNorm I : ℂ) ^ (-z) := (rfl)

@[simp]
theorem badPrimes_normTwist (z : ℂ) (χ : MultiplicativeIdealWeight K) :
    (normTwist z χ).badPrimes = χ.badPrimes := by
  ext 𝔭
  have h : Ideal.absNorm 𝔭.asIdeal ≠ 0 := by
    simpa [Ideal.absNorm_eq_zero_iff] using 𝔭.ne_bot
  simp [badPrimes, mul_eq_zero, Complex.cpow_eq_zero_iff, h]

@[simp]
theorem normTwist_zero (χ : MultiplicativeIdealWeight K) : normTwist 0 χ = χ := by
  ext I
  simp

theorem normTwist_normTwist (z w : ℂ) (χ : MultiplicativeIdealWeight K) :
    normTwist z (normTwist w χ) = normTwist (z + w) χ := by
  ext I
  rcases eq_or_ne I ⊥ with rfl | hI
  · simp
  · have h : ((Ideal.absNorm I : ℕ) : ℂ) ≠ 0 := by
      simpa [Ideal.absNorm_eq_zero_iff] using hI
    rw [normTwist_apply, normTwist_apply, normTwist_apply, neg_add, Complex.cpow_add _ _ h]
    ring

end Operations

/-!
### Passage to the general carrier, and the zero-ideal rejection test
-/

/-- The ideal arithmetic function underlying an ideal weight: its restriction to the nonzero
ideals. -/
def toIdealArithmeticFunction (χ : MultiplicativeIdealWeight K) : IdealArithmeticFunction K :=
  fun I ↦ χ I

@[simp]
theorem toIdealArithmeticFunction_apply (χ : MultiplicativeIdealWeight K) (I : (Ideal (𝓞 K))⁰) :
    χ.toIdealArithmeticFunction I = χ I := (rfl)

/-- An ideal weight is recovered from its restriction to the nonzero ideals by extending by
zero: the zero-ideal law `χ ⊥ = 0` is exactly what makes this work. -/
@[simp]
theorem zeroExtend_toIdealArithmeticFunction (χ : MultiplicativeIdealWeight K) :
    χ.toIdealArithmeticFunction.zeroExtend = ⇑χ := by
  ext I
  rcases eq_or_ne I ⊥ with rfl | hI
  · simp
  · simp [IdealArithmeticFunction.zeroExtend_of_ne_bot _ hI]

theorem toIdealArithmeticFunction_injective :
    Function.Injective
      (toIdealArithmeticFunction : MultiplicativeIdealWeight K → IdealArithmeticFunction K) := by
  intro χ ψ h
  exact DFunLike.coe_injective (by
    rw [← zeroExtend_toIdealArithmeticFunction χ, ← zeroExtend_toIdealArithmeticFunction ψ, h])

@[simp]
theorem toIdealArithmeticFunction_one :
    (1 : MultiplicativeIdealWeight K).toIdealArithmeticFunction = 1 := by
  ext I
  simp [one_apply, (Ideal.mem_nonZeroDivisors_iff_ne_bot.mp I.2)]

/-- **Rejection test.** The everywhere-one function on *all* integral ideals underlies no
multiplicative ideal weight, since `Ideal (𝓞 K) →*₀ ℂ` forces the value `0` at `⊥`. The
everywhere-one function on the *nonzero* ideals is the trivial weight
(`TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_one`). -/
theorem coe_ne_one (χ : MultiplicativeIdealWeight K) : ⇑χ ≠ 1 := by
  intro h
  simpa using congrFun h ⊥

end MultiplicativeIdealWeight

/-!
### The unitary subtype
-/

/-- A **unitary ideal weight**: a multiplicative ideal weight whose values have modulus `1`
away from its bad primes. Finite-order Hecke characters land here
(`TauCeti.UnitaryIdealWeight.ofPowEqOne`), and so do the purely imaginary norm twists
(`TauCeti.UnitaryIdealWeight.normTwist`); a norm twist with `Re z ≠ 0` does not
(`TauCeti.UnitaryIdealWeight.norm_normTwist_apply_ne_one`). -/
abbrev UnitaryIdealWeight (K : Type*) [Field K] [NumberField K] : Type _ :=
  {χ : MultiplicativeIdealWeight K //
    ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭 ∉ χ.badPrimes → ‖χ 𝔭.asIdeal‖ = 1}

namespace UnitaryIdealWeight

/-- The defining property of a unitary weight: modulus `1` at every good prime. -/
theorem norm_apply_asIdeal (χ : UnitaryIdealWeight K) {𝔭 : HeightOneSpectrum (𝓞 K)}
    (h𝔭 : 𝔭 ∉ χ.1.badPrimes) : ‖χ.1 𝔭.asIdeal‖ = 1 := χ.2 𝔭 h𝔭

/-- **A unitary weight has modulus one on every good ideal**, not just on the good primes:
complete multiplicativity propagates the condition along the prime factorization. -/
theorem norm_apply (χ : UnitaryIdealWeight K) {I : Ideal (𝓞 K)} (hI : χ.1.IsGood I) :
    ‖χ.1 I‖ = 1 := by
  refine hI.induction (by simp) fun 𝔭 J h𝔭 _ ih ↦ ?_
  rw [map_mul, norm_mul, χ.2 𝔭 h𝔭, ih, one_mul]

/-- The trivial weight is unitary. -/
noncomputable instance : One (UnitaryIdealWeight K) :=
  ⟨1, fun 𝔭 _ ↦ by simp [MultiplicativeIdealWeight.one_apply, 𝔭.ne_bot]⟩

@[simp]
theorem val_one : (1 : UnitaryIdealWeight K).1 = 1 := rfl

/-- **Finite-order weights are unitary.** If a positive power of `χ` takes the value `1` at
every good prime — as for a finite-order Hecke character — then `χ` is unitary. -/
def ofPowEqOne (χ : MultiplicativeIdealWeight K) {n : ℕ} (hn : n ≠ 0)
    (h : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭 ∉ χ.badPrimes → χ 𝔭.asIdeal ^ n = 1) :
    UnitaryIdealWeight K :=
  ⟨χ, fun 𝔭 h𝔭 ↦ by
    refine (pow_left_inj₀ (norm_nonneg _) zero_le_one hn).mp ?_
    rw [← norm_pow, h 𝔭 h𝔭, norm_one, one_pow]⟩

@[simp]
theorem val_ofPowEqOne (χ : MultiplicativeIdealWeight K) {n : ℕ} (hn : n ≠ 0)
    (h : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭 ∉ χ.badPrimes → χ 𝔭.asIdeal ^ n = 1) :
    (ofPowEqOne χ hn h).1 = χ := (rfl)

/-- **Imaginary norm twists preserve unitarity.** For `Re z = 0` the factor `N(I) ^ (-z)` has
modulus `1`, so the twisted weight is again unitary. -/
noncomputable def normTwist (z : ℂ) (hz : z.re = 0) (χ : UnitaryIdealWeight K) :
    UnitaryIdealWeight K :=
  ⟨MultiplicativeIdealWeight.normTwist z χ.1, fun 𝔭 h𝔭 ↦ by
    have hN : 0 < Ideal.absNorm 𝔭.asIdeal :=
      Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using 𝔭.ne_bot)
    rw [MultiplicativeIdealWeight.normTwist_apply, norm_mul, χ.2 𝔭 (by simpa using h𝔭),
      one_mul, Complex.norm_natCast_cpow_of_pos hN, Complex.neg_re, hz, neg_zero,
      Real.rpow_zero]⟩

@[simp]
theorem val_normTwist (z : ℂ) (hz : z.re = 0) (χ : UnitaryIdealWeight K) :
    (normTwist z hz χ).1 = MultiplicativeIdealWeight.normTwist z χ.1 := (rfl)

/-- **Rejection test.** A norm twist with `Re z ≠ 0` leaves the unitary carrier: at every good
ideal of absolute norm greater than one its modulus differs from `1`. Such twists therefore
live only in `TauCeti.MultiplicativeIdealWeight`. -/
theorem norm_normTwist_apply_ne_one (χ : UnitaryIdealWeight K) {z : ℂ} (hz : z.re ≠ 0)
    {I : Ideal (𝓞 K)} (hI : χ.1.IsGood I) (hN : 1 < Ideal.absNorm I) :
    ‖MultiplicativeIdealWeight.normTwist z χ.1 I‖ ≠ 1 := by
  have hN' : (1 : ℝ) < (Ideal.absNorm I : ℝ) := by exact_mod_cast hN
  rw [MultiplicativeIdealWeight.normTwist_apply, norm_mul, norm_apply χ hI, one_mul,
    Complex.norm_natCast_cpow_of_pos (lt_trans Nat.one_pos hN), Complex.neg_re]
  rcases lt_trichotomy z.re 0 with h | h | h
  · exact ne_of_gt ((Real.one_lt_rpow_iff_of_pos (by linarith)).mpr (Or.inl ⟨hN', by linarith⟩))
  · exact absurd h hz
  · exact ne_of_lt (Real.rpow_lt_one_of_one_lt_of_neg hN' (by linarith))

/-- The conjugate of a unitary weight is unitary. -/
def conj (χ : UnitaryIdealWeight K) : UnitaryIdealWeight K :=
  ⟨χ.1.conj, fun 𝔭 h𝔭 ↦ by
    rw [MultiplicativeIdealWeight.badPrimes_conj] at h𝔭
    simpa using χ.2 𝔭 h𝔭⟩

@[simp]
theorem val_conj (χ : UnitaryIdealWeight K) : (conj χ).1 = χ.1.conj := (rfl)

/-- Restricting a unitary weight away from a finite set of primes keeps it unitary: the
restricted weight is unchanged at the primes that are good for it. -/
noncomputable def restrict (χ : UnitaryIdealWeight K) (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : S.Finite) : UnitaryIdealWeight K :=
  ⟨χ.1.restrict S hS, fun 𝔭 h𝔭 ↦ by
    rw [MultiplicativeIdealWeight.badPrimes_restrict, Set.mem_union, not_or] at h𝔭
    rw [MultiplicativeIdealWeight.restrict_apply]
    simp [h𝔭.2, χ.2 𝔭 h𝔭.1]⟩

@[simp]
theorem val_restrict (χ : UnitaryIdealWeight K) (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : S.Finite) : (restrict χ S hS).1 = χ.1.restrict S hS := (rfl)

/-- The ideal arithmetic function underlying a unitary weight. -/
def toIdealArithmeticFunction (χ : UnitaryIdealWeight K) : IdealArithmeticFunction K :=
  χ.1.toIdealArithmeticFunction

@[simp]
theorem toIdealArithmeticFunction_apply (χ : UnitaryIdealWeight K) (I : (Ideal (𝓞 K))⁰) :
    χ.toIdealArithmeticFunction I = χ.1 I := (rfl)

end UnitaryIdealWeight

end TauCeti
