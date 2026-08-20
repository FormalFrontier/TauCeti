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
public import TauCeti.RingTheory.DedekindDomain.Ideal

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
prime to its bad primes, and `Ideal.IsPrimeTo.induction_on` factors such an ideal into
good primes; this is the engine behind both
`TauCeti.MultiplicativeIdealWeight.apply_ne_zero_iff_isGood` and
`TauCeti.UnitaryIdealWeight.norm_eq_one`.

## Main declarations

* `Ideal.IsPrimeTo`: an ideal is nonzero and no prime of `S` divides it, with its
  multiplicativity (`Ideal.isPrimeTo_mul_iff`) and its induction principle
  (`Ideal.IsPrimeTo.induction_on`);
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
  `TauCeti.UnitaryIdealWeight.norm_eq_one` on all good ideals,
  `TauCeti.UnitaryIdealWeight.ofPowEqOne` for finite-order weights, and the operations
  `TauCeti.UnitaryIdealWeight.conj`, `TauCeti.UnitaryIdealWeight.restrict` and
  `TauCeti.UnitaryIdealWeight.normTwist` (the last for the imaginary norm twists only), and
  `TauCeti.UnitaryIdealWeight.toIdealArithmeticFunction` for its passage to the general carrier;
* `TauCeti.MultiplicativeIdealWeight.map` and `TauCeti.UnitaryIdealWeight.map`, with their
  equivalences `mapEquiv`: functoriality under an isomorphism `K ≃+* L` of the ambient fields,
  together with the identity and composition laws and the compatibilities
  `TauCeti.MultiplicativeIdealWeight.badPrimes_map` and
  `TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_map`.

## Rejection tests

The two worked negative examples of this layer are proved here.
`TauCeti.MultiplicativeIdealWeight.coe_ne_const_one` says the everywhere-one function on *all*
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

namespace TauCeti

open NumberField IsDedekindDomain nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

private theorem absNorm_ne_zero_of_ne_bot {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    Ideal.absNorm I ≠ 0 := by
  simpa [Ideal.absNorm_eq_zero_iff] using hI

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
abbrev IsGood (χ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 K)) : Prop :=
  Ideal.IsPrimeTo I χ.badPrimes

/-- **A completely multiplicative ideal weight is nonzero exactly on the good ideals.** Thus the
good ideals are precisely the nonvanishing locus of the weight. -/
theorem apply_ne_zero_iff_isGood (χ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 K)) :
    χ I ≠ 0 ↔ χ.IsGood I := by
  constructor
  · intro h
    apply Ideal.isPrimeTo_iff.mpr
    constructor
    · exact fun hbot ↦ h (by simp [hbot])
    · intro 𝔭 h𝔭 ⟨J, hJ⟩
      apply h
      rw [hJ, map_mul, mem_badPrimes.mp h𝔭, zero_mul]
  · intro hI
    refine hI.induction_on (by simp) fun 𝔭 J h𝔭 _ ih ↦ ?_
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
      map_zero' := by simp
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
@[simp]
theorem ofBadPrimes_apply (hS : S.Finite) (I : Ideal (𝓞 K)) :
    ofBadPrimes S hS I = if Ideal.IsPrimeTo I S then 1 else 0 := (rfl)

@[simp]
theorem badPrimes_ofBadPrimes (hS : S.Finite) : (ofBadPrimes S hS).badPrimes = S := by
  classical
  ext 𝔭
  simp [badPrimes, ofBadPrimes_apply]

@[simp]
theorem isGood_ofBadPrimes_iff (hS : S.Finite) {I : Ideal (𝓞 K)} :
    (ofBadPrimes S hS).IsGood I ↔ Ideal.IsPrimeTo I S := by
  simp only [IsGood, badPrimes_ofBadPrimes]

/-- The pointwise product of two multiplicative ideal weights. -/
noncomputable instance : Mul (MultiplicativeIdealWeight K) where
  mul χ ψ :=
    { toMonoidWithZeroHom := χ.toMonoidWithZeroHom * ψ.toMonoidWithZeroHom
      finite_setOf_apply_eq_zero := by
        refine (χ.finite_badPrimes.union ψ.finite_badPrimes).subset fun 𝔭 h𝔭 ↦ ?_
        -- the product of two `→*₀` is built from the product of the underlying `→*`, so the
        -- value of the product is computed by `MonoidHom.mul_apply`
        have hzero : χ 𝔭.asIdeal * ψ 𝔭.asIdeal = 0 :=
          (MonoidHom.mul_apply χ.toMonoidWithZeroHom.toMonoidHom
            ψ.toMonoidWithZeroHom.toMonoidHom 𝔭.asIdeal).symm.trans h𝔭
        exact mul_eq_zero.mp hzero }

@[simp]
theorem mul_apply (χ ψ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 K)) :
    (χ * ψ) I = χ I * ψ I := (rfl)

/-- The trivial multiplicative ideal weight. -/
noncomputable instance : One (MultiplicativeIdealWeight K) where
  one :=
    { toMonoidWithZeroHom := 1
      finite_setOf_apply_eq_zero := by
        refine Set.finite_empty.subset fun 𝔭 h𝔭 ↦ ?_
        exact 𝔭.ne_bot (MonoidWithZeroHom.one_apply_eq_zero_iff.mp h𝔭) }

/-- The trivial weight is the indicator of the nonzero ideals. -/
@[simp]
theorem one_apply (I : Ideal (𝓞 K)) :
    (1 : MultiplicativeIdealWeight K) I = if I = ⊥ then 0 else 1 := by
  split_ifs with hI
  · subst I
    simp
  · exact MonoidWithZeroHom.one_apply_of_ne_zero hI

@[simp]
theorem badPrimes_one : (1 : MultiplicativeIdealWeight K).badPrimes = ∅ := by
  ext 𝔭
  simp [badPrimes, one_apply, 𝔭.ne_bot]

@[simp]
theorem badPrimes_mul (χ ψ : MultiplicativeIdealWeight K) :
    (χ * ψ).badPrimes = χ.badPrimes ∪ ψ.badPrimes := by
  ext 𝔭
  simp [badPrimes, mul_eq_zero]

/-- The pointwise product of multiplicative ideal weights, with the trivial weight as unit.
Ideal convolution (roadmap Layer 2) will instead be an operation on
`TauCeti.IdealArithmeticFunction`. -/
noncomputable instance : CommMonoid (MultiplicativeIdealWeight K) where
  mul_assoc χ ψ ω := by ext I; simp [mul_assoc]
  one_mul χ := by
    ext I
    rcases eq_or_ne I ⊥ with rfl | hI
    · simp
    · simp [one_apply, hI]
  mul_one χ := by
    ext I
    rcases eq_or_ne I ⊥ with rfl | hI
    · simp
    · simp [one_apply, hI]
  mul_comm χ ψ := by ext I; simp [mul_comm]
  npow := npowRec
  npow_zero := by intros; rfl
  npow_succ := by intros; rfl

@[simp]
theorem isGood_one_iff {I : Ideal (𝓞 K)} :
    (1 : MultiplicativeIdealWeight K).IsGood I ↔ I ≠ ⊥ := by
  simp only [IsGood, badPrimes_one, Ideal.isPrimeTo_empty]

/-- **Restriction away from a finite set of primes**: `χ` is left unchanged on the ideals prime
to `S` and set to `0` on the others. -/
noncomputable def restrict (χ : MultiplicativeIdealWeight K)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) : MultiplicativeIdealWeight K :=
  χ * ofBadPrimes S hS

open scoped Classical in
@[simp]
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
    simpa [badPrimes, MonoidWithZeroHom.comp_apply] using h𝔭

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
      exact_mod_cast absNorm_ne_zero_of_ne_bot 𝔭.ne_bot
    have h' : χ 𝔭.asIdeal * ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ℂ) ^ (-z) = 0 := by
      simpa [badPrimes] using h𝔭
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
  have h := absNorm_ne_zero_of_ne_bot 𝔭.ne_bot
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
      exact_mod_cast absNorm_ne_zero_of_ne_bot hI
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
  have hI : (I : Ideal (𝓞 K)) ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  simp [one_apply, hI]

@[simp]
theorem toIdealArithmeticFunction_mul (χ ψ : MultiplicativeIdealWeight K) :
    (χ * ψ).toIdealArithmeticFunction =
      χ.toIdealArithmeticFunction * ψ.toIdealArithmeticFunction := by
  ext I
  simp

/-- **Rejection test.** The everywhere-one function on *all* integral ideals underlies no
multiplicative ideal weight, since `Ideal (𝓞 K) →*₀ ℂ` forces the value `0` at `⊥`. The
everywhere-one function on the *nonzero* ideals is the trivial weight
(`TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_one`). -/
theorem coe_ne_const_one (χ : MultiplicativeIdealWeight K) :
    ⇑χ ≠ Function.const _ 1 := by
  intro h
  simpa using congrFun h ⊥

/-!
### Functoriality under an isomorphism of fields
-/

section Transport

variable {L M : Type*} [Field L] [NumberField L] [Field M] [NumberField M]

omit [NumberField K] [NumberField L] in
private theorem asIdeal_equivOfRingEquiv_symm (e : K ≃+* L) (𝔮 : HeightOneSpectrum (𝓞 L)) :
    ((HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)).symm 𝔮).asIdeal =
      Ideal.comap (RingOfIntegers.mapRingEquiv e) 𝔮.asIdeal := rfl

/-- **Transport along an isomorphism of fields.** An isomorphism `e : K ≃+* L` carries a
multiplicative ideal weight on `K` to one on `L`, by pulling ideals of `𝓞 L` back to `𝓞 K`
along `NumberField.RingOfIntegers.mapRingEquiv e`. -/
noncomputable def map (e : K ≃+* L) (χ : MultiplicativeIdealWeight K) :
    MultiplicativeIdealWeight L where
  toMonoidWithZeroHom := χ.toMonoidWithZeroHom.comp
    (Ideal.mapHom (RingOfIntegers.mapRingEquiv e).symm).toMonoidWithZeroHom
  finite_setOf_apply_eq_zero := by
    refine (χ.finite_badPrimes.image
      (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e))).subset fun 𝔮 h𝔮 ↦ ?_
    refine ⟨_, ?_, Equiv.apply_symm_apply _ 𝔮⟩
    rw [mem_badPrimes, asIdeal_equivOfRingEquiv_symm]
    simpa [badPrimes] using h𝔮

@[simp]
theorem map_apply (e : K ≃+* L) (χ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 L)) :
    map e χ I = χ (Ideal.comap (RingOfIntegers.mapRingEquiv e) I) :=
  congrArg ⇑χ (Ideal.map_symm (RingOfIntegers.mapRingEquiv e))

/-- **The bad primes transport too**: they are carried along by the induced bijection of
height-one spectra. -/
@[simp]
theorem badPrimes_map (e : K ≃+* L) (χ : MultiplicativeIdealWeight K) :
    (map e χ).badPrimes =
      HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) '' χ.badPrimes := by
  ext 𝔮
  rw [Equiv.image_eq_preimage_symm, Set.mem_preimage, mem_badPrimes, mem_badPrimes,
    asIdeal_equivOfRingEquiv_symm, map_apply]

@[simp]
theorem toIdealArithmeticFunction_map (e : K ≃+* L) (χ : MultiplicativeIdealWeight K) :
    (map e χ).toIdealArithmeticFunction =
      IdealArithmeticFunction.map e χ.toIdealArithmeticFunction :=
  IdealArithmeticFunction.zeroExtend_injective <| funext fun I ↦ by
    rw [zeroExtend_toIdealArithmeticFunction, IdealArithmeticFunction.zeroExtend_map,
      zeroExtend_toIdealArithmeticFunction, map_apply]

@[simp]
theorem map_id (χ : MultiplicativeIdealWeight K) : map (RingEquiv.refl K) χ = χ :=
  toIdealArithmeticFunction_injective <| by
    rw [toIdealArithmeticFunction_map, IdealArithmeticFunction.map_id]

/-- **Transport is functorial**: transporting along `e` and then along `e'` is the same as
transporting along `e.trans e'`. -/
theorem map_map (e : K ≃+* L) (e' : L ≃+* M) (χ : MultiplicativeIdealWeight K) :
    map e' (map e χ) = map (e.trans e') χ :=
  toIdealArithmeticFunction_injective <| by
    rw [toIdealArithmeticFunction_map, toIdealArithmeticFunction_map,
      toIdealArithmeticFunction_map, IdealArithmeticFunction.map_map]

/-- **Transport along an isomorphism of fields, as an equivalence** of the two carriers, with
inverse the transport along `e.symm`. -/
noncomputable def mapEquiv (e : K ≃+* L) :
    MultiplicativeIdealWeight K ≃ MultiplicativeIdealWeight L where
  toFun := map e
  invFun := map e.symm
  left_inv χ := by rw [map_map, e.self_trans_symm, map_id]
  right_inv χ := by rw [map_map, e.symm_trans_self, map_id]

@[simp]
theorem mapEquiv_apply (e : K ≃+* L) (χ : MultiplicativeIdealWeight K) :
    mapEquiv e χ = map e χ := (rfl)

@[simp]
theorem mapEquiv_symm_apply (e : K ≃+* L) (χ : MultiplicativeIdealWeight L) :
    (mapEquiv e).symm χ = map e.symm χ := (rfl)

end Transport

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

/-- **A unitary weight has modulus one on every good ideal**, extending its defining condition
from good primes to the entire good-ideal locus. -/
theorem norm_eq_one (χ : UnitaryIdealWeight K) {I : Ideal (𝓞 K)} (hI : χ.1.IsGood I) :
    ‖χ.1 I‖ = 1 := by
  refine hI.induction_on (by simp) fun 𝔭 J h𝔭 _ ih ↦ ?_
  rw [map_mul, norm_mul, χ.2 𝔭 h𝔭, ih, one_mul]

/-- The trivial weight is unitary. -/
noncomputable instance : One (UnitaryIdealWeight K) :=
  ⟨1, fun 𝔭 _ ↦ by simp [MultiplicativeIdealWeight.one_apply, 𝔭.ne_bot]⟩

@[simp]
theorem val_one : (1 : UnitaryIdealWeight K).1 = 1 := rfl

/-- The pointwise product of unitary weights is unitary. -/
noncomputable instance : Mul (UnitaryIdealWeight K) where
  mul χ ψ :=
    ⟨χ.1 * ψ.1, fun 𝔭 h𝔭 ↦ by
      rw [MultiplicativeIdealWeight.badPrimes_mul, Set.mem_union, not_or] at h𝔭
      rw [MultiplicativeIdealWeight.mul_apply, norm_mul, χ.2 𝔭 h𝔭.1, ψ.2 𝔭 h𝔭.2,
        one_mul]⟩

@[simp]
theorem val_mul (χ ψ : UnitaryIdealWeight K) : (χ * ψ).1 = χ.1 * ψ.1 := rfl

/-- Pointwise multiplication makes the unitary weights a commutative monoid. -/
noncomputable instance : CommMonoid (UnitaryIdealWeight K) where
  mul_assoc χ ψ ω := Subtype.ext (by simp only [val_mul]; exact mul_assoc _ _ _)
  one_mul χ := Subtype.ext (by simp only [val_mul, val_one]; exact one_mul _)
  mul_one χ := Subtype.ext (by simp only [val_mul, val_one]; exact mul_one _)
  mul_comm χ ψ := Subtype.ext (by simp only [val_mul]; exact mul_comm _ _)
  npow := npowRec
  npow_zero := by intros; rfl
  npow_succ := by intros; rfl

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
      Nat.pos_of_ne_zero (absNorm_ne_zero_of_ne_bot 𝔭.ne_bot)
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
  rw [MultiplicativeIdealWeight.normTwist_apply, norm_mul, norm_eq_one χ hI, one_mul,
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

section Transport

variable {L M : Type*} [Field L] [NumberField L] [Field M] [NumberField M]

/-- **Transport along an isomorphism of fields preserves unitarity**: the transported weight has
the same values as `χ`, read off at the corresponding primes. -/
noncomputable def map (e : K ≃+* L) (χ : UnitaryIdealWeight K) : UnitaryIdealWeight L :=
  ⟨MultiplicativeIdealWeight.map e χ.1, fun 𝔮 h𝔮 ↦ by
    rw [MultiplicativeIdealWeight.badPrimes_map, Equiv.image_eq_preimage_symm,
      Set.mem_preimage] at h𝔮
    rw [MultiplicativeIdealWeight.map_apply,
      ← MultiplicativeIdealWeight.asIdeal_equivOfRingEquiv_symm]
    exact χ.2 _ h𝔮⟩

@[simp]
theorem val_map (e : K ≃+* L) (χ : UnitaryIdealWeight K) :
    (map e χ).1 = MultiplicativeIdealWeight.map e χ.1 := (rfl)

@[simp]
theorem map_id (χ : UnitaryIdealWeight K) : map (RingEquiv.refl K) χ = χ :=
  Subtype.ext (by rw [val_map, MultiplicativeIdealWeight.map_id])

/-- **Transport is functorial** on the unitary carrier as well. -/
theorem map_map (e : K ≃+* L) (e' : L ≃+* M) (χ : UnitaryIdealWeight K) :
    map e' (map e χ) = map (e.trans e') χ :=
  Subtype.ext (by rw [val_map, val_map, val_map, MultiplicativeIdealWeight.map_map])

/-- **Transport along an isomorphism of fields, as an equivalence** of the unitary carriers. -/
noncomputable def mapEquiv (e : K ≃+* L) : UnitaryIdealWeight K ≃ UnitaryIdealWeight L where
  toFun := map e
  invFun := map e.symm
  left_inv χ := by rw [map_map, e.self_trans_symm, map_id]
  right_inv χ := by rw [map_map, e.symm_trans_self, map_id]

@[simp]
theorem mapEquiv_apply (e : K ≃+* L) (χ : UnitaryIdealWeight K) :
    mapEquiv e χ = map e χ := (rfl)

@[simp]
theorem mapEquiv_symm_apply (e : K ≃+* L) (χ : UnitaryIdealWeight L) :
    (mapEquiv e).symm χ = map e.symm χ := (rfl)

end Transport

/-- The ideal arithmetic function underlying a unitary weight: the restriction of the
underlying multiplicative weight to the nonzero ideals. -/
def toIdealArithmeticFunction (χ : UnitaryIdealWeight K) : IdealArithmeticFunction K :=
  χ.1.toIdealArithmeticFunction

@[simp]
theorem toIdealArithmeticFunction_apply (χ : UnitaryIdealWeight K) (I : (Ideal (𝓞 K))⁰) :
    χ.toIdealArithmeticFunction I = χ.1 I := (rfl)

/-- A unitary weight is recovered from its underlying ideal arithmetic function by extending
by zero, just as in `TauCeti.MultiplicativeIdealWeight.zeroExtend_toIdealArithmeticFunction`. -/
@[simp]
theorem zeroExtend_toIdealArithmeticFunction (χ : UnitaryIdealWeight K) :
    χ.toIdealArithmeticFunction.zeroExtend = ⇑χ.1 :=
  χ.1.zeroExtend_toIdealArithmeticFunction

/-- **A unitary weight is determined by its ideal arithmetic function.** -/
theorem toIdealArithmeticFunction_injective :
    Function.Injective
      (toIdealArithmeticFunction : UnitaryIdealWeight K → IdealArithmeticFunction K) :=
  fun _ _ h ↦ Subtype.ext (MultiplicativeIdealWeight.toIdealArithmeticFunction_injective h)

end UnitaryIdealWeight

end TauCeti
