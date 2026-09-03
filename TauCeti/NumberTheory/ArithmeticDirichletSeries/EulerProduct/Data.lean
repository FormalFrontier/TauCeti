/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Weight

/-!
# Euler-product coefficient data over a number field

This file bundles the algebraic input for an Euler product over the height-one primes of the ring
of integers of a number field. An `EulerProductData K` consists of an ideal arithmetic function
that is multiplicative on relatively prime nonzero ideals. The prime-power series and local
arithmetic factors are canonically derived from the function as defined in
`EulerProduct/Basic.lean`, so nothing about the local behaviour is stored: the bundle carries
exactly the one algebraic hypothesis that an Euler product consumes.

The formal Euler-product identity follows from
`IdealArithmeticFunction.normCoeff_eq_eulerProduct`: coprime multiplicativity and unique
factorization prove that `normCoeff` is Mathlib's `ArithmeticFunction.eulerProduct` of the
canonical local factors.

Two hypotheses of the classical theory are deliberately absent, because the identity proved here
does not need either. There is no distinguished finite set of exceptional primes: multiplicativity
is required on every coprime pair of nonzero ideals, and the local factor at a prime is read off
from the coefficients at its powers, good or bad. There is also no analytic input: the identity is
an equality of arithmetic functions, and the convergence of the evaluated factors to an infinite
product is a separate question.

## Main definitions

* `TauCeti.EulerProductData` bundles a multiplicative ideal coefficient system.
* `TauCeti.EulerProductData.ofMultiplicativeIdealWeight` regards a degree-one ideal weight as
  Euler-product data.
* Pointwise multiplication, complex conjugation, and restriction away from sets of primes
  preserve the bundle.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `ArithmeticFunction.ofPowerSeries` and `ArithmeticFunction.eulerProduct` APIs.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors NumberField
open IsDedekindDomain (HeightOneSpectrum)

/-- The algebraic coefficient data of an ideal Euler product. The local prime-power series is
canonically derived from `toIdealArithmeticFunction`. -/
structure EulerProductData (K : Type*) [Field K] [NumberField K] where
  /-- The coefficients indexed by nonzero integral ideals. -/
  toIdealArithmeticFunction : IdealArithmeticFunction K
  /-- Coprime multiplicativity, the exact algebraic hypothesis used by an Euler product. -/
  isMultiplicative : toIdealArithmeticFunction.IsMultiplicative

namespace EulerProductData

variable {K : Type*} [Field K] [NumberField K]

instance : CoeFun (EulerProductData K) fun _ ↦ ((Ideal (𝓞 K))⁰) → ℂ where
  coe D := D.toIdealArithmeticFunction

@[ext]
theorem ext {D E : EulerProductData K} (h : ∀ I, D I = E I) : D = E := by
  cases D with
  | mk D hD =>
    cases E with
    | mk E hE =>
      have hDE : D = E := funext h
      subst E
      rfl

/-- The canonical local power series of bundled Euler-product data at a height-one prime. -/
noncomputable def localPowerSeries (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) : PowerSeries ℂ :=
  D.toIdealArithmeticFunction.localPowerSeries P

/-- Coefficients of the bundled local power series are the prime-power values of the data. -/
@[simp]
theorem coeff_localPowerSeries (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    PowerSeries.coeff n (D.localPowerSeries P) =
      D ⟨P.asIdeal ^ n, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n P.ne_bot)⟩ :=
  IdealArithmeticFunction.coeff_localPowerSeries D.toIdealArithmeticFunction P n

/-- The canonical local arithmetic factor of bundled Euler-product data at a height-one prime. -/
noncomputable def localArithmeticFactor (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) : ArithmeticFunction ℂ :=
  D.toIdealArithmeticFunction.localArithmeticFactor P

/-- The bundled local arithmetic factor is Mathlib's arithmetic function associated to the
bundled local power series at `P`. -/
theorem localArithmeticFactor_def (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) :
    D.localArithmeticFactor P =
      ArithmeticFunction.ofPowerSeries (Ideal.absNorm P.asIdeal) (D.localPowerSeries P) :=
  IdealArithmeticFunction.localArithmeticFactor_def D.toIdealArithmeticFunction P

/-- At a power of `N(P)`, the bundled local arithmetic factor is the corresponding prime-power
coefficient. -/
@[simp]
theorem localArithmeticFactor_apply_pow (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    D.localArithmeticFactor P (Ideal.absNorm P.asIdeal ^ n) =
      D ⟨P.asIdeal ^ n, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n P.ne_bot)⟩ :=
  IdealArithmeticFunction.localArithmeticFactor_apply_pow D.toIdealArithmeticFunction P n

/-- Away from the powers of `N(P)`, the bundled local arithmetic factor vanishes. Together with
`localArithmeticFactor_apply_pow` this determines it at every natural number. -/
@[simp]
theorem localArithmeticFactor_apply_eq_zero_of_not_exists_pow_eq (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) {m : ℕ}
    (hm : ¬ ∃ n : ℕ, Ideal.absNorm P.asIdeal ^ n = m) :
    D.localArithmeticFactor P m = 0 :=
  IdealArithmeticFunction.localArithmeticFactor_apply_eq_zero_of_not_exists_pow_eq
    D.toIdealArithmeticFunction P hm

/-- The norm coefficients of bundled Euler-product data are the formal Euler product of its
canonical local arithmetic factors. -/
theorem normCoeff_eq_eulerProduct (D : EulerProductData K) :
    normCoeff K D.toIdealArithmeticFunction =
      ArithmeticFunction.eulerProduct D.localArithmeticFactor :=
  IdealArithmeticFunction.normCoeff_eq_eulerProduct D.isMultiplicative

/-- A completely multiplicative ideal weight supplies Euler-product data. -/
noncomputable def ofMultiplicativeIdealWeight (χ : MultiplicativeIdealWeight K) :
    EulerProductData K where
  toIdealArithmeticFunction := χ.toIdealArithmeticFunction
  isMultiplicative := χ.isMultiplicative_toIdealArithmeticFunction

@[simp]
theorem ofMultiplicativeIdealWeight_apply (χ : MultiplicativeIdealWeight K)
    (I : (Ideal (𝓞 K))⁰) : ofMultiplicativeIdealWeight χ I = χ I := by
  exact MultiplicativeIdealWeight.toIdealArithmeticFunction_apply χ I

/-- The pointwise product of two Euler-product coefficient systems. -/
noncomputable instance : Mul (EulerProductData K) where
  mul D E :=
    { toIdealArithmeticFunction := D.toIdealArithmeticFunction * E.toIdealArithmeticFunction
      isMultiplicative := D.isMultiplicative.mul E.isMultiplicative }

@[simp]
theorem mul_apply (D E : EulerProductData K) (I : (Ideal (𝓞 K))⁰) :
    (D * E) I = D I * E I := (rfl)

/-- The trivial ideal coefficient system as Euler-product data. -/
noncomputable instance : One (EulerProductData K) where
  one := ofMultiplicativeIdealWeight 1

@[simp]
theorem one_apply (I : (Ideal (𝓞 K))⁰) : (1 : EulerProductData K) I = 1 := by
  have hone : (1 : EulerProductData K) = ofMultiplicativeIdealWeight 1 := rfl
  rw [hone, ofMultiplicativeIdealWeight_apply]
  have hI : (I : Ideal (𝓞 K)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  simp [MultiplicativeIdealWeight.one_apply, hI]

/-- Pointwise multiplication makes Euler-product data a commutative monoid. This product remains
distinct from ideal Dirichlet convolution. -/
noncomputable instance : CommMonoid (EulerProductData K) where
  mul_assoc D E F := by ext I; simp [mul_assoc]
  one_mul D := by ext I; simp
  mul_one D := by ext I; simp
  mul_comm D E := by ext I; simp [mul_comm]
  npow := npowRec
  npow_zero := by intros; rfl
  npow_succ := by intros; rfl

/-- Complex conjugation makes Euler-product data a star monoid. -/
noncomputable instance : StarMul (EulerProductData K) where
  star D :=
    { toIdealArithmeticFunction := star D.toIdealArithmeticFunction
      isMultiplicative := D.isMultiplicative.star }
  star_involutive D := by
    ext I
    simp
  star_mul D E := by
    ext I
    -- `star_apply` cannot be used while this `StarMul` instance is still being constructed, so
    -- expose the pointwise scalar identity by definitional reduction of the bundle operations.
    change star (D I * E I) = star (E I) * star (D I)
    exact star_mul (D I) (E I)

@[simp]
theorem star_apply (D : EulerProductData K) (I : (Ideal (𝓞 K))⁰) :
    (star D) I = star (D I) := (rfl)

/-- Restrict Euler-product data away from a set of height-one primes, leaving its
coefficients unchanged on ideals prime to that set and setting the others to zero. -/
noncomputable def restrictAway (D : EulerProductData K)
    (S : Set (HeightOneSpectrum (𝓞 K))) : EulerProductData K where
  toIdealArithmeticFunction :=
    IdealArithmeticFunction.supportedPart D.toIdealArithmeticFunction Sᶜ
  isMultiplicative := D.isMultiplicative.supportedPart Sᶜ

open scoped Classical in
@[simp]
theorem restrictAway_apply (D : EulerProductData K) (S : Set (HeightOneSpectrum (𝓞 K)))
    (I : (Ideal (𝓞 K))⁰) :
    D.restrictAway S I = if Ideal.IsPrimeTo (I : Ideal (𝓞 K)) S then D I else 0 := by
  classical
  -- The bundle's `CoeFun` coercion is the `toIdealArithmeticFunction` projection, so the goal is
  -- definitionally a statement about `IdealArithmeticFunction.supportedPart`. No simp lemma
  -- exposes that projection through `restrictAway`, so reduce to it once here and then argue
  -- entirely through the `supportedPart` interface.
  change IdealArithmeticFunction.supportedPart D.toIdealArithmeticFunction Sᶜ I = _
  by_cases hI : Ideal.IsPrimeTo (I : Ideal (𝓞 K)) S
  · have hI' : Ideal.IsPrimeTo (I : Ideal (𝓞 K)) (Sᶜ)ᶜ := by
      simpa only [compl_compl] using hI
    simpa only [hI, ↓reduceIte] using
      (IdealArithmeticFunction.supportedPart_apply_of_isPrimeTo_compl
        (f := D.toIdealArithmeticFunction) (S := Sᶜ) (A := I) hI')
  · have hI' : ¬ Ideal.IsPrimeTo (I : Ideal (𝓞 K)) (Sᶜ)ᶜ := by
      simpa only [compl_compl] using hI
    simpa only [hI, ↓reduceIte] using
      (IdealArithmeticFunction.supportedPart_apply_of_not_isPrimeTo_compl
        (f := D.toIdealArithmeticFunction) (S := Sᶜ) (A := I) hI')

end EulerProductData

end TauCeti
