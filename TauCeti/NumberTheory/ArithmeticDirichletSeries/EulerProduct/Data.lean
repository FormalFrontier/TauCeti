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
`EulerProduct/Basic.lean`. A finite bad-prime set is deliberately not stored here until a concrete
good-prime property relates such a set to the local factors.

The formal Euler-product identity follows from
`IdealArithmeticFunction.normCoeff_eq_eulerProduct`: coprime multiplicativity and unique
factorization prove that `normCoeff` is Mathlib's `ArithmeticFunction.eulerProduct` of the
canonical local factors. Analytic convergence of the evaluated factors belongs to Layer 3.3.

## Main definitions

* `TauCeti.EulerProductData` bundles a multiplicative ideal coefficient system.
* `TauCeti.EulerProductData.ofMultiplicativeIdealWeight` regards a degree-one ideal weight as
  Euler-product data.
* Pointwise multiplication, complex conjugation, and restriction away from finitely many primes
  preserve the bundle.

## Roadmap role

This supplies the algebraic coefficient-system part of Layer **3.1** ("Local data") of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`. It consumes the canonical local factors and
finite Euler product of Layer 3.2 already proved in `EulerProduct/Basic.lean`. A later Layer 3.1
prerequisite must formulate the concrete good-prime property before adding finite bad support.
Layer 3.3 then evaluates these formal local factors and passes to the analytic infinite product
under absolute convergence.

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

/-- The trivial Euler-product data is constructed from the trivial multiplicative ideal weight. -/
theorem one_eq_ofMultiplicativeIdealWeight :
    (1 : EulerProductData K) = ofMultiplicativeIdealWeight 1 := rfl

@[simp]
theorem one_apply (I : (Ideal (𝓞 K))⁰) : (1 : EulerProductData K) I = 1 := by
  rw [one_eq_ofMultiplicativeIdealWeight, ofMultiplicativeIdealWeight_apply]
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
    change star (D I * E I) = star (E I) * star (D I)
    exact star_mul (D I) (E I)

@[simp]
theorem star_apply (D : EulerProductData K) (I : (Ideal (𝓞 K))⁰) :
    (star D) I = star (D I) := (rfl)

/-- Restrict Euler-product data away from a finite set of height-one primes, leaving its
coefficients unchanged on ideals prime to that set and setting the others to zero. -/
noncomputable def restrict (D : EulerProductData K)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) : EulerProductData K :=
  D * ofMultiplicativeIdealWeight (MultiplicativeIdealWeight.ofBadPrimes S hS)

open scoped Classical in
@[simp]
theorem restrict_apply (D : EulerProductData K) {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S.Finite) (I : (Ideal (𝓞 K))⁰) :
    D.restrict S hS I = if Ideal.IsPrimeTo (I : Ideal (𝓞 K)) S then D I else 0 := by
  classical
  rw [restrict, mul_apply, ofMultiplicativeIdealWeight_apply,
    MultiplicativeIdealWeight.ofBadPrimes_apply]
  by_cases hI : Ideal.IsPrimeTo (I : Ideal (𝓞 K)) S <;> simp [hI]

end EulerProductData

end TauCeti
