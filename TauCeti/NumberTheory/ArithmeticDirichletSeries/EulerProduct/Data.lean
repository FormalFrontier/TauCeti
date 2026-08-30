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
that is multiplicative on relatively prime nonzero ideals, together with an explicit finite set
of bad primes. The prime-power series and local arithmetic factors are canonically derived from
the function as defined in `EulerProduct/Basic.lean`; in particular, the bad set does not impose
an unrelated condition on the linear prime coefficients.

The formal Euler-product identity follows from
`IdealArithmeticFunction.normCoeff_eq_eulerProduct`: coprime multiplicativity and unique
factorization prove that `normCoeff` is Mathlib's `ArithmeticFunction.eulerProduct` of the
canonical local factors. Analytic convergence of the evaluated factors belongs to Layer 3.3.

## Main definitions

* `TauCeti.EulerProductData` bundles a multiplicative ideal coefficient system with finite
  bad-prime set.
* `TauCeti.EulerProductData.badPrimes` is its explicitly specified finite exceptional set.
* `TauCeti.EulerProductData.ofMultiplicativeIdealWeight` regards a degree-one ideal weight as
  Euler-product data.
* Pointwise multiplication, complex conjugation, and restriction away from finitely many primes
  preserve the bundle.

## Main results

* `TauCeti.EulerProductData.badPrimes_mul`, `badPrimes_star`, and `badPrimes_restrict` compute the
  exceptional primes under the bundled operations.

## Roadmap role

This completes Layer **3.1** ("Local data") of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`. It consumes the canonical local factors and
finite Euler product of Layer 3.2 already proved in `EulerProduct/Basic.lean`. Layer 3.3 can now
evaluate these formal local factors and pass to the analytic infinite product under absolute
convergence; that is the remaining step before Layer 7.2 can identify the all-prime logarithmic
Euler sum with the Dedekind zeta function.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `ArithmeticFunction.ofPowerSeries` and `ArithmeticFunction.eulerProduct` APIs.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors NumberField
open IsDedekindDomain (HeightOneSpectrum)

/-- The algebraic coefficient data of an ideal Euler product. The local prime-power series is
canonically derived from `toIdealArithmeticFunction`, while `badPrimes` records the finite set of
exceptional local factors without constraining the linear prime coefficients. -/
structure EulerProductData (K : Type*) [Field K] [NumberField K] where
  /-- The coefficients indexed by nonzero integral ideals. -/
  toIdealArithmeticFunction : IdealArithmeticFunction K
  /-- Coprime multiplicativity, the exact algebraic hypothesis used by an Euler product. -/
  isMultiplicative : toIdealArithmeticFunction.IsMultiplicative
  /-- The height-one primes where the local data is exceptional. -/
  badPrimes : Set (HeightOneSpectrum (𝓞 K))
  /-- The exceptional set is finite. -/
  finite_badPrimes : badPrimes.Finite

namespace EulerProductData

variable {K : Type*} [Field K] [NumberField K]

instance : CoeFun (EulerProductData K) fun _ ↦ ((Ideal (𝓞 K))⁰) → ℂ where
  coe D := D.toIdealArithmeticFunction

@[ext]
theorem ext {D E : EulerProductData K} (h : ∀ I, D I = E I)
    (hbad : D.badPrimes = E.badPrimes) : D = E := by
  cases D with
  | mk D hD S hS =>
    cases E with
    | mk E hE T hT =>
      have hDE : D = E := funext h
      subst E
      change S = T at hbad
      subst T
      rfl

/-- Evaluating the stored ideal arithmetic function agrees with evaluating the bundle. -/
@[simp]
theorem toIdealArithmeticFunction_apply (D : EulerProductData K) (I : (Ideal (𝓞 K))⁰) :
    D.toIdealArithmeticFunction I = D I := rfl

/-- A completely multiplicative ideal weight supplies Euler-product data. Its finite zero support
supplies the explicit exceptional set. -/
noncomputable def ofMultiplicativeIdealWeight (χ : MultiplicativeIdealWeight K) :
    EulerProductData K where
  toIdealArithmeticFunction := χ.toIdealArithmeticFunction
  isMultiplicative := χ.isMultiplicative_toIdealArithmeticFunction
  badPrimes := χ.badPrimes
  finite_badPrimes := χ.finite_badPrimes

@[simp]
theorem ofMultiplicativeIdealWeight_apply (χ : MultiplicativeIdealWeight K)
    (I : (Ideal (𝓞 K))⁰) : ofMultiplicativeIdealWeight χ I = χ I := by
  exact MultiplicativeIdealWeight.toIdealArithmeticFunction_apply χ I

@[simp]
theorem badPrimes_ofMultiplicativeIdealWeight (χ : MultiplicativeIdealWeight K) :
    (ofMultiplicativeIdealWeight χ).badPrimes = χ.badPrimes := by
  rw [ofMultiplicativeIdealWeight]

/-- The pointwise product of two Euler-product coefficient systems. -/
noncomputable instance : Mul (EulerProductData K) where
  mul D E :=
    { toIdealArithmeticFunction := D.toIdealArithmeticFunction * E.toIdealArithmeticFunction
      isMultiplicative := D.isMultiplicative.mul E.isMultiplicative
      badPrimes := D.badPrimes ∪ E.badPrimes
      finite_badPrimes := D.finite_badPrimes.union E.finite_badPrimes }

@[simp]
theorem mul_apply (D E : EulerProductData K) (I : (Ideal (𝓞 K))⁰) :
    (D * E) I = D I * E I := (rfl)

/-- The bad primes of a pointwise product are the union of the bad primes of its factors. -/
@[simp]
theorem badPrimes_mul (D E : EulerProductData K) :
    (D * E).badPrimes = D.badPrimes ∪ E.badPrimes := rfl

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

@[simp]
theorem badPrimes_one : (1 : EulerProductData K).badPrimes = ∅ := by
  rw [one_eq_ofMultiplicativeIdealWeight, badPrimes_ofMultiplicativeIdealWeight,
    MultiplicativeIdealWeight.badPrimes_one]

/-- Pointwise multiplication makes Euler-product data a commutative monoid. This product remains
distinct from ideal Dirichlet convolution. -/
noncomputable instance : CommMonoid (EulerProductData K) where
  mul_assoc D E F := by ext I <;> simp [mul_assoc, Set.union_assoc]
  one_mul D := by ext I <;> simp
  mul_one D := by ext I <;> simp
  mul_comm D E := by ext I <;> simp [mul_comm, Set.union_comm]
  npow := npowRec
  npow_zero := by intros; rfl
  npow_succ := by intros; rfl

/-- Complex conjugation makes Euler-product data a star monoid. -/
noncomputable instance : StarMul (EulerProductData K) where
  star D :=
    { toIdealArithmeticFunction := star D.toIdealArithmeticFunction
      isMultiplicative := D.isMultiplicative.star
      badPrimes := D.badPrimes
      finite_badPrimes := D.finite_badPrimes }
  star_involutive D := by
    ext I <;> simp
  star_mul D E := by
    apply ext
    · intro I
      change star (D I * E I) = star (E I) * star (D I)
      exact star_mul (D I) (E I)
    · exact Set.union_comm D.badPrimes E.badPrimes

@[simp]
theorem star_apply (D : EulerProductData K) (I : (Ideal (𝓞 K))⁰) :
    (star D) I = star (D I) := (rfl)

/-- Complex conjugation leaves the specified bad-prime set unchanged. -/
@[simp]
theorem badPrimes_star (D : EulerProductData K) : (star D).badPrimes = D.badPrimes := rfl

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

/-- Restricting away from `S` adjoins `S` to the canonical bad-prime set. -/
@[simp]
theorem badPrimes_restrict (D : EulerProductData K)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    (D.restrict S hS).badPrimes = D.badPrimes ∪ S := by
  rw [restrict, badPrimes_mul, badPrimes_ofMultiplicativeIdealWeight,
    MultiplicativeIdealWeight.badPrimes_ofBadPrimes hS]

end EulerProductData

end TauCeti
