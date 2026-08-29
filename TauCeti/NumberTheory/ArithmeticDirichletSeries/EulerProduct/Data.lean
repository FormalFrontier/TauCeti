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
that is multiplicative on relatively prime nonzero ideals and has only finitely many vanishing
prime coefficients. Its bad-prime set is derived from that function, so the bundle carries no
unconstrained local data. The prime-power series and local arithmetic factors are likewise the
canonical ones defined in `EulerProduct/Basic.lean`.

The formal Euler-product identity follows from
`IdealArithmeticFunction.normCoeff_eq_eulerProduct`: coprime multiplicativity and unique
factorization prove that `normCoeff` is Mathlib's `ArithmeticFunction.eulerProduct` of the
canonical local factors. Analytic convergence of the evaluated factors belongs to Layer 3.3.

## Main definitions

* `TauCeti.EulerProductData` bundles a multiplicative ideal coefficient system with finite
  bad-prime set.
* `TauCeti.EulerProductData.badPrimes` is its canonically determined vanishing set.
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
canonically derived from `toIdealArithmeticFunction`; the final field says that the prime
coefficients vanish at only finitely many height-one primes. -/
structure EulerProductData (K : Type*) [Field K] [NumberField K] where
  /-- The coefficients indexed by nonzero integral ideals. -/
  toIdealArithmeticFunction : IdealArithmeticFunction K
  /-- Coprime multiplicativity, the exact algebraic hypothesis used by an Euler product. -/
  isMultiplicative : toIdealArithmeticFunction.IsMultiplicative
  /-- Only finitely many height-one prime coefficients vanish. -/
  finite_setOf_apply_prime_eq_zero :
    {P : HeightOneSpectrum (𝓞 K) |
      toIdealArithmeticFunction
        ⟨P.asIdeal, mem_nonZeroDivisors_of_ne_zero P.ne_bot⟩ = 0}.Finite

namespace EulerProductData

variable {K : Type*} [Field K] [NumberField K]

instance : FunLike (EulerProductData K) ((Ideal (𝓞 K))⁰) ℂ where
  coe D := D.toIdealArithmeticFunction
  coe_injective D E h := by
    cases D
    cases E
    congr

@[ext]
theorem ext {D E : EulerProductData K} (h : ∀ I, D I = E I) : D = E :=
  DFunLike.ext D E h

/-- Evaluating the stored ideal arithmetic function agrees with evaluating the bundle. -/
@[simp]
theorem toIdealArithmeticFunction_apply (D : EulerProductData K) (I : (Ideal (𝓞 K))⁰) :
    D.toIdealArithmeticFunction I = D I := rfl

/-- The bad primes of Euler-product data: precisely the height-one primes at which its prime
coefficient vanishes. This is derived rather than stored independently. -/
def badPrimes (D : EulerProductData K) : Set (HeightOneSpectrum (𝓞 K)) :=
  {P | D ⟨P.asIdeal, mem_nonZeroDivisors_of_ne_zero P.ne_bot⟩ = 0}

@[simp]
theorem mem_badPrimes {D : EulerProductData K} {P : HeightOneSpectrum (𝓞 K)} :
    P ∈ D.badPrimes ↔ D ⟨P.asIdeal, mem_nonZeroDivisors_of_ne_zero P.ne_bot⟩ = 0 := Iff.rfl

/-- The bad-prime set of Euler-product data is finite. -/
theorem finite_badPrimes (D : EulerProductData K) : D.badPrimes.Finite :=
  D.finite_setOf_apply_prime_eq_zero

/-- A completely multiplicative ideal weight supplies Euler-product data. Its finite zero support
is exactly the finiteness condition required here. -/
noncomputable def ofMultiplicativeIdealWeight (χ : MultiplicativeIdealWeight K) :
    EulerProductData K where
  toIdealArithmeticFunction := χ.toIdealArithmeticFunction
  isMultiplicative := χ.isMultiplicative_toIdealArithmeticFunction
  finite_setOf_apply_prime_eq_zero := by
    simpa only [MultiplicativeIdealWeight.toIdealArithmeticFunction_apply,
      MultiplicativeIdealWeight.coe_toMonoidWithZeroHom] using χ.finite_setOf_apply_eq_zero

@[simp]
theorem ofMultiplicativeIdealWeight_apply (χ : MultiplicativeIdealWeight K)
    (I : (Ideal (𝓞 K))⁰) : ofMultiplicativeIdealWeight χ I = χ I := by
  exact MultiplicativeIdealWeight.toIdealArithmeticFunction_apply χ I

@[simp]
theorem badPrimes_ofMultiplicativeIdealWeight (χ : MultiplicativeIdealWeight K) :
    (ofMultiplicativeIdealWeight χ).badPrimes = χ.badPrimes := by
  ext P
  simp

/-- The pointwise product of two Euler-product coefficient systems. -/
noncomputable instance : Mul (EulerProductData K) where
  mul D E :=
    { toIdealArithmeticFunction := D.toIdealArithmeticFunction * E.toIdealArithmeticFunction
      isMultiplicative := D.isMultiplicative.mul E.isMultiplicative
      finite_setOf_apply_prime_eq_zero :=
        (D.finite_badPrimes.union E.finite_badPrimes).subset fun P hP ↦ by
          simpa only [Set.mem_union, mem_badPrimes, toIdealArithmeticFunction_apply] using
            mul_eq_zero.mp hP }

@[simp]
theorem mul_apply (D E : EulerProductData K) (I : (Ideal (𝓞 K))⁰) :
    (D * E) I = D I * E I := (rfl)

/-- The bad primes of a pointwise product are the union of the bad primes of its factors. -/
@[simp]
theorem badPrimes_mul (D E : EulerProductData K) :
    (D * E).badPrimes = D.badPrimes ∪ E.badPrimes := by
  ext P
  simp [mul_eq_zero]

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
      isMultiplicative := D.isMultiplicative.star
      finite_setOf_apply_prime_eq_zero := by
        simpa only [Pi.star_apply, star_eq_zero] using D.finite_setOf_apply_prime_eq_zero }
  star_involutive D := by
    ext I
    exact star_star (D I)
  star_mul D E := by
    ext I
    change star (D I * E I) = star (E I) * star (D I)
    exact star_mul (D I) (E I)

@[simp]
theorem star_apply (D : EulerProductData K) (I : (Ideal (𝓞 K))⁰) :
    (star D) I = star (D I) := (rfl)

/-- Complex conjugation leaves the canonical bad-prime set unchanged. -/
@[simp]
theorem badPrimes_star (D : EulerProductData K) : (star D).badPrimes = D.badPrimes := by
  ext P
  simp

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
