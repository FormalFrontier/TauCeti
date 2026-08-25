/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Twisted divisor sums

This file defines the twisted divisor sum

`sigma e psi phi n = sum_{d | n} psi (n / d) * phi d * d ^ e`

attached to two Dirichlet characters. These sums are the nonconstant Fourier coefficients of
Eisenstein series with character: the weight-`k` coefficient uses exponent `e = k - 1`.

The definition is expressed as a Dirichlet convolution of multiplicative arithmetic functions.
The resulting API includes its divisor-sum formula, multiplicativity, and its values at prime
powers. For characters of level one it specializes to Mathlib's ordinary divisor sum
`ArithmeticFunction.sigma`.

## Main declarations

* `TauCeti.DirichletCharacter.twistedDivisorSum`: the arithmetic function of twisted divisor sums;
* `TauCeti.DirichletCharacter.isMultiplicative_twistedDivisorSum`: its multiplicativity;
* `TauCeti.DirichletCharacter.twistedDivisorSum_apply_prime_pow`: its prime-power formula;
* `TauCeti.DirichletCharacter.twistedDivisorSum_apply_prime_pow_of_dvd_left_level`: its
  bad-level specialization;
* `TauCeti.DirichletCharacter.twistedDivisorSum_modOne_eq_sigma`: its reduction to the ordinary
  divisor sum.

The convention follows Diamond--Shurman, *A First Course in Modular Forms*, Chapter 4
(especially Sections 4.5--4.8).
-/

public section

namespace TauCeti.DirichletCharacter

open ArithmeticFunction

variable {R : Type*} [CommSemiring R] {u v : ℕ}

/-- The twisted divisor sum attached to `psi`, `phi`, and the exponent `e`.

At a positive integer `n` its value is
`sum_{d | n} psi (n / d) * phi d * d ^ e`. It is packaged as an arithmetic function so that
Dirichlet convolution supplies its multiplicativity. -/
def twistedDivisorSum (e : ℕ) (psi : DirichletCharacter R u) (phi : DirichletCharacter R v) :
    ArithmeticFunction R :=
  toArithmeticFunction (psi ·) *
    (toArithmeticFunction (phi ·)).pmul
      (ArithmeticFunction.pow e : ArithmeticFunction R)

/-- The defining divisor-sum formula for `twistedDivisorSum`. -/
theorem twistedDivisorSum_apply (e : ℕ) (psi : DirichletCharacter R u)
    (phi : DirichletCharacter R v) (n : ℕ) :
    twistedDivisorSum e psi phi n =
      ∑ d ∈ n.divisors, psi (n / d) * phi d * (d : R) ^ e := by
  rw [twistedDivisorSum, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal' (fun a b ↦
      toArithmeticFunction (psi ·) a *
        ((toArithmeticFunction (phi ·)).pmul
          (ArithmeticFunction.pow e : ArithmeticFunction R)) b)]
  refine Finset.sum_congr rfl fun (d : ℕ) hd ↦ ?_
  have hn : n ≠ 0 := Nat.ne_zero_of_mem_divisors hd
  have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hdiv_pos : 0 < n / d :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) hd_pos
  simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.pow_apply]
  rw [
    ← psi.apply_eq_toArithmeticFunction_apply hdiv_pos.ne',
    ← phi.apply_eq_toArithmeticFunction_apply hd_pos.ne']
  simp [hd_pos.ne', mul_assoc]

/-- Twisted divisor sums are multiplicative arithmetic functions. -/
@[arith_mult]
theorem isMultiplicative_twistedDivisorSum (e : ℕ) (psi : DirichletCharacter R u)
    (phi : DirichletCharacter R v) : (twistedDivisorSum e psi phi).IsMultiplicative :=
  psi.isMultiplicative_toArithmeticFunction.mul
    (phi.isMultiplicative_toArithmeticFunction.pmul
      ArithmeticFunction.isMultiplicative_pow.natCast)

/-- The twisted divisor sum at `1` is `1`. -/
@[simp]
theorem twistedDivisorSum_one (e : ℕ) (psi : DirichletCharacter R u)
    (phi : DirichletCharacter R v) : twistedDivisorSum e psi phi 1 = 1 :=
  (isMultiplicative_twistedDivisorSum e psi phi).map_one

/-- The twisted divisor sum on a prime power is a finite geometric-type sum. -/
theorem twistedDivisorSum_apply_prime_pow (e : ℕ) (psi : DirichletCharacter R u)
    (phi : DirichletCharacter R v) (r : ℕ) {p : ℕ} (hp : p.Prime) :
    twistedDivisorSum e psi phi (p ^ r) =
      ∑ j ∈ Finset.range (r + 1),
        psi p ^ (r - j) * phi p ^ j * (p : R) ^ (j * e) := by
  rw [twistedDivisorSum_apply, Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp [Nat.pow_div hjr hp.pos, map_pow, Nat.cast_pow, pow_mul]

/-- At a prime, the twisted divisor sum has its two expected Euler-factor terms. -/
theorem twistedDivisorSum_apply_prime (e : ℕ) (psi : DirichletCharacter R u)
    (phi : DirichletCharacter R v) {p : ℕ} (hp : p.Prime) :
    twistedDivisorSum e psi phi p = psi p + phi p * (p : R) ^ e := by
  simpa [Finset.sum_range_succ, mul_assoc] using
    twistedDivisorSum_apply_prime_pow e psi phi 1 hp

/-- If `p` divides the level of the left character, only the right-character term remains in
the value at `p ^ r`. -/
theorem twistedDivisorSum_apply_prime_pow_of_dvd_left_level (e : ℕ)
    (psi : DirichletCharacter R u) (phi : DirichletCharacter R v) (r : ℕ) {p : ℕ}
    (hp : p.Prime) (hpu : p ∣ u) :
    twistedDivisorSum e psi phi (p ^ r) = phi p ^ r * (p : R) ^ (r * e) := by
  have hpsi : psi p = 0 := psi.map_nonunit <| by
    rw [ZMod.isUnit_iff_coprime]
    exact hp.dvd_iff_not_coprime.mp hpu
  rw [twistedDivisorSum_apply_prime_pow e psi phi r hp, Finset.sum_eq_single r]
  · simp [hpsi]
  · intro j hj hne
    have hjr : j < r :=
      Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hne
    simp [hpsi, Nat.sub_ne_zero_of_lt hjr]
  · simp

/-- If `p` divides the level of the left character, only the right-character term remains in
the value at `p`. -/
theorem twistedDivisorSum_apply_prime_of_dvd_left_level (e : ℕ)
    (psi : DirichletCharacter R u) (phi : DirichletCharacter R v) {p : ℕ} (hp : p.Prime)
    (hpu : p ∣ u) :
    twistedDivisorSum e psi phi p = phi p * (p : R) ^ e := by
  simpa using
    twistedDivisorSum_apply_prime_pow_of_dvd_left_level e psi phi 1 hp hpu

/-- If `p` divides the level of the right character, only the left-character term remains in
the value at `p ^ r`. -/
theorem twistedDivisorSum_apply_prime_pow_of_dvd_right_level (e : ℕ)
    (psi : DirichletCharacter R u) (phi : DirichletCharacter R v) (r : ℕ) {p : ℕ}
    (hp : p.Prime) (hpv : p ∣ v) : twistedDivisorSum e psi phi (p ^ r) = psi p ^ r := by
  have hphi : phi p = 0 := phi.map_nonunit <| by
    rw [ZMod.isUnit_iff_coprime]
    exact hp.dvd_iff_not_coprime.mp hpv
  rw [twistedDivisorSum_apply_prime_pow e psi phi r hp, Finset.sum_eq_single 0]
  · simp [hphi]
  · intro j _ hne
    simp [hphi, hne]
  · simp

/-- If `p` divides the level of the right character, only the left-character term remains in
the value at `p`. -/
theorem twistedDivisorSum_apply_prime_of_dvd_right_level (e : ℕ)
    (psi : DirichletCharacter R u) (phi : DirichletCharacter R v) {p : ℕ} (hp : p.Prime)
    (hpv : p ∣ v) : twistedDivisorSum e psi phi p = psi p := by
  simpa using
    twistedDivisorSum_apply_prime_pow_of_dvd_right_level e psi phi 1 hp hpv

/-- With both characters of level one, the twisted divisor sum is Mathlib's ordinary divisor
sum `ArithmeticFunction.sigma`. -/
@[simp]
theorem twistedDivisorSum_modOne_eq_sigma (e : ℕ) (psi phi : DirichletCharacter R 1) :
    twistedDivisorSum e psi phi =
      (ArithmeticFunction.sigma e : ArithmeticFunction R) := by
  have h_one : toArithmeticFunction (1 : ℕ → R) =
      (ArithmeticFunction.zeta : ArithmeticFunction R) := by
    rw [← ArithmeticFunction.toArithmeticFunction_eq_self
      (ArithmeticFunction.zeta : ArithmeticFunction R)]
    exact toArithmeticFunction_congr ArithmeticFunction.const_one_eq_zeta
  rw [twistedDivisorSum, DirichletCharacter.modOne_eq_one (χ := psi),
    DirichletCharacter.modOne_eq_one (χ := phi), h_one, ArithmeticFunction.zeta_pmul]
  simpa using congrArg (fun f : ArithmeticFunction ℕ ↦ (f : ArithmeticFunction R))
    (ArithmeticFunction.zeta_mul_pow_eq_sigma (k := e))

end TauCeti.DirichletCharacter
