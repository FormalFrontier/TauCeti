/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Collapsing an iterated product of powers into a single product of powers

`Finset.prod_pow_eq_pow_sum` collapses a product of natural powers of one fixed element into a
single power. This file records the analogue for integral powers of an invertible element of a
commutative group with zero, and the three substitution rules that follow from it: substituting a
family of monomials into a monomial multiplies the two exponent matrices.

These are the bookkeeping rules behind composing monomial maps in coordinates, where the exponent
matrices may carry natural or integral entries depending on whether the coordinate they act on is
allowed to vanish.

## Main results

* `Finset.prod_zpow_eq_zpow_sum`: `∏ i ∈ s, y ^ e i = y ^ ∑ i ∈ s, e i` for `y ≠ 0`.
* `Finset.prod_prod_pow`, `Finset.prod_prod_zpow` and `Finset.prod_prod_zpow_pow`: substituting
  monomials into a monomial multiplies the exponent matrices, for the three combinations of
  natural and integral exponents that make sense.
-/

public section

namespace Finset

variable {ι κ M G₀ : Type*}

/-- A product of integral powers of one fixed invertible element collapses to a single power.
This is the integral-exponent analogue of `Finset.prod_pow_eq_pow_sum`. -/
theorem prod_zpow_eq_zpow_sum [CommGroupWithZero G₀] (s : Finset ι) {y : G₀} (hy : y ≠ 0)
    (e : ι → ℤ) : ∏ i ∈ s, y ^ e i = y ^ ∑ i ∈ s, e i := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [prod_cons, sum_cons, ih, zpow_add₀ hy]

/-- Substituting the monomials `∏ b ∈ t, x b ^ e a b` into the monomial with natural exponents
`g` produces the monomial whose exponent matrix is the product `∑ a ∈ s, g a * e a b`. -/
theorem prod_prod_pow [CommMonoid M] (s : Finset ι) (t : Finset κ) (x : κ → M) (e : ι → κ → ℕ)
    (g : ι → ℕ) :
    ∏ a ∈ s, (∏ b ∈ t, x b ^ e a b) ^ g a = ∏ b ∈ t, x b ^ ∑ a ∈ s, g a * e a b := by
  calc ∏ a ∈ s, (∏ b ∈ t, x b ^ e a b) ^ g a = ∏ b ∈ t, ∏ a ∈ s, x b ^ (g a * e a b) := by
        rw [Finset.prod_comm]
        exact prod_congr rfl fun a _ ↦ by
          rw [← Finset.prod_pow]
          exact prod_congr rfl fun b _ ↦ by rw [← pow_mul, mul_comm]
    _ = ∏ b ∈ t, x b ^ ∑ a ∈ s, g a * e a b :=
        prod_congr rfl fun b _ ↦ prod_pow_eq_pow_sum _ _ _

/-- Substituting the monomials `∏ b ∈ t, y b ^ e a b` in invertible coordinates into the monomial
with integral exponents `g` produces the monomial whose exponent matrix is the product
`∑ a ∈ s, g a * e a b`. -/
theorem prod_prod_zpow [CommGroupWithZero G₀] (s : Finset ι) (t : Finset κ) {y : κ → G₀}
    (hy : ∀ b ∈ t, y b ≠ 0) (e : ι → κ → ℤ) (g : ι → ℤ) :
    ∏ a ∈ s, (∏ b ∈ t, y b ^ e a b) ^ g a = ∏ b ∈ t, y b ^ ∑ a ∈ s, g a * e a b := by
  calc ∏ a ∈ s, (∏ b ∈ t, y b ^ e a b) ^ g a = ∏ b ∈ t, ∏ a ∈ s, y b ^ (g a * e a b) := by
        rw [Finset.prod_comm]
        exact prod_congr rfl fun a _ ↦ by
          rw [← Finset.prod_zpow]
          exact prod_congr rfl fun b _ ↦ by rw [← zpow_mul, mul_comm]
    _ = ∏ b ∈ t, y b ^ ∑ a ∈ s, g a * e a b :=
        prod_congr rfl fun b hb ↦ prod_zpow_eq_zpow_sum _ (hy b hb) _

/-- The mixed case of `Finset.prod_prod_zpow`: monomials with integral exponents in invertible
coordinates, substituted into a monomial with natural exponents `g`. -/
theorem prod_prod_zpow_pow [CommGroupWithZero G₀] (s : Finset ι) (t : Finset κ) {y : κ → G₀}
    (hy : ∀ b ∈ t, y b ≠ 0) (e : ι → κ → ℤ) (g : ι → ℕ) :
    ∏ a ∈ s, (∏ b ∈ t, y b ^ e a b) ^ g a = ∏ b ∈ t, y b ^ ∑ a ∈ s, (g a : ℤ) * e a b := by
  rw [← prod_prod_zpow s t hy e fun a ↦ (g a : ℤ)]
  exact prod_congr rfl fun a _ ↦ (zpow_natCast _ _).symm

end Finset
