/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# The trivial valuation attached to a prime ideal

The trivial valuation of a prime ideal `𝔭` of a commutative ring: it is `0` on `𝔭` and `1`
off it. It is the pullback of Mathlib's trivial valuation `1` on the quotient domain `A ⧸ 𝔭`
along the quotient map. This is the construction behind the trivial-valuation section of
the support map of the valuation spectrum.

## Main definitions

* `Valuation.trivialValuation 𝔭` : The trivial valuation attached to a prime
  ideal `𝔭`, with values in any linearly ordered commutative monoid with zero `Γ₀`
  (the valuation-spectrum section specializes it to `WithZero (Multiplicative ℤ)`).

## Main results

* `Valuation.trivialValuation_eq_zero_iff` : The trivial valuation vanishes exactly
  on `𝔭`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Remark 4.6.
-/

public section

namespace Valuation

variable {A : Type*} [CommRing A] {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]

open scoped Classical in
/-- The trivial valuation attached to a prime ideal `𝔭` (Wedhorn, Remark 4.6): it is `0` on
`𝔭` and `1` off it, as the pullback of the trivial valuation on the quotient domain `A ⧸ 𝔭`
along the quotient map. -/
noncomputable def trivialValuation (𝔭 : Ideal A) [𝔭.IsPrime] : Valuation A Γ₀ :=
  (1 : Valuation (A ⧸ 𝔭) Γ₀).comap (Ideal.Quotient.mk 𝔭)

open scoped Classical in
/-- The value of the trivial valuation, as an `if`. -/
lemma trivialValuation_apply {𝔭 : Ideal A} [𝔭.IsPrime] (a : A) :
    trivialValuation (Γ₀ := Γ₀) 𝔭 a = if a ∈ 𝔭 then 0 else 1 := by
  rw [trivialValuation, Valuation.comap_apply, Valuation.one_apply_def]
  simp only [Ideal.Quotient.eq_zero_iff_mem]

open scoped Classical in
/-- The trivial valuation vanishes exactly on the prime ideal. -/
@[simp]
lemma trivialValuation_eq_zero_iff [Nontrivial Γ₀] {𝔭 : Ideal A} [𝔭.IsPrime] {a : A} :
    trivialValuation (Γ₀ := Γ₀) 𝔭 a = 0 ↔ a ∈ 𝔭 := by
  rw [trivialValuation, Valuation.comap_apply, Valuation.one_apply_eq_zero_iff,
    Ideal.Quotient.eq_zero_iff_mem]

open scoped Classical in
/-- The trivial valuation takes the value `1` exactly off the prime ideal. -/
@[simp]
lemma trivialValuation_eq_one_iff [Nontrivial Γ₀] {𝔭 : Ideal A} [𝔭.IsPrime] {a : A} :
    trivialValuation (Γ₀ := Γ₀) 𝔭 a = 1 ↔ a ∉ 𝔭 := by
  rw [trivialValuation_apply]
  split <;> simp_all

end Valuation
