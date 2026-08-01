/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Legendre symbols and square-class changes of radicand

Replacing an integer `a` by `a * u ^ 2`, with `p ∤ u`, changes neither whether `p` divides it
nor its Legendre symbol modulo `p`. This file records that elementary single-variable API:
the positive divisibility equivalence `dvd_mul_sq_iff` and its negation `not_dvd_mul_sq_iff`,
and the Legendre-symbol invariance `legendreSym_mul_sq`, together with indexed-family
wrappers in the form used by the multiquadratic splitting law.

These facts are generic Legendre-symbol and divisibility statements.
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]

/-- An integer prime from the ambient natural prime `p`. -/
private theorem prime_intCast_of_fact : Prime (p : ℤ) :=
  Nat.prime_iff_prime_int.mp Fact.out

/-- For `u` with `p ∤ u`, the prime `p` divides `a * u ^ 2` exactly when it divides `a`. -/
@[simp]
theorem dvd_mul_sq_iff {a u : ℤ} (hu : ¬ (p : ℤ) ∣ u) : (p : ℤ) ∣ a * u ^ 2 ↔ (p : ℤ) ∣ a := by
  refine ⟨fun h => ?_, fun ha => dvd_mul_of_dvd_left ha _⟩
  rcases (prime_intCast_of_fact (p := p)).dvd_mul.mp h with ha | hu2
  · exact ha
  · exact absurd ((prime_intCast_of_fact (p := p)).dvd_of_dvd_pow hu2) hu

/-- Multiplying by `u ^ 2` with `p ∤ u` preserves non-divisibility by `p`. -/
theorem not_dvd_mul_sq_iff {a u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    ¬ (p : ℤ) ∣ a * u ^ 2 ↔ ¬ (p : ℤ) ∣ a :=
  not_congr (dvd_mul_sq_iff hu)

/-- Multiplying an integer by `u ^ 2` with `p ∤ u` does not change its Legendre symbol. -/
@[simp]
theorem legendreSym_mul_sq {a u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    legendreSym p (a * u ^ 2) = legendreSym p a := by
  rw [legendreSym.mul,
    legendreSym.sq_one' p (by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]), mul_one]

/-- Replacing each radicand in a family by `d i * u i ^ 2` with `p ∤ u i` preserves all the
Legendre symbols pointwise. -/
theorem forall_legendreSym_eq_of_forall_eq_mul_sq {ι : Type*} {d e u : ι → ℤ}
    (he : ∀ i, e i = d i * u i ^ 2) (hu : ∀ i, ¬ (p : ℤ) ∣ u i) :
    ∀ i, legendreSym p (e i) = legendreSym p (d i) := fun i => by
  rw [he i, legendreSym_mul_sq (hu i)]

/-- The quadratic-residue conditions of a family are unchanged by replacing each radicand by
`d i * u i ^ 2` with `p ∤ u i`. -/
theorem forall_legendreSym_eq_one_iff_of_forall_eq_mul_sq {ι : Type*} {d e u : ι → ℤ}
    (he : ∀ i, e i = d i * u i ^ 2) (hu : ∀ i, ¬ (p : ℤ) ∣ u i) :
    (∀ i, legendreSym p (e i) = 1) ↔ ∀ i, legendreSym p (d i) = 1 := by
  simp_rw [he, legendreSym_mul_sq (p := p) (hu _)]

/-- The unramifiedness conditions of a family are unchanged by replacing each radicand by
`d i * u i ^ 2` with `p ∤ u i`. -/
theorem forall_not_dvd_iff_of_forall_eq_mul_sq {ι : Type*} {d e u : ι → ℤ}
    (he : ∀ i, e i = d i * u i ^ 2) (hu : ∀ i, ¬ (p : ℤ) ∣ u i) :
    (∀ i, ¬ (p : ℤ) ∣ e i) ↔ ∀ i, ¬ (p : ℤ) ∣ d i := by
  simp_rw [he, not_dvd_mul_sq_iff (p := p) (hu _)]

end TauCeti
