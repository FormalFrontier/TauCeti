/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Polynomial expressions in the integers of a valuation

A valuation takes value at most `1` on every polynomial expression in an element of value at most
`1`, provided the images of the coefficients also have value at most `1`. Concretely, the ring of
integers `v.integer` is a subring containing the images of the coefficients, so it contains every
`aeval t p` with `t` in it; the proof below is the ultrametric bound on the coefficient sum, which
is what `Valuation` supplies directly.

For the tautological valuation of a valuation subring containing a field of constants, a polynomial
with nonzero constant term evaluated at an element of value less than `1` has value exactly `1`:
the constant term strictly dominates all the others. This is the polynomial estimate used in
Stichtenoth's proof that valuation rings of algebraic function fields are discrete.

## Main results

* `Valuation.aeval_le_one`: `v (Polynomial.aeval t p) ≤ 1` whenever `v t ≤ 1` and the images of
  the coefficients have value at most `1`.
* `TauCeti.valuation_aeval_eq_one`: a polynomial with nonzero constant term has value `1` when
  evaluated at an element of the maximal ideal of a valuation subring containing the coefficients.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, Layer 0–1 infrastructure: the place-at-infinity
argument for isogenies in
`AlgebraicGeometry/EllipticCurve/Isogeny/InfinityPlace.lean` needs exactly this to see that a
pulled-back affine function of a Weierstrass curve — a polynomial in the pulled-back coordinates —
stays in the valuation ring at infinity. The statement is about a valuation and a polynomial and
nothing else, so it is stated here rather than there.

`TauCetiRoadmap/AlgebraicCurves/README.md`, Layer 0: `TauCeti.valuation_aeval_eq_one` is the
constant-term estimate used in Stichtenoth, Lemma 1.1.7, on the path to existence of places.
-/

public section

namespace Valuation

variable {R L Γ₀ : Type*} [CommSemiring R] [Ring L] [Algebra R L]
  [LinearOrderedCommMonoidWithZero Γ₀]

/-- **A valuation integral on the coefficients is at most `1` on polynomial expressions in an
element of the integers.** -/
theorem aeval_le_one (v : Valuation L Γ₀) (hR : ∀ r : R, v (algebraMap R L r) ≤ 1)
    {t : L} (ht : v t ≤ 1) (p : Polynomial R) : v (Polynomial.aeval t p) ≤ 1 := by
  rw [Polynomial.aeval_eq_sum_range]
  refine v.map_sum_le fun i _ ↦ ?_
  rw [Algebra.smul_def, v.map_mul, v.map_pow]
  exact mul_le_one' (hR _) (pow_le_one' ht i)

end Valuation

open Polynomial

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
  {A : ValuationSubring F}

/-- A polynomial with nonzero constant term, evaluated at a nonunit of a valuation subring
containing the constants, is a unit: the constant term dominates. -/
theorem valuation_aeval_eq_one (hk : ∀ c : k, algebraMap k F c ∈ A) {x : F}
    (hx : A.valuation x < 1) {p : k[X]} (hp : p.coeff 0 ≠ 0) :
    A.valuation (aeval x p) = 1 := by
  have hkle : ∀ c : k, A.valuation (algebraMap k F c) ≤ 1 :=
    fun c ↦ (A.valuation_le_one_iff _).2 (hk c)
  have : A.valuation.IsTrivialOn k := .of_le_one _ hkle
  obtain ⟨q, hq⟩ : (X : k[X]) ∣ p - C (p.coeff 0) := X_dvd_iff.2 (by simp)
  have hsplit : aeval x p = x * aeval x q + algebraMap k F (p.coeff 0) := by
    have := congrArg (aeval x) hq
    simp only [map_sub, map_mul, aeval_X, aeval_C] at this
    linear_combination (norm := ring_nf) this
  rw [hsplit, Valuation.map_add_eq_of_lt_right, Valuation.IsTrivialOn.eq_one _ hp]
  rw [Valuation.IsTrivialOn.eq_one (A := k) _ hp, map_mul]
  calc A.valuation x * A.valuation (aeval x q)
      ≤ A.valuation x * 1 := by gcongr; exact A.valuation.aeval_le_one hkle hx.le q
    _ = A.valuation x := mul_one _
    _ < 1 := hx

end TauCeti

end
