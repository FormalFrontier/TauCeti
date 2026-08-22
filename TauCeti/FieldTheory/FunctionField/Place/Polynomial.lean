/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div

/-!
# Clearing a common power of `X` from a finite family of polynomials

Stichtenoth's linear-independence arguments for places of an algebraic function field all begin
by taking a relation whose coefficients are polynomials in a fixed element and dividing out the
largest power of that element dividing every coefficient, so that at least one coefficient
acquires a nonzero constant term. This file isolates that elementary step on the polynomial ring,
where it is a statement about `Polynomial.rootMultiplicity 0` and nothing else.

It is used both by `TauCeti.FieldTheory.FunctionField.Place.Degree`, for Stichtenoth,
*Algebraic Function Fields and Codes*, Proposition 1.1.15, and by
`TauCeti.FieldTheory.FunctionField.Place.OfValuationSubring`, for his Lemma 1.1.7.

## Main results

* `TauCeti.Place.exists_common_X_pow_factor`: a finite family of polynomials, not all zero, is
  `X ^ m` times a family in which some member has nonzero constant term.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Lemma 1.1.7 and Proposition 1.1.15.
-/

public section

open Polynomial

namespace TauCeti

universe u

variable {k : Type u} [Field k]

namespace Place

/-- Dividing a finite family of polynomials, not all zero, by the largest power of `X` that
divides every member leaves at least one quotient with nonzero constant term. The exponent is
the least `Polynomial.rootMultiplicity 0` over the nonzero members. -/
theorem exists_common_X_pow_factor {ι : Type*} (s : Finset ι) (p : ι → k[X])
    (hne : ∃ i ∈ s, p i ≠ 0) :
    ∃ m, ∃ q : ι → k[X], (∀ i ∈ s, p i = X ^ m * q i) ∧
      ∃ j ∈ s, (q j).coeff 0 ≠ 0 := by
  classical
  have hfilter : (s.filter fun i ↦ p i ≠ 0).Nonempty := by
    obtain ⟨i, hi, hpi⟩ := hne
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hpi⟩⟩
  obtain ⟨j, hj, hjmin⟩ :=
    (s.filter fun i ↦ p i ≠ 0).exists_min_image (fun i ↦ rootMultiplicity 0 (p i)) hfilter
  obtain ⟨hjs, hjne⟩ := Finset.mem_filter.mp hj
  let m := rootMultiplicity (0 : k) (p j)
  let q : ι → k[X] := fun i ↦ p i /ₘ (X : k[X]) ^ m
  have hdvd : ∀ i ∈ s, (X : k[X]) ^ m ∣ p i := by
    intro i hi
    rcases eq_or_ne (p i) 0 with h | h
    · simp [h]
    · refine dvd_trans (pow_dvd_pow _ (hjmin i (Finset.mem_filter.mpr ⟨hi, h⟩))) ?_
      simpa [m] using pow_rootMultiplicity_dvd (p i) 0
  have hfactor : ∀ i ∈ s, p i = (X : k[X]) ^ m * q i := by
    intro i hi
    conv_lhs => rw [← modByMonic_add_div (p i) ((X : k[X]) ^ m)]
    rw [(modByMonic_eq_zero_iff_dvd (monic_X.pow m)).mpr (hdvd i hi), zero_add]
  refine ⟨m, q, hfactor, j, hjs, ?_⟩
  simpa [q, m, coeff_zero_eq_eval_zero] using
    (eval_divByMonic_pow_rootMultiplicity_ne_zero (p := p j) 0 hjne)

end Place

end TauCeti
