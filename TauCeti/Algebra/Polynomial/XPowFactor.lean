/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.Finset.Max

/-!
# Dividing a family of polynomials by the largest common power of `X`

A finite family of polynomials over a field, not all zero, has a largest power of `X` dividing
every member; after dividing it out, at least one quotient has a nonzero constant term. The
exponent is the least `Polynomial.rootMultiplicity 0` over the nonzero members of the family.

This is the step that clears a common factor `x` from a linear relation with coefficients in
`k[x]`, so that "not every coefficient is divisible by `x`" may be assumed. Stichtenoth,
*Algebraic Function Fields and Codes*, runs it twice: once in the proof of Proposition 1.1.15,
that the degree of a place is finite, and once in the proof of Proposition 1.3.3, the bound on
the zeros of a function. The statement mentions neither valuations nor function fields, so it
lives here.

## Main results

* `TauCeti.Polynomial.exists_forall_eq_X_pow_mul`: the division itself.
-/

public section

open Polynomial

namespace TauCeti.Polynomial

variable {k : Type*} [Field k]

/-- Dividing a finite family of polynomials, not all zero, by the largest power of `X` that
divides every member leaves at least one quotient with nonzero constant term. The exponent is
the least `Polynomial.rootMultiplicity 0` over the nonzero members. -/
theorem exists_forall_eq_X_pow_mul {ι : Type*} (s : Finset ι) (p : ι → k[X])
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

end TauCeti.Polynomial

end
