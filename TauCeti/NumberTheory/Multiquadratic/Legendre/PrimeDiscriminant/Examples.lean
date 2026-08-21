/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminants
public import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Examples.Lists

/-!
# Concrete Legendre criteria for the first genus-field examples

The multiquadratic roadmap's genus-field worked examples begin with the prime-discriminant
lists `[-4, 5]` for `ℚ(√-5)` and `[-4, -3, -7]` for `ℚ(√-21)`. This file records the
corresponding concrete Legendre-character criteria, so later worked-example code can consume
the familiar congruence and reciprocal-symbol conditions directly.

The prime-discriminant convention follows Cox's *Primes of the Form x² + ny²* and
Lemmermeyer's *Reciprocity Laws*, as in the prime-discriminant splitting API this file reuses.

## Main results

* `TauCeti.Multiquadratic.forall_legendreSym_neg_four_five_eq_one_iff`: the `-5`
  genus-field character list `[-4, 5]` is trivial at an odd prime `p` exactly when
  `p ≡ 1 (mod 4)` and `(p / 5) = 1`.
* `TauCeti.Multiquadratic.forall_legendreSym_neg_four_neg_three_neg_seven_eq_one_iff`: the
  `-21` genus-field character list `[-4, -3, -7]` is trivial exactly when
  `p ≡ 1 (mod 4)`, `(p / 3) = 1`, and `(p / 7) = 1`.
-/

public section

namespace TauCeti.Multiquadratic

/-- **The `ℚ(√-5)` genus-field character condition.** For an odd prime `p`, the Legendre
symbols of the prime-discriminant list `[-4, 5]` are all `1` exactly when
`p ≡ 1 (mod 4)` and the reciprocal symbol `(p / 5)` is `1`. -/
@[simp]
theorem forall_legendreSym_neg_four_five_eq_one_iff {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) :
    (∀ i, legendreSym p (negFourFivePrimeDiscriminants i) = 1) ↔
      p % 4 = 1 ∧ @legendreSym 5 ⟨by decide⟩ (p : ℤ) = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  constructor
  · intro h
    constructor
    · have h0 := h 0
      simpa using
        (legendreSym_evenPrimeDiscriminant_neg_four_eq_one_iff (q := p) hodd).mp h0
    · have h1 := h 1
      simpa [oddPrimeDiscriminant] using
        (legendreSym_oddPrimeDiscriminant_eq_one_iff
          (p := 5) (q := p) (by norm_num) hodd).mp h1
  · rintro ⟨hfour, hfive⟩ i
    fin_cases i
    · exact
        (legendreSym_evenPrimeDiscriminant_neg_four_eq_one_iff (q := p) hodd).mpr hfour
    · simpa [oddPrimeDiscriminant] using
        (legendreSym_oddPrimeDiscriminant_eq_one_iff
          (p := 5) (q := p) (by norm_num) hodd).mpr hfive

/-- **The `ℚ(√-21)` genus-field character condition.** For an odd prime `p`, the Legendre
symbols of the prime-discriminant list `[-4, -3, -7]` are all `1` exactly when
`p ≡ 1 (mod 4)`, `(p / 3) = 1`, and `(p / 7) = 1`. -/
@[simp]
theorem forall_legendreSym_neg_four_neg_three_neg_seven_eq_one_iff {p : ℕ}
    [Fact p.Prime] (hodd : p ≠ 2) :
    (∀ i, legendreSym p (negFourNegThreeNegSevenPrimeDiscriminants i) = 1) ↔
      p % 4 = 1 ∧ @legendreSym 3 ⟨by decide⟩ (p : ℤ) = 1 ∧
        @legendreSym 7 ⟨by decide⟩ (p : ℤ) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  constructor
  · intro h
    constructor
    · have h0 := h 0
      simpa using
        (legendreSym_evenPrimeDiscriminant_neg_four_eq_one_iff (q := p) hodd).mp h0
    · constructor
      · have h1 := h 1
        simpa [oddPrimeDiscriminant] using
          (legendreSym_oddPrimeDiscriminant_eq_one_iff
            (p := 3) (q := p) (by norm_num) hodd).mp h1
      · have h2 := h 2
        simpa [oddPrimeDiscriminant] using
          (legendreSym_oddPrimeDiscriminant_eq_one_iff
            (p := 7) (q := p) (by norm_num) hodd).mp h2
  · rintro ⟨hfour, hthree, hseven⟩ i
    fin_cases i
    · exact
        (legendreSym_evenPrimeDiscriminant_neg_four_eq_one_iff (q := p) hodd).mpr hfour
    · simpa [oddPrimeDiscriminant] using
        (legendreSym_oddPrimeDiscriminant_eq_one_iff
          (p := 3) (q := p) (by norm_num) hodd).mpr hthree
    · simpa [oddPrimeDiscriminant] using
        (legendreSym_oddPrimeDiscriminant_eq_one_iff
          (p := 7) (q := p) (by norm_num) hodd).mpr hseven

end TauCeti.Multiquadratic
