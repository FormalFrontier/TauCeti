/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Basic

/-!
# The fundamental discriminant of a squarefree radicand

For a squarefree integer `d`, the quadratic field `ℚ(√d)` has discriminant `d` when
`d ≡ 1 (mod 4)` and `4 * d` otherwise. This file packages that assignment as a function
`TauCeti.Multiquadratic.fundamentalDiscriminant` and proves the two facts the genus-field layer
needs of it: for squarefree `d` the value is a fundamental discriminant (so
`FundamentalDiscriminant/Factorization` splits it into prime discriminants), and it differs from
`d` by a square, so it names the *same* quadratic field `ℚ(√d)`.

The genus field of `ℚ(√d)` is the compositum of the `ℚ(√(radicand D*))` over the prime
discriminants `D*` dividing the discriminant of `ℚ(√d)`; this function supplies that discriminant
from the squarefree radicand `d`.

## Main definitions and results

* `TauCeti.Multiquadratic.fundamentalDiscriminant`: `d` if `d ≡ 1 (mod 4)`, else `4 * d`, with its
  defining equation `fundamentalDiscriminant_def`.
* `TauCeti.Multiquadratic.isFundamentalDiscriminant_fundamentalDiscriminant`: for squarefree `d`,
  its fundamental discriminant is a fundamental discriminant.
* `TauCeti.Multiquadratic.exists_sq_mul_eq_fundamentalDiscriminant`: it equals `c² * d` for some
  `c ∈ {1, 2}`, so it lies in the square class of `d`.
-/

public section

namespace TauCeti.Multiquadratic

/-- The **fundamental discriminant** attached to an integer `d`: the discriminant of the quadratic
field `ℚ(√d)` for squarefree `d`, namely `d` when `d ≡ 1 (mod 4)` and `4 * d` otherwise. -/
def fundamentalDiscriminant (d : ℤ) : ℤ := if d % 4 = 1 then d else 4 * d

@[simp] theorem fundamentalDiscriminant_of_mod_four_eq_one {d : ℤ} (hd : d % 4 = 1) :
    fundamentalDiscriminant d = d := if_pos hd

@[simp] theorem fundamentalDiscriminant_of_mod_four_ne_one {d : ℤ} (hd : d % 4 ≠ 1) :
    fundamentalDiscriminant d = 4 * d := if_neg hd

theorem fundamentalDiscriminant_def (d : ℤ) :
    fundamentalDiscriminant d = if d % 4 = 1 then d else 4 * d := by
  by_cases h : d % 4 = 1
  · rw [if_pos h]; exact fundamentalDiscriminant_of_mod_four_eq_one h
  · rw [if_neg h]; exact fundamentalDiscriminant_of_mod_four_ne_one h

/-- `fundamentalDiscriminant d` is `d` or `4 * d`. Implementation helper for
`exists_sq_mul_eq_fundamentalDiscriminant`. -/
private theorem fundamentalDiscriminant_eq_self_or_four_mul (d : ℤ) :
    fundamentalDiscriminant d = d ∨ fundamentalDiscriminant d = 4 * d := by
  by_cases h : d % 4 = 1
  · exact Or.inl (fundamentalDiscriminant_of_mod_four_eq_one h)
  · exact Or.inr (fundamentalDiscriminant_of_mod_four_ne_one h)

/-- `c² * d = fundamentalDiscriminant d` for some `c ∈ {1, 2}`: the fundamental discriminant
differs from `d` by a nonzero square, so `ℚ(√(fundamentalDiscriminant d)) = ℚ(√d)`. The
`c = 1 ∨ c = 2` restriction is part of the statement, so the multiplier is genuinely a
unit-or-`2` square (not the vacuous `c = 0`). -/
theorem exists_sq_mul_eq_fundamentalDiscriminant (d : ℤ) :
    ∃ c : ℤ, (c = 1 ∨ c = 2) ∧ c ^ 2 * d = fundamentalDiscriminant d := by
  rcases fundamentalDiscriminant_eq_self_or_four_mul d with h | h
  · exact ⟨1, Or.inl rfl, by rw [h]; ring⟩
  · exact ⟨2, Or.inr rfl, by rw [h]; ring⟩

/-- **The fundamental discriminant of a squarefree integer is a fundamental discriminant.** When
`d ≡ 1 (mod 4)` the value is `d` itself (`≡ 1 (mod 4)`, squarefree); otherwise `d ≡ 2` or
`3 (mod 4)` (it cannot be `0 (mod 4)`, as `4 = 2²` would break squarefreeness) and the value is
`4 * d`. -/
theorem isFundamentalDiscriminant_fundamentalDiscriminant {d : ℤ} (hd : Squarefree d) :
    IsFundamentalDiscriminant (fundamentalDiscriminant d) := by
  have h4 : d % 4 ≠ 0 := by
    intro h
    obtain ⟨q, hq⟩ : (4 : ℤ) ∣ d := by omega
    exact absurd (hd 2 ⟨q, by rw [hq]; ring⟩) (by norm_num [Int.isUnit_iff])
  by_cases hmod : d % 4 = 1
  · rw [fundamentalDiscriminant_of_mod_four_eq_one hmod, isFundamentalDiscriminant_iff]
    exact Or.inl ⟨hmod, hd⟩
  · rw [fundamentalDiscriminant_of_mod_four_ne_one hmod, isFundamentalDiscriminant_iff]
    exact Or.inr ⟨d, rfl, by omega, hd⟩

end TauCeti.Multiquadratic
