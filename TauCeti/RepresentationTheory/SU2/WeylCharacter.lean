/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.SU2.ConjugacyClasses
public import TauCeti.RepresentationTheory.SU2.SymmetricPower

/-!
# The Weyl character formula for `SU(2)`

`TauCeti/RepresentationTheory/SU2/SymmetricPower.lean` computes the character of the symmetric
power `Symᵈ(ℂ²)` of the standard representation of `SU(2)` on the maximal torus as the weight
string

`χ_d (diag (z, z⁻¹)) = z^{-d} + z^{2-d} + ⋯ + z^d`.

This file sums that string.  Multiplying it by the **Weyl denominator** `z - z⁻¹` telescopes, so

`(z - z⁻¹) · χ_d (diag (z, z⁻¹)) = z^{d+1} - z^{-(d+1)}`

with no hypothesis on `z`, and away from the two points `z = ±1` where the denominator vanishes
this is the **Weyl character formula**

`χ_d (diag (z, z⁻¹)) = (z^{d+1} - z^{-(d+1)}) / (z - z⁻¹)`.

At the two excluded points the character is `(d + 1) · z^d`, so the value there is the dimension up
to sign, and the description of the character on the torus is complete.

In the angle parametrisation `z = e^{iθ}` of the torus the numerator and the denominator are
`2i·sin ((d+1)θ)` and `2i·sin θ`, so the telescoping identity reads `sin θ · χ_d = sin ((d+1)θ)`
-- again with no hypothesis, both sides vanishing at the multiples of `π` -- and the character
formula becomes the classical

`χ_d (diag (e^{iθ}, e^{-iθ})) = sin ((d+1)θ) / sin θ`.

Since every element of `SU(2)` is conjugate into the maximal torus
(`TauCeti.SU2.exists_isConj_torusHom`) and a character is a class function, these formulas compute
the character of `Symᵈ(ℂ²)` everywhere.

## Main results

* `TauCeti.SU2.sub_inv_mul_character_symPower_torusHom`: the telescoped identity
  `(z - z⁻¹) · χ_d = z^{d+1} - z^{-(d+1)}`, valid for every `z`.
* `TauCeti.SU2.character_symPower_torusHom_eq_div`: the **Weyl character formula** on the torus,
  away from `z = ±1`.
* `TauCeti.SU2.character_symPower_torusHom_of_sq_eq_one`: the character at the two points
  `z = ±1`, where the Weyl denominator vanishes.
* `TauCeti.SU2.sin_mul_character_symPower_torusExp` and
  `TauCeti.SU2.character_symPower_torusExp_eq_sin_div_sin`: the same two statements in the angle
  parametrisation, `sin θ · χ_d = sin ((d+1)θ)` and `χ_d = sin ((d+1)θ) / sin θ`.
* `TauCeti.SU2.character_symPower_torusExp_eq_div`: the alternating-sum form
  `χ_d = (e^{i(d+1)θ} - e^{-i(d+1)θ}) / (e^{iθ} - e^{-iθ})`.
* `TauCeti.SU2.character_symPower_eq_sin_div_sin_of_isConj` and
  `TauCeti.SU2.exists_mem_Icc_character_symPower_eq`: the same formulas off the torus, the
  character being a class function on a group in which every element is conjugate into the torus.

## References

This serves the engine case of
`TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md`, "Engine case: `SU(2)` and the
maximal torus", which asks for the character on the torus in the closed forms
`sin ((n+1)θ) / sin θ` and `(e^{i(n+1)θ} - e^{-i(n+1)θ}) / (e^{iθ} - e^{-iθ})`.

* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 18.
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter II, §5.
-/

public section

open Finset

namespace TauCeti

namespace SU2

variable (d : ℕ)

/-- The Weyl denominator `z - z⁻¹` vanishes exactly at the two points `z = ±1` of the circle, that
is, exactly when `z ^ 2 = 1`. -/
private theorem coe_sub_inv_ne_zero {z : Circle} (hz : (z : ℂ) ^ 2 ≠ 1) :
    (z : ℂ) - (z : ℂ)⁻¹ ≠ 0 := by
  intro h
  refine hz ?_
  rw [sub_eq_zero] at h
  rw [sq]
  nth_rewrite 2 [h]
  exact mul_inv_cancel₀ z.coe_ne_zero

/-- **The Weyl numerator identity.**  Multiplying the weight string of `Symᵈ(ℂ²)` by the Weyl
denominator `z - z⁻¹` telescopes to `z^{d+1} - z^{-(d+1)}`.

No hypothesis is needed on `z`: at the two points `z = ±1` where the denominator vanishes both
sides are `0`. -/
theorem sub_inv_mul_character_symPower_torusHom (z : Circle) :
    ((z : ℂ) - (z : ℂ)⁻¹) * (symPower d).character (torusHom z)
      = (z : ℂ) ^ (d + 1) - ((z : ℂ)⁻¹) ^ (d + 1) := by
  have hz : (z : ℂ) ≠ 0 := z.coe_ne_zero
  rw [character_symPower_torusHom_zpow, mul_sum]
  have key : ∀ i ∈ range (d + 1),
      ((z : ℂ) - (z : ℂ)⁻¹) * (z : ℂ) ^ (2 * (i : ℤ) - d)
        = (z : ℂ) ^ (2 * ((i + 1 : ℕ) : ℤ) - d - 1) - (z : ℂ) ^ (2 * (i : ℤ) - d - 1) := by
    intro i _
    have hsplit : (z : ℂ) - (z : ℂ)⁻¹ = (z : ℂ) ^ (1 : ℤ) - (z : ℂ) ^ (-1 : ℤ) := by
      simp
    rw [hsplit, sub_mul, ← zpow_add₀ hz, ← zpow_add₀ hz]
    congr 2 <;> push_cast <;> ring
  rw [sum_congr rfl key, sum_range_sub (fun j : ℕ => (z : ℂ) ^ (2 * (j : ℤ) - d - 1)) (d + 1),
    inv_pow, ← zpow_natCast (z : ℂ) (d + 1)]
  push_cast
  rw [show (0 : ℤ) - (d : ℤ) - 1 = -((d : ℤ) + 1) by ring, zpow_neg,
    show 2 * ((d : ℤ) + 1) - (d : ℤ) - 1 = (d : ℤ) + 1 by ring]

/-- **The Weyl character formula for `SU(2)`.**  Away from the two points `z = ±1` of the maximal
torus, where the Weyl denominator vanishes, the character of `Symᵈ(ℂ²)` at `diag (z, z⁻¹)` is the
quotient of the Weyl numerator by the Weyl denominator. -/
theorem character_symPower_torusHom_eq_div {z : Circle} (hz : (z : ℂ) ^ 2 ≠ 1) :
    (symPower d).character (torusHom z)
      = ((z : ℂ) ^ (d + 1) - ((z : ℂ)⁻¹) ^ (d + 1)) / ((z : ℂ) - (z : ℂ)⁻¹) :=
  eq_div_of_mul_eq (coe_sub_inv_ne_zero hz)
    (by rw [mul_comm]; exact sub_inv_mul_character_symPower_torusHom d z)

/-- **The character at the two points where the Weyl denominator vanishes.**  At `z = ±1` every one
of the `d + 1` weights contributes `z^d`, so the character is `(d + 1) · z^d`; in particular it is
`d + 1` at the identity and `(-1)^d · (d + 1)` at the central element `-1`. -/
theorem character_symPower_torusHom_of_sq_eq_one {z : Circle} (hz : (z : ℂ) ^ 2 = 1) :
    (symPower d).character (torusHom z) = ((d : ℂ) + 1) * (z : ℂ) ^ d := by
  have hz0 : (z : ℂ) ≠ 0 := z.coe_ne_zero
  have hpow : ((z : ℂ) ^ d) * ((z : ℂ) ^ d) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, hz, one_pow]
  rw [character_symPower_torusHom_zpow]
  have hterm : ∀ i ∈ range (d + 1), (z : ℂ) ^ (2 * (i : ℤ) - d) = (z : ℂ) ^ d := by
    intro i _
    have hsq : (z : ℂ) ^ (2 : ℤ) = 1 := by
      rw [zpow_two, ← pow_two]
      exact hz
    have h2 : (z : ℂ) ^ (2 * (i : ℤ)) = 1 := by
      rw [zpow_mul, hsq, one_zpow]
    rw [zpow_sub₀ hz0, h2, zpow_natCast, one_div, eq_comm]
    exact eq_inv_of_mul_eq_one_left hpow
  rw [sum_congr rfl hterm, sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

/-- The Weyl numerator and denominator in the angle parametrisation: for a real `t`,
`e^{it} - e^{-it} = 2i·sin t`. -/
private theorem exp_sub_exp_neg_mul_I (t : ℝ) :
    Complex.exp ((t : ℂ) * Complex.I) - Complex.exp (-((t : ℂ) * Complex.I))
      = 2 * Complex.I * (Real.sin t : ℂ) := by
  have hneg : -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hneg, Complex.exp_mul_I, Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg,
    Complex.sin_neg, Complex.ofReal_sin]
  ring

/-- **The Weyl numerator identity in the angle parametrisation:** writing the torus element as
`diag (e^{iθ}, e^{-iθ})`, the identity of
`TauCeti.SU2.sub_inv_mul_character_symPower_torusHom` reads `sin θ · χ_d (θ) = sin ((d+1)θ)`.

As there, no hypothesis is needed on `θ`: at a multiple of `π` both sides vanish. -/
theorem sin_mul_character_symPower_torusExp (θ : ℝ) :
    (Real.sin θ : ℂ) * (symPower d).character (torusExp θ)
      = (Real.sin (((d : ℝ) + 1) * θ) : ℂ) := by
  have hI : (2 : ℂ) * Complex.I ≠ 0 := by
    simp [Complex.I_ne_zero]
  refine mul_left_cancel₀ hI ?_
  have hz : ((Circle.exp θ : Circle) : ℂ) = Complex.exp ((θ : ℂ) * Complex.I) :=
    Circle.coe_exp θ
  have hden : ((Circle.exp θ : Circle) : ℂ) - ((Circle.exp θ : Circle) : ℂ)⁻¹
      = 2 * Complex.I * (Real.sin θ : ℂ) := by
    rw [hz, ← Complex.exp_neg, exp_sub_exp_neg_mul_I]
  have h₁ : ((d : ℂ) + 1) * ((θ : ℂ) * Complex.I)
      = ((((d : ℝ) + 1) * θ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have h₂ : ((d : ℂ) + 1) * -((θ : ℂ) * Complex.I)
      = -(((((d : ℝ) + 1) * θ : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  have hnum : ((Circle.exp θ : Circle) : ℂ) ^ (d + 1)
      - (((Circle.exp θ : Circle) : ℂ)⁻¹) ^ (d + 1)
      = 2 * Complex.I * (Real.sin (((d : ℝ) + 1) * θ) : ℂ) := by
    rw [hz, ← Complex.exp_neg, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Nat.cast_add,
      Nat.cast_one, h₁, h₂, exp_sub_exp_neg_mul_I]
  rw [torusExp_def, ← mul_assoc, ← hden, sub_inv_mul_character_symPower_torusHom d (Circle.exp θ)]
  exact hnum

/-- **The Weyl character formula in the angle parametrisation.**  Off the multiples of `π`, where
the Weyl denominator `2i·sin θ` vanishes, the character of `Symᵈ(ℂ²)` at `diag (e^{iθ}, e^{-iθ})`
is `sin ((d+1)θ) / sin θ`.  In particular it is real. -/
theorem character_symPower_torusExp_eq_sin_div_sin {θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    (symPower d).character (torusExp θ)
      = ((Real.sin (((d : ℝ) + 1) * θ) / Real.sin θ : ℝ) : ℂ) := by
  have hθ' : (Real.sin θ : ℂ) ≠ 0 := by exact_mod_cast hθ
  rw [Complex.ofReal_div, eq_div_iff hθ', mul_comm]
  exact sin_mul_character_symPower_torusExp d θ

/-- **The alternating-sum form of the Weyl character formula.**  Off the multiples of `π` the
character of `Symᵈ(ℂ²)` on the torus is the quotient of the alternating sums
`e^{i(d+1)θ} - e^{-i(d+1)θ}` and `e^{iθ} - e^{-iθ}`. -/
theorem character_symPower_torusExp_eq_div {θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    (symPower d).character (torusExp θ)
      = (Complex.exp ((((d : ℝ) + 1) * θ : ℝ) * Complex.I)
            - Complex.exp (-((((d : ℝ) + 1) * θ : ℝ) * Complex.I)))
          / (Complex.exp ((θ : ℂ) * Complex.I) - Complex.exp (-((θ : ℂ) * Complex.I))) := by
  have hθ' : (Real.sin θ : ℂ) ≠ 0 := by exact_mod_cast hθ
  have hI : (2 : ℂ) * Complex.I ≠ 0 := by
    simp [Complex.I_ne_zero]
  rw [exp_sub_exp_neg_mul_I, exp_sub_exp_neg_mul_I,
    character_symPower_torusExp_eq_sin_div_sin d hθ, Complex.ofReal_div,
    div_eq_div_iff hθ' (mul_ne_zero hI hθ')]
  ring

/-! ### The character away from the maximal torus -/

/-- The character of `Symᵈ(ℂ²)` is a class function, so it takes at a conjugate of a torus element
the value it takes at that torus element. -/
theorem character_symPower_eq_of_isConj {g : SU2} {θ : ℝ} (hg : IsConj g (torusExp θ)) :
    (symPower d).character g = (symPower d).character (torusExp θ) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hg
  rw [← hc, Representation.char_conj]

/-- **The Weyl character formula at an arbitrary element of `SU(2)`.**  Every element is conjugate
to a torus element `diag (e^{iθ}, e^{-iθ})` (`TauCeti.SU2.exists_isConj_torusExp`), so the formula
on the torus computes the character of `Symᵈ(ℂ²)` off the torus as well. -/
theorem character_symPower_eq_sin_div_sin_of_isConj {g : SU2} {θ : ℝ}
    (hg : IsConj g (torusExp θ)) (hθ : Real.sin θ ≠ 0) :
    (symPower d).character g = ((Real.sin (((d : ℝ) + 1) * θ) / Real.sin θ : ℝ) : ℂ) := by
  rw [character_symPower_eq_of_isConj d hg, character_symPower_torusExp_eq_sin_div_sin d hθ]

/-- **The character of `Symᵈ(ℂ²)` is determined by its values on the Weyl chamber.**  Each element
of `SU(2)` is conjugate to a torus element whose angle lies in `[0, π]`
(`TauCeti.SU2.exists_isConj_torusExp_mem_Icc`), where the angle is moreover unique
(`TauCeti.SU2.eq_of_mem_Icc_of_isConj_torusExp`). -/
theorem exists_mem_Icc_character_symPower_eq (g : SU2) :
    ∃ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      (symPower d).character g = (symPower d).character (torusExp θ) := by
  obtain ⟨θ, hθ, hconj⟩ := exists_isConj_torusExp_mem_Icc g
  exact ⟨θ, hθ, character_symPower_eq_of_isConj d hconj⟩

end SU2

end TauCeti
