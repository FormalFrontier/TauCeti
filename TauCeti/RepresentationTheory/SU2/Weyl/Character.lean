/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.SU2.SymmetricPower
import TauCeti.Topology.Circle.Basic
import TauCeti.Topology.Circle.Metric

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

At a multiple of `π` the character is `(d + 1) cosᵈ θ`, the two excluded points `z = ±1` read in
the angle coordinate, so the description in that coordinate is complete as well.

These formulas compute the character of `Symᵈ(ℂ²)` everywhere, no declaration here being needed
for that: a character is conjugation invariant (`Representation.char_conj`), and
`TauCeti.SU2.exists_mem_Icc_eq_torusExp_of_conjInvariant`
(`TauCeti/RepresentationTheory/SU2/ConjugacyClasses.lean`, not imported here) carries a
conjugation-invariant function to the angle in the Weyl chamber `[0, π]` of the torus element that
the given element is conjugate to, where the closed forms below apply.

## Main results

* `TauCeti.SU2.sub_inv_mul_character_symPower_torusHom`: the telescoped identity
  `(z - z⁻¹) · χ_d = z^{d+1} - z^{-(d+1)}`, valid for every `z`.
* `TauCeti.SU2.character_symPower_torusHom_eq_div`: the **Weyl character formula** on the torus,
  away from `z = ±1`.
* `TauCeti.SU2.character_symPower_torusHom_of_sq_eq_one`: the character at the two points
  `z = ±1`, where the Weyl denominator vanishes.
* `TauCeti.SU2.sin_mul_character_symPower_torusExp`,
  `TauCeti.SU2.character_symPower_torusExp_eq_sin_div_sin` and
  `TauCeti.SU2.character_symPower_torusExp_of_sin_eq_zero`: the same three statements in the angle
  parametrisation, `sin θ · χ_d = sin ((d+1)θ)`, `χ_d = sin ((d+1)θ) / sin θ` and, at the multiples
  of `π`, `χ_d = (d + 1) cosᵈ θ`.
* `TauCeti.SU2.conj_character_symPower_torusExp`: the character is **real** on the torus, both
  closed forms exhibiting it as the coercion of a real number.
* `TauCeti.SU2.character_symPower_torusExp_eq_div`: the alternating-sum form
  `χ_d = (e^{i(d+1)θ} - e^{-i(d+1)θ}) / (e^{iθ} - e^{-iθ})`.

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
  have hbot : (0 : ℤ) - (d : ℤ) - 1 = -((d : ℤ) + 1) := by ring
  have htop : 2 * ((d : ℤ) + 1) - (d : ℤ) - 1 = (d : ℤ) + 1 := by ring
  push_cast
  rw [hbot, zpow_neg, htop]

/-- **The Weyl character formula for `SU(2)`.**  Away from the two points `z = ±1` of the maximal
torus, where the Weyl denominator vanishes, the character of `Symᵈ(ℂ²)` at `diag (z, z⁻¹)` is the
quotient of the Weyl numerator by the Weyl denominator. -/
theorem character_symPower_torusHom_eq_div {z : Circle} (hz : (z : ℂ) ^ 2 ≠ 1) :
    (symPower d).character (torusHom z)
      = ((z : ℂ) ^ (d + 1) - ((z : ℂ)⁻¹) ^ (d + 1)) / ((z : ℂ) - (z : ℂ)⁻¹) :=
  eq_div_of_mul_eq (circle_sub_inv_ne_zero hz)
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
`e^{it} - e^{-it} = 2i·sin t`.  This is the antipodal case `β = -α` of the polar chord identity
`TauCeti.exp_mul_I_sub_exp_mul_I`, in the shape the rewrites below need. -/
private theorem exp_sub_exp_neg_mul_I (t : ℝ) :
    Complex.exp ((t : ℂ) * Complex.I) - Complex.exp (-((t : ℂ) * Complex.I))
      = 2 * Complex.I * (Real.sin t : ℂ) := by
  have h := exp_mul_I_sub_exp_mul_I t (-t)
  simp only [Complex.ofReal_neg, neg_mul, sub_neg_eq_add, add_self_div_two, add_neg_cancel,
    zero_div, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] at h
  rw [h]
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

/-- **The character at the multiples of `π`, where the Weyl denominator vanishes**, in the angle
parametrisation: there `e^{iθ} = cos θ = ±1`, and the character of `Symᵈ(ℂ²)` is `(d + 1) cosᵈ θ`.
This is `TauCeti.SU2.character_symPower_torusHom_of_sq_eq_one` read in the angle coordinate, and
with `TauCeti.SU2.character_symPower_torusExp_eq_sin_div_sin` it evaluates the character at every
angle. -/
theorem character_symPower_torusExp_of_sin_eq_zero {θ : ℝ} (hθ : Real.sin θ = 0) :
    (symPower d).character (torusExp θ) = ((d : ℂ) + 1) * (Real.cos θ : ℂ) ^ d := by
  have hz : ((Circle.exp θ : Circle) : ℂ) = (Real.cos θ : ℂ) := by
    rw [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hθ]
    simp
  have hcos : Real.cos θ ^ 2 = 1 := by
    have hpyth := Real.sin_sq_add_cos_sq θ
    rw [hθ] at hpyth
    simpa using hpyth
  have hsq : ((Circle.exp θ : Circle) : ℂ) ^ 2 = 1 := by
    rw [hz, ← Complex.ofReal_pow, hcos, Complex.ofReal_one]
  rw [torusExp_def, character_symPower_torusHom_of_sq_eq_one d hsq, hz]

/-- **The character of `Symᵈ(ℂ²)` is real on the maximal torus**: it is a sum of a weight string
`z^{-d} + ⋯ + z^{d}` closed under inversion, and both closed forms above exhibit it as the
coercion of a real number, so complex conjugation leaves it fixed. -/
@[simp]
theorem conj_character_symPower_torusExp (θ : ℝ) :
    (starRingEnd ℂ) ((symPower d).character (torusExp θ))
      = (symPower d).character (torusExp θ) := by
  rcases eq_or_ne (Real.sin θ) 0 with hθ | hθ
  · rw [character_symPower_torusExp_of_sin_eq_zero d hθ]
    simp only [map_mul, map_pow, map_add, map_one, map_natCast, Complex.conj_ofReal]
  · rw [character_symPower_torusExp_eq_sin_div_sin d hθ, Complex.conj_ofReal]

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

end SU2

end TauCeti
