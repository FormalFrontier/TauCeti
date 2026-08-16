/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Orthogonality
public import TauCeti.RepresentationTheory.SU2.Weyl.Character

/-!
# Orthonormality of the `SU(2)` characters over the Weyl chamber

`TauCeti/RepresentationTheory/SU2/Weyl/Character.lean` computes the character of the symmetric
power `Symᵈ(ℂ²)` on the maximal torus in the angle parametrisation:
`sin θ · χ_d (diag (e^{iθ}, e^{-iθ})) = sin ((d+1) θ)`, with no hypothesis on `θ`.

This file integrates the resulting products against the `SU(2)` **Weyl density**. Writing a class
function on `SU(2)` as a function of the angle `θ` on the Weyl chamber `[0, π]`, the Weyl
integration formula transports the Haar probability measure to the density
`(2π)⁻¹ · 4 sin²θ dθ`, whose Weyl factor `4 sin²θ = |e^{iθ} - e^{-iθ}|²` is the squared modulus of
the Weyl denominator. Against that density the characters of the symmetric powers are
**orthonormal**:

`(2π)⁻¹ ∫₀^π χ_m · conj χ_n · 4 sin²θ dθ = δ_{mn}`.

The computation is short once the Weyl numerator identity is in hand: the two factors of `sin θ`
in the density are absorbed by the two characters, turning the integrand into
`4 sin ((m+1) θ) sin ((n+1) θ)`, and the identity becomes the orthogonality of the sine system on
`[0, π]` (`TauCeti.two_div_pi_mul_integral_sin_succ_mul_sin_succ`). No case distinction at the
zeros of `sin` is needed, because the numerator identity holds there too.

Two things are deliberately *not* proved here. First, the Weyl integration formula itself -- that
integrating a class function over `SU(2)` against Haar equals the right-hand side above -- is a
measure-theoretic statement about `SU(2)`, and it is the missing input that would turn the results
below into the roadmap's `su2Character_orthonormal`. Second, that the `Symᵈ(ℂ²)` exhaust the
irreducible representations of `SU(2)`: that is the separate highest-weight classification, and
character orthonormality is validation for it, not a substitute.

## Main results

* `TauCeti.SU2.conj_character_symPower_torusExp`: the character of `Symᵈ(ℂ²)` is **real** on the
  maximal torus, so conjugating it in the integrand below changes nothing.
* `TauCeti.SU2.character_symPower_mul_conj_mul_weylFactor`: the pointwise absorption
  `χ_m · conj χ_n · 4 sin²θ = 4 sin ((m+1) θ) sin ((n+1) θ)`, valid at every angle.
* `TauCeti.SU2.weyl_integration_formula_normalized`: the total mass of the Weyl density is `1`,
  the normalization test `(2π)⁻¹ ∫₀^π 4 sin²θ dθ = 1`.
* `TauCeti.SU2.character_symPower_orthonormal`: **the orthonormality relation**
  `(2π)⁻¹ ∫₀^π χ_m · conj χ_n · 4 sin²θ dθ = δ_{mn}`.

## References

This is the Weyl-chamber half of the engine case of
`TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md`, "Engine case: `SU(2)` and the
maximal torus", whose acceptance criterion asks for the character orthonormality of `SU(2)` to be
computed through the Weyl integration formula, reducing to
`(2/π) ∫₀^π sin ((m+1) θ) sin ((n+1) θ) dθ = δ_{mn}`.

* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapters 17-18.
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter II, §5 and Chapter IV, §1.
-/

public section

namespace TauCeti

namespace SU2

/-- The character of `Symᵈ(ℂ²)` is **real on the maximal torus**: it is a sum of a weight string
`z^{-d} + ⋯ + z^{d}` closed under inversion, and both closed forms of
`TauCeti/RepresentationTheory/SU2/Weyl/Character.lean` exhibit it as the coercion of a real
number. -/
theorem conj_character_symPower_torusExp (d : ℕ) (θ : ℝ) :
    (starRingEnd ℂ) ((symPower d).character (torusExp θ))
      = (symPower d).character (torusExp θ) := by
  rcases eq_or_ne (Real.sin θ) 0 with hθ | hθ
  · rw [character_symPower_torusExp_of_sin_eq_zero d hθ]
    simp only [map_mul, map_pow, map_add, map_one, map_natCast, Complex.conj_ofReal]
  · rw [character_symPower_torusExp_eq_sin_div_sin d hθ, Complex.conj_ofReal]

/-- **The Weyl factor absorbs the two characters.** The factor `4 sin²θ = |e^{iθ} - e^{-iθ}|²` of
the Weyl density supplies one `sin θ` to each character, and each is turned into a Weyl numerator
by `TauCeti.SU2.sin_mul_character_symPower_torusExp`:

`χ_m (diag (e^{iθ}, e^{-iθ})) · conj χ_n (diag (e^{iθ}, e^{-iθ})) · 4 sin²θ
  = 4 sin ((m+1) θ) sin ((n+1) θ)`.

No hypothesis on `θ` is needed, in particular none at the zeros of `sin`, because the numerator
identity itself needs none. -/
theorem character_symPower_mul_conj_mul_weylFactor (m n : ℕ) (θ : ℝ) :
    (symPower m).character (torusExp θ)
        * (starRingEnd ℂ) ((symPower n).character (torusExp θ))
        * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ)
      = ((4 * Real.sin (((m : ℝ) + 1) * θ) * Real.sin (((n : ℝ) + 1) * θ) : ℝ) : ℂ) := by
  rw [conj_character_symPower_torusExp]
  have habsorb : (symPower m).character (torusExp θ) * (symPower n).character (torusExp θ)
      * (4 * (Real.sin θ : ℂ) ^ 2)
      = 4 * ((Real.sin θ : ℂ) * (symPower m).character (torusExp θ))
          * ((Real.sin θ : ℂ) * (symPower n).character (torusExp θ)) := by
    ring
  rw [show ((4 * Real.sin θ ^ 2 : ℝ) : ℂ) = 4 * (Real.sin θ : ℂ) ^ 2 by push_cast; ring, habsorb,
    sin_mul_character_symPower_torusExp, sin_mul_character_symPower_torusExp]
  push_cast
  ring

/-- **The Weyl density has total mass `1`.** This is the `f = 1` normalization test for the Weyl
integration formula of `SU(2)`: the transported torus density `(2π)⁻¹ · 4 sin²θ` on the Weyl
chamber `[0, π]` integrates to `1`, as it must if it is to represent the Haar *probability*
measure. -/
theorem weyl_integration_formula_normalized :
    (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..Real.pi, ((4 * Real.sin θ ^ 2 : ℝ) : ℂ) = 1 := by
  have hmass : ∫ θ in (0 : ℝ)..Real.pi, 4 * Real.sin θ ^ 2 = 2 * Real.pi := by
    rw [intervalIntegral.integral_const_mul, integral_sin_sq, Real.sin_zero, Real.sin_pi]
    ring
  rw [intervalIntegral.integral_ofReal, hmass]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- **Orthonormality of the `SU(2)` characters over the Weyl chamber.** Against the Weyl density
`(2π)⁻¹ · 4 sin²θ dθ` on `[0, π]`, the characters of the symmetric powers `Symᵈ(ℂ²)` of the
standard representation are orthonormal:

`(2π)⁻¹ ∫₀^π χ_m · conj χ_n · 4 sin²θ dθ = δ_{mn}`.

Composing this with the Weyl integration formula -- which reduces the Haar integral of a class
function on `SU(2)` to exactly this right-hand side, and which is *not* proved here -- gives the
character orthonormality `∫ χ_m · conj χ_n dμ = δ_{mn}` of the compact-groups roadmap.

The degree `m = n = 0` is the total-mass statement
`TauCeti.SU2.weyl_integration_formula_normalized`, since `Sym⁰(ℂ²)` is the trivial representation
and its character is `1`. -/
theorem character_symPower_orthonormal (m n : ℕ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..Real.pi,
        (symPower m).character (torusExp θ)
          * (starRingEnd ℂ) ((symPower n).character (torusExp θ))
          * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ)
      = if m = n then 1 else 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  -- The Weyl factor absorbs the characters, leaving a product of two Weyl numerators.
  simp only [character_symPower_mul_conj_mul_weylFactor]
  rw [intervalIntegral.integral_ofReal]
  -- Read the resulting real integral off the orthogonality of the sine system on `[0, π]`.
  have hconst : ∫ θ in (0 : ℝ)..Real.pi,
      4 * Real.sin (((m : ℝ) + 1) * θ) * Real.sin (((n : ℝ) + 1) * θ)
      = 4 * ∫ θ in (0 : ℝ)..Real.pi,
          Real.sin (((m : ℝ) + 1) * θ) * Real.sin (((n : ℝ) + 1) * θ) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun θ _ => by ring
  rw [hconst, integral_sin_succ_mul_sin_succ]
  rcases eq_or_ne m n with rfl | hmn
  · rw [ite_eq_left rfl, ite_eq_left rfl]
    push_cast
    field_simp
    norm_num
  · rw [ite_eq_right hmn, ite_eq_right hmn]
    simp

end SU2

end TauCeti
