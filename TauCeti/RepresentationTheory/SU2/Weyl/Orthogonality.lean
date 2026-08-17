/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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

* `TauCeti.SU2.character_symPower_mul_conj_mul_four_mul_sin_sq`: the pointwise absorption
  `χ_m · conj χ_n · 4 sin²θ = 4 · (sin ((m+1) θ) · sin ((n+1) θ))`, valid at every angle.
* `TauCeti.SU2.character_symPower_orthonormal_torusExp`: **the orthonormality relation**
  `(2π)⁻¹ ∫₀^π χ_m · conj χ_n · 4 sin²θ dθ = δ_{mn}`.
* `TauCeti.SU2.weyl_integration_formula_normalized`: the total mass of the Weyl density is `1`,
  the normalization test `(2π)⁻¹ ∫₀^π 4 sin²θ dθ = 1`. This is the degree `m = n = 0` case of the
  orthonormality relation, and is derived from it.

The realness of the character on the torus, which makes the conjugation in the integrand
harmless, is `TauCeti.SU2.conj_character_symPower_torusExp`, proved with the closed forms in
`TauCeti/RepresentationTheory/SU2/Weyl/Character.lean`.

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

/-- **The Weyl factor absorbs the two characters.** The factor `4 sin²θ = |e^{iθ} - e^{-iθ}|²` of
the Weyl density supplies one `sin θ` to each character, and each is turned into a Weyl numerator
by `TauCeti.SU2.sin_mul_character_symPower_torusExp`:

`χ_m (diag (e^{iθ}, e^{-iθ})) · conj χ_n (diag (e^{iθ}, e^{-iθ})) · 4 sin²θ
  = 4 · (sin ((m+1) θ) · sin ((n+1) θ))`.

No hypothesis on `θ` is needed, in particular none at the zeros of `sin`, because the numerator
identity itself needs none. -/
theorem character_symPower_mul_conj_mul_four_mul_sin_sq (m n : ℕ) (θ : ℝ) :
    (symPower m).character (torusExp θ)
        * (starRingEnd ℂ) ((symPower n).character (torusExp θ))
        * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ)
      = ((4 * (Real.sin (((m : ℝ) + 1) * θ) * Real.sin (((n : ℝ) + 1) * θ)) : ℝ) : ℂ) := by
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

/-- **Orthonormality of the `SU(2)` characters over the Weyl chamber.** Against the Weyl density
`(2π)⁻¹ · 4 sin²θ dθ` on `[0, π]`, the characters of the symmetric powers `Symᵈ(ℂ²)` of the
standard representation are orthonormal:

`(2π)⁻¹ ∫₀^π χ_m · conj χ_n · 4 sin²θ dθ = δ_{mn}`.

The name records that this is orthonormality of the characters *restricted to the torus*, against
the transported density, not against Haar measure on `SU(2)`. Composing it with the Weyl
integration formula -- which reduces the Haar integral of a class function on `SU(2)` to exactly
this right-hand side, and which is *not* proved here -- gives the character orthonormality
`∫ χ_m · conj χ_n dμ = δ_{mn}` of the compact-groups roadmap, in the shape of the abstract
`TauCeti.ContRepresentation.character_orthonormal_self` and
`TauCeti.ContRepresentation.character_orthonormal_distinct`
(`TauCeti/RepresentationTheory/Compact/Character/Basic.lean`), whose name shape this deliberately
does *not* reuse. -/
theorem character_symPower_orthonormal_torusExp (m n : ℕ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..Real.pi,
        (symPower m).character (torusExp θ)
          * (starRingEnd ℂ) ((symPower n).character (torusExp θ))
          * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ)
      = if m = n then 1 else 0 := by
  -- The Weyl factor absorbs the characters, leaving a product of two Weyl numerators.
  simp only [character_symPower_mul_conj_mul_four_mul_sin_sq]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul]
  -- The Weyl normalization `(2π)⁻¹` and the factor `4` combine into the `2/π` of the sine system.
  have hnorm : ∀ I : ℝ, 1 / (2 * Real.pi) * (4 * I) = 2 / Real.pi * I := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    intro I
    field_simp
    ring
  have hreal : 1 / (2 * Real.pi) * (4 * ∫ θ in (0 : ℝ)..Real.pi,
      Real.sin (((m : ℝ) + 1) * θ) * Real.sin (((n : ℝ) + 1) * θ))
      = if m = n then (1 : ℝ) else 0 := by
    rw [hnorm, two_div_pi_mul_integral_sin_succ_mul_sin_succ]
  rw [show (if m = n then (1 : ℂ) else 0) = ((if m = n then (1 : ℝ) else 0 : ℝ) : ℂ) by
    split <;> simp, ← hreal]
  push_cast
  ring

/-- **The Weyl density has total mass `1`.** This is the `f = 1` normalization test for the Weyl
integration formula of `SU(2)`: the transported torus density `(2π)⁻¹ · 4 sin²θ` on the Weyl
chamber `[0, π]` integrates to `1`, as it must if it is to represent the Haar *probability*
measure.

It is the degree `m = n = 0` case of `TauCeti.SU2.character_symPower_orthonormal_torusExp`, since
`Sym⁰(ℂ²)` is the trivial representation and its character is `1`, and is proved that way. -/
theorem weyl_integration_formula_normalized :
    (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..Real.pi, ((4 * Real.sin θ ^ 2 : ℝ) : ℂ) = 1 := by
  have h := character_symPower_orthonormal_torusExp 0 0
  rw [ite_eq_left rfl] at h
  -- `Sym⁰(ℂ²)` has character `1`, so its integrand is the Weyl factor itself.
  have hint : ∫ θ in (0 : ℝ)..Real.pi, ((4 * Real.sin θ ^ 2 : ℝ) : ℂ)
      = ∫ θ in (0 : ℝ)..Real.pi, (symPower 0).character (torusExp θ)
          * (starRingEnd ℂ) ((symPower 0).character (torusExp θ))
          * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ) :=
    intervalIntegral.integral_congr fun θ _ => by
      rw [character_symPower_mul_conj_mul_four_mul_sin_sq]
      norm_num [pow_two]
  rw [hint, h]

end SU2

end TauCeti
