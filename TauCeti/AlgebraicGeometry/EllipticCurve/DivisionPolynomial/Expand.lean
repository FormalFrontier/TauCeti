/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.Algebra.Polynomial.Expand

/-!
# Division polynomials in characteristic `p` are `p`-th power substitutions

In characteristic `p` the low division polynomials of a Weierstrass curve lie in the image of
`Polynomial.expand R p`, that is, they are polynomials in `Xᵖ`. This is the base case of the
factorisation of the `p`-power isogeny through Frobenius (Silverman III.6.2): the terms that
obstruct it all carry a factor of `p`.

Concretely, in characteristic `2` the `2 * b₆ * X` term of `Φ₂` and the `4X³`, `2b₄X` terms of
`ΨSq₂` vanish; in characteristic `3` the `3X⁴`, `3b₄X²`, `3b₆X` terms of `Ψ₃` vanish. Everything
is stated over an arbitrary commutative ring carrying `CharP`, so it specialises unchanged to a
field or to a universal polynomial ring.

## Main results

* `TauCeti.WeierstrassCurve.Φ_two_mem_range_expand`, `ΨSq_two_mem_range_expand`: characteristic
  two.
* `TauCeti.WeierstrassCurve.Ψ₃_mem_range_expand`, `ΨSq_three_mem_range_expand`,
  `Φ_three_mem_range_expand`: characteristic three.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/Verschiebung/DivPolyExpand.lean`, declarations `Φ_two_mem_expand_two_charP`,
`ΨSq_two_mem_expand_two_charP`, `Ψ₃_mem_expand_three_charP`,
`ΨSq_three_mem_expand_three_charP` and `Φ_three_mem_expand_three_charP`.

The source's `b_relation_of_charP_three` is not ported: Mathlib already has it verbatim as
`WeierstrassCurve.b_relation_of_char_three` (`Weierstrass.lean:213`).

The source's proof of `Φ_three_mem_expand_three_charP` raises the elaboration heartbeat limit
to five times the default, which this repository forbids. The witness cubic and the
`linear_combination` strategy here are the source's (its multipliers are symbolically verified
over `ℤ`, as there); substituting the characteristic-three `b`-relation at the `C`-level inside
the `linear_combination`, rather than rewriting it into the goal, is what lets the same argument
elaborate within the default budget.
-/

public section

open Polynomial

namespace TauCeti

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : _root_.WeierstrassCurve R)

/-- In characteristic two, `Φ₂` is a polynomial in `X²`.

`Φ₂ = X⁴ − b₄X² − 2b₆X − b₈`, and the `2b₆X` term vanishes. -/
theorem Φ_two_mem_range_expand [CharP R 2] : W.Φ 2 ∈ Set.range (⇑(expand R 2)) := by
  refine ⟨X ^ 2 - C W.b₄ * X - C W.b₈, ?_⟩
  simp only [W.Φ_two, map_sub, map_mul, map_pow, expand_C, expand_X, C_ofNat]
  linear_combination (X * C W.b₆) * CharP.cast_eq_zero R[X] 2

/-- In characteristic two, `ΨSq₂` is a polynomial in `X²`.

`ΨSq₂ = Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆`, and the `4X³` and `2b₄X` terms vanish. -/
theorem ΨSq_two_mem_range_expand [CharP R 2] : W.ΨSq 2 ∈ Set.range (⇑(expand R 2)) := by
  refine ⟨C W.b₂ * X + C W.b₆, ?_⟩
  simp only [W.ΨSq_two, _root_.WeierstrassCurve.Ψ₂Sq, map_add, map_mul, expand_C, expand_X,
    C_ofNat]
  linear_combination (-2 * X ^ 3 - X * C W.b₄) * CharP.cast_eq_zero R[X] 2

/-- In characteristic three, `Ψ₃` is a polynomial in `X³`.

`Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈`, and every term with a factor of `3` vanishes. -/
theorem Ψ₃_mem_range_expand [CharP R 3] : W.Ψ₃ ∈ Set.range (⇑(expand R 3)) := by
  refine ⟨C W.b₂ * X + C W.b₈, ?_⟩
  simp only [_root_.WeierstrassCurve.Ψ₃, map_add, map_mul, expand_C, expand_X]
  linear_combination -(X ^ 4 + C W.b₄ * X ^ 2 + C W.b₆ * X) * CharP.cast_eq_zero R[X] 3

/-- In characteristic three, `ΨSq₃` is a polynomial in `X³`, since it is `Ψ₃²` and `expand` is
multiplicative. -/
theorem ΨSq_three_mem_range_expand [CharP R 3] : W.ΨSq 3 ∈ Set.range (⇑(expand R 3)) := by
  obtain ⟨g, hg⟩ := Ψ₃_mem_range_expand W
  exact ⟨g ^ 2, by rw [W.ΨSq_three, ← hg, map_pow]⟩

/-- In characteristic three, `Φ₃` is a polynomial in `X³`: explicitly, `Φ₃ = expand 3 g` for the
cubic `g = X³ − b₂b₄X² + (b₂²b₄² − b₂³b₆ + b₂b₄b₆)X + (b₄³b₆ − b₂b₄b₆² + b₆³)`.

The difference `expand 3 g − Φ₃` is `3·M + N·(b₂b₆ − b₄² − b₈)` for explicit polynomials `M`, `N`
(computed symbolically over `ℤ`, entering through `linear_combination`), so it vanishes by
`CharP.cast_eq_zero` and the characteristic-three `b`-relation
`WeierstrassCurve.b_relation_of_char_three`. -/
theorem Φ_three_mem_range_expand [CharP R 3] : W.Φ 3 ∈ Set.range (⇑(expand R 3)) := by
  have h3 : (3 : R[X]) = 0 := by exact_mod_cast CharP.cast_eq_zero R[X] 3
  have hbC : C W.b₈ = C W.b₂ * C W.b₆ - C W.b₄ ^ 2 := by
    rw [W.b_relation_of_char_three, map_sub, map_mul, map_pow]
  refine ⟨X ^ 3 - C W.b₂ * C W.b₄ * X ^ 2 +
    (C W.b₂ ^ 2 * C W.b₄ ^ 2 - C W.b₂ ^ 3 * C W.b₆ + C W.b₂ * C W.b₄ * C W.b₆) * X +
    (C W.b₄ ^ 3 * C W.b₆ - C W.b₂ * C W.b₄ * C W.b₆ ^ 2 + C W.b₆ ^ 3), ?_⟩
  rw [_root_.WeierstrassCurve.Φ_three]
  simp only [_root_.WeierstrassCurve.Ψ₃, _root_.WeierstrassCurve.preΨ₄,
    _root_.WeierstrassCurve.Ψ₂Sq, map_add, map_sub, map_mul, map_pow, map_ofNat, expand_C,
    expand_X]
  linear_combination (2 * C W.b₄ * X ^ 7 + 8 * C W.b₆ * X ^ 6 +
      (13 * C W.b₂ * C W.b₆ - 11 * C W.b₄ ^ 2) * X ^ 5 +
      (4 * C W.b₂ ^ 2 * C W.b₆ - 4 * C W.b₂ * C W.b₄ ^ 2 + C W.b₄ * C W.b₆) * X ^ 4 +
      (6 * C W.b₂ * C W.b₄ * C W.b₆ - 6 * C W.b₄ ^ 3 - C W.b₆ ^ 2) * X ^ 3 +
      (C W.b₂ ^ 2 * C W.b₄ * C W.b₆ - C W.b₂ * C W.b₄ ^ 3 + C W.b₂ * C W.b₆ ^ 2 -
        2 * C W.b₄ ^ 2 * C W.b₆) * X ^ 2 +
      (C W.b₂ * C W.b₄ ^ 2 * C W.b₆ - C W.b₄ ^ 4 - C W.b₄ * C W.b₆ ^ 2) * X) * h3 +
    (34 * X ^ 5 + 12 * C W.b₂ * X ^ 4 + (C W.b₂ ^ 2 + 18 * C W.b₄) * X ^ 3 +
      (3 * C W.b₂ * C W.b₄ + 4 * C W.b₆) * X ^ 2 + (3 * C W.b₄ ^ 2 - C W.b₈) * X +
      C W.b₄ * C W.b₆) * hbC

end WeierstrassCurve

end TauCeti
