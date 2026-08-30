/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The duplication formulae and the `x`-coordinate addition formulae

Affine-coordinate arithmetic on a Weierstrass curve, independent of any theory of heights: the
numerator and denominator of the duplication formula, the `x`-coordinate addition formulae, and
their transport to the projective representative `Point.xRep`.

Finiteness of the fibres of `xRep` is *not* here — it uses none of these formulae and lives in
`TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.XRep`.

Nothing here mentions a height. These are consumed by
`TauCeti.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap` and, through it, by the naïve-height
development in `TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.NaiveHeight`.

## Main results

* `WeierstrassCurve.Affine.den_duplication_eq` : the denominator of the duplication formula.
* `WeierstrassCurve.Affine.addX_self_of_Y_ne`, `addX_of_X_ne` : the `x`-coordinate addition
  formulae, as quotients.
* `WeierstrassCurve.Affine.Point.xRep_add_self_of_Y_ne` and companions : the same, transported to
  the projective representative.

## Relation to Mathlib

Mathlib's `Point.xRep` and the `addSubMap` / `sym2x` apparatus are *consumed*, not restated. The
declarations here are absent from Mathlib at the version this repository pins, which is why they
are stated rather than imported: Stoll's source brackets exactly this block with a reference to
Mathlib PR `#40303`, and `Mathlib/NumberTheory/Height/EllipticCurve.lean` — a file by the same
author — carries a `TODO` naming this scope. This is a deliberate, temporary duplication with a
defined end: if a later pin bump lands that upstream work, the superseded declarations here must
be deleted and their uses repointed at Mathlib in the same pull request, per this repository's
no-compatibility-shims rule.

## References

* [M. Stoll, *EllipticCurves*](https://github.com/MichaelStollBayreuth/EllipticCurves), commit
  `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, `EllipticCurves/MordellWeil.lean`, Apache-2.0.
-/

public section

namespace WeierstrassCurve

namespace Affine

variable {R : Type*} [CommRing R] {W' : Affine R}

/-! ### The duplication numerator and denominator -/

/-- The denominator of the duplication formula is a square on the curve. -/
lemma den_duplication_eq {x y : R} (h : W'.Equation x y) :
    4 * x ^ 3 + W'.b₂ * x ^ 2 + 2 * W'.b₄ * x + W'.b₆ = (2 * y + W'.a₁ * x + W'.a₃) ^ 2 := by
  have Heq := (W'.equation_iff x y).mp h
  simp only [b₂, b₄, b₆]
  linear_combination -4 * Heq

/-- The duplication denominator vanishes exactly when the solution is fixed by `negY`.

Deliberately *not* phrased as "the points of order dividing `2`": `R` here is only a reduced
commutative ring and `(x, y)` only a solution of the Weierstrass equation, so there is no group
in which such a point has an order. That reading needs a field and nonsingularity, and belongs
with a statement carrying those hypotheses. -/
lemma den_duplication_eq_zero_iff [IsReduced R] {x y : R} (h : W'.Equation x y) :
    4 * x ^ 3 + W'.b₂ * x ^ 2 + 2 * W'.b₄ * x + W'.b₆ = 0 ↔ y = W'.negY x y := by
  rw [den_duplication_eq h, sq_eq_zero_iff, negY]
  grind only

variable {F : Type*} [Field F] {W : Affine F}

/-- At a nonsingular point the duplication numerator and denominator do not both vanish. -/
lemma den_duplication_ne_zero_or_num_duplication_ne_zero {x y : F} (h : W.Nonsingular x y) :
    4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ ≠ 0 ∨
      x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ ≠ 0 := by
  have ⟨h₁, h₂⟩ := (W.nonsingular_iff x y).mp h
  rw [equation_iff x y] at h₁
  by_cases H : 2 * y + W.a₁ * x + W.a₃ = 0
  · right
    replace h₂ : W.a₁ * y ≠ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by grind
    contrapose! h₂
    rw [b₄, b₆, b₈] at h₂
    grobner
  · left
    clear h₂
    contrapose! H
    rw [b₂, b₄, b₆] at H
    grobner

section Decidable

variable [DecidableEq F]

/-- The duplication formula for the `x`-coordinate, as a quotient. -/
lemma addX_self_of_Y_ne {x y : F} (h : W.Equation x y) (hn : y ≠ W.negY x y) :
    W.addX x x (W.slope x x y y) =
      (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
  have aux {a b c : F} (h : a ≠ 0) : a ^ 2 * (b * (c / a)) = a * b * c := by field
  have hn' := (den_duplication_eq_zero_iff h).not.mpr hn
  refine mul_left_cancel₀ hn' ?_
  have hn'' : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    rw [den_duplication_eq h] at hn'
    grind
  rw [mul_div_cancel₀ _ hn', addX, sub_sub, sub_sub, mul_sub, mul_add]
  simp only [slope, ↓reduceIte, hn]
  have hy : y - (-y - W.a₁ * x - W.a₃) = 2 * y + W.a₁ * x + W.a₃ := by ring
  rw [negY, hy, div_pow]
  nth_rewrite 1 2 [den_duplication_eq h]
  rw [mul_div_cancel₀ _ <| pow_ne_zero 2 hn'', aux hn'', b₂, b₄, b₆, b₈]
  linear_combination -W.a₁ ^ 2 * (W.equation_iff x y).mp h

/-- The addition formula for the `x`-coordinate at points with distinct `x`, as a quotient. -/
lemma addX_of_X_ne {xP yP xQ yQ : F} (hn : xP ≠ xQ) :
     W.addX xP xQ (W.slope xP xQ yP yQ) =
       ((yP - yQ) ^ 2 + W.a₁ * (yP - yQ) * (xP - xQ) - (W.a₂ + xP + xQ) * (xP - xQ) ^2) /
         (xP - xQ) ^ 2 := by
  have hxPQ' : xP - xQ ≠ 0 := by grind only
  simp [addX, slope, hn, div_pow]
  field

/-- The projective `x`-coordinate of `P + P` when `2 • P ≠ 0`. -/
lemma Point.xRep_add_self_of_Y_ne {x y : F} (h : W.Nonsingular x y) (hn : y ≠ W.negY x y) :
    (some x y h + some x y h).xRep =
      ![(x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆), 1] := by
  simp only [add_self_of_Y_ne hn, ← addX_self_of_Y_ne h.1 hn, xRep_some]

/-- The projective `x`-coordinate of `P + P` when `P ≠ 0` and `2 • P = 0`. -/
lemma Point.xRep_add_self_of_Y_eq {x y : F} (h : W.Nonsingular x y) (hn : y = W.negY x y) :
    (some x y h + some x y h).xRep = ![1, 0] := by
  simp only [add_self_of_Y_eq hn, xRep_zero]

/-- The projective `x`-coordinate of `P + Q` when `P ≠ ±Q`. -/
lemma Point.xRep_add_of_X_ne {xP yP xQ yQ : F} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hn : xP ≠ xQ) :
    (some xP yP hP + some xQ yQ hQ).xRep =
      ![((yP - yQ) ^ 2 + W.a₁ * (yP - yQ) * (xP - xQ) - (W.a₂ + xP + xQ) * (xP - xQ) ^2) /
         (xP - xQ) ^ 2, 1] := by
  simp only [add_of_X_ne (h₁ := hP) (h₂ := hQ) hn, xRep_some, addX_of_X_ne hn]

/-- The projective `x`-coordinate of `P - Q` when `P ≠ ±Q`. -/
lemma Point.xRep_sub_of_X_ne {xP yP xQ yQ : F} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hn : xP ≠ xQ) :
    (some xP yP hP - some xQ yQ hQ).xRep =
      ![((yP + yQ + W.a₁ * xQ + W.a₃) ^ 2 + W.a₁ * (yP + yQ + W.a₁ * xQ + W.a₃) * (xP - xQ)
           - (W.a₂ + xP + xQ) * (xP - xQ) ^2) / (xP - xQ) ^ 2, 1] := by
  simp only [sub_eq_add_neg (some ..), neg_some hQ,
    add_of_X_ne (h₁ := hP) (h₂ := (nonsingular_neg ..).mpr hQ) hn, xRep_some,
    addX_of_X_ne hn]
  grind only [negY]

end Decidable

end Affine

end WeierstrassCurve

end
