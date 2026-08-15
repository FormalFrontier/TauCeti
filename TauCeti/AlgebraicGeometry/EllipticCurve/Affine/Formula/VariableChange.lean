/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula

/-!
# The affine group-law formulae under a change of variables

An admissible change of variables `C : VariableChange R` carries a point `(x, y)` of `C • W` to
the point `(u²x + r, u³y + u²sx + t)` of `W`. This file records what that substitution does to
each formula Mathlib's `Affine/Formula.lean` defines — `negY`, `addX`, `negAddY`, `addY` and
`slope` — to the two partial derivatives `polynomialX` and `polynomialY`, and to the two
predicates `Equation` and `Nonsingular` that cut the curve out.

## Main statements

* `WeierstrassCurve.Affine.variableChange_negY`, `_addX`, `_negAddY`, `_addY`: each formula
  transforms by an explicit power of `u`, together with the shear and translation the change of
  variables applies to the coordinate concerned.
* `WeierstrassCurve.Affine.variableChange_evalEval_polynomialX`, `_polynomialY`: the two partial
  derivatives transform by the matrix `![![u⁴, -su³], ![0, u³]]` — the `Y`-partial simply scales
  by `u³`, while the `X`-partial scales by `u⁴` and is sheared by an `s`-multiple of the
  `Y`-partial. Invertibility of that matrix is what `variableChange_nonsingular` runs on.
* `WeierstrassCurve.Affine.variableChange_equation`, `_nonsingular`: `(x, y)` lies on `C • W`,
  respectively is a smooth point of it, exactly when its image lies on `W`. Both are `@[simp]`.
  These are what make the change of variables carry points to points.
* `WeierstrassCurve.Affine.variableChange_slope`: the slope of the chord or tangent scales by `u`
  and translates by `s`.

## Implementation notes

The file is in two halves, split exactly where division starts. Everything except the slope is a
polynomial identity in the coefficients and the unit `u`, so it is stated over a commutative ring;
`variableChange_slope` is a quotient and needs a field.

Mathlib writes the coefficients of `C • W` with powers of `u⁻¹`. The five private
`u_pow_mul_variableChange_aᵢ` lemmas clear those denominators once, as `uⁱ * (C • W).aᵢ = …`, and
every identity in the first half is then a `linear_combination` of them which treats `(C • W).aᵢ`
as an atom and mentions no inverse at all. Multiplying an inverse away where it appears is what
needs a field; multiplying by `u` to cancel it does not.

The point-group isomorphism these identities are for is
`WeierstrassCurve.Affine.Point.equivVariableChange`, in `Affine/Point/VariableChange.lean`. The
split between the two files follows Mathlib's own: the formulae live in `Affine/Formula.lean` and
the point type in `Affine/Point.lean`, and nothing here mentions `Point`.

This is a prerequisite for `TauCetiRoadmap/EllipticCurves/README.md` §Layer 5's point isomorphism
for the quadratic twist.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean` at the roadmap's pin
`bc2fe8ff7396`, FLT PR #1088, Apache 2.0). That file's own header reads
`Authors: Michael Stoll, Claude`. Following this repository's convention for adapted material, the
upstream authorship is credited here rather than in the copyright header. FLT states these
identities over a field, as part of the file that builds the point map; stating the polynomial
ones over a commutative ring, and separating them from the point map, is this repository's.
-/

public section

namespace WeierstrassCurve.Affine

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R)

/-! ### The polynomial identities

Throughout, the change of variables carries a point `(x, y)` of `C • W` to the point
`(u²x + r, u³y + u²sx + t)` of `W`. -/

-- Mathlib's `variableChange_aᵢ` state the coefficients of `C • W` with a factor of `u⁻¹ ^ i`.
-- These five clear that factor, and are the only place `u⁻¹` is mentioned in this half of the
-- file: every identity below is a `linear_combination` of them over `R`, with `(C • W).aᵢ` left
-- as an atom. They are `private` because the `variableChange_aᵢ` themselves are the public way to
-- ask what the coefficients are.
private lemma u_mul_variableChange_a₁ : (C.u : R) * (C • W).a₁ = W.a₁ + 2 * C.s := by
  simp only [variableChange_a₁, Units.mul_inv_cancel_left]

private lemma u_pow_mul_variableChange_a₂ :
    (C.u : R) ^ 2 * (C • W).a₂ = W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2 := by
  simp only [variableChange_a₂, ← Units.val_pow_eq_pow_val, inv_pow, Units.mul_inv_cancel_left]

private lemma u_pow_mul_variableChange_a₃ :
    (C.u : R) ^ 3 * (C • W).a₃ = W.a₃ + C.r * W.a₁ + 2 * C.t := by
  simp only [variableChange_a₃, ← Units.val_pow_eq_pow_val, inv_pow, Units.mul_inv_cancel_left]

private lemma u_pow_mul_variableChange_a₄ :
    (C.u : R) ^ 4 * (C • W).a₄ = W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂
      - (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2 - 2 * C.s * C.t := by
  simp only [variableChange_a₄, ← Units.val_pow_eq_pow_val, inv_pow, Units.mul_inv_cancel_left]

private lemma u_pow_mul_variableChange_a₆ :
    (C.u : R) ^ 6 * (C • W).a₆ = W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3
      - C.t * W.a₃ - C.t ^ 2 - C.r * C.t * W.a₁ := by
  simp only [variableChange_a₆, ← Units.val_pow_eq_pow_val, inv_pow, Units.mul_inv_cancel_left]

/-- **`negY` under the change of variables.** The negation of the `y`-coordinate scales by `u³`
and picks up the same shear and translation the change of variables applies to `y`. -/
lemma variableChange_negY (x y : R) :
    W.toAffine.negY ((C.u : R) ^ 2 * x + C.r)
        ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      = (C.u : R) ^ 3 * (C • W).toAffine.negY x y + (C.u : R) ^ 2 * C.s * x + C.t := by
  simp only [negY]
  linear_combination (C.u : R) ^ 2 * x * u_mul_variableChange_a₁ W C
    + u_pow_mul_variableChange_a₃ W C

/-- **`addX` under the change of variables.** The `x`-coordinate of a sum scales by `u²` and
translates by `r`, the same law the change of variables applies to any `x`. -/
lemma variableChange_addX (x₁ x₂ ℓ : R) :
    W.toAffine.addX ((C.u : R) ^ 2 * x₁ + C.r) ((C.u : R) ^ 2 * x₂ + C.r) ((C.u : R) * ℓ + C.s)
      = (C.u : R) ^ 2 * (C • W).toAffine.addX x₁ x₂ ℓ + C.r := by
  simp only [addX]
  linear_combination (-(C.u : R) * ℓ) * u_mul_variableChange_a₁ W C
    + u_pow_mul_variableChange_a₂ W C

/-- **`negAddY` under the change of variables**, scaling by `u³` with the shear and translation
of the `y`-coordinate. -/
lemma variableChange_negAddY (x₁ x₂ y₁ ℓ : R) :
    W.toAffine.negAddY ((C.u : R) ^ 2 * x₁ + C.r) ((C.u : R) ^ 2 * x₂ + C.r)
        ((C.u : R) ^ 3 * y₁ + (C.u : R) ^ 2 * C.s * x₁ + C.t) ((C.u : R) * ℓ + C.s)
      = (C.u : R) ^ 3 * (C • W).toAffine.negAddY x₁ x₂ y₁ ℓ
        + (C.u : R) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp only [negAddY, variableChange_addX]
  ring

/-- **`addY` under the change of variables**, scaling by `u³` with the shear and translation of
the `y`-coordinate, plus the shear applied to `addX`. -/
lemma variableChange_addY (x₁ x₂ y₁ ℓ : R) :
    W.toAffine.addY ((C.u : R) ^ 2 * x₁ + C.r) ((C.u : R) ^ 2 * x₂ + C.r)
        ((C.u : R) ^ 3 * y₁ + (C.u : R) ^ 2 * C.s * x₁ + C.t) ((C.u : R) * ℓ + C.s)
      = (C.u : R) ^ 3 * (C • W).toAffine.addY x₁ x₂ y₁ ℓ
        + (C.u : R) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp only [addY, variableChange_negAddY, variableChange_addX, variableChange_negY]

/-- A point `(x, y)` lies on `C • W` if and only if `(u²x + r, u³y + u²sx + t)` lies on `W`: the
change of variables scales the Weierstrass polynomial by `u⁶`, and `u` is a unit. -/
@[simp] lemma variableChange_equation (x y : R) :
    W.toAffine.Equation ((C.u : R) ^ 2 * x + C.r)
        ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      ↔ (C • W).toAffine.Equation x y := by
  rw [equation_iff', equation_iff']
  refine Iff.trans ?_ (C.u.isUnit.pow 6).mul_right_eq_zero
  constructor
  · intro h
    linear_combination h + (C.u : R) ^ 5 * x * y * u_mul_variableChange_a₁ W C
      - (C.u : R) ^ 4 * x ^ 2 * u_pow_mul_variableChange_a₂ W C
      + (C.u : R) ^ 3 * y * u_pow_mul_variableChange_a₃ W C
      - (C.u : R) ^ 2 * x * u_pow_mul_variableChange_a₄ W C - u_pow_mul_variableChange_a₆ W C
  · intro h
    linear_combination h - (C.u : R) ^ 5 * x * y * u_mul_variableChange_a₁ W C
      + (C.u : R) ^ 4 * x ^ 2 * u_pow_mul_variableChange_a₂ W C
      - (C.u : R) ^ 3 * y * u_pow_mul_variableChange_a₃ W C
      + (C.u : R) ^ 2 * x * u_pow_mul_variableChange_a₄ W C + u_pow_mul_variableChange_a₆ W C

/-- **`polynomialY` under the change of variables**, scaling by `u³`. The `Y`-partial derivative
of the Weierstrass polynomial, evaluated at the image point, is `u³` times the corresponding
derivative of `C • W` evaluated at the source point. This is the second row `(0, u³)` of the
matrix in `variableChange_nonsingular` below. -/
lemma variableChange_evalEval_polynomialY (x y : R) :
    W.toAffine.polynomialY.evalEval ((C.u : R) ^ 2 * x + C.r)
        ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      = (C.u : R) ^ 3 * (C • W).toAffine.polynomialY.evalEval x y := by
  simp only [evalEval_polynomialY]
  linear_combination (-(C.u : R) ^ 2 * x) * u_mul_variableChange_a₁ W C
    - u_pow_mul_variableChange_a₃ W C

/-- **`polynomialX` under the change of variables**, scaling by `u⁴` and picking up a shear. The
`X`-partial derivative, evaluated at the image point, is `u⁴` times the corresponding derivative
of `C • W` at the source point, *minus* `s` times the `u³`-scaled `Y`-partial there. That extra
shear term is the one asymmetry between the two derivative laws, and it makes this the first row
`(u⁴, -su³)` of the matrix in `variableChange_nonsingular` below. -/
lemma variableChange_evalEval_polynomialX (x y : R) :
    W.toAffine.polynomialX.evalEval ((C.u : R) ^ 2 * x + C.r)
        ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      = (C.u : R) ^ 4 * (C • W).toAffine.polynomialX.evalEval x y
        - C.s * ((C.u : R) ^ 3 * (C • W).toAffine.polynomialY.evalEval x y) := by
  simp only [evalEval_polynomialX, evalEval_polynomialY]
  linear_combination (-(C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x) * u_mul_variableChange_a₁ W C
    + (2 * (C.u : R) ^ 2 * x) * u_pow_mul_variableChange_a₂ W C
    + C.s * u_pow_mul_variableChange_a₃ W C + u_pow_mul_variableChange_a₄ W C

/-- **Nonsingularity transfers across the change of variables.** The two partial derivatives
transform by the matrix `![![u⁴, -su³], ![0, u³]]` — the two lemmas just above — which is
invertible because `u` is, so `W_X ≠ 0 ∨ W_Y ≠ 0` holds at the image exactly when it holds at the
source.

This is what lets the point map of `Affine/Point/VariableChange.lean` avoid `[W.IsElliptic]`:
`equation_iff_nonsingular` would supply nonsingularity from the equation, but only for an elliptic
curve, whereas carrying a point to a point needs no such hypothesis. -/
@[simp] lemma variableChange_nonsingular (x y : R) :
    W.toAffine.Nonsingular ((C.u : R) ^ 2 * x + C.r)
        ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      ↔ (C • W).toAffine.Nonsingular x y := by
  rw [Nonsingular, Nonsingular, variableChange_equation]
  refine and_congr_right fun _ ↦ ?_
  rw [variableChange_evalEval_polynomialX W C x y, variableChange_evalEval_polynomialY W C x y,
    ← not_and_or, ← not_and_or]
  refine not_congr ⟨fun ⟨h1, h2⟩ ↦ ?_, fun ⟨h1, h2⟩ ↦ ?_⟩
  · have hB := (C.u.isUnit.pow 3).mul_right_eq_zero.mp h2
    rw [hB, mul_zero, mul_zero, sub_zero] at h1
    exact ⟨(C.u.isUnit.pow 4).mul_right_eq_zero.mp h1, hB⟩
  · exact ⟨by rw [h1, h2]; ring, by rw [h2]; ring⟩

end CommRing

section Field

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (C : VariableChange F)

/-! ### The slope

The slope of the chord or tangent is a quotient, so this is the first statement that needs to
divide, and the only one here that asks for a field. -/

/-- **The tangent case of `variableChange_slope`**: at a single point that is not its own
negation, the tangent slope scales by `u` and translates by `s`. The curve equations are not
needed — they are what `variableChange_slope` uses to reach this case. -/
private lemma variableChange_slope_of_Y_ne [DecidableEq F] {x y : F}
    (hy : y ≠ (C • W).toAffine.negY x y) :
    W.toAffine.slope ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      = (C.u : F) * (C • W).toAffine.slope x x y y + C.s := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  have hΦy : (C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t
      ≠ W.toAffine.negY ((C.u : F) ^ 2 * x + C.r)
          ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) := by
    rw [variableChange_negY]
    exact fun h ↦ hy (mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination h))
  rw [W.toAffine.slope_of_Y_ne rfl hΦy, (C • W).toAffine.slope_of_Y_ne rfl hy,
    ← mul_div_assoc, div_add' _ _ _ (sub_ne_zero.mpr hy),
    div_eq_div_iff (sub_ne_zero.mpr hΦy) (sub_ne_zero.mpr hy)]
  simp [negY, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄]
  field

/-- **The chord case of `variableChange_slope`**: through two points with distinct
`x`-coordinates, which stay distinct after the change of variables because `u` is a unit. The
curve equations are not needed here either. -/
private lemma variableChange_slope_of_X_ne [DecidableEq F] {x₁ x₂ y₁ y₂ : F} (hx : x₁ ≠ x₂) :
    W.toAffine.slope ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
        ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)
      = (C.u : F) * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  have hΦx : (C.u : F) ^ 2 * x₁ + C.r ≠ (C.u : F) ^ 2 * x₂ + C.r := by
    simpa [mul_right_inj' (pow_ne_zero 2 hu)] using hx
  rw [W.toAffine.slope_of_X_ne hΦx, (C • W).toAffine.slope_of_X_ne hx]
  have h1 := sub_ne_zero.mpr hΦx
  have h2 := sub_ne_zero.mpr hx
  field

/-- **The slope under the change of variables**, scaling by `u` and translating by `s` — the law
the change of variables applies to a slope, as `y` scales by `u³` and `x` by `u²`. Stated for two
points of `C • W` on the curve, excluding the degenerate case `x₁ = x₂ ∧ y₁ = negY x₂ y₂` —
where the two points are inverse to one another and the chord through them is vertical. -/
lemma variableChange_slope [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : (C • W).toAffine.Equation x₁ y₁) (h₂ : (C • W).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    W.toAffine.slope ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
        ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)
      = (C.u : F) * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  rcases eq_or_ne x₁ x₂ with rfl | hx
  · have hy : y₁ ≠ (C • W).toAffine.negY x₁ y₂ := fun h ↦ hxy ⟨rfl, h⟩
    obtain rfl := Y_eq_of_Y_ne h₁ h₂ rfl hy
    exact variableChange_slope_of_Y_ne W C hy
  · exact variableChange_slope_of_X_ne W C hx

end Field

end WeierstrassCurve.Affine

end
