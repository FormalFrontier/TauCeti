/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The chord construction computes the group law

Over a field, a point of a Weierstrass curve `W` away from the origin can be written in the
`(z, w)`-chart of `WeierstrassCurve.formalW` as `(z / w, -1 / w)`, coming from the substitution
`x = z / w`, `y = -1 / w`. This file proves that such a point is nonsingular, and that the chord
construction in that chart computes the group law: the third intersection point of the chord
through two of them is, after negation, their sum in `WeierstrassCurve.Affine.Point`.

Everything here is an identity between field elements. The parameters `Λ`, `N` and `z₃` of the
chord enter as hypotheses saying they satisfy the defining relations — the same relations that
`formalSlope`, `formalIntercept` and `formalThirdRoot` satisfy as power series — so that this
file is independent of the power-series development and can be applied to it later.

## Main results

* `WeierstrassCurve.chord_point_nonsingular`: a point of the `(z, w)`-chart is nonsingular.
* `WeierstrassCurve.chord_point_add`: the third point of the chord computes the group law.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeierstrassFormalGroup/ThirdPoint.lean`, its `FieldChord` section —
declarations `chord_x_ne`, `chord_point_nonsingular`, `chord_addX_addY` and `chord_point_add`.
-/

public section

namespace WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

private lemma chord_x_ne {q₁ q₂ w₁ w₂ : F} (hw₁0 : w₁ ≠ 0) (hw₂0 : w₂ ≠ 0)
    (hx : q₁ * w₂ - q₂ * w₁ ≠ 0) : q₁ / w₁ ≠ q₂ / w₂ := by
  intro h
  apply hx
  field_simp at h
  linear_combination h

/-- The parametrized point `(q/w, -1/w)` is nonsingular whenever `(q, w)` satisfies the
Weierstrass equation in the `(z, w)`-chart and the discriminant does not vanish. -/
lemma chord_point_nonsingular {q w : F}
    (hw : w = q ^ 3 + W.a₁ * q * w + W.a₂ * q ^ 2 * w + W.a₃ * w ^ 2 +
      W.a₄ * q * w ^ 2 + W.a₆ * w ^ 3)
    (hw0 : w ≠ 0) (hΔ : W.Δ ≠ 0) :
    W.toAffine.Nonsingular (q / w) (-1 / w) := by
  refine (W.toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp ?_
  rw [Affine.equation_iff]
  field_simp
  linear_combination hw


/-- The cubic in the chord parameter left by substituting the line `w = Λ z + N` into the
`(z, w)`-form of the Weierstrass equation, with its leading coefficient carried as the parameter
`AA`.

The geometric reading needs `AA` pinned: **when** `AA = 1 + a₂Λ + a₄Λ² + a₆Λ³`, which is what
`hAA2` supplies at every use below, this is the cubic whose roots are the parameters of the points
where the chord meets the curve. For an unconstrained `AA` it is just the substituted expression
and carries no such meaning. -/
-- `AA` is carried as a parameter rather than inlined because the `linear_combination` certificates
-- below are written against it as a single atom: substituting the expansion here makes `ring` fail
-- in `chordCubic_eq_zero`, `chord_addX` and `chord_addY` alike.
private def chordCubic (AA Λ N q : F) : F :=
  -N + AA * q ^ 3 + W.a₃ * N ^ 2 + W.a₆ * N ^ 3 - Λ * q + Λ * W.a₁ * q ^ 2 +
    N * W.a₁ * q + N * W.a₂ * q ^ 2 + W.a₃ * Λ ^ 2 * q ^ 2 + W.a₄ * q * N ^ 2 +
    2 * Λ * N * W.a₃ * q + 2 * Λ * N * W.a₄ * q ^ 2 + 3 * Λ * W.a₆ * q * N ^ 2 +
    3 * N * W.a₆ * Λ ^ 2 * q ^ 2

/-- Each chord parameter is a root of `chordCubic`: a point of the `(z, w)`-chart lying on the
line `w = Λ z + N` has its parameter annihilate the cubic. Applied at each of `z₁`, `z₂`. -/
private lemma chordCubic_eq_zero {AA Λ N q w : F}
    (hAA2 : AA = 1 + W.a₂ * Λ + W.a₄ * Λ ^ 2 + W.a₆ * Λ ^ 3)
    (hw : w = q ^ 3 + W.a₁ * q * w + W.a₂ * q ^ 2 * w + W.a₃ * w ^ 2 +
      W.a₄ * q * w ^ 2 + W.a₆ * w ^ 3)
    (hline : w = Λ * q + N) :
    W.chordCubic AA Λ N q = 0 := by
  simp only [chordCubic]
  linear_combination -hw + (1 + w*(-W.a₃ - N*W.a₆ - W.a₄*q - Λ*W.a₆*q) - N*W.a₃
    - W.a₁*q - W.a₂*q^2 - W.a₆*N^2 - W.a₆*w^2 - Λ*W.a₃*q - Λ*W.a₄*q^2 - N*W.a₄*q
    - W.a₆*Λ^2*q^2 - 2*Λ*N*W.a₆*q) * hline + (q^3) * hAA2

/-- The `x`-coordinate half of the chord identity: the third parameter gives Mathlib's `addX`. -/
private lemma chord_addX {AA Λ N q₁ q₂ w₁ w₂ T₃ wT : F}
    (hAA2 : AA = 1 + W.a₂ * Λ + W.a₄ * Λ ^ 2 + W.a₆ * Λ ^ 3)
    (hline₁ : w₁ = Λ * q₁ + N) (hline₂ : w₂ = Λ * q₂ + N)
    (hCub₁ : W.chordCubic AA Λ N q₁ = 0) (hCub₂ : W.chordCubic AA Λ N q₂ = 0)
    (hT₃ : AA * (T₃ + q₁ + q₂) =
      -(W.a₁ * Λ + W.a₂ * N + W.a₃ * Λ ^ 2 + 2 * W.a₄ * Λ * N + 3 * W.a₆ * Λ ^ 2 * N))
    (hwT : wT = Λ * T₃ + N) (hA : AA ≠ 0) (hq12 : q₁ - q₂ ≠ 0) (hN0 : N ≠ 0)
    (hw₁0 : w₁ ≠ 0) (hw₂0 : w₂ ≠ 0) (hwT0 : wT ≠ 0) :
    T₃ / wT = W.toAffine.addX (q₁ / w₁) (q₂ / w₂) (Λ / N) := by
  simp only [chordCubic] at hCub₁ hCub₂
  rw [Affine.addX]
  field_simp
  refine mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 3 hA) hq12) ?_
  linear_combination (AA^3*(w₂*N^2*q₁^2 - w₁*N^2*q₂^2 + q₁*q₂*w₁*N^2 + q₂*w₁*w₂*Λ^2
    - q₁*q₂*w₂*N^2 - q₁*w₁*w₂*Λ^2 + W.a₂*q₁*w₁*w₂*N^2 - W.a₂*q₂*w₁*w₂*N^2
    + Λ*N*W.a₁*q₂*w₁*w₂ - Λ*N*W.a₁*q₁*w₁*w₂)) * hwT +
  (AA^3*(-N^3*q₂^2 + q₁*q₂*N^3 + N*q₂*w₂*Λ^2 + T₃*q₁*w₂*N^2 + T₃*q₂*w₂*Λ^3 + W.a₂*q₁*w₂*N^3
    - Λ*T₃*N^2*q₂^2 - N*q₁*w₂*Λ^2 - T₃*q₁*w₂*Λ^3 - T₃*q₂*w₂*N^2 - W.a₂*q₂*w₂*N^3
    + Λ*T₃*q₁*q₂*N^2 + Λ*W.a₁*q₂*w₂*N^2 - Λ*W.a₁*q₁*w₂*N^2 + Λ*T₃*W.a₂*q₁*w₂*N^2
    + N*T₃*W.a₁*q₂*w₂*Λ^2 - Λ*T₃*W.a₂*q₂*w₂*N^2 - N*T₃*W.a₁*q₁*w₂*Λ^2)) * hline₁ +
  (AA^3*(N^3*q₁^2 + T₃*q₁*N^3 + W.a₂*q₁*N^4 + q₂*Λ^2*N^2 - N*Λ^3*q₁^2 - T₃*q₂*N^3
    - T₃*Λ^4*q₁^2 - W.a₂*q₂*N^4 - q₁*q₂*N^3 - q₁*Λ^2*N^2 + Λ*W.a₁*q₂*N^3 + Λ*W.a₂*N^3*q₁^2
    + N*T₃*q₂*Λ^3 + N*q₁*q₂*Λ^3 + T₃*q₁*q₂*Λ^4 - Λ*W.a₁*q₁*N^3 - N*T₃*q₁*Λ^3
    - W.a₁*Λ^2*N^2*q₁^2 + 2*Λ*T₃*N^2*q₁^2 + Λ*T₃*W.a₂*q₁*N^3 + T₃*W.a₁*q₂*Λ^2*N^2
    + T₃*W.a₂*Λ^2*N^2*q₁^2 + W.a₁*q₁*q₂*Λ^2*N^2 - Λ*T₃*W.a₂*q₂*N^3 - Λ*W.a₂*q₁*q₂*N^3
    - N*T₃*W.a₁*Λ^3*q₁^2 - T₃*W.a₁*q₁*Λ^2*N^2 - 2*Λ*T₃*q₁*q₂*N^2 + N*T₃*W.a₁*q₁*q₂*Λ^3
    - T₃*W.a₂*q₁*q₂*Λ^2*N^2)) * hline₂ +
  (AA^2*(q₁*N^4 - q₂*N^4 + N*Λ^4*q₂^2 + q₁*Λ^5*q₂^2 + q₂*Λ^3*N^2 - N*Λ^4*q₁^2 - q₁*Λ^3*N^2
    - q₂*Λ^5*q₁^2 - 2*Λ*N^3*q₂^2 + 2*Λ*N^3*q₁^2 + Λ*W.a₂*q₁*N^4 + W.a₁*q₂*Λ^2*N^3
    + W.a₁*Λ^3*N^2*q₂^2 + W.a₂*Λ^2*N^3*q₁^2 - Λ*W.a₂*q₂*N^4 - W.a₁*q₁*Λ^2*N^3
    - W.a₁*Λ^3*N^2*q₁^2 - W.a₂*Λ^2*N^3*q₂^2 - 3*q₁*Λ^2*N^2*q₂^2 + 3*q₂*Λ^2*N^2*q₁^2
    + N*W.a₁*q₁*Λ^4*q₂^2 + W.a₂*q₂*Λ^3*N^2*q₁^2 - N*W.a₁*q₂*Λ^4*q₁^2
    - W.a₂*q₁*Λ^3*N^2*q₂^2)) * hT₃ +
  (AA*(AA*N*Λ^4 + AA*q₂*Λ^5 - 2*AA*Λ*N^3 + AA*W.a₁*Λ^3*N^2 - AA*W.a₂*Λ^2*N^3
    - 3*AA*q₂*Λ^2*N^2 + AA*N*W.a₁*q₂*Λ^4 - AA*W.a₂*q₂*Λ^3*N^2)) * hCub₁ +
  (-N*AA^2*Λ^4 - q₁*AA^2*Λ^5 + 2*Λ*AA^2*N^3 + W.a₂*AA^2*Λ^2*N^3 - W.a₁*AA^2*Λ^3*N^2
    + 3*q₁*AA^2*Λ^2*N^2 + W.a₂*q₁*AA^2*Λ^3*N^2 - N*W.a₁*q₁*AA^2*Λ^4) * hCub₂ +
  (AA^2*(W.a₂*q₁*N^5 + q₂*Λ^2*N^3 - W.a₂*q₂*N^5 - q₁*Λ^2*N^3 + Λ*W.a₁*q₂*N^4
    - Λ*W.a₁*q₁*N^4)) * hAA2

/-- The `y`-coordinate half of the chord identity: the third parameter gives Mathlib's `addY`. -/
private lemma chord_addY {AA Λ N q₁ q₂ w₁ w₂ T₃ wT : F}
    (hAA2 : AA = 1 + W.a₂ * Λ + W.a₄ * Λ ^ 2 + W.a₆ * Λ ^ 3)
    (hline₁ : w₁ = Λ * q₁ + N) (hline₂ : w₂ = Λ * q₂ + N)
    (hCub₁ : W.chordCubic AA Λ N q₁ = 0) (hCub₂ : W.chordCubic AA Λ N q₂ = 0)
    (hT₃ : AA * (T₃ + q₁ + q₂) =
      -(W.a₁ * Λ + W.a₂ * N + W.a₃ * Λ ^ 2 + 2 * W.a₄ * Λ * N + 3 * W.a₆ * Λ ^ 2 * N))
    (hwT : wT = Λ * T₃ + N) (hA : AA ≠ 0) (hq12 : q₁ - q₂ ≠ 0) (hN0 : N ≠ 0)
    (hw₁0 : w₁ ≠ 0) (hw₂0 : w₂ ≠ 0) (hwT0 : wT ≠ 0) :
    (1 - W.a₁ * T₃ - W.a₃ * wT) / wT =
      W.toAffine.addY (q₁ / w₁) (q₂ / w₂) (-1 / w₁) (Λ / N) := by
  simp only [chordCubic] at hCub₁ hCub₂
  rw [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY]
  field_simp
  refine mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 3 hA) hq12) ?_
  linear_combination (AA^3*(q₂*w₂*N^3 - q₁*w₂*N^3 + Λ*w₁*N^2*q₂^2 + W.a₁*w₁*N^3*q₂^2
    + q₁*w₁*w₂*Λ^3 - W.a₁*w₂*N^3*q₁^2 - q₂*w₁*w₂*Λ^3 - 2*Λ*w₂*N^2*q₁^2 + W.a₁*q₁*q₂*w₂*N^3
    - Λ*q₁*q₂*w₁*N^2 - W.a₁*q₁*q₂*w₁*N^3 + 2*Λ*q₁*q₂*w₂*N^2 + Λ*W.a₂*q₂*w₁*w₂*N^2
    + Λ*q₁*w₁*w₂*N^2*W.a₁^2 + W.a₁*W.a₂*q₂*w₁*w₂*N^3 - Λ*W.a₂*q₁*w₁*w₂*N^2
    - Λ*q₂*w₁*w₂*N^2*W.a₁^2 - W.a₁*W.a₂*q₁*w₁*w₂*N^3 - 2*N*W.a₁*q₂*w₁*w₂*Λ^2
    + 2*N*W.a₁*q₁*w₁*w₂*Λ^2)) * hwT +
  (AA^3*(Λ*N^3*q₂^2 + W.a₁*N^4*q₂^2 + q₁*w₂*N^3 - q₂*w₂*N^3 + N*q₁*w₂*Λ^3 + T₃*q₁*w₂*Λ^4
    + T₃*Λ^2*N^2*q₂^2 - Λ*q₁*q₂*N^3 - N*q₂*w₂*Λ^3 - T₃*q₂*w₂*Λ^4 - W.a₁*q₁*q₂*N^4
    + Λ*T₃*W.a₁*N^3*q₂^2 + Λ*W.a₂*q₂*w₂*N^3 + Λ*q₁*w₂*N^3*W.a₁^2 + T₃*W.a₁*q₂*w₂*N^3
    + W.a₁*W.a₂*q₂*w₂*N^4 - Λ*W.a₂*q₁*w₂*N^3 - Λ*q₂*w₂*N^3*W.a₁^2 - T₃*W.a₁*q₁*w₂*N^3
    - T₃*q₁*q₂*Λ^2*N^2 - W.a₁*W.a₂*q₁*w₂*N^4 - 2*W.a₁*q₂*w₂*Λ^2*N^2 + 2*W.a₁*q₁*w₂*Λ^2*N^2
    + T₃*W.a₂*q₂*w₂*Λ^2*N^2 + T₃*q₁*w₂*Λ^2*N^2*W.a₁^2 - Λ*T₃*W.a₁*q₁*q₂*N^3
    - T₃*W.a₂*q₁*w₂*Λ^2*N^2 - T₃*q₂*w₂*Λ^2*N^2*W.a₁^2 - 2*N*T₃*W.a₁*q₂*w₂*Λ^3
    + 2*N*T₃*W.a₁*q₁*w₂*Λ^3 + Λ*T₃*W.a₁*W.a₂*q₂*w₂*N^3
    - Λ*T₃*W.a₁*W.a₂*q₁*w₂*N^3)) * hline₁ +
  (AA^3*(N*Λ^4*q₁^2 + T₃*Λ^5*q₁^2 + q₁*Λ^3*N^2 - Λ*N^3*q₁^2 - W.a₁*N^4*q₁^2 - q₂*Λ^3*N^2
    + Λ*T₃*q₂*N^3 + Λ*W.a₂*q₂*N^4 + Λ*q₁*q₂*N^3 + Λ*q₁*N^4*W.a₁^2 + N*T₃*q₁*Λ^4
    + T₃*W.a₁*q₂*N^4 + W.a₁*W.a₂*q₂*N^5 + W.a₁*q₁*q₂*N^4 + Λ^2*N^3*W.a₁^2*q₁^2
    - Λ*T₃*q₁*N^3 - Λ*W.a₂*q₁*N^4 - Λ*q₂*N^4*W.a₁^2 - N*T₃*q₂*Λ^4 - N*q₁*q₂*Λ^4
    - T₃*W.a₁*q₁*N^4 - T₃*q₁*q₂*Λ^5 - W.a₁*W.a₂*q₁*N^5 - W.a₂*Λ^2*N^3*q₁^2
    - 2*T₃*Λ^2*N^2*q₁^2 - 2*W.a₁*q₂*Λ^2*N^3 + 2*W.a₁*q₁*Λ^2*N^3 + 2*W.a₁*Λ^3*N^2*q₁^2
    + T₃*W.a₂*q₂*Λ^2*N^3 + T₃*q₁*Λ^2*N^3*W.a₁^2 + T₃*Λ^3*N^2*W.a₁^2*q₁^2
    + W.a₂*q₁*q₂*Λ^2*N^3 - Λ*W.a₁*W.a₂*N^4*q₁^2 - T₃*W.a₂*q₁*Λ^2*N^3
    - T₃*W.a₂*Λ^3*N^2*q₁^2 - T₃*q₂*Λ^2*N^3*W.a₁^2 - q₁*q₂*Λ^2*N^3*W.a₁^2
    - 2*Λ*T₃*W.a₁*N^3*q₁^2 - 2*T₃*W.a₁*q₂*Λ^3*N^2 - 2*W.a₁*q₁*q₂*Λ^3*N^2
    + 2*N*T₃*W.a₁*Λ^4*q₁^2 + 2*T₃*W.a₁*q₁*Λ^3*N^2 + 2*T₃*q₁*q₂*Λ^2*N^2
    + Λ*T₃*W.a₁*W.a₂*q₂*N^4 + Λ*W.a₁*W.a₂*q₁*q₂*N^4 + T₃*W.a₂*q₁*q₂*Λ^3*N^2
    - Λ*T₃*W.a₁*W.a₂*q₁*N^4 - T₃*W.a₁*W.a₂*Λ^2*N^3*q₁^2 - T₃*q₁*q₂*Λ^3*N^2*W.a₁^2
    - 2*N*T₃*W.a₁*q₁*q₂*Λ^4 + 2*Λ*T₃*W.a₁*q₁*q₂*N^3 + T₃*W.a₁*W.a₂*q₁*q₂*Λ^2*N^3)) * hline₂ +
  (AA^2*(Λ*q₂*N^4 + N*Λ^5*q₁^2 + W.a₁*q₂*N^5 + q₁*Λ^4*N^2 + q₂*Λ^6*q₁^2 - Λ*q₁*N^4
    - N*Λ^5*q₂^2 - W.a₁*q₁*N^5 - q₁*Λ^6*q₂^2 - q₂*Λ^4*N^2 - 2*Λ^2*N^3*q₁^2 + 2*Λ^2*N^3*q₂^2
    + W.a₂*q₂*Λ^2*N^4 + W.a₂*Λ^3*N^3*q₂^2 + q₁*Λ^2*N^4*W.a₁^2 + Λ^3*N^3*W.a₁^2*q₁^2
    - W.a₂*q₁*Λ^2*N^4 - W.a₂*Λ^3*N^3*q₁^2 - q₂*Λ^2*N^4*W.a₁^2 - Λ^3*N^3*W.a₁^2*q₂^2
    - 3*q₂*Λ^3*N^2*q₁^2 - 2*Λ*W.a₁*N^4*q₁^2 - 2*W.a₁*q₂*Λ^3*N^3 - 2*W.a₁*Λ^4*N^2*q₂^2
    + 2*Λ*W.a₁*N^4*q₂^2 + 2*W.a₁*q₁*Λ^3*N^3 + 2*W.a₁*Λ^4*N^2*q₁^2 + 3*q₁*Λ^3*N^2*q₂^2
    + Λ*W.a₁*W.a₂*q₂*N^5 + W.a₁*W.a₂*Λ^2*N^4*q₂^2 + W.a₂*q₁*Λ^4*N^2*q₂^2
    + q₂*Λ^4*N^2*W.a₁^2*q₁^2 - Λ*W.a₁*W.a₂*q₁*N^5 - W.a₁*W.a₂*Λ^2*N^4*q₁^2
    - W.a₂*q₂*Λ^4*N^2*q₁^2 - q₁*Λ^4*N^2*W.a₁^2*q₂^2 - 3*W.a₁*q₂*Λ^2*N^3*q₁^2
    - 2*N*W.a₁*q₁*Λ^5*q₂^2 + 2*N*W.a₁*q₂*Λ^5*q₁^2 + 3*W.a₁*q₁*Λ^2*N^3*q₂^2
    + W.a₁*W.a₂*q₁*Λ^3*N^3*q₂^2 - W.a₁*W.a₂*q₂*Λ^3*N^3*q₁^2)) * hT₃ +
  (AA*(-AA*N*Λ^5 - AA*q₂*Λ^6 + 2*AA*Λ^2*N^3 + AA*W.a₂*Λ^3*N^3 - AA*Λ^3*N^3*W.a₁^2
    - 2*AA*W.a₁*Λ^4*N^2 + 2*AA*Λ*W.a₁*N^4 + 3*AA*q₂*Λ^3*N^2 + AA*W.a₁*W.a₂*Λ^2*N^4
    + AA*W.a₂*q₂*Λ^4*N^2 - AA*q₂*Λ^4*N^2*W.a₁^2 - 2*AA*N*W.a₁*q₂*Λ^5
    + 3*AA*W.a₁*q₂*Λ^2*N^3 + AA*W.a₁*W.a₂*q₂*Λ^3*N^3)) * hCub₁ +
  (N*AA^2*Λ^5 + q₁*AA^2*Λ^6 - 2*AA^2*Λ^2*N^3 + AA^2*Λ^3*N^3*W.a₁^2 - W.a₂*AA^2*Λ^3*N^3
    - 3*q₁*AA^2*Λ^3*N^2 - 2*Λ*W.a₁*AA^2*N^4 + 2*W.a₁*AA^2*Λ^4*N^2 + q₁*AA^2*Λ^4*N^2*W.a₁^2
    - W.a₁*W.a₂*AA^2*Λ^2*N^4 - W.a₂*q₁*AA^2*Λ^4*N^2 - 3*W.a₁*q₁*AA^2*Λ^2*N^3
    + 2*N*W.a₁*q₁*AA^2*Λ^5 - W.a₁*W.a₂*q₁*AA^2*Λ^3*N^3) * hCub₂ +
  (AA^2*(q₁*Λ^3*N^3 - q₂*Λ^3*N^3 + Λ*W.a₂*q₂*N^5 + Λ*q₁*N^5*W.a₁^2 + W.a₁*W.a₂*q₂*N^6
    - Λ*W.a₂*q₁*N^5 - Λ*q₂*N^5*W.a₁^2 - W.a₁*W.a₂*q₁*N^6 - 2*W.a₁*q₂*Λ^2*N^4
    + 2*W.a₁*q₁*Λ^2*N^4)) * hAA2

variable [DecidableEq F]

private lemma chord_addX_addY {q₁ q₂ w₁ w₂ Λ N T₃ wT : F}
    (hw₁ : w₁ = q₁ ^ 3 + W.a₁ * q₁ * w₁ + W.a₂ * q₁ ^ 2 * w₁ + W.a₃ * w₁ ^ 2 +
      W.a₄ * q₁ * w₁ ^ 2 + W.a₆ * w₁ ^ 3)
    (hw₂ : w₂ = q₂ ^ 3 + W.a₁ * q₂ * w₂ + W.a₂ * q₂ ^ 2 * w₂ + W.a₃ * w₂ ^ 2 +
      W.a₄ * q₂ * w₂ ^ 2 + W.a₆ * w₂ ^ 3)
    (hslope : Λ * (q₂ - q₁) = w₂ - w₁)
    (hN : N = w₁ - Λ * q₁)
    (hT₃ : (1 + W.a₂ * Λ + W.a₄ * Λ ^ 2 + W.a₆ * Λ ^ 3) * (T₃ + q₁ + q₂) =
      -(W.a₁ * Λ + W.a₂ * N + W.a₃ * Λ ^ 2 + 2 * W.a₄ * Λ * N + 3 * W.a₆ * Λ ^ 2 * N))
    (hwT : wT = Λ * T₃ + N)
    (hA : (1 + W.a₂ * Λ + W.a₄ * Λ ^ 2 + W.a₆ * Λ ^ 3) ≠ 0)
    (hw₁0 : w₁ ≠ 0) (hw₂0 : w₂ ≠ 0) (hwT0 : wT ≠ 0)
    (hx : q₁ * w₂ - q₂ * w₁ ≠ 0) :
    T₃ / wT = W.toAffine.addX (q₁ / w₁) (q₂ / w₂)
        (W.toAffine.slope (q₁ / w₁) (q₂ / w₂) (-1 / w₁) (-1 / w₂)) ∧
      (1 - W.a₁ * T₃ - W.a₃ * wT) / wT =
        W.toAffine.addY (q₁ / w₁) (q₂ / w₂) (-1 / w₁)
          (W.toAffine.slope (q₁ / w₁) (q₂ / w₂) (-1 / w₁) (-1 / w₂)) := by
  have hxq := chord_x_ne hw₁0 hw₂0 hx
  have hne : q₁ / w₁ - q₂ / w₂ ≠ 0 := sub_ne_zero.mpr hxq
  have hline₁ : w₁ = Λ * q₁ + N := by linear_combination -hN
  have hline₂ : w₂ = Λ * q₂ + N := by linear_combination -hN - hslope
  have hqw : q₁ * w₂ - q₂ * w₁ = N * (q₁ - q₂) := by
    linear_combination q₁ * hline₂ - q₂ * hline₁
  have hN0 : N ≠ 0 := fun h ↦ hx (by rw [hqw, h, zero_mul])
  have hq12 : q₁ - q₂ ≠ 0 := fun h ↦ hx (by rw [hqw, h, mul_zero])
  have hℓ : W.toAffine.slope (q₁ / w₁) (q₂ / w₂) (-1 / w₁) (-1 / w₂) = Λ / N := by
    rw [Affine.slope_of_X_ne hxq, div_eq_div_iff (sub_ne_zero.mpr hxq) hN0]
    field_simp
    linear_combination (w₂ - Λ * q₂) * hline₁ - w₁ * hline₂ + Λ * q₂ * hline₁
  have hCub₁ := chordCubic_eq_zero W rfl hw₁ hline₁
  have hCub₂ := chordCubic_eq_zero W rfl hw₂ hline₂
  rw [hℓ]
  exact ⟨chord_addX W rfl hline₁ hline₂ hCub₁ hCub₂ hT₃ hwT hA hq12 hN0 hw₁0 hw₂0 hwT0,
    chord_addY W rfl hline₁ hline₂ hCub₁ hCub₂ hT₃ hwT hA hq12 hN0 hw₁0 hw₂0 hwT0⟩


/-- The chord construction computes the group law, at the level of nonsingular points. -/
lemma chord_point_add {q₁ q₂ w₁ w₂ Λ N T₃ wT : F}
    (hw₁ : w₁ = q₁ ^ 3 + W.a₁ * q₁ * w₁ + W.a₂ * q₁ ^ 2 * w₁ + W.a₃ * w₁ ^ 2 +
      W.a₄ * q₁ * w₁ ^ 2 + W.a₆ * w₁ ^ 3)
    (hw₂ : w₂ = q₂ ^ 3 + W.a₁ * q₂ * w₂ + W.a₂ * q₂ ^ 2 * w₂ + W.a₃ * w₂ ^ 2 +
      W.a₄ * q₂ * w₂ ^ 2 + W.a₆ * w₂ ^ 3)
    (hslope : Λ * (q₂ - q₁) = w₂ - w₁)
    (hN : N = w₁ - Λ * q₁)
    (hT₃ : (1 + W.a₂ * Λ + W.a₄ * Λ ^ 2 + W.a₆ * Λ ^ 3) * (T₃ + q₁ + q₂) =
      -(W.a₁ * Λ + W.a₂ * N + W.a₃ * Λ ^ 2 + 2 * W.a₄ * Λ * N + 3 * W.a₆ * Λ ^ 2 * N))
    (hwT : wT = Λ * T₃ + N)
    (hA : (1 + W.a₂ * Λ + W.a₄ * Λ ^ 2 + W.a₆ * Λ ^ 3) ≠ 0)
    (hw₁0 : w₁ ≠ 0) (hw₂0 : w₂ ≠ 0) (hwT0 : wT ≠ 0)
    (hx : q₁ * w₂ - q₂ * w₁ ≠ 0)
    (h₁ : W.toAffine.Nonsingular (q₁ / w₁) (-1 / w₁))
    (h₂ : W.toAffine.Nonsingular (q₂ / w₂) (-1 / w₂)) :
    ∃ h₃ : W.toAffine.Nonsingular (T₃ / wT) ((1 - W.a₁ * T₃ - W.a₃ * wT) / wT),
      Affine.Point.some _ _ h₁ + Affine.Point.some _ _ h₂ = Affine.Point.some _ _ h₃ := by
  obtain ⟨hX, hY⟩ := chord_addX_addY W hw₁ hw₂ hslope hN hT₃ hwT hA hw₁0 hw₂0 hwT0 hx
  have hxq := chord_x_ne hw₁0 hw₂0 hx
  have hxy : ¬(q₁ / w₁ = q₂ / w₂ ∧ -1 / w₁ = W.toAffine.negY (q₂ / w₂) (-1 / w₂)) :=
    fun h ↦ hxq h.1
  refine ⟨hX ▸ hY ▸ Affine.nonsingular_add h₁ h₂ hxy, ?_⟩
  rw [Affine.Point.add_some hxy]
  simp only [Affine.Point.some.injEq]
  exact ⟨hX.symm, hY.symm⟩

end WeierstrassCurve
