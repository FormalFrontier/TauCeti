/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Complements on Weierstrass curves

Two facts about the invariants of an elliptic curve, complementing
`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`:

* `WeierstrassCurve.a₁_ne_zero_or_a₃_ne_zero_of_two_eq_zero`: where `2 = 0`, an elliptic curve
  has `a₁ ≠ 0` or `a₃ ≠ 0`;
* `WeierstrassCurve.j_eq_1728_iff`: `j = 1728 ↔ c₆ = 0`, the analogue for `j = 1728` of Mathlib's
  `WeierstrassCurve.j_eq_zero_iff` (`j = 0 ↔ c₄ = 0`), together with its unreduced companion
  `WeierstrassCurve.j_eq_1728_iff'` mirroring `WeierstrassCurve.j_eq_zero_iff'`.

Both are stated over a commutative ring, matching the generality of the Mathlib results they
complement. Both are consumed by the automorphism-group development in
`TauCeti/AlgebraicGeometry/EllipticCurve/Aut.lean`, the `Aut (E, O)` milestone of
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 1.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean` at the roadmap's pin
`bc2fe8ff7396` (FLT PR #1088), Apache 2.0, by Kevin Buzzard and Claude), with both results
generalised here from FLT's field-level statements to a commutative ring.
-/

public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (E : WeierstrassCurve R) [E.IsElliptic]

/-- Where `2 = 0`, an elliptic curve has `a₁ ≠ 0` or `a₃ ≠ 0`: otherwise `a₁ = a₃ = 0` makes the
partial derivative `∂/∂y = 2y + a₁x + a₃` vanish identically, so `Δ = 0`. -/
lemma a₁_ne_zero_or_a₃_ne_zero_of_two_eq_zero [Nontrivial R] (h2 : (2 : R) = 0) :
    E.a₁ ≠ 0 ∨ E.a₃ ≠ 0 := by
  by_contra! h
  exact E.isUnit_Δ.ne_zero (by rw [Δ, b₈, b₆, b₄, b₂, h.1, h.2]; grobner)

/-- `j(E) = 1728` if and only if `c₆(E)² = 0`, by the relation `1728·Δ = c₄³ - c₆²`. This is the
analogue for `j = 1728` of `WeierstrassCurve.j_eq_zero_iff'` (`j = 0 ↔ c₄³ = 0`). -/
lemma j_eq_1728_iff' : E.j = 1728 ↔ E.c₆ ^ 2 = 0 := by
  have h : E.c₆ ^ 2 = E.c₄ ^ 3 - 1728 * E.Δ := by linear_combination E.c_relation
  rw [h, sub_eq_zero, j, Units.inv_mul_eq_iff_eq_mul, coe_Δ', mul_comm E.Δ 1728]

/-- `j(E) = 1728` if and only if `c₆(E) = 0`, by the relation `1728·Δ = c₄³ - c₆²`. This is the
analogue for `j = 1728` of `WeierstrassCurve.j_eq_zero_iff` (`j = 0 ↔ c₄ = 0`). -/
lemma j_eq_1728_iff [IsReduced R] : E.j = 1728 ↔ E.c₆ = 0 := by
  rw [j_eq_1728_iff', pow_eq_zero_iff two_ne_zero]

end WeierstrassCurve

end
