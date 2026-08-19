/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Complements on Weierstrass curves

Facts about the invariants of an elliptic curve, complementing
`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`:

* `WeierstrassCurve.a₁_ne_zero_or_a₃_ne_zero_of_two_eq_zero`: where `2 = 0`, an elliptic curve
  has `a₁ ≠ 0` or `a₃ ≠ 0`;
* `WeierstrassCurve.j_eq_1728_iff`: `j = 1728 ↔ c₆ = 0`, the analogue for `j = 1728` of Mathlib's
  `WeierstrassCurve.j_eq_zero_iff` (`j = 0 ↔ c₄ = 0`), together with its unreduced companion
  `WeierstrassCurve.j_eq_1728_iff'` mirroring `WeierstrassCurve.j_eq_zero_iff'`;
* `WeierstrassCurve.baseChange_c₄_ne_zero` and `WeierstrassCurve.baseChange_c₆_ne_zero`: the two
  corollaries of those criteria that say `j ≠ 0` and `j ≠ 1728` survive base change along an
  injection, in the `c₄`/`c₆` form the automorphism criterion consumes.
* `WeierstrassCurve.cusp`: the cusp curve `Y² = X³`, its coefficient projections, and the point
  `(1, 1)` on it (`WeierstrassCurve.equation_cusp_one_one`). It depends on nothing beyond a
  Weierstrass equation, and is the specialization target
  `TauCeti/AlgebraicGeometry/EllipticCurve/Universal.lean` uses to retract the universal ring
  onto `ℤ`.

All are stated over a commutative ring, matching the generality of the Mathlib results they
complement. The first two are consumed by the automorphism-group development in
`TauCeti/AlgebraicGeometry/EllipticCurve/Aut.lean`, the `Aut (E, O)` milestone of
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 1; the base-change pair is consumed by the
twist classification in `TauCeti/AlgebraicGeometry/EllipticCurve/QuadraticTwist.lean`, which
needs `Aut(Eᴸ) = {±1}` after base change to a splitting field.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean` at the roadmap's pin
`bc2fe8ff7396` (FLT PR #1088), Apache 2.0, by Kevin Buzzard and Claude). Every result here
**except the cusp curve** is adapted from that file, and all are generalised from FLT's
field-level statements to a commutative ring: the two `j`-criteria, and the base-change pair
`baseChange_c₄_ne_zero` /
`baseChange_c₆_ne_zero`, which FLT states only for a field extension. The cusp curve is not
from FLT: it came with the universal-curve port and is placed here because it needs no universal
machinery.
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

section BaseChange

variable {A : Type*} [CommRing A] [Algebra R A] (hRA : Function.Injective (algebraMap R A))

include hRA

omit [E.IsElliptic] in
/-- **`c₄ ≠ 0` survives base change** along an injection, since `c₄` of the base change is the
image of `c₄`. Stated on `c₄` rather than on `j`: nothing here needs `[IsReduced R]` or the
`j`-criterion — nor even that `E` be elliptic — and a caller with `j ≠ 0` gets the hypothesis from
`j_eq_zero_iff`. -/
lemma baseChange_c₄_ne_zero (hc₄ : E.c₄ ≠ 0) : (E.baseChange A).c₄ ≠ 0 := by
  simp only [baseChange, map_c₄]
  exact (map_ne_zero_iff _ hRA).mpr hc₄

omit [E.IsElliptic] in
/-- **`c₆ ≠ 0` survives base change** along an injection. The companion of
`baseChange_c₄_ne_zero`; a caller with `j ≠ 1728` gets the hypothesis from `j_eq_1728_iff`. -/
lemma baseChange_c₆_ne_zero (hc₆ : E.c₆ ≠ 0) : (E.baseChange A).c₆ ≠ 0 := by
  simp only [baseChange, map_c₆]
  exact (map_ne_zero_iff _ hRA).mpr hc₆

end BaseChange

/-! ## The cusp curve -/

/-- The cusp curve `Y² = X³` over a commutative ring `R`. -/
def cusp (R : Type*) [Zero R] : Affine R := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }

/-- Every coefficient of the cusp curve vanishes, and likewise for `cusp_a₂` through `cusp_a₆`.
The definition body is unexposed, so these are how a consumer projects out of `cusp` — for instance
when specialising the universal curve along it. -/
@[simp] lemma cusp_a₁ (R : Type*) [Zero R] : (cusp R).a₁ = 0 := (rfl)
/-- The `a₂` coefficient of the cusp curve vanishes. -/
@[simp] lemma cusp_a₂ (R : Type*) [Zero R] : (cusp R).a₂ = 0 := (rfl)
/-- The `a₃` coefficient of the cusp curve vanishes. -/
@[simp] lemma cusp_a₃ (R : Type*) [Zero R] : (cusp R).a₃ = 0 := (rfl)
/-- The `a₄` coefficient of the cusp curve vanishes. -/
@[simp] lemma cusp_a₄ (R : Type*) [Zero R] : (cusp R).a₄ = 0 := (rfl)
/-- The `a₆` coefficient of the cusp curve vanishes. -/
@[simp] lemma cusp_a₆ (R : Type*) [Zero R] : (cusp R).a₆ = 0 := (rfl)

/-- `(1, 1)` lies on the cusp curve `Y² = X³`, over any commutative ring.

The case `R = ℤ` is the one the universal curve uses: specializing along that point is the cheap
route to nonvanishing statements, since `ψₙ(1,1) = n`, so a universal quantity that vanished would
have to vanish in `ℤ`. The `CharZero Universal.Ring` instance in
`TauCeti/AlgebraicGeometry/EllipticCurve/Universal.lean` is obtained that way. -/
lemma equation_cusp_one_one (R : Type*) [CommRing R] : (cusp R).Equation 1 1 := by
  simp [Affine.Equation, Affine.polynomial, cusp, Polynomial.evalEval]

end WeierstrassCurve

end
