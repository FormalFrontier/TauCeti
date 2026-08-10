/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The ideal of a point of a Weierstrass curve is maximal

For a point `(x, y)` on an affine Weierstrass curve `W` over a field, Mathlib's
`CoordinateRing.XYIdeal W x (C y)` is the ideal `⟨X - x, Y - y⟩` of the coordinate ring, and
`CoordinateRing.quotientXYIdealEquiv` identifies the quotient by it with the base field. This file
records the consequence: that ideal is maximal.

## Main results

* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal`: `XYIdeal W x y` is maximal
  for any `y : F[X]` solving the Weierstrass equation at `x`, matching the generality of
  `XYIdeal` and `quotientXYIdealEquiv` themselves.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal_of_equation`: the point case,
  `XYIdeal W x (C y)` for `(x, y)` on `W`.

Mathlib has the quotient isomorphism but records nothing about the ideal itself; the many `XYIdeal`
lemmas it does state (`XYIdeal_eq₁`, `XYIdeal_eq₂`, `XYIdeal_mul_XYIdeal`, `XYIdeal_neg_mul`) are
all about products and rewriting, not about the ideal's place in the spectrum.

Only the curve equation is needed, not nonsingularity: the quotient is the base field either way.

This supports `TauCetiRoadmap/EllipticCurves/README.md`, Layer 0, whose point–place dictionary
identifies the affine places of `W` with the maximal ideals of its coordinate ring — "the affine
places are the maximal ideals of the coordinate ring". Maximality of `XYIdeal` is the direction
that sends a point to a place. The roadmap's §"What Mathlib already has (consume)" lists
`Affine.CoordinateRing` as consumed infrastructure that "is load-bearing API here, not an
implementation detail"; this is a complement to that API, not a reimplementation of it.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`), `HasseWeil/Curves/Basic.lean`, declaration
`maximalIdealAt_isMaximal`.

Changes from the source. There the ideal is reached through a `SmoothPlaneCurve` structure wrapping
`WeierstrassCurve.Affine` and a `SmoothPoint` structure bundling the coordinates with their
nonsingularity proof; the surrounding wrappers are not ported, and the statement is made directly
about Mathlib's `XYIdeal`. The hypothesis is correspondingly weakened from nonsingularity to the
curve equation, which is all the quotient isomorphism consumes.
-/

public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] {W : _root_.WeierstrassCurve.Affine F} {x : F}

/-- **The ideal `⟨X - x, Y - y(X)⟩` of the coordinate ring is maximal** whenever `y` is a
polynomial solving the Weierstrass equation at `x`. Equivalently, the quotient by it is the base
field. -/
theorem XYIdeal_isMaximal {y : F[X]} (h : (W.polynomial.eval y).eval x = 0) :
    (CoordinateRing.XYIdeal W x y).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _
    ((CoordinateRing.quotientXYIdealEquiv h).toRingEquiv.isField (Field.toIsField F))

/-- **The ideal of a point of a Weierstrass curve is maximal**, the constant-polynomial case of
`XYIdeal_isMaximal`. -/
theorem XYIdeal_isMaximal_of_equation {y : F} (h : W.Equation x y) :
    (CoordinateRing.XYIdeal W x (C y)).IsMaximal :=
  XYIdeal_isMaximal h

end WeierstrassCurve.Affine.CoordinateRing

end TauCeti

end
