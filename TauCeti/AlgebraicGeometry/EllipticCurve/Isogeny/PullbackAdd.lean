/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.TautologicalPoint

/-!
# Adding coordinate pullbacks

A coordinate pullback `W₂.CoordinateRing →ₐ[F] W₁.FunctionField` is the same thing as a point of
`W₂` over `F(W₁)` — its tautological point — so two of them can be added by adding those points
in the group law of `W₂⁄F(W₁)` and evaluating the coordinate ring at the result. This is the
Weierstrass addition law read on function fields, taken from Mathlib's group structure on points
rather than from the rational formulas directly.

The sum of two points may be the point at infinity, which is not the tautological point of
anything, so `add` takes that exclusion as a hypothesis. On the hom carrier, where a zero element
is available, that case is the zero map; making the sum an *isogeny* rather than a bare pullback
needs pointedness of the result, and neither is established here.

## Main definitions

* `TauCeti.CoordinatePullback.add`: the sum of two coordinate pullbacks whose tautological points
  do not cancel.

## Main results

* `TauCeti.CoordinatePullback.add_of_X` and `TauCeti.CoordinatePullback.add_root`: the sum's
  values on the two coordinate functions of `W₂`.
* `TauCeti.CoordinatePullback.tautologicalPoint_add`: the defining property — the tautological
  point of the sum is the sum of the tautological points.
* `TauCeti.CoordinatePullback.eq_add_of_tautologicalPoint_eq`: that property characterises the
  sum.
* `TauCeti.CoordinatePullback.add_comm` and `TauCeti.CoordinatePullback.add_assoc`: addition is
  commutative and associative where it is defined.

## Provenance

The same construction is formalised in the AINTLIB `HasseWeil` project (Chris Birkbeck),
Apache-2.0, `HasseWeil/AdditionPullback.lean` at commit
`513e83879e2f8cbc626eb9e04d660e92be16ccba`, declarations `addSlope`, `addPullback_x`,
`addPullback_y`, `addCoordAlgHomPair` and `addIsog`, which build the sum from the explicit
rational formulas. Nothing here is adapted from it: that construction assumes the induced map on
points as data, and its case analysis on the formulas is what Mathlib's `AddCommGroup` on points
already discharges, so the declarations below are written against the point group instead.
-/

public section

open Polynomial WeierstrassCurve.Affine

open scoped Polynomial.Bivariate

namespace TauCeti

open _root_.WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

namespace CoordinatePullback

variable [W₂.IsElliptic]

/-- **The sum of two coordinate pullbacks**, when their tautological points do not cancel:
evaluation of the coordinate ring of `W₂` at the sum of those points. -/
noncomputable def add (p q : CoordinatePullback W₁ W₂)
    (h : p.tautologicalPoint + q.tautologicalPoint ≠ 0) : CoordinatePullback W₁ W₂ :=
  CoordinateRing.evalAlgHom (Point.nonsingular_coords h).left

/-- The sum sends the coordinate function `x` of `W₂` to the `x`-coordinate of the sum point. -/
@[simp]
theorem add_of_X (p q : CoordinatePullback W₁ W₂)
    (h : p.tautologicalPoint + q.tautologicalPoint ≠ 0) :
    add p q h (AdjoinRoot.of W₂.polynomial X) =
      Point.xCoord (p.tautologicalPoint + q.tautologicalPoint) := by
  rw [add, CoordinateRing.evalAlgHom_of_X]

/-- The sum sends the coordinate function `y` of `W₂` to the `y`-coordinate of the sum point. -/
@[simp]
theorem add_root (p q : CoordinatePullback W₁ W₂)
    (h : p.tautologicalPoint + q.tautologicalPoint ≠ 0) :
    add p q h (AdjoinRoot.root W₂.polynomial) =
      Point.yCoord (p.tautologicalPoint + q.tautologicalPoint) := by
  rw [add, CoordinateRing.evalAlgHom_root]

/-- **The defining property of the sum**: its tautological point is the sum of the tautological
points. -/
@[simp]
theorem tautologicalPoint_add (p q : CoordinatePullback W₁ W₂)
    (h : p.tautologicalPoint + q.tautologicalPoint ≠ 0) :
    (add p q h).tautologicalPoint = p.tautologicalPoint + q.tautologicalPoint :=
  Point.eq_of_coords (tautologicalPoint_ne_zero _) h
    (by rw [xCoord_tautologicalPoint, add, CoordinateRing.evalAlgHom_of_X])
    (by rw [yCoord_tautologicalPoint, add, CoordinateRing.evalAlgHom_root])

/-- **The defining property characterises the sum**: a pullback whose tautological point is the
sum of two others is their sum. -/
theorem eq_add_of_tautologicalPoint_eq {p q r : CoordinatePullback W₁ W₂}
    (hr : r.tautologicalPoint = p.tautologicalPoint + q.tautologicalPoint) :
    r = add p q (hr ▸ tautologicalPoint_ne_zero r) :=
  tautologicalPoint_injective (by rw [tautologicalPoint_add]; exact hr)

/-- **Addition of coordinate pullbacks is commutative** where it is defined. -/
theorem add_comm (p q : CoordinatePullback W₁ W₂)
    (h : p.tautologicalPoint + q.tautologicalPoint ≠ 0) :
    add p q h =
      add q p (_root_.add_comm p.tautologicalPoint q.tautologicalPoint ▸ h) :=
  eq_add_of_tautologicalPoint_eq (by rw [tautologicalPoint_add]; exact _root_.add_comm _ _)

/-- **Addition of coordinate pullbacks is associative** where both regroupings are defined. -/
theorem add_assoc (p q r : CoordinatePullback W₁ W₂)
    (hpq : p.tautologicalPoint + q.tautologicalPoint ≠ 0)
    (hqr : q.tautologicalPoint + r.tautologicalPoint ≠ 0)
    (h : (add p q hpq).tautologicalPoint + r.tautologicalPoint ≠ 0) :
    add (add p q hpq) r h =
      add p (add q r hqr) (by
        rw [tautologicalPoint_add] at h ⊢
        rwa [_root_.add_assoc] at h) :=
  tautologicalPoint_injective (by
    rw [tautologicalPoint_add, tautologicalPoint_add, tautologicalPoint_add,
      tautologicalPoint_add, _root_.add_assoc])

end CoordinatePullback

end TauCeti

end
