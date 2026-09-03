/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# Characteristic-≠-2 normal form: transport, and its elementary consequences

Mathlib's `WeierstrassCurve.IsCharNeTwoNF` asserts `a₁ = a₃ = 0`, and its `NormalForms` file
proves a great deal from that hypothesis. This file collects two things it does not record.

**Transport.** The condition is preserved by `map` and `baseChange` — the coefficients of
`W.map f` are the images of `W`'s, so a vanishing coefficient stays vanishing.

**Elementary consequences.** Facts that follow from `a₁ = a₃ = 0` alone, by unfolding `negY`, with
no further machinery. `y_eq_zero_of_order_two` is the current example: negation is `(x, y) ↦
(x, -y)`, so a `2`-torsion point has `y = 0`. It lives here rather than with the division-polynomial
material that first proved it because it needs none of that — this module's closure is one file,
against thirty-three for `DivisionPolynomial/ShortNagellLutz.lean` — and its consumers, Nagell–Lutz
and the `2`-descent torsion count, sit in unrelated parts of the library.

That gap matters as soon as a statement is about a curve over `ℤ` and a point over `ℚ`, which is
the shape of the classical Nagell–Lutz theorem: the hypothesis is natural on the integral model,
while the point lives on the base change, and without these instances the class has to be
re-established by hand at every such crossing.

## Main results

* `WeierstrassCurve.isCharNeTwoNF_map`: `a₁ = a₃ = 0` is preserved by a ring hom.
* `WeierstrassCurve.isCharNeTwoNF_baseChange`: the same for a base change, which is the spelling
  consumers hold. Both are instances, so the crossing is silent.
* `WeierstrassCurve.y_eq_zero_of_order_two`: in a characteristic-≠-2 normal form, an affine
  point killed by `2` has `y = 0`.
-/

public section

namespace WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

/-- **Characteristic-≠-2 normal form is preserved by a ring hom.** `(W.map f).a₁` is `f W.a₁`, and
a hom sends `0` to `0`, so the vanishing survives.

As an `instance`, this is what lets typeclass search carry `IsCharNeTwoNF` across `W.map f`: a
caller who has the hypothesis on `W` and a statement about `W.map f` needs no bridging term. -/
instance isCharNeTwoNF_map (f : R →+* S) [W.IsCharNeTwoNF] : (W.map f).IsCharNeTwoNF :=
  ⟨by simp, by simp⟩

/-- **Characteristic-≠-2 normal form is preserved by a base change.** This is
`isCharNeTwoNF_map` at `algebraMap R S`, stated separately because `baseChange` is the spelling a
caller holds and instance search does not unfold it. -/
instance isCharNeTwoNF_baseChange [Algebra R S] [W.IsCharNeTwoNF] :
    (W.baseChange S).IsCharNeTwoNF :=
  W.isCharNeTwoNF_map (algebraMap R S)

/-- **In characteristic-≠-2 normal form, a two-torsion point has `y = 0`.** Negation is
`(x, y) ↦ (x, -y)`, so a point equal to its own negative has `2y = 0`; cancelling `2` finishes it.

Nothing here sees `ℤ` or `ℚ`, and nothing needs `a₂ = 0`: the argument is the normal-form identity
plus the ability to cancel `2` in the point's own field, so those are exactly the hypotheses.

The hypothesis is annihilation by `2` rather than `addOrderOf P = 2`, which is what the proof and
every caller actually have. For an *affine* point the two are equivalent — `Point.some _ _ _` is
never `0` — so the name remains exact; the weaker form simply spares callers the reconstruction. -/
lemma y_eq_zero_of_order_two {F : Type*} [Field F] [DecidableEq F]
    {E : WeierstrassCurve F} [E.IsCharNeTwoNF] (h2F : (2 : F) ≠ 0)
    {x y : F} (hns : E.toAffine.Nonsingular x y)
    (h2 : (2 : ℕ) • (Affine.Point.some _ _ hns) = 0) : y = 0 := by
  rw [two_nsmul, add_eq_zero_iff_eq_neg, Affine.Point.neg_some, Affine.Point.some.injEq] at h2
  have hneg : E.toAffine.negY x y = -y := by
    simp [Affine.negY, a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF]
  have hy : 2 * y = 0 := by linear_combination h2.2.trans hneg
  exact (mul_eq_zero.mp hy).resolve_left h2F

end WeierstrassCurve
