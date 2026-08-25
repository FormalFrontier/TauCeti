/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# Weierstrass normal forms survive a base change

Mathlib's `WeierstrassCurve.IsCharNeTwoNF` asserts `a₁ = a₃ = 0`, and its `NormalForms` file
proves a great deal from that hypothesis. What it does not record is that the condition is
preserved by `map` and `baseChange` — the coefficients of `W.map f` are the images of `W`'s, so a
vanishing coefficient stays vanishing.

That gap matters as soon as a statement is about a curve over `ℤ` and a point over `ℚ`, which is
the shape of the classical Nagell–Lutz theorem: the hypothesis is natural on the integral model,
while the point lives on the base change, and without these instances the class has to be
re-established by hand at every such crossing.

## Main results

* `WeierstrassCurve.isCharNeTwoNF_map`: `a₁ = a₃ = 0` is preserved by a ring hom.
* `WeierstrassCurve.isCharNeTwoNF_baseChange`: the same for a base change, which is the spelling
  consumers hold. Both are instances, so the crossing is silent.
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

end WeierstrassCurve
