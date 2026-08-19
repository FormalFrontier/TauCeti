/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# What surjectivity of `Point.toClass` is equivalent to

Mathlib builds `WeierstrassCurve.Affine.Point.toClass : W.Point →+ Additive (ClassGroup
W.CoordinateRing)` and proves it **injective**, realising the points of an affine Weierstrass
curve as a subgroup of the affine ideal class group. It does not prove surjectivity.

This file records what surjectivity amounts to: that every ideal class is trivial or the class of
an `XYIdeal'` at a nonsingular affine point.

## Main results

* `WeierstrassCurve.Affine.Point.toClass_surjective_iff`: `toClass` is surjective exactly when
  every element of `ClassGroup W.CoordinateRing` is trivial or the class of `XYIdeal' h` for a
  nonsingular affine point.

## What this is, mathematically

The right-hand side is stated for an arbitrary affine Weierstrass curve; nothing here assumes
smoothness or ellipticity, and no divisor group occurs.

On a smooth genus-1 curve, and under the identification of the affine ideal class group with
degree-zero divisor classes, it becomes the familiar divisor-reduction statement — every such
class is `(P) - (O)` for a rational point `P`. That is the reading which motivates recording the
equivalence, since it turns "prove `toClass` is surjective" into the form the geometric proof
takes; but it is an interpretation under extra hypotheses, not the content of the statement.

## What is deliberately not here

**No proof that either side holds.** The equivalence is formal — it unfolds `toClass` and
re-packages a witness — and carries no ellipticity hypothesis. The geometric proof planned for the
right-hand side, to be imported from AINTLIB, *will* carry `[W.IsElliptic]`: it recovers a point
from an ideal and has to exhibit that point as nonsingular, which it gets from `Δ ≠ 0`. That is a
property of the route that proof takes, not of the statement — nothing here rules out
establishing it for a particular non-elliptic curve by other means. That step is a separate slice.

Keeping the split at exactly this line is the point of the file. Everything here is true of any
affine Weierstrass curve over a field, so nothing downstream that only needs the *equivalence* has
to assume ellipticity to get it.

**No named predicate and no packaged isomorphism.** An earlier revision wrapped the right-hand
side in a `ClassRepresentableByPoints` predicate and packaged `AddEquiv.ofBijective` behind a
`toClassEquivOfSurjective` def. Both were dropped: `Function.Surjective` already names the
left-hand side, so a predicate adds only an unfolding layer for consumers to cross, and a consumer
holding surjectivity writes `AddEquiv.ofBijective toClass ⟨toClass_injective, hsurj⟩` in one
line — which additionally keeps Mathlib's `AddEquiv.ofBijective_apply` available as a `simp`
lemma, where a sealed wrapper blocked it. The roadmap's `toClassEquiv` is the *unconditional*
isomorphism, which becomes definable once surjectivity itself is proved; it is not this
hypothesis-parametrised form.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at the
roadmap's HasseWeil pin `dev/hasse-weil @ 513e83879e2f`, file
`HasseWeil/Pic0/ToClassSurjective.lean` (by Chris Birkbeck). The source states the equivalence
through a named `ClassRepresentableByPoints` predicate, with the two directions as
`toClass_surjective_of_classRepresentableByPoints` and
`classRepresentableByPoints_of_toClass_surjective`; here they are one `iff` with the disjunction
spelled out, so no name is carried over.

That file is 920 lines and splits at its line 319: everything above is stated over
`{F} [Field F] {W} [DecidableEq F]`, and everything from `eq_XYIdeal_of_finrank_quotient_eq_one`
onward adds `[W.IsElliptic]`. This port takes the first block only, which is why nothing here
assumes ellipticity.

`Point.toClass_surjective` and `toClassEquiv` are **also** components of D. Angdinata's in-flight
upstream `CoordinateRing` split-out, which `TauCetiRoadmap/EllipticCurves/README.md:1095` lists at
this same hypothesis strength — that bullet's "no ellipticity hypothesis" phrase describes his
split-out, not the AINTLIB source above, whose headline surjectivity theorem is elliptic. ⚠
mathlib-track: dedupe on landing.
-/

public section

open WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] {W : _root_.WeierstrassCurve.Affine F} [DecidableEq F]

/-- **Surjectivity of `toClass` is exactly representability of every ideal class by a point.**

`toClass` is surjective precisely when each element of `ClassGroup W.CoordinateRing` is either
trivial or the class of `XYIdeal' h` for a nonsingular affine point `(x, y)`. This records what
remains to be proved for full surjectivity.

Stated for an arbitrary affine Weierstrass curve: neither smoothness nor ellipticity is assumed,
and no divisor group appears. Under the hypotheses that make `W` a smooth genus-1 curve, and the
identification of `ClassGroup W.CoordinateRing` with degree-zero divisor classes, the right-hand
side reads as the familiar statement that every such class is `(P) - (O)` for a rational point
`P` — but that reading is an interpretation under extra hypotheses, not part of what is stated
here.

The disjunction is spelled out rather than named: `Function.Surjective` already expresses the
left-hand side, so a separate predicate would only add an unfolding layer for consumers to
cross. -/
theorem toClass_surjective_iff :
    Function.Surjective (toClass (W := W)) ↔ ∀ g : ClassGroup W.CoordinateRing,
      g = 1 ∨ ∃ (x y : F) (h : W.Nonsingular x y),
        g = ClassGroup.mk W.FunctionField (CoordinateRing.XYIdeal' (W := W) h) := by
  constructor
  · intro hsurj g
    obtain ⟨P, hP⟩ := hsurj (Additive.ofMul g)
    cases P with
    | zero =>
        left
        rw [← zero_def, toClass_zero] at hP
        exact (Additive.ofMul.injective hP).symm
    | some x y h =>
        right
        refine ⟨x, y, h, ?_⟩
        rw [toClass_some] at hP
        exact (Additive.ofMul.injective hP).symm
  · intro hrep c
    obtain hg | ⟨x, y, h, hg⟩ := hrep (Additive.toMul c)
    · -- `ofMul_one` names the step `Additive.ofMul 1 = 0`, so the trivial branch closes without
      -- appealing to the type synonym at all.
      exact ⟨0, by rw [toClass_zero, ← ofMul_toMul c, hg, ofMul_one]⟩
    · refine ⟨some x y h, ?_⟩
      rw [toClass_some, ← ofMul_toMul c, hg]
      -- What is left is `g = Additive.ofMul g`. `Additive.ofMul` is `Equiv.refl` on the
      -- underlying type and Mathlib names no lemma for it at a general element, so this last
      -- step is the type synonym and nothing else.
      rfl

end WeierstrassCurve.Affine.Point
