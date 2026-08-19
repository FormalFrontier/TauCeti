/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.XYIdealMaximal
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# The local ring of an elliptic curve at an affine point is a discrete valuation ring

The coordinate ring of an elliptic curve is a Dedekind domain
(`TauCeti.WeierstrassCurve.Affine.isDedekindDomain_coordinateRing`), and the ideal of a point is
maximal and nonzero (`XYIdeal_isMaximal_of_equation`, `XYIdeal_ne_bot`). Localising at that ideal
therefore gives a discrete valuation ring.

## Main results

* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.isDiscreteValuationRing_localizationAtPrime`: the
  localisation of the coordinate ring at `⟨X - x, Y - y(X)⟩` is a discrete valuation ring, for any
  `y : F[X]` solving the Weierstrass equation at `x` — in particular at a point of the curve,
  through `XYIdeal_isMaximal_of_equation`.

Mathlib's `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain` is applied directly;
what this file contributes is that both of its hypotheses hold at such an ideal — primality from
`XYIdeal_isMaximal` and non-vanishing from `XYIdeal_ne_bot` — over a coordinate ring already known
to be Dedekind.

No valuation is defined here: the result gives the `IsDiscreteValuationRing` structure, which is
what an order-of-vanishing and uniformiser API would be built on.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0** (the function field, places, and divisors).
That layer's §Places asks for the affine places as the maximal ideals of the coordinate ring, "for
elliptic `W` a Dedekind domain — itself a worthwhile lemma", together with an API of `ord_v`,
uniformisers and residue fields; this supplies the local rings that such an API is stated over. The
layer says its own place types are new API to be built there rather than pinned, and it seeds no
declaration this competes with; it also records that the design is coordinated with D. Angdinata's
in-flight upstream `CoordinateRing` work.

## Provenance

The statement is that of `localRing_isDVR` in the AINTLIB `HasseWeil` project
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by that roadmap at
`dev/hasse-weil @ 513e83879e2f`), `HasseWeil/Valuation.lean`. Its proof is not ported: with the
coordinate ring already known to be a Dedekind domain, Mathlib's
`IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain` gives the conclusion directly.
The source's hypothesis is nonsingularity of the point; here the curve equation suffices, matching
the weakening already made for `XYIdeal_isMaximal_of_equation`.
-/

public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] {W : _root_.WeierstrassCurve.Affine F} {x : F}

/-- **The local ring of an elliptic curve at `⟨X - x, Y - y(X)⟩` is a discrete valuation ring**,
whenever `y` solves the Weierstrass equation at `x`. The primality of the ideal is a consequence of
that hypothesis, through `XYIdeal_isMaximal`, so it is installed in the statement rather than
assumed. -/
theorem isDiscreteValuationRing_localizationAtPrime [W.IsElliptic] {y : F[X]}
    (h : (W.polynomial.eval y).eval x = 0) :
    haveI : (CoordinateRing.XYIdeal W x y).IsPrime := (XYIdeal_isMaximal h).isPrime
    IsDiscreteValuationRing (Localization.AtPrime (CoordinateRing.XYIdeal W x y)) :=
  haveI : (CoordinateRing.XYIdeal W x y).IsPrime := (XYIdeal_isMaximal h).isPrime
  have := isDedekindDomain_coordinateRing W
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain W.CoordinateRing
    (XYIdeal_ne_bot x y) _

end WeierstrassCurve.Affine.CoordinateRing

end TauCeti

end
