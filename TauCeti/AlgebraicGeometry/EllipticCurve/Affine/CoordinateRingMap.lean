/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import TauCeti.RingTheory.AdjoinRoot

/-!
# Surjectivity of the coordinate-ring map

Mathlib's `WeierstrassCurve.Affine.CoordinateRing.map` sends a ring homomorphism `f : R →+* S` to
`R[W] →+* S[W.map f]`, and proves it injective when `f` is (`CoordinateRing.map_injective`). It
states no surjectivity. Since `R[W]` is `AdjoinRoot W.polynomial`, the argument lives at the
`AdjoinRoot` level in `TauCeti/RingTheory/AdjoinRoot.lean`; the coordinate-ring statements follow
in a line each.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.map_surjective` and
  `WeierstrassCurve.Affine.CoordinateRing.map_bijective`: the coordinate-ring specialisations,
  stated like Mathlib's `CoordinateRing.map_injective` for an arbitrary `f : R →+* S`.

For a base *equivalence* `e` these give `RingEquiv.ofBijective (map W e) (map_bijective W
e.bijective)` in one line at the use site, so no equivalence is defined here; Mathlib's generic
`AdjoinRoot.mapRingEquiv` is the other route to the same object.

Stated over arbitrary commutative rings; the curve need not be elliptic.

This supports the Hasse strand of `TauCetiRoadmap/EllipticCurves/README.md`, Layer 3. That
roadmap's Layer-0 narrative makes the Frobenius "the key input to Layer 3", and the arithmetic
Frobenius of the function field over a finite field is obtained by transporting the `q`-power map
of the base to the coordinate ring, which needs exactly this bijectivity. The roadmap's §"What
Mathlib already has (consume)" lists `Affine.CoordinateRing` as consumed infrastructure that "is
load-bearing API here, not an implementation detail"; this is a complement to that API, not a
reimplementation of it.

## Provenance

The need for these statements is from the AINTLIB `HasseWeil` project
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by that roadmap at
`dev/hasse-weil @ 513e83879e2f`), `HasseWeil/WeilPairing/FrobeniusFunctionFieldEquiv.lean`,
declaration `coordRingMap_bijective`. There they are bundled as bijectivity of one map, for a ring
*equivalence* only — surjectivity being obtained by lifting along `e.symm` — inside a 267-line
file that also constructs the function-field Frobenius. Here there is no inverse to lift along:
the statement is for an arbitrary surjective `f : R →+* S`, matching the generality of Mathlib's
`CoordinateRing.map_injective`, and preimages come from `Polynomial.map_surjective`. The argument
itself lives one level down, in `TauCeti/RingTheory/AdjoinRoot.lean`; the equivalence the source
bundled it for is left to the use site.
-/

public section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine.CoordinateRing

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve.Affine R)

/-- **`CoordinateRing.map` is surjective when the base map is**, the companion of Mathlib's
`CoordinateRing.map_injective`. -/
lemma map_surjective {f : R →+* S} (hf : Function.Surjective f) :
    Function.Surjective (map W f) :=
  AdjoinRoot.map_surjective (Polynomial.map_surjective f hf)
    (dvd_of_eq (WeierstrassCurve.Affine.map_polynomial (W := W) (f := f)))

/-- **`CoordinateRing.map` is bijective when the base map is.** -/
lemma map_bijective {f : R →+* S} (hf : Function.Bijective f) :
    Function.Bijective (map W f) :=
  ⟨map_injective hf.1, map_surjective W hf.2⟩

end WeierstrassCurve.Affine.CoordinateRing

end
