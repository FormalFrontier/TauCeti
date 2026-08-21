/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot

/-!
# Complements on `AdjoinRoot.map`

Mathlib's `AdjoinRoot.map` sends a ring homomorphism `f : R →+* S`, together with a divisibility
`q ∣ p.map f`, to a ring homomorphism `AdjoinRoot p →+* AdjoinRoot q`. It records the action on
`AdjoinRoot.of` and on `AdjoinRoot.root` (`map_of`, `map_root`) but not the action on the class of
a general polynomial, and says nothing about surjectivity. Both are added here.

## Main results

* `AdjoinRoot.map_mk`: the map sends the class of `x` to the class of `x.map f`. Mathlib states
  this only in the specialised form `WeierstrassCurve.Affine.CoordinateRing.map_mk`. Marked
  `@[simp]`, like its neighbours `AdjoinRoot.map_of` and `AdjoinRoot.map_root`.
* `AdjoinRoot.map_surjective`: the map is surjective when `f` is.

Stated over arbitrary commutative rings.

This is consumed by `TauCeti/AlgebraicGeometry/EllipticCurve/Affine/CoordinateRingMap.lean`, which
specialises it to the coordinate ring of a Weierstrass curve for the Hasse strand of
`TauCetiRoadmap/EllipticCurves/README.md`, Layer 3.

## Provenance

The surjectivity argument — lift a class to a polynomial, then lift that polynomial along `f` — is
adapted from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`),
`HasseWeil/WeilPairing/FrobeniusFunctionFieldEquiv.lean`, declaration `coordRingMap_bijective`.
There it is carried out for the coordinate ring of a Weierstrass curve and only for a base ring
*equivalence*; here it is stated for `AdjoinRoot.map` along any surjective base homomorphism, with
`map_mk` — which the source does not isolate — extracted as the step that makes it routine.
-/

public section

open Polynomial

namespace AdjoinRoot

variable {R S : Type*} [CommRing R] [CommRing S]

/-- `AdjoinRoot.map` on the class of a polynomial is the class of its image. Mathlib states this
for `WeierstrassCurve.Affine.CoordinateRing.map` but not for the underlying `AdjoinRoot.map`. -/
@[simp]
lemma map_mk {f : R →+* S} {p : R[X]} {q : S[X]} (h : q ∣ p.map f) (x : R[X]) :
    map f p q h (mk p x) = mk q (x.map f) := by
  rw [map, lift_mk, ← Polynomial.eval₂_map]
  exact aeval_eq (x.map f)

/-- **`AdjoinRoot.map` is surjective when the base map is.** -/
lemma map_surjective {f : R →+* S} (hf : Function.Surjective f) {p : R[X]} {q : S[X]}
    (h : q ∣ p.map f) : Function.Surjective (map f p q h) := fun y => by
  obtain ⟨t, rfl⟩ := mk_surjective y
  obtain ⟨u, rfl⟩ := Polynomial.map_surjective f hf t
  exact ⟨mk p u, map_mk h u⟩

end AdjoinRoot


end
