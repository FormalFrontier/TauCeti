/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The affine points of a Weierstrass curve over a finite ring form a finite type

`E(𝔽_q)` is finite. Mathlib does not have this, and it is needed before the count `#E(𝔽_q)` means
anything: `Nat.card` reads `0` on an infinite type, so a statement like the Hasse bound is only the
honest count when accompanied by finiteness.

## Main results

* `TauCeti.WeierstrassCurve.Affine.finite_point`: `W.Point` is finite whenever the base is.

Stated over an arbitrary finite commutative ring and an arbitrary affine Weierstrass curve: neither
a field nor `IsElliptic` is needed. The roadmap seeds this over a finite field with
`[W.IsElliptic]`; that form is discharged by `inferInstance` from the instance below, which I
checked before writing this.

It is an `instance`, so `Nat.card`/`Finset` arguments about `E(𝔽_q)` pick it up without being
handed a proof. It is named — contrary to the usual preference for anonymous instances — because
the name is the roadmap's identifier for this milestone.

This is the finiteness milestone of `TauCetiRoadmap/EllipticCurves/README.md`, Layer 3
("elliptic curves over finite fields — the Hasse bound"), seeded in that roadmap's
`Suggested.lean` as `finite_point`, where it is called "a prerequisite Mathlib lacks" and the
"required companion" of the Hasse bound.

## Provenance

Not ported: this is a direct proof. The AINTLIB `HasseWeil` project (the roadmap's pinned Hasse
provenance) assumes `[Fintype W.toAffine.Point]` as a hypothesis rather than proving it, and the
roadmap records that `finite_point` is "NOT proven upstream".
-/

public section

namespace TauCeti

namespace WeierstrassCurve

namespace Affine

variable {R : Type*} [CommRing R] [Finite R] (W : _root_.WeierstrassCurve.Affine R)

/-- **The affine points of a Weierstrass curve over a finite ring form a finite type.** -/
instance finite_point : Finite W.Point :=
  -- transport along Mathlib's decomposition of `Point` as the point at infinity together with the
  -- pairs satisfying `Nonsingular`; `WithZero` carries no `Finite` instance of its own, so it is
  -- taken from the `Option` it unfolds to
  have : Finite (WithZero {xy : R × R // W.Nonsingular xy.1 xy.2}) :=
    inferInstanceAs (Finite (Option _))
  .of_equiv _ W.nonsingularPointEquiv.symm

end Affine

end WeierstrassCurve

end TauCeti
