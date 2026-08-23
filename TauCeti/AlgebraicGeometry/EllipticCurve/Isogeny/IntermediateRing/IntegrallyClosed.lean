/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# The intermediate ring is integrally closed

For an isogeny `φ : Isogeny W₁ W₂`, the intermediate ring — the integral closure of
`W₂.CoordinateRing` in `W₁.FunctionField` — is itself integrally closed. With
`Isogeny.moduleFinite_intermediateRing` this is the normality half of what the relative ideal norm
needs, and through it `pushClass` and the induced map on points.

**No finiteness is involved.** An integral closure is integrally closed in the ambient ring for the
formal reason that integrality is transitive: an element of `W₁.FunctionField` integral over the
closure is integral over `W₂.CoordinateRing`, hence already in it. Since `W₁.FunctionField` is a
field, being integrally closed *in* it upgrades to `IsIntegrallyClosed`
(`IsIntegrallyClosed.of_isIntegrallyClosedIn`). In particular this holds for **inseparable**
isogenies, Frobenius included, and does not inherit the separability hypothesis that the sibling
`Isogeny.moduleFinite_intermediateRing` carries for want of a trace-free route to finiteness.

## Main results

* `TauCeti.Isogeny.isIntegrallyClosed_intermediateRing`: `φ.intermediateRing` is integrally closed.

## Design

**The statement takes the isogeny and nothing else.** Its conclusion mentions only
`φ.intermediateRing`, so an `Algebra` argument, a scalar tower or a hypothesis pinning a structure
map would all be proof infrastructure escaping into the API: every consumer would have to rebuild
them to use a fact that does not depend on them. The structures the proof does need are the
canonical ones — the pullback acting on `W₁.FunctionField`, and its corestriction
`Isogeny.pullbackToIntermediateRing` acting on the intermediate ring — so the proof installs them
itself.

They stay local rather than becoming global instances: `IntermediateRing/Basic.lean` records that
registering the pullback-induced structure would reintroduce the very diamond the `Subring` choice
avoids, since one curve can receive several pullbacks. A `letI` inside a proof is the scoped use
that design leaves open.

**Why the sibling still takes them.** `Isogeny.moduleFinite_intermediateRing` concludes
`Module.Finite W₂.CoordinateRing φ.intermediateRing` — its statement names the base and is therefore
*relative to* a `W₂.CoordinateRing`-algebra structure, which the caller must supply and which the
statement must let the caller choose. Being integrally closed is an absolute property of a single
ring, so nothing is left for a caller to fix. The difference is in what the two statements say, not
a difference of convention between the two files.

## Provenance

⚠ *mathlib-track*. `TauCetiRoadmap/EllipticCurves/README.md:1092` lists
`intermediateRingIsIntegrallyClosed` among the components of D. Angdinata's shared isogeny
development, under the same flag the sibling `Isogeny` files carry.

The result is also proved in the AINTLIB project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, by
Chris Birkbeck), though not separately: `HasseWeil/Curves/RamificationFinite.lean` proves
`instDedekindB` for `B := integralClosure C₂.CoordinateRing C₁.FunctionField`, the same object this
file calls `φ.intermediateRing`, and a Dedekind domain is integrally closed. What is built here
rather than taken from there is the reduction to `intermediateRing` as this repository defines it,
through the corestricted pullback, and the statement of normality on its own rather than as a
by-product of the Dedekind instance — which is what lets it hold without the finiteness that
instance carries.

The proof route is assembled from Mathlib: `IsIntegrallyClosedIn.of_isIntegralClosure` for the
closure being closed in the ambient field, then `IsIntegrallyClosed.of_isIntegrallyClosedIn` to
read that as an absolute property over a field. Neither step is the source's.
-/

public section

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **The intermediate ring is integrally closed.** It is the integral closure of
`W₂.CoordinateRing` in `W₁.FunctionField`, and an integral closure is integrally closed in the
ambient ring by transitivity of integrality; over a field that upgrades to `IsIntegrallyClosed`.

No hypotheses beyond the isogeny: the algebra structures the proof runs through are the canonical
pullback ones, installed locally rather than asked of the caller.

No finiteness and no separability either: unlike the sibling `Isogeny.moduleFinite_intermediateRing`
this covers inseparable isogenies, Frobenius included. -/
theorem isIntegrallyClosed_intermediateRing (φ : Isogeny W₁ W₂) :
    IsIntegrallyClosed φ.intermediateRing := by
  let _ := φ.pullback.toRingHom.toAlgebra
  let _ := φ.pullbackToIntermediateRing.toAlgebra
  have hpb : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x := fun x ↦ by
    rw [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  have : IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField :=
    φ.isScalarTower_intermediateRing rfl hpb
  -- the integral-closure property is not assumed: it is what `intermediateRing` is
  have := φ.isIntegralClosure_intermediateRing hpb
  have : IsIntegrallyClosedIn φ.intermediateRing W₁.FunctionField :=
    IsIntegrallyClosedIn.of_isIntegralClosure W₂.CoordinateRing
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn _ W₁.FunctionField

end Isogeny

end TauCeti
