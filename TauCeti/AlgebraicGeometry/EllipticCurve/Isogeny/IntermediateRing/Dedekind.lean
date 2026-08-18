/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Basic
-- Proof-only: `finiteDimensional_functionField` is used inside the proof, not in the statement.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# The intermediate ring is a Dedekind domain

For an isogeny `φ : Isogeny W₁ W₂`, the intermediate ring — the integral closure of
`W₂.CoordinateRing` in `W₁.FunctionField` — is a Dedekind domain whenever the target's coordinate
ring is one and the extension of function fields is separable.

This is what the relative ideal norm asks of the *middle* ring: `ClassGroup.relNorm`, and through
it `ClassGroup.extendedRelNormHom`, is stated over a module-finite extension of Dedekind domains,
so `Isogeny.pushClass` needs `φ.intermediateRing` to be Dedekind and not merely normal.

## Main results

* `TauCeti.Isogeny.isDedekindDomain_intermediateRing`: `φ.intermediateRing` is a Dedekind domain.

## Design

**Why this is separate from `IntegrallyClosed.lean`, and why it costs more.**
`Isogeny.isIntegrallyClosed_intermediateRing` is hypothesis-free: an integral closure is integrally
closed because integral closure is idempotent, and that argument sees no trace form. Being
*Dedekind* is a conjunction — integrally closed, Noetherian, dimension at most one — and the
Noetherian half is where the cost enters. Mathlib's route, `IsIntegralClosure.isDedekindDomain`,
is stated for a finite **separable** extension of the fraction field, because it obtains
Noetherianity from the trace pairing, which is nondegenerate exactly in the separable case.

So the hypothesis set here matches the sibling `Isogeny.moduleFinite_intermediateRing` rather than
`Isogeny.isIntegrallyClosed_intermediateRing`, and for the same reason: both go through the trace.

**The hypothesis is a limitation of the route, not of the result.** `W₂.CoordinateRing` is a
finite-type algebra over a field and therefore Nagata, so its normalization in a finite extension
is finite — and the conclusion is expected to hold with no separability at all, inseparable
isogenies and Frobenius included. What blocks that here is availability, and it is measurable:
every route to the Noetherian half in `Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`
falls under the section variable `[Algebra.IsSeparable K L]` declared at its line 147, and the
pinned Mathlib has no Krull–Akizuki (the identifier and the hyphenated prose spelling both occur
zero times, against 69 files mentioning `IsDedekindDomain`) and no usable Nagata
normalization-finiteness API.

Removing the hypothesis therefore means building that route first. That is not an open-ended
wish: `TauCetiRoadmap/EllipticCurves/README.md:1096` already names
`RingTheory/IntegralClosure/NormalizationFinite` as one of the supports of this same isogeny
development. So the inseparable statement is scheduled work with a home, and a slice of its own
under this repository's one-topic-per-PR rule — not something to be folded into this file. This
is the interim result until it lands. `IntermediateRing/Finite.lean` records the same limitation
for the finiteness half.

`IsDedekindDomain W₂.CoordinateRing` is taken as a hypothesis rather than derived. For an elliptic
curve it is supplied by `WeierstrassCurve.Affine.isDedekindDomain_coordinateRing`, which needs
`[W₂.IsElliptic]`; taking the Dedekind property directly keeps that ellipticity out of this file,
exactly as the sibling takes `[IsIntegrallyClosed W₂.CoordinateRing]` rather than assuming a curve.

## Provenance

⚠ *mathlib-track*. `TauCetiRoadmap/EllipticCurves/README.md:1092` lists the `IntermediateRing`
with `intermediateRingFinite` and `intermediateRingIsIntegrallyClosed` among the components of
D. Angdinata's shared isogeny development, on the way to `pushClass` and `toPointHom`; the Dedekind
property is what those two facts are combined for.

AINTLIB proves the same statement about the same object as
`NormConormIntegralClosure.instDedekindB` (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`HasseWeil/Curves/NormConormIntegralClosure.lean`, by Chris Birkbeck), for
`B := integralClosure C₂.CoordinateRing C₁.FunctionField`. What is adapted here is the reduction to
`intermediateRing` as this repository defines it — through the corestricted pullback and
`Isogeny.isIntegralClosure_intermediateRing` — rather than to Mathlib's literal `integralClosure`
subalgebra.
-/

public section

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **The intermediate ring is a Dedekind domain.** It is the integral closure of
`W₂.CoordinateRing` in `W₁.FunctionField`, and the integral closure of a Dedekind domain in a
finite separable extension of its fraction field is again Dedekind.

Separability is a restriction of the proof route, not of the result; the module docstring's
Design section says why, and what removing it would take. -/
theorem isDedekindDomain_intermediateRing (φ : Isogeny W₁ W₂)
    [IsDedekindDomain W₂.CoordinateRing]
    [Algebra W₂.CoordinateRing W₁.FunctionField]
    [Algebra W₂.FunctionField W₁.FunctionField]
    [IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField]
    [Algebra.IsSeparable W₂.FunctionField W₁.FunctionField]
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x) :
    IsDedekindDomain φ.intermediateRing := by
  -- the algebra structure on the intermediate ring and its tower are the canonical ones built
  -- from `φ`, so they are installed here rather than demanded of the caller
  let _ := φ.pullbackToIntermediateRing.toAlgebra
  have : IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField :=
    φ.isScalarTower_intermediateRing rfl h
  -- the integral-closure property is not assumed: it is what `intermediateRing` is
  have := φ.isIntegralClosure_intermediateRing h
  have := φ.finiteDimensional_functionField (φ.algebraMap_functionField_eq_fieldPullback h)
  exact IsIntegralClosure.isDedekindDomain W₂.CoordinateRing W₂.FunctionField W₁.FunctionField
    φ.intermediateRing

end Isogeny

end TauCeti
