/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
-- Proof-only: `finiteDimensional_functionField` is used inside the proof, not in the statement.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
-- Proof-only: the separability-free Dedekind route for an integral closure, used in the proof.
import TauCeti.RingTheory.DedekindDomain.IntegralClosure

/-!
# The intermediate ring is a Dedekind domain

For an isogeny `φ : Isogeny W₁ W₂`, the intermediate ring — the integral closure of
`W₂.CoordinateRing` in `W₁.FunctionField` — is a Dedekind domain whenever the target's coordinate
ring is one. Nothing is assumed about the function-field extension beyond what the isogeny already
gives, so **inseparable isogenies are covered, Frobenius included**.

This is what the relative ideal norm asks of the *middle* ring: `ClassGroup.relNorm`, and through
it `ClassGroup.extendedRelNormHom`, is stated over a module-finite extension of Dedekind domains,
so `Isogeny.pushClass` needs `φ.intermediateRing` to be Dedekind and not merely normal.

## Main results

* `TauCeti.Isogeny.isDedekindDomain_intermediateRing`: `φ.intermediateRing` is a Dedekind domain.

## Design

**Why this is separate from `IntegrallyClosed.lean`.**
`Isogeny.isIntegrallyClosed_intermediateRing` is proved from the formal fact that integrality is
transitive, and sees neither a trace form nor a finiteness hypothesis. Being *Dedekind* is a
conjunction — integrally closed, Noetherian, dimension at most one — and the Noetherian half is
where the cost enters: it needs the extension `W₂.FunctionField ≤ W₁.FunctionField` to be finite,
which is why this file takes the algebra structures and the tower that name that extension while
its sibling takes only the isogeny.

**Where the separability hypothesis went.** Until `TauCeti.IsIntegralClosure.isDedekindDomain`
existed, the Noetherian half could only be had from Mathlib's
`IsIntegralClosure.isDedekindDomain`, whose route is the trace pairing and which therefore sits
under the section variable `[Algebra.IsSeparable K L]` at
`Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean` line 147. This file carried that
hypothesis for exactly that reason, and its own docstring recorded that the conclusion was
expected to hold without it. Krull–Akizuki
(`TauCeti/RingTheory/IntegralClosure/NormalizationFinite.lean`) removed the obstruction, and
`TauCeti/RingTheory/DedekindDomain/IntegralClosure.lean` assembles the Dedekind conclusion from it,
so the hypothesis is now gone from the statement.

**The sibling `Finite.lean` still carries it, and no longer for a shared reason.**
`Isogeny.moduleFinite_intermediateRing` concludes that `φ.intermediateRing` is a finite
`W₂.CoordinateRing`-module, and Krull–Akizuki does not supply that: the integral closure it
produces is Noetherian but need not be a finite module. Removing separability there is a
normalization-finiteness question of Nagata type, separate from this one.

`IsDedekindDomain W₂.CoordinateRing` is taken as a hypothesis rather than derived. For an elliptic
curve it is supplied by `WeierstrassCurve.Affine.isDedekindDomain_coordinateRing`, which needs
`[W₂.IsElliptic]`; taking the Dedekind property directly keeps that ellipticity out of this file,
exactly as the sibling takes `[IsIntegrallyClosed W₂.CoordinateRing]` rather than assuming a curve.

## Provenance

⚠ *mathlib-track*. `TauCetiRoadmap/EllipticCurves/README.md:1092` lists the `IntermediateRing`
with `intermediateRingFinite` and `intermediateRingIsIntegrallyClosed` among the components of
D. Angdinata's shared isogeny development, on the way to `pushClass` and `toPointHom`; the Dedekind
property is what those two facts are combined for. The same target records at `:1097` that the
hypothesis inventory of that development is "genuinely minimal", which is what dropping
separability here restores.

AINTLIB proves the same statement about the same object as
`NormConormIntegralClosure.instDedekindB` (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`HasseWeil/Curves/NormConormIntegralClosure.lean`, by Chris Birkbeck), for
`B := integralClosure C₂.CoordinateRing C₁.FunctionField`, but only in the separable case and by
the Mathlib route this file no longer uses. What is adapted here is the reduction to
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
finite extension of its fraction field is again Dedekind.

No separability of the function-field extension is assumed — the Noetherian half comes from
Krull–Akizuki through `TauCeti.IsIntegralClosure.isDedekindDomain` — so this covers inseparable
isogenies, Frobenius included, exactly as `Isogeny.isIntegrallyClosed_intermediateRing` does. -/
theorem isDedekindDomain_intermediateRing (φ : Isogeny W₁ W₂)
    [IsDedekindDomain W₂.CoordinateRing]
    [Algebra W₂.CoordinateRing W₁.FunctionField]
    [Algebra W₂.FunctionField W₁.FunctionField]
    [IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField]
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
  exact TauCeti.IsIntegralClosure.isDedekindDomain W₂.CoordinateRing W₂.FunctionField
    W₁.FunctionField φ.intermediateRing

end Isogeny

end TauCeti
