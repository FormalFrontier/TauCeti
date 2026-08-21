/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Dedekind
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Finite
-- Public: `Isogeny/Separability.lean` is where separability of an isogeny is spelled, and where
-- the instance witnessing it for `id` lives.
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Separability
-- Public: `Algebra.IsSeparable f.fieldRange L` is the hypothesis of every statement here, and the
-- transfer across `f.equivFieldRange` is what turns it into the siblings' hypothesis.
public import TauCeti.FieldTheory.IntermediateField.FieldRange
public import TauCeti.Algebra.Algebra.Hom

/-!
# The intermediate ring of a separable isogeny, with no algebra structures to supply

`IntermediateRing/Finite.lean` and `IntermediateRing/Dedekind.lean` state module-finiteness and
Dedekindness of `φ.intermediateRing` against algebra structures the caller supplies, pinned to the
pullback by a hypothesis `h`. That is the right shape for a consumer who already holds such
structures, and the wrong shape for one who holds only `φ`: nothing in the repository registers
`Algebra W₂.CoordinateRing W₁.FunctionField` or `Algebra W₂.FunctionField W₁.FunctionField`, since
different isogenies induce different ones and any global instance would be a diamond.

This file closes that gap. Each result below takes **separability of `φ` in the repository's own
spelling** — `Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField`, the definition
`Isogeny/Separability.lean` works with, which mentions no algebra structure because
`φ.fieldPullback.fieldRange` is an intermediate field of `W₁.FunctionField` — and builds every
structure the sibling wants out of `φ` alone.

The bridge between the two spellings of separability is `TauCeti.isSeparable_of_fieldRange`: the
range restriction `φ.fieldPullback.equivFieldRange` identifies `W₂.FunctionField` with
`φ.fieldPullback.fieldRange`, so a separable extension of the one is a separable extension of the
other.

## Main results

* `TauCeti.Isogeny.isSeparable_functionField`: a separable isogeny has separable function-field
  extension, over `W₂.FunctionField` rather than over the range.
* `TauCeti.Isogeny.finite_pullbackToIntermediateRing`: the corestricted pullback is a finite ring
  map — `IntermediateRing/Finite.lean`'s conclusion with nothing to supply.
* `TauCeti.Isogeny.isDedekindDomain_intermediateRing_of_isSeparable`:
  `IntermediateRing/Dedekind.lean`'s conclusion with nothing to supply, as an instance.

## Design

**Why `RingHom.Finite` rather than `Module.Finite`.** Module-finiteness of `φ.intermediateRing`
over `W₂.CoordinateRing` is finiteness *along the corestricted pullback*, and there is no algebra
instance to state it against. Mathlib's `RingHom.Finite` is exactly the predicate for that
situation — `letI := f.toAlgebra; Module.Finite A B` — so the conclusion is stated about
`φ.pullbackToIntermediateRing` and needs no structure in the statement at all. Dedekindness needs
no such care, being intrinsic to the ring, and is therefore an `instance` where finiteness cannot
be.

**The consumer is `Isogeny.pushClass`**, whose two structural hypotheses are exactly the two
conclusions here: an ideal class is extended into `φ.intermediateRing` and normed back down, and
`ClassGroup.relNorm` is stated over a module-finite extension of Dedekind domains.

**Separability is inherited from the siblings, not introduced here.** Both of them explain at
length that the hypothesis is a limitation of Mathlib's trace-form route rather than of the
mathematics, and that removing it means building Krull–Akizuki or Nagata normalization-finiteness
first. Nothing here changes that; when the siblings lose the hypothesis, so does this file. The
rank statement `Isogeny.finrank_intermediateRing` already needs no separability.

## Provenance

⚠ *mathlib-track*, inherited. Every conclusion here is a sibling's conclusion repackaged, and both
siblings are flagged against `TauCetiRoadmap/EllipticCurves/README.md:1092`, which lists the
`IntermediateRing` with `intermediateRingFinite` among the components of D. Angdinata's shared
isogeny development; this file is deduplicated with them when that lands. Nothing is ported from
AINTLIB: the source states its structural facts for a fixed extension with the algebra structures
supplied as instance arguments, which is the shape this file exists to remove.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
-/

public section

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **A separable isogeny has separable function-field extension.** Separability of `φ` is recorded
over `φ.fieldPullback.fieldRange`, an intermediate field of `W₁.FunctionField`; this reads it over
`W₂.FunctionField` instead, which is the form every Mathlib result about a separable extension
takes.

Stated for an arbitrary algebra structure whose structure map is the pullback, matching
`Isogeny.degree_eq_finrank` and the siblings in this directory. -/
theorem isSeparable_functionField (φ : Isogeny W₁ W₂)
    [Algebra W₂.CoordinateRing W₁.FunctionField]
    [Algebra W₂.FunctionField W₁.FunctionField]
    [IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField]
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField]
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x) :
    Algebra.IsSeparable W₂.FunctionField W₁.FunctionField :=
  isSeparable_of_fieldRange φ.fieldPullback
    (φ.algebraMap_functionField_eq_fieldPullback h)

/-- The canonical tower `W₂.CoordinateRing → W₂.FunctionField → W₁.FunctionField` of an isogeny,
along the pullback and the function-field pullback. Every result below installs it, and it is the
only thing the two `letI`s do not give directly. -/
private theorem isScalarTower_pullback (φ : Isogeny W₁ W₂) :
    letI := φ.pullback.toRingHom.toAlgebra
    letI := φ.fieldPullback.toRingHom.toAlgebra
    IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField := by
  let _ := φ.pullback.toRingHom.toAlgebra
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  rw [φ.fieldPullback.algebraMap_toAlgebra_apply, φ.pullback.algebraMap_toAlgebra_apply,
    fieldPullback_algebraMap]

/-- **The corestricted pullback of a separable isogeny is a finite ring map**: the intermediate
ring is a finite module over the target coordinate ring, along `φ.pullbackToIntermediateRing`.

This is `Isogeny.moduleFinite_intermediateRing` with the algebra structures built from `φ` rather
than supplied by the caller, and separability taken in the `fieldRange` spelling of
`Isogeny/Separability.lean`. Integral closedness of `W₂.CoordinateRing` comes from
`WeierstrassCurve.Affine.isIntegrallyClosed_coordinateRing` for an elliptic curve. -/
theorem finite_pullbackToIntermediateRing (φ : Isogeny W₁ W₂)
    [IsIntegrallyClosed W₂.CoordinateRing]
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField] :
    φ.pullbackToIntermediateRing.Finite := by
  let _ := φ.pullback.toRingHom.toAlgebra
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  let _ := φ.pullbackToIntermediateRing.toAlgebra
  have h := φ.pullback.algebraMap_toAlgebra_apply
  have := φ.isScalarTower_pullback
  have := φ.isSeparable_functionField h
  have := φ.isScalarTower_intermediateRing rfl h
  exact φ.moduleFinite_intermediateRing h

/-- **The intermediate ring of a separable isogeny is a Dedekind domain**, with nothing for the
caller to supply.

This is `Isogeny.isDedekindDomain_intermediateRing` with the algebra structures built from `φ` and
separability taken in the `fieldRange` spelling of `Isogeny/Separability.lean`. The Dedekind
property of `W₂.CoordinateRing` comes from
`WeierstrassCurve.Affine.isDedekindDomain_coordinateRing` for an elliptic curve.

An `instance`: `Isogeny.pushClass` asks for exactly this hypothesis, and both of the premises are
themselves classes, so instance search can discharge it whenever the caller has a separable isogeny
into a curve with Dedekind coordinate ring. -/
instance isDedekindDomain_intermediateRing_of_isSeparable (φ : Isogeny W₁ W₂)
    [IsDedekindDomain W₂.CoordinateRing]
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField] :
    IsDedekindDomain φ.intermediateRing := by
  let _ := φ.pullback.toRingHom.toAlgebra
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  have h := φ.pullback.algebraMap_toAlgebra_apply
  have := φ.isScalarTower_pullback
  have := φ.isSeparable_functionField h
  exact φ.isDedekindDomain_intermediateRing h

end Isogeny

end TauCeti
