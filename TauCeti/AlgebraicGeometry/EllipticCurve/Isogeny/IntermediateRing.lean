/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Basic

/-!
# The intermediate ring of an isogeny

The integral closure of the target coordinate ring inside the source function field, taken along
an isogeny's pullback. This is the normalization that `CoordinatePullback.MapsInfinity` names,
and it receives both coordinate rings: the target's through the pullback, and the source's
because `mapsInfinity` is precisely the assertion that it lands there.

## Main definitions

* `TauCeti.Isogeny.intermediateRing`: the integral closure of `W₂.CoordinateRing` in
  `W₁.FunctionField` along `φ.pullback`.
* `TauCeti.Isogeny.toIntermediateRing` and `TauCeti.Isogeny.pullbackToIntermediateRing`: the two
  coordinate rings corestricted into it, along which ideals are extended and the relative norm
  is taken.

## Main results

* `TauCeti.Isogeny.algebraMap_mem_intermediateRing`: the source coordinate ring lands in it.
* `TauCeti.Isogeny.pullback_mem_intermediateRing`: so does the target coordinate ring.
* `TauCeti.Isogeny.id_intermediateRing`: an identity isogeny's intermediate ring is the
  coordinate ring itself, sitting inside its own fraction field.

## Design

The result is a `Subring W₁.FunctionField`, not a `Subalgebra`. The algebra structure that
`φ.pullback` induces on `W₁.FunctionField` is deliberately not a global instance — different
isogenies induce different ones, so registering any would be a diamond, as `Isogeny/Basic.lean`
explains. A `Subalgebra` would put that structure into the *type*, forcing every statement about
the object to fix a choice of it; a `Subring` keeps it inside the definition, exactly where
`MapsInfinity` already keeps it.

The two corestrictions are plain `RingHom`s rather than an `Algebra W₂.CoordinateRing`
instance on the intermediate ring. An algebra *instance* would reintroduce the diamond the
`Subring` choice exists to avoid, since the structure it would register is the pullback-induced
one; a bundled map carries the same information to consumers without registering anything.

Nothing here assumes separability, so purely inseparable isogenies such as Frobenius are covered.
`id_intermediateRing` is stated for an integrally closed coordinate ring rather than an elliptic
one, which is all its proof uses; the elliptic case is that hypothesis discharged by
`WeierstrassCurve.Affine.isIntegrallyClosed_coordinateRing`, and is not given a separate name
because nothing would consume it.

The structural theory of this ring — module-finiteness over `W₂.CoordinateRing`, and its being a
Dedekind domain — is deliberately not proved here. Every route to it in Mathlib
(`IsIntegralClosure.finite`, `integralClosure.isDedekindDomain`) carries an
`Algebra.IsSeparable` hypothesis, so the inseparable case that this roadmap wants is separate
work rather than a corollary of the definition.

This opens the "points come along" milestone of Layer 1 of
`TauCetiRoadmap/EllipticCurves/README.md`, which names this object as "the **intermediate ring**
— the integral closure of `W₂.CoordinateRing` in `W₁.FunctionField`, the normalization
`mapsInfinity` names", receiving both coordinate rings on the way to `pushClass` and
`toPointHom`. It follows Silverman, *The Arithmetic of Elliptic Curves*, II.2.

## Provenance

The choice of object is taken from the AINTLIB project (`github.com/CBirkbeck/AINTLIB`, at
revision `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache 2.0 per the source file's header, by
Chris Birkbeck): `projects/HasseWeil/HasseWeil/Curves/NormConormIntegralClosure.lean`, which
introduces `B := integralClosure C₂.CoordinateRing C₁.FunctionField` and carries its structural
instances `instDedekindB`, `instModuleFiniteB`, `instFractionRingB` and `instTorsionFreeB`, proved
in `projects/HasseWeil/HasseWeil/Curves/RamificationFinite.lean`.

What is adapted here is the object and the observation that the integral closure over the
*coordinate* ring — rather than over a localization — is the right home for the norm and
class-group route to the induced map on points. The structural instances are deliberately **not**
ported: the source proves them for a fixed extension carrying `[Algebra.IsSeparable K L]`, with
the algebra structures supplied as instance arguments, whereas this file takes the pullback-induced
structure locally and assumes no separability. None of the declarations below is a transcription
of a source declaration.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
-/

public section

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **The intermediate ring of an isogeny**: the integral closure of the target coordinate ring
inside the source function field, along the isogeny's pullback. -/
noncomputable def intermediateRing (φ : Isogeny W₁ W₂) : Subring W₁.FunctionField :=
  letI := φ.pullback.toRingHom.toAlgebra
  (integralClosure W₂.CoordinateRing W₁.FunctionField).toSubring

/-- Membership in the intermediate ring is integrality over the target coordinate ring acting
through the pullback. The definition's body is not exposed across the module boundary, so this
is how downstream modules compute with it.

Deliberately not `@[simp]`: it would rewrite every `z ∈ φ.intermediateRing` into the `IsIntegral`
form, which is exactly the left-hand side of the two membership lemmas below, so tagging it would
stop those firing. The simp-normal form of a membership goal is discharge by one of them; this
lemma is the escape hatch for the goals they do not cover. -/
theorem mem_intermediateRing_iff (φ : Isogeny W₁ W₂) (z : W₁.FunctionField) :
    z ∈ φ.intermediateRing ↔
      @IsIntegral W₂.CoordinateRing W₁.FunctionField _ _ φ.pullback.toRingHom.toAlgebra z :=
  Iff.rfl

/-- **The source coordinate ring lands in the intermediate ring.** This is `mapsInfinity` read
as a statement about that ring: pointedness of the isogeny says exactly that the source
coordinates are integral over the pulled-back target coordinate ring. -/
@[simp]
theorem algebraMap_mem_intermediateRing (φ : Isogeny W₁ W₂) (x : W₁.CoordinateRing) :
    algebraMap W₁.CoordinateRing W₁.FunctionField x ∈ φ.intermediateRing :=
  (CoordinatePullback.mapsInfinity_iff φ.pullback).1 φ.mapsInfinity x

/-- **The target coordinate ring lands in the intermediate ring**, through the pullback: each
element of the image is integral over the ring it is the image of. -/
@[simp]
theorem pullback_mem_intermediateRing (φ : Isogeny W₁ W₂) (x : W₂.CoordinateRing) :
    φ.pullback x ∈ φ.intermediateRing :=
  letI := φ.pullback.toRingHom.toAlgebra
  isIntegral_algebraMap

/-- The source coordinate ring, corestricted into the intermediate ring. Extending an ideal of
`W₁.CoordinateRing` into the intermediate ring is done along this map. -/
noncomputable def toIntermediateRing (φ : Isogeny W₁ W₂) :
    W₁.CoordinateRing →+* φ.intermediateRing :=
  (algebraMap W₁.CoordinateRing W₁.FunctionField).codRestrict _
    φ.algebraMap_mem_intermediateRing

@[simp]
theorem coe_toIntermediateRing (φ : Isogeny W₁ W₂) (x : W₁.CoordinateRing) :
    (φ.toIntermediateRing x : W₁.FunctionField) =
      algebraMap W₁.CoordinateRing W₁.FunctionField x := (rfl)

/-- The target coordinate ring, corestricted into the intermediate ring along the pullback. The
relative ideal norm back down to `W₂.CoordinateRing` is taken over this map. -/
noncomputable def pullbackToIntermediateRing (φ : Isogeny W₁ W₂) :
    W₂.CoordinateRing →+* φ.intermediateRing :=
  φ.pullback.toRingHom.codRestrict _ φ.pullback_mem_intermediateRing

@[simp]
theorem coe_pullbackToIntermediateRing (φ : Isogeny W₁ W₂) (x : W₂.CoordinateRing) :
    (φ.pullbackToIntermediateRing x : W₁.FunctionField) = φ.pullback x := (rfl)

/-- **The identity isogeny's intermediate ring is the coordinate ring itself**, embedded in its
own fraction field: nothing in the function field beyond an integrally closed coordinate ring is
integral over it. For an elliptic curve the hypothesis is
`WeierstrassCurve.Affine.isIntegrallyClosed_coordinateRing`. -/
@[simp]
theorem id_intermediateRing (W : WeierstrassCurve.Affine F) [IsIntegrallyClosed W.CoordinateRing] :
    (id W).intermediateRing = (algebraMap W.CoordinateRing W.FunctionField).range := by
  -- the identity pullback induces the coordinate ring's own algebra structure on the function
  -- field, so the integral closure below is the ordinary one
  have halg : (CoordinatePullback.id W).toRingHom.toAlgebra =
      (inferInstance : Algebra W.CoordinateRing W.FunctionField) := by
    apply Algebra.algebra_ext
    intro x
    rw [RingHom.algebraMap_toAlgebra]
    exact CoordinatePullback.id_apply W x
  ext z
  rw [mem_intermediateRing_iff, RingHom.mem_range, id_pullback, halg]
  constructor
  · intro hz
    have hbot : z ∈ integralClosure W.CoordinateRing W.FunctionField := hz
    rw [IsIntegrallyClosed.integralClosure_eq_bot] at hbot
    exact Algebra.mem_bot.1 hbot
  · rintro ⟨x, rfl⟩
    exact isIntegral_algebraMap

end Isogeny

end TauCeti
