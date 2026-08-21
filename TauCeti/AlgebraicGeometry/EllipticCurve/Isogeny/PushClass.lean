/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Dedekind
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Finite
public import TauCeti.RingTheory.ClassGroup.ExtendedRelNorm
-- Proof-only: `Algebra.IsSeparable.of_equiv_equiv` moves separability off the pullback's range.
import Mathlib.FieldTheory.Separable
-- Proof-only: `AlgHom.algebraMap_toAlgebra_apply` discharges the structure-map hypotheses.
import TauCeti.Algebra.Algebra.Hom

/-!
# The map on ideal class groups induced by an isogeny

An isogeny `φ : Isogeny W₁ W₂` gives no map of coordinate rings in either direction: its pullback
lands in `W₁.FunctionField`, not in `W₁.CoordinateRing`. What both coordinate rings do map into is
`Isogeny.intermediateRing`, the integral closure of `W₂.CoordinateRing` in `W₁.FunctionField`. So
an ideal class of `W₁.CoordinateRing` travels to `W₂.CoordinateRing` in two steps: **extend** it
into the intermediate ring, then take its **relative norm** back down. That composite is
`Isogeny.pushClass`, and this file defines it, computes it on the class of an integral ideal, and
evaluates it at the identity isogeny.

## Main definitions

* `TauCeti.Isogeny.pushClass`: the induced homomorphism
  `ClassGroup W₁.CoordinateRing →* ClassGroup W₂.CoordinateRing`.

## Main results

* `TauCeti.Isogeny.pushClass_eq_extendedRelNormHom`: it is `ClassGroup.extendedRelNormHom` through
  the intermediate ring, read against whatever structures the caller holds.
* `TauCeti.Isogeny.pushClass_mk0`: its value on the class of a nonzero integral ideal — extend the
  ideal, norm it down, take the class.
* `TauCeti.Isogeny.pushClass_id`: the identity isogeny induces the identity homomorphism.
* `TauCeti.Isogeny.isScalarTower_functionField`, `TauCeti.Isogeny.isSeparable_functionField`,
  `TauCeti.Isogeny.isDedekindDomain_intermediateRing_of_isSeparable` and
  `TauCeti.Isogeny.moduleFinite_intermediateRing_of_isSeparable`: the structural inputs, restated
  so that separability of `φ` is the *only* hypothesis beyond a Dedekind target coordinate ring.
* `TauCeti.Isogeny.id_pullbackToIntermediateRing`: the identity isogeny's two corestrictions into
  its intermediate ring are the same map, which is what makes `pushClass_id` a tower computation.

## What this is, mathematically

Geometrically this is push-forward of divisor classes along `φ`. A degree-zero divisor class on
`W₁` is carried to one on `W₂` by summing over fibres with multiplicity, which is exactly what
extending an ideal into the normalization and norming it down does — the intermediate ring is the
ring of functions regular away from the whole fibre `φ⁻¹(O₂)`, and the relative norm is the
fibrewise product.

This is the algebraic half of the roadmap's "points come along, with the group law for free"
milestone. The other half is `toPointHom : W₁.Point →+ W₂.Point`, obtained by conjugating
`pushClass` with the identification of the point group with the whole ideal class group. That
identification is `Point.toClass`, which the pinned Mathlib proves **injective** but not
surjective; `WeierstrassCurve.Affine.Point.toClass_surjective_iff` records what its
surjectivity amounts to, and until that is discharged `toPointHom` cannot be defined. Nothing in
this file needs it: `pushClass` is a statement about class groups alone.

Additivity of `toPointHom` — Silverman III.4.8, "a pointed morphism is a homomorphism" — will then
be automatic, since `pushClass` is a homomorphism by construction. That is the point of routing
the induced map through the class group rather than through coordinates.

## Design

**The definition is intrinsic; the theorems accept the caller's structures.** `pushClass` builds
the two algebra structures on the intermediate ring from the bundled `Isogeny.toIntermediateRing`
and `Isogeny.pullbackToIntermediateRing`, so it is a function of `φ` alone, matching
`Isogeny.degree`, which is `Module.finrank` over `φ.fieldPullback.fieldRange` for the same reason.
The equation lemmas then take an arbitrary pair of structures together with the hypotheses saying
they *are* those two corestrictions, matching `Isogeny.degree_eq_finrank` and
`Isogeny.moduleFinite_intermediateRing`.

Neither structure can be a global instance, and the obstruction is not hypothetical: for an
endomorphism `W₁ = W₂` the two have the *same* type `Algebra W₁.CoordinateRing φ.intermediateRing`
and different values, so registering both is a diamond — the one
`TauCeti.RingTheory.ClassGroup.ExtendedRelNorm` records from its source. This is why every
statement here that mentions them takes them as hypotheses rather than assuming they are found.

**Separability is a hypothesis of the route, not of the result.** `ClassGroup.extendedRelNormHom`
needs the intermediate ring to be a Dedekind domain and module-finite over `W₂.CoordinateRing`,
and both of those are available in the pinned Mathlib only through the trace form, hence only for
a separable extension — `IntermediateRing/Dedekind.lean` measures exactly what removing the
hypothesis would take. So `pushClass` is defined for separable isogenies only, and in particular
not for Frobenius. When the inseparable case of those two structural results lands, this
definition loses the hypothesis without changing its body.

Separability is spelt `Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField`, which is
the repository's convention for "`φ` is separable" (`Isogeny/Separability.lean` explains why there
is no `Isogeny.IsSeparable` predicate): it is intrinsic to `φ`, so it can appear as an instance
argument of a definition, where the sibling files' `Algebra.IsSeparable W₂.FunctionField
W₁.FunctionField` cannot — that one is a statement about a structure the caller supplies.
`isSeparable_functionField` is the bridge between the two, and together with
`isScalarTower_functionField` it turns the siblings' caller-supplied setups into consequences of
separability alone. Those restatements live here rather than beside their siblings because they
are stated against the canonical structures `pushClass` is built from, which is a fact about this
construction rather than about the intermediate ring; the siblings remain the general forms.

## Provenance

⚠ *mathlib-track*. `TauCetiRoadmap/EllipticCurves/README.md:1092` lists `pushClass` among the
components of D. Angdinata's shared isogeny development, on the way to `toPointHom`, under the same
flag `Isogeny/Basic.lean` and the `IntermediateRing` files carry; it is built here until those PRs
land. That development reaches `pushClass` with **no** separability hypothesis — its inventory
asks only for `[IsIntegrallyClosed W₂.CoordinateRing]` and `[DecidableEq F]` — because it carries
`RingTheory/IntegralClosure/NormalizationFinite` among its supports. The pinned Mathlib has no
such route, and that gap is exactly the separability hypothesis here.

The endomorphism case of this composite is `classNorm_comp_classMap` in AINTLIB's
`HasseWeil/Pic0/IsogenyClassGroup.lean` (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`dev/hasse-weil @ 513e83879e2f`, by Chris Birkbeck), where both class groups are
`ClassGroup E.CoordinateRing`; the two-curve form here is not a transcription of it, and the
arithmetic it rests on — `ClassGroup.relNorm` and `ClassGroup.relNorm_extendedHom`, which
`pushClass_id` consumes — is already ported in `TauCeti.RingTheory.ClassGroup.RelNorm`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2, III.4.
-/

public section

open scoped nonZeroDivisors

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F} (φ : Isogeny W₁ W₂)

/-- **The coordinate and function-field pullbacks of an isogeny form a tower.** Both structures
are the ones `φ` induces; the tower is `fieldPullback_algebraMap`, that the function-field
pullback extends the coordinate one.

This is the setup every structural theorem about `φ.intermediateRing` asks for, collected once
rather than rebuilt at each use. -/
theorem isScalarTower_functionField :
    letI := φ.pullback.toRingHom.toAlgebra
    letI := φ.fieldPullback.toRingHom.toAlgebra
    IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField :=
  letI := φ.pullback.toRingHom.toAlgebra
  letI := φ.fieldPullback.toRingHom.toAlgebra
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [_root_.AlgHom.algebraMap_toAlgebra_apply, _root_.AlgHom.algebraMap_toAlgebra_apply,
      φ.fieldPullback_algebraMap]

section Separable

variable [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField]

/-- **A separable isogeny has a separable function-field extension**, over `W₂.FunctionField`
itself rather than over the range of the pullback.

Separability of `φ` is separability over `φ.fieldPullback.fieldRange`, which is intrinsic to `φ`;
Mathlib's theorems about separable extensions want the abstract source field, which is only
available once a structure is chosen. This moves between the two along `AlgHom.equivFieldRange`. -/
theorem isSeparable_functionField :
    letI := φ.fieldPullback.toRingHom.toAlgebra
    Algebra.IsSeparable W₂.FunctionField W₁.FunctionField :=
  letI := φ.fieldPullback.toRingHom.toAlgebra
  -- `equivFieldRange` is the range restriction of the pullback; it is the identity on
  -- `W₁.FunctionField`, and the square commutes because the structure map is the pullback
  Algebra.IsSeparable.of_equiv_equiv φ.fieldPullback.equivFieldRange.symm.toRingEquiv
    (RingEquiv.refl W₁.FunctionField) <| by
      ext z
      simpa [_root_.AlgHom.algebraMap_toAlgebra_apply] using
        (_root_.AlgHom.equivFieldRange_apply_coe φ.fieldPullback
          (φ.fieldPullback.equivFieldRange.symm z)).symm

variable [IsDedekindDomain W₂.CoordinateRing]

/-- **The intermediate ring of a separable isogeny is a Dedekind domain.**

This is `Isogeny.isDedekindDomain_intermediateRing` with every hypothesis about a caller-supplied
algebra structure discharged, leaving separability of `φ` and a Dedekind target coordinate ring.
For an elliptic `W₂` the latter is `WeierstrassCurve.Affine.isDedekindDomain_coordinateRing`. -/
theorem isDedekindDomain_intermediateRing_of_isSeparable :
    IsDedekindDomain φ.intermediateRing :=
  letI := φ.pullback.toRingHom.toAlgebra
  letI := φ.fieldPullback.toRingHom.toAlgebra
  haveI := φ.isScalarTower_functionField
  haveI := φ.isSeparable_functionField
  φ.isDedekindDomain_intermediateRing (_root_.AlgHom.algebraMap_toAlgebra_apply φ.pullback)

/-- **The intermediate ring of a separable isogeny is module-finite over the target coordinate
ring**, for the structure the corestricted pullback induces.

The canonical-structure form of `Isogeny.moduleFinite_intermediateRing`, as
`isDedekindDomain_intermediateRing_of_isSeparable` is of its Dedekind sibling. -/
theorem moduleFinite_intermediateRing_of_isSeparable :
    letI := φ.pullbackToIntermediateRing.toAlgebra
    Module.Finite W₂.CoordinateRing φ.intermediateRing :=
  letI := φ.pullback.toRingHom.toAlgebra
  letI := φ.fieldPullback.toRingHom.toAlgebra
  letI := φ.pullbackToIntermediateRing.toAlgebra
  haveI := φ.isScalarTower_functionField
  haveI := φ.isSeparable_functionField
  haveI : IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField :=
    φ.isScalarTower_intermediateRing rfl (_root_.AlgHom.algebraMap_toAlgebra_apply φ.pullback)
  φ.moduleFinite_intermediateRing (_root_.AlgHom.algebraMap_toAlgebra_apply φ.pullback)

/-- **The map on ideal class groups induced by an isogeny**: extend a class of
`W₁.CoordinateRing` into `φ.intermediateRing` along the source coordinate ring's embedding, then
take its relative norm down to `W₂.CoordinateRing` along the pulled-back one.

It is a homomorphism because both steps are, which is what makes the induced map on points
additive with no separate rigidity theorem. Defined for a separable `φ`, which is what the
intermediate ring's Dedekind property and module-finiteness currently cost; see the module
docstring. -/
noncomputable def pushClass : ClassGroup W₁.CoordinateRing →* ClassGroup W₂.CoordinateRing :=
  letI := φ.toIntermediateRing.toAlgebra
  letI := φ.pullbackToIntermediateRing.toAlgebra
  haveI := φ.isDedekindDomain_intermediateRing_of_isSeparable
  haveI := φ.moduleFinite_intermediateRing_of_isSeparable
  haveI : Module.IsTorsionFree W₁.CoordinateRing φ.intermediateRing :=
    Module.isTorsionFree_iff_algebraMap_injective.2 φ.toIntermediateRing_injective
  haveI : Module.IsTorsionFree W₂.CoordinateRing φ.intermediateRing :=
    Module.isTorsionFree_iff_algebraMap_injective.2 φ.pullbackToIntermediateRing_injective
  ClassGroup.extendedRelNormHom W₁.CoordinateRing φ.intermediateRing W₂.CoordinateRing

variable [instS : Algebra W₁.CoordinateRing φ.intermediateRing]
  [instT : Algebra W₂.CoordinateRing φ.intermediateRing]
  [IsDedekindDomain φ.intermediateRing]
  [Module.IsTorsionFree W₁.CoordinateRing φ.intermediateRing]
  [Module.Finite W₂.CoordinateRing φ.intermediateRing]
  [Module.IsTorsionFree W₂.CoordinateRing φ.intermediateRing]

/-- **`pushClass` is extension into the intermediate ring followed by the relative norm.**

The definition builds the two algebra structures on `φ.intermediateRing` itself; this reads it
against a caller's own, which the two hypotheses pin to the same corestrictions. Neither structure
can be an instance — for an endomorphism the two have the same type — so a consumer installs them
with `let _ := φ.toIntermediateRing.toAlgebra` and `let _ := φ.pullbackToIntermediateRing.toAlgebra`
and discharges both hypotheses by `rfl`. -/
theorem pushClass_eq_extendedRelNormHom
    (hS : ∀ x, algebraMap W₁.CoordinateRing φ.intermediateRing x = φ.toIntermediateRing x)
    (hT : ∀ x, algebraMap W₂.CoordinateRing φ.intermediateRing x =
      φ.pullbackToIntermediateRing x) :
    φ.pushClass =
      ClassGroup.extendedRelNormHom W₁.CoordinateRing φ.intermediateRing W₂.CoordinateRing := by
  have hs : instS = φ.toIntermediateRing.toAlgebra := Algebra.algebra_ext _ _ hS
  have ht : instT = φ.pullbackToIntermediateRing.toAlgebra := Algebra.algebra_ext _ _ hT
  subst hs
  subst ht
  -- `subst` leaves the two structures as bare terms, so re-register them for synthesis
  let _ := φ.toIntermediateRing.toAlgebra
  let _ := φ.pullbackToIntermediateRing.toAlgebra
  rfl

/-- **The value of `pushClass` on the class of a nonzero integral ideal**: extend the ideal into
the intermediate ring, norm it back down, and take the class. This is the computation rule, and
the form in which a divisor-theoretic consumer meets the map. -/
theorem pushClass_mk0 [IsDedekindDomain W₁.CoordinateRing]
    (hS : ∀ x, algebraMap W₁.CoordinateRing φ.intermediateRing x = φ.toIntermediateRing x)
    (hT : ∀ x, algebraMap W₂.CoordinateRing φ.intermediateRing x =
      φ.pullbackToIntermediateRing x)
    (I : (Ideal W₁.CoordinateRing)⁰) :
    φ.pushClass (ClassGroup.mk0 I) =
      ClassGroup.mk0 (Ideal.relNorm0 W₂.CoordinateRing
        (ClassGroup.extendedIdeal W₁.CoordinateRing φ.intermediateRing I)) := by
  rw [φ.pushClass_eq_extendedRelNormHom hS hT, ClassGroup.extendedRelNormHom_mk0]

end Separable

section Id

variable (W : WeierstrassCurve.Affine F)

/-- **The identity isogeny is separable.** Its function-field pullback is the identity, so the
extension its degree measures is `W.FunctionField` over a copy of itself.

Deliberately not an instance. It is wanted once, to state `pushClass_id`, and registering it
would change how `simp` computes elsewhere: `Isogeny.separableDegree_eq_degree_of_isSeparable`
would then fire on the identity isogeny, making the existing simp lemmas
`Isogeny.separableDegree_id` and `Isogeny.inseparableDegree_id` redundant. A `haveI` at the one
use site keeps that global effect out of a file about class groups. -/
theorem isSeparable_id : Algebra.IsSeparable (id W).fieldPullback.fieldRange W.FunctionField :=
  Algebra.IsSeparable.of_equiv_equiv (id W).fieldPullback.equivFieldRange.toRingEquiv
    (RingEquiv.refl W.FunctionField) <| by
      ext z
      simp [_root_.AlgHom.equivFieldRange_apply_coe]

/-- **The identity isogeny's two corestrictions into its intermediate ring agree**, both being the
coordinate ring's own embedding into its function field. This is what collapses the
extend-then-norm composite to a single tower. -/
theorem id_pullbackToIntermediateRing :
    (id W).pullbackToIntermediateRing = (id W).toIntermediateRing :=
  RingHom.ext fun x ↦ Subtype.ext <| by
    rw [coe_pullbackToIntermediateRing, coe_toIntermediateRing, id_pullback,
      CoordinatePullback.id_apply]

/-- **The identity isogeny induces the identity on class groups.**

Its intermediate ring is the coordinate ring's own image in the function field, so extending and
norming run up and down the same degree-one tower: `ClassGroup.relNorm_extendedHom` raises a class
to the `Module.finrank` power, and that rank is `1`. -/
theorem pushClass_id [IsDedekindDomain W.CoordinateRing] :
    haveI := isSeparable_id W
    (id W).pushClass = MonoidHom.id (ClassGroup W.CoordinateRing) := by
  have := isSeparable_id W
  -- the identity's two corestrictions agree, so one structure serves for both sides
  let _ := (id W).toIntermediateRing.toAlgebra
  have hT : ∀ x, algebraMap W.CoordinateRing (id W).intermediateRing x =
      (id W).pullbackToIntermediateRing x := fun x ↦ by
    rw [id_pullbackToIntermediateRing]
    rfl
  have : Module.IsTorsionFree W.CoordinateRing (id W).intermediateRing :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (id W).toIntermediateRing_injective
  have := (id W).isDedekindDomain_intermediateRing_of_isSeparable
  -- the corestriction is onto: the identity's intermediate ring is the range of the coordinate
  -- ring in its own fraction field, an integrally closed ring having nothing integral above it
  have hsurj : Function.Surjective (id W).toIntermediateRing := fun z ↦ by
    have hz : (z : W.FunctionField) ∈
        (algebraMap W.CoordinateRing W.FunctionField).range := by
      rw [← id_intermediateRing W]
      exact z.2
    obtain ⟨x, hx⟩ := hz
    exact ⟨x, Subtype.ext (((id W).coe_toIntermediateRing x).trans hx)⟩
  have hrank : Module.finrank W.CoordinateRing (id W).intermediateRing = 1 :=
    ((LinearEquiv.ofBijective (Algebra.linearMap W.CoordinateRing (id W).intermediateRing)
      ⟨(id W).toIntermediateRing_injective, hsurj⟩).finrank_eq).symm.trans
      (Module.finrank_self W.CoordinateRing)
  have : Module.Finite W.CoordinateRing (id W).intermediateRing :=
    Module.Finite.of_surjective (Algebra.linearMap W.CoordinateRing (id W).intermediateRing) hsurj
  rw [(id W).pushClass_eq_extendedRelNormHom (fun _ ↦ rfl) hT]
  ext c
  rw [ClassGroup.extendedRelNormHom_apply, ClassGroup.relNorm_extendedHom, hrank, pow_one,
    MonoidHom.id_apply]

end Id

end Isogeny

end TauCeti
