/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Basic
public import TauCeti.RingTheory.ClassGroup.ExtendedRelNorm
-- Public: `finite_pullbackToIntermediateRing` occurs in the statement of `pushClass_id`, and the
-- Dedekind instance beside it is what makes that statement elaborate.
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Separable
-- Proof-only: the rank of the intermediate ring is what makes the identity's pushforward the
-- identity, and the degree is read through it; neither occurs in a statement here.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Rank

/-!
# The class-group pushforward of an isogeny

An isogeny `φ : W₁ → W₂` pushes ideal classes forward,
`pushClass φ : ClassGroup W₁.CoordinateRing →* ClassGroup W₂.CoordinateRing`, by extending an
ideal of `W₁.CoordinateRing` into `φ.intermediateRing` — the integral closure of
`W₂.CoordinateRing` in `W₁.FunctionField`, which receives both coordinate rings — and taking the
relative ideal norm back down to `W₂.CoordinateRing`. Both steps are already available:
`ClassGroup.extendedRelNormHom` is exactly this composite for three rings sharing an overring, and
`IntermediateRing/Basic.lean` corestricts the two coordinate rings into that overring.

This is the middle link of the "points come along" milestone of
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 1: "Ideal extension into it followed by the
**relative ideal norm** down to `W₂.CoordinateRing` gives `pushClass` on class groups, whence
`toPointHom : W₁.Point →+ W₂.Point` through `toClassEquiv`". Conjugating `pushClass` by
`toClassEquiv` is what remains, and it waits on surjectivity of Mathlib's `Point.toClass` — the
Layer-0 anchor, of which only the equivalent condition
`WeierstrassCurve.Affine.Point.toClass_surjective_iff` is in the repository. The point of routing
the induced map on points this way is that it is additive *by construction*: `pushClass` is a
monoid homomorphism of class groups, so no separate rigidity theorem (AEC III.4.8) is needed.

## Main definitions

* `TauCeti.Isogeny.pushClass`: the class-group pushforward of an isogeny.

## Main results

* `TauCeti.Isogeny.pushClass_eq_extendedRelNormHom`: `pushClass` is `ClassGroup.extendedRelNormHom`
  read against any algebra structures agreeing with the two corestrictions — the gateway to that
  homomorphism's computation rules, `ClassGroup.extendedRelNormHom_apply` and
  `ClassGroup.extendedRelNormHom_mk0`.
* `TauCeti.Isogeny.pushClass_id`: **the identity isogeny pushes classes forward by the identity.**

## Design

**The algebra structures are built into the definition, not asked of the caller.** Neither
`Algebra W₁.CoordinateRing φ.intermediateRing` nor `Algebra W₂.CoordinateRing φ.intermediateRing`
is a global instance — for an endomorphism the two would be a diamond, which is precisely the
elaboration problem `ClassGroup/ExtendedRelNorm.lean` records — so `pushClass` installs
`φ.toIntermediateRing.toAlgebra` and `φ.pullbackToIntermediateRing.toAlgebra` itself. That is what
makes it more than a specialisation of `ClassGroup.extendedRelNormHom`: it pins the two structures
that the composite is otherwise free to choose, and the choice is what carries the geometry (the
source coordinate ring enters as functions, the target through the pullback).

Consequently the two remaining hypotheses are stated so that no structure is needed to write them
down. Dedekindness of `φ.intermediateRing` is intrinsic to the ring, so it is an instance argument
and `IntermediateRing/Separable.lean` discharges it by instance search for a separable isogeny into
a curve with Dedekind coordinate ring; module-finiteness over `W₂.CoordinateRing` is finiteness
*along* the corestricted pullback, which is Mathlib's `RingHom.Finite` — not a class, so it is
passed by name, `Isogeny.finite_pullbackToIntermediateRing` being the same file's witness.
`pushClass_id` below exercises both. Torsion-freeness on either side is not a hypothesis at all: it
is injectivity of the two corestrictions, proved in `IntermediateRing/Basic.lean`.

**Why the composite is a homomorphism of the *whole* class group.** `ClassGroup.relNorm` is
multiplicative because `Ideal.relNorm` is, and it descends to classes because the norm of a
principal ideal is principal; extension of ideals is multiplicative for the same reason. Neither
step sees the curve. What the curve supplies is the ring in the middle — that
`W₁.CoordinateRing` lands in the integral closure of `W₂.CoordinateRing` is exactly
`mapsInfinity`, the pointedness of the isogeny.

**What is not here.** Functoriality `pushClass (ψ ∘ φ) = pushClass ψ ∘ pushClass φ` is left to
separate work: the intermediate rings of `φ`, `ψ` and `ψ ∘ φ` form a tower — `φ.intermediateRing`
does sit inside `(ψ.comp φ).intermediateRing`, since `W₂.CoordinateRing` is integral over the
pulled-back `W₃.CoordinateRing` by `ψ.mapsInfinity` — but the composition law needs transitivity of
`Ideal.relNorm` along that tower, which the pinned Mathlib does not carry. The identity law below
needs no such input.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2, III.4.
-/

public section

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **The class-group pushforward of an isogeny.** An ideal class of the source coordinate ring is
extended into `φ.intermediateRing`, the integral closure of the target coordinate ring in the
source function field, and normed back down to the target coordinate ring.

The two algebra structures on the intermediate ring are the corestrictions
`φ.toIntermediateRing` and `φ.pullbackToIntermediateRing` of `IntermediateRing/Basic.lean`; they
are installed here rather than demanded of the caller, since neither can be a global instance.
Torsion-freeness over both coordinate rings is their injectivity and so costs no hypothesis. -/
noncomputable def pushClass (φ : Isogeny W₁ W₂) [IsDedekindDomain W₂.CoordinateRing]
    [IsDedekindDomain φ.intermediateRing] (hfin : φ.pullbackToIntermediateRing.Finite) :
    ClassGroup W₁.CoordinateRing →* ClassGroup W₂.CoordinateRing :=
  letI := φ.toIntermediateRing.toAlgebra
  letI := φ.pullbackToIntermediateRing.toAlgebra
  haveI : Module.Finite W₂.CoordinateRing φ.intermediateRing := hfin
  haveI : Module.IsTorsionFree W₁.CoordinateRing φ.intermediateRing :=
    Module.isTorsionFree_iff_algebraMap_injective.2 φ.toIntermediateRing_injective
  haveI : Module.IsTorsionFree W₂.CoordinateRing φ.intermediateRing :=
    Module.isTorsionFree_iff_algebraMap_injective.2 φ.pullbackToIntermediateRing_injective
  ClassGroup.extendedRelNormHom W₁.CoordinateRing φ.intermediateRing W₂.CoordinateRing

/-- **`pushClass` is `ClassGroup.extendedRelNormHom` for the two corestrictions.**

Stated for arbitrary algebra structures on `φ.intermediateRing` whose structure maps are the
corestricted `algebraMap` and the corestricted pullback, so that a caller's own structures are
accepted rather than only the locally-built ones — the idiom of
`Isogeny.isIntegralClosure_intermediateRing` and `Isogeny.isScalarTower_intermediateRing`. This is
how a consumer computes with `pushClass`: rewriting by it turns a goal about the pushforward into
one about `ClassGroup.extendedRelNormHom`, where `ClassGroup.extendedRelNormHom_apply` unfolds the
composite and `ClassGroup.extendedRelNormHom_mk0` evaluates it on the class of an integral ideal. -/
theorem pushClass_eq_extendedRelNormHom (φ : Isogeny W₁ W₂) [IsDedekindDomain W₂.CoordinateRing]
    [IsDedekindDomain φ.intermediateRing] (hfin : φ.pullbackToIntermediateRing.Finite)
    [inst₁ : Algebra W₁.CoordinateRing φ.intermediateRing]
    [inst₂ : Algebra W₂.CoordinateRing φ.intermediateRing]
    [Module.IsTorsionFree W₁.CoordinateRing φ.intermediateRing]
    [Module.Finite W₂.CoordinateRing φ.intermediateRing]
    [Module.IsTorsionFree W₂.CoordinateRing φ.intermediateRing]
    (h₁ : inst₁ = φ.toIntermediateRing.toAlgebra)
    (h₂ : inst₂ = φ.pullbackToIntermediateRing.toAlgebra) :
    φ.pushClass hfin =
      ClassGroup.extendedRelNormHom W₁.CoordinateRing φ.intermediateRing W₂.CoordinateRing := by
  -- the remaining instances are propositions, so the two sides agree once the data does
  subst h₁
  subst h₂
  rfl

/-- **The identity isogeny's two corestrictions coincide.** Its pullback is the embedding of the
coordinate ring in its own function field, so extending an ideal along `toIntermediateRing` and
norming along `pullbackToIntermediateRing` happen over one and the same ring map. -/
theorem id_toIntermediateRing (W : WeierstrassCurve.Affine F) :
    (id W).toIntermediateRing = (id W).pullbackToIntermediateRing := by
  refine RingHom.ext fun x ↦ Subtype.ext ?_
  rw [coe_toIntermediateRing, coe_pullbackToIntermediateRing, id_pullback,
    CoordinatePullback.id_apply]

/-- **The identity isogeny pushes ideal classes forward by the identity.**

Extending and norming back down along one and the same ring map raises a class to the power
`[φ.intermediateRing : W.CoordinateRing]` (`ClassGroup.relNorm_extendedHom`), and for the identity
that rank is `deg (id W) = 1` by `Isogeny.finrank_intermediateRing` — the intermediate ring being
`W.CoordinateRing` itself, sitting in its own function field.

Both structural hypotheses of `pushClass` are discharged rather than assumed: the identity is
separable (`Isogeny.isSeparable_id`), so `IntermediateRing/Separable.lean` supplies Dedekindness of
its intermediate ring by instance search and finiteness of the corestricted pullback by name. For
an elliptic `W` the remaining hypothesis is
`WeierstrassCurve.Affine.isDedekindDomain_coordinateRing`. -/
@[simp]
theorem pushClass_id (W : WeierstrassCurve.Affine F) [IsDedekindDomain W.CoordinateRing] :
    (id W).pushClass (id W).finite_pullbackToIntermediateRing =
      MonoidHom.id (ClassGroup W.CoordinateRing) := by
  let _ := (id W).pullbackToIntermediateRing.toAlgebra
  have hfin := (id W).finite_pullbackToIntermediateRing
  have : Module.Finite W.CoordinateRing (id W).intermediateRing := hfin
  have : Module.IsTorsionFree W.CoordinateRing (id W).intermediateRing :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (id W).pullbackToIntermediateRing_injective
  -- the identity pullback is the embedding into the function field, so both corestrictions are
  -- the registered structure map
  have hpull : ∀ x, algebraMap W.CoordinateRing W.FunctionField x = (id W).pullback x :=
    fun x ↦ by rw [id_pullback, CoordinatePullback.id_apply]
  have := (id W).isScalarTower_intermediateRing rfl hpull
  have hrank : Module.finrank W.CoordinateRing (id W).intermediateRing = 1 := by
    rw [(id W).finrank_intermediateRing hpull, degree_id]
  refine MonoidHom.ext fun c ↦ ?_
  rw [(id W).pushClass_eq_extendedRelNormHom hfin (congrArg RingHom.toAlgebra
    (id_toIntermediateRing W).symm) rfl, ClassGroup.extendedRelNormHom_apply,
    ClassGroup.relNorm_extendedHom, hrank, pow_one, MonoidHom.id_apply]

end Isogeny

end TauCeti
