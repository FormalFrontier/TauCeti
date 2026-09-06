/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Dedekind
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Finite
public import TauCeti.RingTheory.ClassGroup.ExtendedRelNorm

/-!
# The class-group map induced by an isogeny

For an isogeny `φ : Isogeny W₁ W₂`, extending an ideal of `W₁.CoordinateRing` into the
intermediate ring and taking the relative norm down to `W₂.CoordinateRing` gives a homomorphism
of class groups.

## Main definitions

* `TauCeti.Isogeny.pushClassMonoidHom`: the multiplicative form,
  `ClassGroup W₁.CoordinateRing →* ClassGroup W₂.CoordinateRing`.
* `TauCeti.Isogeny.pushClass`: the same map written additively, which is the form the point
  group consumes.

## Design

**The intermediate ring's algebra structures are built here, not accepted.**
`Isogeny.intermediateRing` is a `Subring W₁.FunctionField` carrying no `Algebra` instance over
either coordinate ring — `IntermediateRing/Basic.lean` records that an instance would reintroduce a
diamond — so the two structures have to come from somewhere. Taking them as arguments would leave
the exported map a *family indexed by the caller's choice*: nothing would force them to be
`toIntermediateRing` and `pullbackToIntermediateRing`. For `φ = Isogeny.id W`, precomposing either
with a nontrivial `F`-automorphism of `W.CoordinateRing` satisfies every hypothesis — injectivity,
finiteness and Dedekindness are all automorphism-stable — while yielding a different map, so
`(Isogeny.id W).pushClass` would not need to be the identity. The definitions below therefore build
both structures internally from the corestricted embeddings, which is what makes them *the* maps
induced by `φ`, and what a functoriality statement and `toPointHom` need.

**What `h` is for.** The one thing that cannot be built is the agreement between the ambient
`Algebra W₂.CoordinateRing W₁.FunctionField` and `φ.pullback`:

`h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x`

That structure is a `variable`, so it need not be the pullback's; `h` pins it, and it is what
`Isogeny.isScalarTower_intermediateRing` consumes to place `φ.intermediateRing` between
`W₂.CoordinateRing` and `W₁.FunctionField`. The `example` below witnesses that `h` is satisfiable
rather than vacuous: it holds by construction when the ambient structure is the pullback's own.

**Every other hypothesis is discharged internally**, from suppliers that live with the object they
describe, in the one-property-per-file `IntermediateRing/` series:

* `IsDedekindDomain φ.intermediateRing` — `Isogeny.isDedekindDomain_intermediateRing`. That lemma is
  where separability of the function-field extension is consumed, so the inseparable case is
  excluded there rather than silently here;
* `Module.Finite W₂.CoordinateRing φ.intermediateRing` — `Isogeny.moduleFinite_intermediateRing`;
* both `Module.IsTorsionFree` instances — Mathlib's `Module.isTorsionFree_iff_algebraMap_injective`
  applied to `Isogeny.toIntermediateRing_injective` and
  `Isogeny.pullbackToIntermediateRing_injective`. These are what make
  `ClassGroup.extendedRelNormHom` applicable at all: its variable block requires them.

  **There is deliberately no `Isogeny.isTorsionFree_intermediateRing` to cite.** Named lemmas of
  that shape were written alongside the embeddings and removed there as one-step wrappers of the
  `iff` above: a `theorem` carrying an explicit pointwise hypothesis can never be selected by
  instance search, so it saves a consumer nothing over the one-liner.

The instance arguments that remain are ambient facts about the curves and their function fields,
not about the intermediate ring, so they stay arguments.

`ClassGroup.extendedRelNormHom` orders its rings `A M R` — source, middle, target — so the
instantiation is `A := W₁.CoordinateRing`, `M := φ.intermediateRing`, `R := W₂.CoordinateRing`.

## Provenance

⚠ *mathlib-track*. Adapted from D. Angdinata's shared isogeny development, `Isogeny.lean`, by
David Kurniadi Angdinata, declarations `pushClassMonoidHom` and `pushClass`, which builds
`pushClass` by ideal extension and relative norm (`ClassGroup.extendedRelNormHom`) on the way to
`toPointHom`. No revision is cited because there is none to cite: that source is shared with its
authors ahead of their Mathlib PRs, so the shared files are the contract, and it should be pinned
to the PR numbers once those exist. For the same reason no licence is asserted here.

Two adaptations are forced by how this
repository states the surrounding API:

* the source writes `ClassGroup.extendedRelNormHom W₂.CoordinateRing W₁.CoordinateRing
  f.IntermediateRing`, ordering the rings target-source-middle; `TauCeti.ClassGroup`'s own
  `extendedRelNormHom` orders them source-middle-target, so the arguments are permuted here;
* the source obtains its algebra structures from a `letI := f.pullback.coordinateRingAlgebra`
  inside each proof; `intermediateRing` here carries no such instance by design, so the same is
  done from the corestricted embeddings, but inside the definition rather than inside a proof —
  which is what lets the exported map be canonical.

The source's `pushFractionalIdeal` and `pushClassMonoidHom_mk` are **not** ported. They are
stated through `ClassGroup.normIntegralUnitIdeal` and `ClassGroup.integralUnitIdealRep`, an
integral-representative API for fractional-ideal units that this repository does not have;
`ExtendedRelNorm.lean` instead characterises the composite by `extendedRelNormHom_apply` and, on
integral ideals, `extendedRelNormHom_mk0`.

**No transported characterisation is offered here, deliberately.** The algebra structures are built
inside the definitions below rather than accepted from the caller, which is what makes them *the*
isogeny's maps; but it also means a characterisation lemma cannot name those structures — a `letI`
in a statement builds different terms, and `ClassGroup.relNorm` and `ClassGroup.extendedRelNormHom`
are
unexposed, so nothing reconciles them. The first real consumer (`toPointHom`) should decide what
characterisation it needs and in what form, rather than this file guessing.
-/

public section

namespace TauCeti

namespace Isogeny

open scoped nonZeroDivisors

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

section PushClass

variable (φ : Isogeny W₁ W₂)
  [IsDomain W₁.CoordinateRing] [IsDedekindDomain W₂.CoordinateRing]
  [Algebra W₂.CoordinateRing W₁.FunctionField]
  [Algebra W₂.FunctionField W₁.FunctionField]
  [IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField]
  [Algebra.IsSeparable W₂.FunctionField W₁.FunctionField]

/-- **The class-group map induced by an isogeny**, multiplicatively: extend a class of
`W₁.CoordinateRing` into the intermediate ring, then norm it down to `W₂.CoordinateRing`.

The two coordinate rings carry no map between them; the intermediate ring is what connects
them, receiving `W₁.CoordinateRing` by inclusion and lying module-finite over
`W₂.CoordinateRing`. -/
noncomputable def pushClassMonoidHom
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x) :
    ClassGroup W₁.CoordinateRing →* ClassGroup W₂.CoordinateRing :=
  letI : Algebra W₁.CoordinateRing φ.intermediateRing := φ.toIntermediateRing.toAlgebra
  letI : Algebra W₂.CoordinateRing φ.intermediateRing := φ.pullbackToIntermediateRing.toAlgebra
  haveI : IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField :=
    φ.isScalarTower_intermediateRing rfl h
  haveI := φ.isDedekindDomain_intermediateRing h
  haveI := φ.moduleFinite_intermediateRing h
  haveI : Module.IsTorsionFree W₁.CoordinateRing φ.intermediateRing :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr φ.toIntermediateRing_injective
  haveI : Module.IsTorsionFree W₂.CoordinateRing φ.intermediateRing :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr φ.pullbackToIntermediateRing_injective
  ClassGroup.extendedRelNormHom W₁.CoordinateRing φ.intermediateRing W₂.CoordinateRing

/-- **The additive form of `Isogeny.pushClassMonoidHom`.** The point group is described additively
by its class group, so this is the shape the induced map on points is built from. -/
noncomputable def pushClass
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x) :
    Additive (ClassGroup W₁.CoordinateRing) →+ Additive (ClassGroup W₂.CoordinateRing) :=
  MonoidHom.toAdditive (φ.pushClassMonoidHom h)

end PushClass

section Instantiable

/- **The definitions' hypotheses are satisfiable** (documentation, not public API). The algebra
structures are no longer a caller's choice — `pushClassMonoidHom` builds them from `φ` — so what
remains to witness is that the pinning hypothesis `h` can be met at all. It is met by construction
whenever the ambient `W₂.CoordinateRing`-algebra structure on `W₁.FunctionField` is the pullback's
own. Without this the definitions could be unusable, satisfied by nothing.

Kept as an `example`, and behind a plain block comment rather than a docstring: it is a one-off
sanity check with no downstream consumer, and an unnamed declaration's doc comment reaches no
generated documentation. This follows the non-vacuity check in
`Analysis/Complex/Conformal/DiscInjection.lean`. -/
example (φ : Isogeny W₁ W₂) :
    letI : Algebra W₂.CoordinateRing W₁.FunctionField := φ.pullback.toRingHom.toAlgebra
    ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x :=
  fun x ↦ RingHom.congr_fun (RingHom.algebraMap_toAlgebra _) x

end Instantiable

end Isogeny

end TauCeti
