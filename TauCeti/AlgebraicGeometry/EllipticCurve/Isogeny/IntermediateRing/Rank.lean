/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Basic
public import Mathlib.RingTheory.RamificationInertia.Basic
-- Proof-only: the fraction field of the intermediate ring.
import Mathlib.RingTheory.Localization.Integral

/-!
# The intermediate ring of an isogeny has rank the degree, and its fibres count it

The intermediate ring of an isogeny `φ : W₁ → W₂` — the integral closure of `W₂.CoordinateRing`
inside `W₁.FunctionField` — is a `W₂.CoordinateRing`-module of rank exactly `φ.degree`. This is the
arithmetic content of the roadmap's *place-free* count: the degree, defined as a dimension of
function fields, is also a rank over the coordinate ring, so for a maximal prime it can be read off
the fibre of an affine place instead of off a field extension.

The bridge is a localization comparison. `W₂.FunctionField` is the fraction field of
`W₂.CoordinateRing` by definition, and `W₁.FunctionField` is the fraction field of the intermediate
ring — the intermediate ring is an integral closure inside a finite extension of the fraction field
below, and such a closure always has the ambient field as its fraction field. `Module.finrank` is
insensitive to passing to fraction rings on both sides (`IsFractionRing.finrank_eq`), so the rank
downstairs equals the degree upstairs.

Once the extension is finite and flat the rank turns into a fibre count. Over a Dedekind coordinate
ring its torsion-freeness supplies flatness, so Mathlib's fundamental identity
`Ideal.sum_ramification_inertia_eq_finrank` applies verbatim: for a prime `p` of
`W₂.CoordinateRing`, the primes of the intermediate ring lying over `p`, weighted by ramification
index times inertia degree, total `φ.degree`. When `p` is maximal (equivalently, nonzero in the
Dedekind case), this is the fibre over the affine point named by `p`; dropping the weights bounds
the number of its primes by the degree.

## Main results

* `TauCeti.Isogeny.isFractionRing_intermediateRing`: `W₁.FunctionField` is the fraction field of
  the intermediate ring.
* `TauCeti.Isogeny.finrank_intermediateRing_eq_degree`: the intermediate ring has rank `φ.degree`
  over `W₂.CoordinateRing`.
* `TauCeti.Isogeny.projective_intermediateRing`: it is projective, hence locally free, over
  `W₂.CoordinateRing` once it is module-finite.
* `TauCeti.Isogeny.sum_ramificationIdx_mul_inertiaDeg_eq_degree`: the **fundamental identity** for
  an isogeny — `∑_{q ∣ p} e_q · f_q = deg φ` over every prime `p` of `W₂.CoordinateRing`.
* `TauCeti.Isogeny.ncard_primesOver_le_degree`: hence there are at most `deg φ` primes above `p`.

## Design

**The rank statement needs no separability, no Dedekind hypothesis and no ellipticity.**
`IsFractionRing.finrank_eq` identifies the two ranks with no finiteness input at all, so nothing
about the module structure of the intermediate ring has to be known in advance. What the proof
does spend is the finiteness of the *function-field* extension, which every isogeny has
(`Isogeny.finiteDimensional_functionField`) — purely inseparable ones, Frobenius among them,
included. So `finrank_intermediateRing_eq_degree` is
available exactly where `Isogeny.degree` is, and in particular it is not blocked by the
separability limitation that `IntermediateRing/Finite.lean` and `IntermediateRing/Dedekind.lean`
record for their own conclusions.

**Why not `IsIntegralClosure.rank`.** Mathlib states the same comparison for an integral closure,
but only over a *principal ideal* base (`Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`),
a hypothesis unavailable from the current assumptions. The roadmap's intended identification of
the coordinate ring's class group with the point group is context for this limitation, not an
obstruction established here. `IsFractionRing.finrank_eq` compares the ranks with no hypothesis on
the base at all, so it is the route taken here.

**Module-finiteness is an instance argument of the fibre count, not a derived fact.** The two
statements below that do need it take `[Module.Finite W₂.CoordinateRing φ.intermediateRing]`
rather than `[Algebra.IsSeparable W₂.FunctionField W₁.FunctionField]` and a call to
`Isogeny.moduleFinite_intermediateRing`. Separability is not what the fundamental identity is
about; it is what the only currently available route to finiteness happens to need, and
`IntermediateRing/Finite.lean` says so in its own header. Taking the finiteness directly means
these statements apply unchanged the day a trace-free route lands, and a caller in the separable
case supplies it in one line from the sibling.

**Flatness follows automatically in the Dedekind application.** The fundamental identity is
stated under its natural finite-flat hypotheses. Over a Dedekind domain a torsion-free module is
flat, and torsion-freeness of the intermediate ring is injectivity of `algebraMap W₂.CoordinateRing
φ.intermediateRing`, which follows from the hypotheses already present: the composite into
`W₁.FunctionField` is the pullback, and the pullback of an isogeny is injective. So
`projective_intermediateRing` supplies the flatness needed in the roadmap's Dedekind setting. The
argument is made once there rather than repeated: `IntermediateRing/Basic.lean` records that a
standalone torsion-freeness lemma about this ring was removed in review as a one-step wrapper, and
nothing here reinstates one.

**Why `isFractionRing_intermediateRing` is an instance while its neighbours are theorems.** Its
statement mentions only the canonical structures: the intermediate ring, its coercion into
`W₁.FunctionField`, and the subring's own algebra structure. There is no
`W₂.CoordinateRing`-algebra structure to choose, hence no diamond of the kind
`IntermediateRing/Basic.lean` avoids by keeping the pullback-induced structures local, and the
discrimination key `Isogeny.intermediateRing` confines instance search to the object it is about.
The sibling statements do name a chosen structure and therefore stay theorems with an explicit
hypothesis pinning it, as `Isogeny.moduleFinite_intermediateRing` does.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 1**, the "points come along" milestone, whose
place-free alternate route reads: "the intermediate ring is locally free of rank `deg φ` over the
Dedekind coordinate ring, so every fibre over an affine point has `deg φ` points with
multiplicity, and translation moves the kernel fibre onto one". This file is that rank and that
fibre count. It is also the form in which **Layer 0**'s fundamental identity
`Σ_{w ∣ v} e_w · f_w = [F₁ : F₂]` reaches the affine places of `W₂`, the maximal ideals of its
coordinate ring.

## Provenance

The fraction-field statement is the content of `instFractionRingB` in the AINTLIB project
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `dev/hasse-weil @ 513e83879e2f`, by Chris Birkbeck),
proved in `HasseWeil/Curves/RamificationFinite.lean` alongside the finiteness that
`IntermediateRing/Finite.lean` ports; `IntermediateRing/Basic.lean` records it as unported, which
this file changes. The proof route — `IsIntegralClosure.isFractionRing_of_finite_extension` — is
the source's. The source states it for a fixed extension with the algebra structures supplied as
instance arguments; here the structures are the pullback-induced ones, installed inside the proof,
so the statement is hypothesis-free. The rank identity and the fibre count are not in that source.

⚠ *mathlib-track*, with the sibling `Isogeny` files: `TauCetiRoadmap/EllipticCurves/README.md`
pins D. Angdinata's shared isogeny development as carrying the intermediate ring and its
structural theory.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, III.1.11.
-/

public section

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **The source function field is the fraction field of the intermediate ring.** The intermediate
ring is the integral closure of `W₂.CoordinateRing` in `W₁.FunctionField`, and `W₁.FunctionField`
is a finite extension of `W₂.FunctionField` through the pullback, so the closure has the whole
ambient field as its fraction field.

No separability and no Dedekind hypothesis: the only input is finiteness of the function-field
extension, which every isogeny has. -/
instance isFractionRing_intermediateRing (φ : Isogeny W₁ W₂) :
    IsFractionRing φ.intermediateRing W₁.FunctionField := by
  -- the pullback-induced structures are local, as `IntermediateRing/Basic.lean` prescribes
  let _ := φ.pullback.toRingHom.toAlgebra
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  let _ := φ.pullbackToIntermediateRing.toAlgebra
  have h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x :=
    φ.pullback.algebraMap_toAlgebra_apply
  have : IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      rw [h, φ.fieldPullback.algebraMap_toAlgebra_apply, fieldPullback_algebraMap]
  have : IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField :=
    φ.isScalarTower_intermediateRing rfl h
  have := φ.isIntegralClosure_intermediateRing h
  have := φ.finiteDimensional_functionField (φ.algebraMap_functionField_eq_fieldPullback h)
  exact IsIntegralClosure.isFractionRing_of_finite_extension W₂.CoordinateRing W₂.FunctionField
    W₁.FunctionField φ.intermediateRing

/-- **The intermediate ring has rank the degree of the isogeny.** Both sides of
`W₂.CoordinateRing ⊆ φ.intermediateRing` become the corresponding function fields after passing to
fraction fields, and `Module.finrank` is unchanged by that passage, so the rank over the coordinate
ring is the degree of the extension of function fields — which is `Isogeny.degree`.

Stated for an arbitrary algebra structure whose coordinate-level structure map is the pullback,
matching `Isogeny.degree_eq_finrank` and `Isogeny.moduleFinite_intermediateRing`: registering such
a structure globally would be a diamond, since different isogenies induce different ones.

Nothing here is spent on separability or on the coordinate rings being Dedekind. -/
@[simp]
theorem finrank_intermediateRing_eq_degree (φ : Isogeny W₁ W₂)
    [Algebra W₂.CoordinateRing W₁.FunctionField]
    [Algebra W₂.FunctionField W₁.FunctionField]
    [IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField]
    [Algebra W₂.CoordinateRing φ.intermediateRing]
    [IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField]
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x) :
    Module.finrank W₂.CoordinateRing φ.intermediateRing = φ.degree := by
  rw [φ.degree_eq_finrank (φ.algebraMap_functionField_eq_fieldPullback h)]
  exact (IsFractionRing.finrank_eq W₂.CoordinateRing W₂.FunctionField φ.intermediateRing
    W₁.FunctionField).symm

/-- **The intermediate ring is projective over the target coordinate ring**, hence locally free of
rank `φ.degree` by `finrank_intermediateRing_eq_degree`. This is the form in which the roadmap's
place-free fibre count is stated.

The structure map is injective, because it factors the pullback of the isogeny and that is
injective, so the intermediate ring is torsion-free and hence flat over the Dedekind coordinate
ring; a finite module over a Noetherian ring is finitely presented, and a finitely presented flat
module is projective. -/
theorem projective_intermediateRing (φ : Isogeny W₁ W₂)
    [IsDedekindDomain W₂.CoordinateRing]
    [Algebra W₂.CoordinateRing W₁.FunctionField]
    [Algebra W₂.CoordinateRing φ.intermediateRing]
    [IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField]
    [Module.Finite W₂.CoordinateRing φ.intermediateRing]
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x) :
    Module.Projective W₂.CoordinateRing φ.intermediateRing := by
  have : Module.IsTorsionFree W₂.CoordinateRing φ.intermediateRing :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr <| Function.Injective.of_comp
      (f := algebraMap φ.intermediateRing W₁.FunctionField) fun a b hab ↦ φ.pullback_injective <| by
        rw [← h a, ← h b]
        simpa only [Function.comp_apply, IsScalarTower.algebraMap_apply W₂.CoordinateRing
          φ.intermediateRing W₁.FunctionField] using hab
  have : Module.FinitePresentation W₂.CoordinateRing φ.intermediateRing :=
    Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

/-- **The fundamental identity for an isogeny** (Stichtenoth III.1.11): over a prime `p` of
`W₂.CoordinateRing`, the primes of the intermediate ring lying over `p`, each weighted by its
ramification index times its inertia degree, total `φ.degree`.

When `p` is maximal (equivalently, nonzero when the coordinate ring is Dedekind), this is the fibre
of `φ` over the affine place of `W₂` named by `p`, counted with multiplicity: the intermediate ring
is the ring of functions regular away from `φ⁻¹(O₂)`, so its primes over `p` are the points of
`W₁` above that point of `W₂`.

Module-finiteness is taken directly rather than through separability of the function-field
extension; the module docstring says why. In the separable case
`Isogeny.moduleFinite_intermediateRing` supplies it. The `Fintype` binder is what the sum ranges
over, so it belongs to the statement rather than to the proof: finiteness of the module gives
only `Finite` (`Algebra.QuasiFinite.finite_primesOver`), which no `∑ q : _` elaborates against.
Mathlib's `Ideal.sum_ramification_inertia_eq_finrank` takes the binder the same way, under the
same `Module.Finite`. -/
theorem sum_ramificationIdx_mul_inertiaDeg_eq_degree (φ : Isogeny W₁ W₂)
    [Algebra W₂.CoordinateRing W₁.FunctionField]
    [Algebra W₂.FunctionField W₁.FunctionField]
    [IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField]
    [Algebra W₂.CoordinateRing φ.intermediateRing]
    [IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField]
    [Module.Finite W₂.CoordinateRing φ.intermediateRing]
    [Module.Flat W₂.CoordinateRing φ.intermediateRing]
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x)
    (p : Ideal W₂.CoordinateRing) [p.IsPrime]
    [Fintype (p.primesOver φ.intermediateRing)] :
    ∑ q : p.primesOver φ.intermediateRing,
        q.1.ramificationIdx W₂.CoordinateRing * q.1.inertiaDeg W₂.CoordinateRing = φ.degree := by
  rw [Ideal.sum_ramification_inertia_eq_finrank, φ.finrank_intermediateRing_eq_degree h]

/-- **There are at most `deg φ` primes above `p`.** Dropping the weights from the fundamental
identity: every ramification index and every inertia degree is at least one, so the primes over
`p` number at most the degree. The count is `Set.ncard`, the spelling Mathlib's own cardinality
API for this set uses (`Ideal.ncard_primesOver_lt_of_not_le`). When `p` is maximal, these are the
primes in the fibre over the affine place that `p` names.

Equality holds exactly when every ramification index and every inertia degree over `p` is one.
Turning the weighted identity above into an honest count of geometric points is therefore Layer 1's
separable-⟹-unramified milestone (`e_q = 1`) together with a separably closed base (`f_q = 1`);
neither is assumed here. -/
theorem ncard_primesOver_le_degree (φ : Isogeny W₁ W₂)
    [Algebra W₂.CoordinateRing W₁.FunctionField]
    [Algebra W₂.FunctionField W₁.FunctionField]
    [IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField]
    [Algebra W₂.CoordinateRing φ.intermediateRing]
    [IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField]
    [Module.Finite W₂.CoordinateRing φ.intermediateRing]
    [Module.Flat W₂.CoordinateRing φ.intermediateRing]
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x)
    (p : Ideal W₂.CoordinateRing) [p.IsPrime] :
    (p.primesOver φ.intermediateRing).ncard ≤ φ.degree := by
  have : Fintype (p.primesOver φ.intermediateRing) :=
    (Algebra.QuasiFinite.finite_primesOver p).fintype
  rw [← φ.sum_ramificationIdx_mul_inertiaDeg_eq_degree h p, ← Nat.card_coe_set_eq,
    Nat.card_eq_fintype_card, ← Finset.card_univ, Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  have : q.1.IsPrime := q.2.1
  exact Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (q.1.ramificationIdx_pos W₂.CoordinateRing).ne'
      (q.1.inertiaDeg_pos W₂.CoordinateRing).ne')

end Isogeny

end TauCeti
