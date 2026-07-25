/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.Basic

/-!
# Isomorphisms of abelian varieties

This file supplies the scheme-level interface to isomorphisms in the category of abelian
varieties. An isomorphism `e : A ≅ B` forgets first to an isomorphism of schemes over `Spec K`,
then to an isomorphism of the underlying schemes.

As a first geometric consequence, isomorphic abelian varieties have the same dimension. This is
the interface needed to compare constructions characterized by the Jacobian's universal property
and to state its base-change compatibility as an isomorphism of abelian varieties.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer E, “Abelian variety = smooth,
proper, geometrically connected group scheme over `k`; basic API, dim,” and prepares the
isomorphisms in the end goal and Layer F. No external mathematics is vendored. The implementation
reuses Mathlib's `Functor.mapIso`, `Over.isoMk`, and invariance of topological Krull dimension
under homeomorphism.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianVariety

variable {K : Type u} [Field K]

noncomputable section

/-- The isomorphism of schemes over `Spec K` underlying an isomorphism of abelian varieties. -/
abbrev isoToOver {A B : AbelianVariety K} (e : A ≅ B) : A.toOver ≅ B.toOver :=
  Hom.toOverFunctor.mapIso e

/-- The isomorphism of schemes underlying an isomorphism of abelian varieties. -/
abbrev isoToScheme {A B : AbelianVariety K} (e : A ≅ B) : A.toScheme ≅ B.toScheme :=
  (Over.forget (Spec (.of K))).mapIso (isoToOver e)

/-- Isomorphic abelian varieties have equal topological Krull dimension. -/
lemma dim_eq_of_iso {A B : AbelianVariety K} (e : A ≅ B) :
    A.dim = B.dim :=
  (isoToScheme e).hom.homeomorph.isHomeomorph.topologicalKrullDim_eq

end

end AbelianVariety

end AlgebraicGeometry

end TauCeti
