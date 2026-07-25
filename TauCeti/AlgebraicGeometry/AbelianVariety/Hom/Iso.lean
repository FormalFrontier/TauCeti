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
then to an isomorphism of the underlying schemes. The resulting isomorphisms are characterized
by their forward and inverse morphisms and are functorial under identity, inverse, and
composition.

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

/-- The forward map of the underlying `Over` isomorphism is the underlying homomorphism of the
forward abelian-variety isomorphism. -/
@[simp]
lemma isoToOver_hom {A B : AbelianVariety K} (e : A ≅ B) :
    (isoToOver e).hom = Hom.toOverHom e.hom :=
  rfl

/-- The inverse map of the underlying `Over` isomorphism is the underlying homomorphism of the
inverse abelian-variety isomorphism. -/
@[simp]
lemma isoToOver_inv {A B : AbelianVariety K} (e : A ≅ B) :
    (isoToOver e).inv = Hom.toOverHom e.inv :=
  rfl

/-- The forward map of the underlying scheme isomorphism is the underlying scheme morphism of
the forward abelian-variety isomorphism. -/
@[simp]
lemma isoToScheme_hom {A B : AbelianVariety K} (e : A ≅ B) :
    (isoToScheme e).hom = Hom.toSchemeHom e.hom :=
  rfl

/-- The inverse map of the underlying scheme isomorphism is the underlying scheme morphism of
the inverse abelian-variety isomorphism. -/
@[simp]
lemma isoToScheme_inv {A B : AbelianVariety K} (e : A ≅ B) :
    (isoToScheme e).inv = Hom.toSchemeHom e.inv :=
  rfl

/-- The underlying `Over` isomorphism of the identity isomorphism is the identity. -/
lemma isoToOver_refl (A : AbelianVariety K) :
    isoToOver (Iso.refl A) = Iso.refl A.toOver :=
  (Hom.toOverFunctor.mapIso_refl A)

/-- Forgetting an inverse isomorphism to schemes over the base commutes with taking inverses. -/
@[simp]
lemma isoToOver_symm {A B : AbelianVariety K} (e : A ≅ B) :
    isoToOver e.symm = (isoToOver e).symm :=
  rfl

/-- Forgetting a composite isomorphism to schemes over the base commutes with composition. -/
lemma isoToOver_trans {A B C : AbelianVariety K} (e : A ≅ B) (f : B ≅ C) :
    isoToOver (e.trans f) = (isoToOver e).trans (isoToOver f) :=
  (Hom.toOverFunctor.mapIso_trans e f)

/-- The underlying scheme isomorphism of the identity isomorphism is the identity. -/
@[simp]
lemma isoToScheme_refl (A : AbelianVariety K) :
    isoToScheme (Iso.refl A) = Iso.refl A.toScheme := by
  apply Iso.ext
  exact Hom.toSchemeHom_id A

/-- Forgetting an inverse isomorphism to schemes commutes with taking inverses. -/
@[simp]
lemma isoToScheme_symm {A B : AbelianVariety K} (e : A ≅ B) :
    isoToScheme e.symm = (isoToScheme e).symm := by
  apply Iso.ext
  rfl

/-- Forgetting a composite isomorphism to schemes commutes with composition. -/
@[simp]
lemma isoToScheme_trans {A B C : AbelianVariety K} (e : A ≅ B) (f : B ≅ C) :
    isoToScheme (e.trans f) = (isoToScheme e).trans (isoToScheme f) := by
  apply Iso.ext
  exact Hom.toSchemeHom_comp e.hom f.hom

/-- Isomorphic abelian varieties have equal topological Krull dimension. -/
lemma dim_eq_of_iso {A B : AbelianVariety K} (e : A ≅ B) :
    A.dim = B.dim :=
  (isoToScheme e).hom.homeomorph.isHomeomorph.topologicalKrullDim_eq

end

end AbelianVariety

end AlgebraicGeometry

end TauCeti
