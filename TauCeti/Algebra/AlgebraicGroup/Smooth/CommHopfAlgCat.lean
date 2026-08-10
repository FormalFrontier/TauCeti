/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Basic

/-!
# Smooth commutative Hopf algebras

This file packages smooth commutative Hopf algebras over a commutative ring `R`. These are the
coordinate Hopf algebras for smooth affine group schemes in the reductive-groups roadmap: the
Hopf algebra structure carries the group law, while `Algebra.Smooth R H` records smoothness of
the coordinate ring separately.

## Main declarations

* `TauCeti.smoothCommHopfAlgProperty`: the object property on `CommHopfAlgCat R` selecting
  objects whose underlying `R`-algebra is smooth.
* `TauCeti.SmoothCommHopfAlgCat`: the full subcategory of smooth commutative Hopf algebras.
* `TauCeti.SmoothCommHopfAlgCat.of`: construct a bundled smooth commutative Hopf algebra from
  unbundled typeclasses.

## References

This is the smooth coordinate-Hopf-algebra wrapper requested by
`ReductiveGroups/README.md` in TauCetiRoadmap, in the standing hypotheses and Layer 0
three-way dictionary. Smoothness remains a separate object property rather than being built
into the category, as required by the roadmap.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

/-- The object property on commutative Hopf algebras selecting coordinate algebras smooth over
the base ring. -/
def smoothCommHopfAlgProperty (R : Type u) [CommRing R] :
    ObjectProperty (CommHopfAlgCat.{v} R) :=
  fun H => Algebra.Smooth R H

/-- Membership in the smooth commutative-Hopf-algebra object property. -/
@[simp]
lemma smoothCommHopfAlgProperty_iff {R : Type u} [CommRing R]
    (H : CommHopfAlgCat.{v} R) :
    smoothCommHopfAlgProperty R H ↔ Algebra.Smooth R H :=
  Iff.rfl

/-- The category of commutative Hopf algebras smooth over a commutative ring `R`.

Smoothness is kept as an object property rather than included in the Hopf algebra typeclass. -/
abbrev SmoothCommHopfAlgCat (R : Type u) [CommRing R] :=
  (smoothCommHopfAlgProperty R).FullSubcategory

namespace SmoothCommHopfAlgCat

variable {R : Type u} [CommRing R]

instance : CoeSort (SmoothCommHopfAlgCat.{u, v} R) (Type v) :=
  ⟨fun H => H.obj⟩

instance commRing (H : SmoothCommHopfAlgCat.{u, v} R) : CommRing H :=
  inferInstanceAs (CommRing H.obj)

instance hopfAlgebra (H : SmoothCommHopfAlgCat.{u, v} R) : HopfAlgebra R H :=
  inferInstanceAs (HopfAlgebra R H.obj)

instance smooth (H : SmoothCommHopfAlgCat.{u, v} R) : Algebra.Smooth R H :=
  (smoothCommHopfAlgProperty_iff H.obj).mp H.property

variable (R) in
/-- Construct a bundled smooth commutative Hopf algebra from the usual unbundled typeclasses. -/
abbrev of (H : Type v) [CommRing H] [HopfAlgebra R H] [Algebra.Smooth R H] :
    SmoothCommHopfAlgCat.{u, v} R :=
  ⟨CommHopfAlgCat.of R H,
    (smoothCommHopfAlgProperty_iff _).mpr (inferInstanceAs (Algebra.Smooth R H))⟩

/-- Turn a morphism in `SmoothCommHopfAlgCat` back into a bialgebra morphism. -/
abbrev toBialgHom {H K : SmoothCommHopfAlgCat.{u, v} R} (φ : H ⟶ K) :
    H →ₐc[R] K :=
  φ.hom.hom

/-- Typecheck a bialgebra morphism between smooth commutative Hopf algebras as a morphism in
`SmoothCommHopfAlgCat`. -/
abbrev ofHom {H K : Type v} [CommRing H] [CommRing K]
    [HopfAlgebra R H] [HopfAlgebra R K]
    [Algebra.Smooth R H] [Algebra.Smooth R K] (φ : H →ₐc[R] K) :
    of R H ⟶ of R K :=
  ObjectProperty.homMk (CommHopfAlgCat.ofHom φ)

/-- Two morphisms of smooth commutative Hopf algebras are equal when their underlying bialgebra
morphisms are equal. -/
@[ext]
lemma hom_ext {H K : SmoothCommHopfAlgCat.{u, v} R} {φ ψ : H ⟶ K}
    (h : toBialgHom φ = toBialgHom ψ) : φ = ψ :=
  ObjectProperty.hom_ext (P := smoothCommHopfAlgProperty R)
    (CommHopfAlgCat.hom_ext h)

@[simp]
lemma toBialgHom_id {H : SmoothCommHopfAlgCat.{u, v} R} :
    toBialgHom (𝟙 H : H ⟶ H) = BialgHom.id R H :=
  rfl

@[simp]
lemma toBialgHom_comp {H K L : SmoothCommHopfAlgCat.{u, v} R}
    (φ : H ⟶ K) (ψ : K ⟶ L) :
    toBialgHom (φ ≫ ψ) = (toBialgHom ψ).comp (toBialgHom φ) :=
  rfl

@[simp]
lemma ofHom_toBialgHom {H K : SmoothCommHopfAlgCat.{u, v} R} (φ : H ⟶ K) :
    ofHom (toBialgHom φ) = φ :=
  rfl

@[simp]
lemma toBialgHom_ofHom {H K : Type v} [CommRing H] [CommRing K]
    [HopfAlgebra R H] [HopfAlgebra R K]
    [Algebra.Smooth R H] [Algebra.Smooth R K] (φ : H →ₐc[R] K) :
    toBialgHom (ofHom (R := R) φ) = φ :=
  rfl

end SmoothCommHopfAlgCat

end TauCeti
