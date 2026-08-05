/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Basic

/-!
# Finite-type commutative Hopf algebras

This file packages finite-type commutative Hopf algebras over a commutative ring `R`.
These are the coordinate Hopf algebras for affine group schemes of finite type in the
reductive-groups roadmap: the Hopf algebra structure carries the group law, while
`Algebra.FiniteType R H` records the finite-type coordinate-ring hypothesis separately.

## Main declarations

* `TauCeti.finiteTypeCommHopfAlgProperty`: the object property on `CommHopfAlgCat R`
  selecting objects whose underlying `R`-algebra is of finite type.
* `TauCeti.FiniteTypeCommHopfAlgCat`: the full subcategory of finite-type commutative
  Hopf algebras.
* `TauCeti.FiniteTypeCommHopfAlgCat.of`: construct a bundled finite-type commutative
  Hopf algebra from unbundled typeclasses.
* `forget₂ (FiniteTypeCommHopfAlgCat R) (FGAlgCat R)`: the forgetful functor to Mathlib's
  finitely generated commutative `R`-algebras.
* `TauCeti.FiniteTypeCommHopfAlgCat.pointsFunctor`: the inherited contravariant functor
  of points.

## References

This is the finite-type coordinate-Hopf-algebra wrapper requested by
`ReductiveGroups/README.md` in TauCetiRoadmap, in the standing hypotheses and Layer 0
three-way dictionary: an affine group scheme of finite type over `k` is modeled by a
commutative Hopf `k`-algebra finitely generated as a `k`-algebra. The finite-type algebra
infrastructure is Mathlib's `FGAlgCat` and `Algebra.FiniteType`; the Hopf algebra category
is Mathlib's bundled `CommHopfAlgCat`, on top of which Tau Ceti adds the points functor.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v w

/-- The object property on commutative Hopf algebras selecting finite-type coordinate
algebras. -/
@[expose] def finiteTypeCommHopfAlgProperty (R : Type u) [CommRing R] :
    ObjectProperty (_root_.CommHopfAlgCat.{v} R) :=
  fun H => Algebra.FiniteType R H

/-- Membership in the finite-type commutative Hopf algebra object property. -/
@[simp]
lemma finiteTypeCommHopfAlgProperty_iff {R : Type u} [CommRing R]
    (H : _root_.CommHopfAlgCat.{v} R) :
    finiteTypeCommHopfAlgProperty R H ↔ Algebra.FiniteType R H :=
  Iff.rfl

/-- The category of finite-type commutative Hopf algebras over a commutative ring `R`.

This is the full subcategory of `CommHopfAlgCat R` on objects whose underlying commutative
`R`-algebra is finitely generated. The finite-type hypothesis is deliberately a separate
object property, not part of the Hopf algebra typeclass. -/
abbrev FiniteTypeCommHopfAlgCat (R : Type u) [CommRing R] :=
  (finiteTypeCommHopfAlgProperty (R := R)).FullSubcategory

namespace FiniteTypeCommHopfAlgCat

variable {R : Type u} [CommRing R]

instance : CoeSort (FiniteTypeCommHopfAlgCat.{u, v} R) (Type v) :=
  ⟨fun H => H.obj⟩

instance commRing (H : FiniteTypeCommHopfAlgCat.{u, v} R) : CommRing H :=
  inferInstanceAs (CommRing H.obj)

instance hopfAlgebra (H : FiniteTypeCommHopfAlgCat.{u, v} R) :
    _root_.HopfAlgebra R H :=
  inferInstanceAs (_root_.HopfAlgebra R H.obj)

instance finiteType (H : FiniteTypeCommHopfAlgCat.{u, v} R) : Algebra.FiniteType R H :=
  H.property

variable (R) in
/-- Construct a bundled finite-type commutative Hopf algebra from the usual unbundled
typeclasses. -/
abbrev of (H : Type v) [CommRing H] [_root_.HopfAlgebra R H]
    [Algebra.FiniteType R H] : FiniteTypeCommHopfAlgCat.{u, v} R :=
  ⟨_root_.CommHopfAlgCat.of R H,
    inferInstanceAs (Algebra.FiniteType R (_root_.CommHopfAlgCat.of R H))⟩

/-- Turn a morphism in `FiniteTypeCommHopfAlgCat` back into a bialgebra morphism. -/
abbrev toBialgHom {H K : FiniteTypeCommHopfAlgCat.{u, v} R} (φ : H ⟶ K) :
    H →ₐc[R] K :=
  φ.hom.hom

/-- Typecheck a bialgebra morphism between finite-type commutative Hopf algebras as a
morphism in `FiniteTypeCommHopfAlgCat`. -/
abbrev ofHom {H K : Type v} [CommRing H] [CommRing K]
    [_root_.HopfAlgebra R H] [_root_.HopfAlgebra R K]
    [Algebra.FiniteType R H] [Algebra.FiniteType R K] (φ : H →ₐc[R] K) :
    of R H ⟶ of R K :=
  ObjectProperty.homMk (_root_.CommHopfAlgCat.ofHom φ)

/-- Two morphisms of finite-type commutative Hopf algebras are equal when their underlying
bialgebra morphisms are equal. -/
@[ext]
lemma hom_ext {H K : FiniteTypeCommHopfAlgCat.{u, v} R} {φ ψ : H ⟶ K}
    (h : toBialgHom φ = toBialgHom ψ) : φ = ψ :=
  ObjectProperty.hom_ext (P := finiteTypeCommHopfAlgProperty R)
    (_root_.CommHopfAlgCat.hom_ext h)

@[simp]
lemma toBialgHom_id {H : FiniteTypeCommHopfAlgCat.{u, v} R} :
    toBialgHom (𝟙 H : H ⟶ H) = BialgHom.id R H :=
  rfl

@[simp]
lemma toBialgHom_comp {H K L : FiniteTypeCommHopfAlgCat.{u, v} R}
    (φ : H ⟶ K) (ψ : K ⟶ L) :
    toBialgHom (φ ≫ ψ) = (toBialgHom ψ).comp (toBialgHom φ) :=
  rfl

@[simp]
lemma ofHom_toBialgHom {H K : FiniteTypeCommHopfAlgCat.{u, v} R} (φ : H ⟶ K) :
    ofHom (toBialgHom φ) = φ :=
  rfl

@[simp]
lemma toBialgHom_ofHom {H K : Type v} [CommRing H] [CommRing K]
    [_root_.HopfAlgebra R H] [_root_.HopfAlgebra R K]
    [Algebra.FiniteType R H] [Algebra.FiniteType R K] (φ : H →ₐc[R] K) :
    toBialgHom (ofHom (R := R) φ) = φ :=
  rfl

@[simp]
lemma forget₂_commHopfAlgCat_obj (H : FiniteTypeCommHopfAlgCat.{u, v} R) :
    (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R) (_root_.CommHopfAlgCat.{v} R)).obj H =
      H.obj :=
  rfl

@[simp]
lemma forget₂_commHopfAlgCat_map {H K : FiniteTypeCommHopfAlgCat.{u, v} R}
    (φ : H ⟶ K) :
    (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R) (_root_.CommHopfAlgCat.{v} R)).map φ =
      φ.hom :=
  rfl

/-- The forgetful functor from finite-type commutative Hopf algebras to finitely generated
commutative algebras. -/
instance hasForgetToFGAlgCat :
    HasForget₂ (FiniteTypeCommHopfAlgCat.{u, v} R) (FGAlgCat.{v, u} R) where
  forget₂ :=
    { obj H := ⟨CommAlgCat.of R H, inferInstanceAs (Algebra.FiniteType R H)⟩
      map φ := ObjectProperty.homMk (CommAlgCat.ofHom (toBialgHom φ).toAlgHom) }

@[simp]
lemma forget₂_fgAlgCat_obj (H : FiniteTypeCommHopfAlgCat.{u, v} R) :
    (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R) (FGAlgCat.{v, u} R)).obj H =
      ⟨CommAlgCat.of R H, inferInstanceAs (Algebra.FiniteType R H)⟩ :=
  rfl

@[simp]
lemma forget₂_fgAlgCat_map {H K : FiniteTypeCommHopfAlgCat.{u, v} R} (φ : H ⟶ K) :
    (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R) (FGAlgCat.{v, u} R)).map φ =
      ObjectProperty.homMk (CommAlgCat.ofHom (toBialgHom φ).toAlgHom) :=
  rfl

/-- The contravariant group-valued functor of points of a finite-type commutative Hopf
algebra. -/
@[expose] noncomputable def pointsFunctor :
    (FiniteTypeCommHopfAlgCat.{u, v} R)ᵒᵖ ⥤ CommAlgCat.{w} R ⥤ GrpCat.{max v w} :=
  CategoryTheory.Functor.op
      (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R) (_root_.CommHopfAlgCat.{v} R)) ⋙
    CommHopfAlgCat.pointsFunctor (R := R)

/-- The object part of `pointsFunctor` is the points functor of the underlying commutative
Hopf algebra. -/
lemma pointsFunctor_obj (H : (FiniteTypeCommHopfAlgCat.{u, v} R)ᵒᵖ) :
    (pointsFunctor (R := R)).obj H =
      HopfAlgebra.pointsFunctor (R := R) (H := H.unop) :=
  rfl

/-- The morphism part of `pointsFunctor` is pre-composition in the coordinate commutative
Hopf algebra. -/
lemma pointsFunctor_map {H K : (FiniteTypeCommHopfAlgCat.{u, v} R)ᵒᵖ} (φ : H ⟶ K) :
    (pointsFunctor (R := R)).map φ = CommHopfAlgCat.mapPointsFunctor φ.unop.hom :=
  rfl

/-- Pointwise form of the morphism part of `pointsFunctor`: the image of a point `f` under `φ`
sends `h` to the value of `f` at the image of `h` under `φ`. -/
-- The point is ascribed to its algebra-map type by `show … from`, so that the application to `h`
-- elaborates through the `WithConv` synonym that `HopfAlgebra.points` carries.
@[simp]
lemma pointsFunctor_map_app_apply_apply {H K : (FiniteTypeCommHopfAlgCat.{u, v} R)ᵒᵖ}
    (φ : H ⟶ K) (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := H.unop) A) (h : K.unop) :
    (show K.unop.obj →ₐ[R] A from
      (((pointsFunctor (R := R)).map φ).app A f).ofConv) h =
      f.ofConv (toBialgHom φ.unop (h : K.unop.obj)) := by
  rw [pointsFunctor_map]
  exact CommHopfAlgCat.mapPointsFunctor_app_apply_apply (R := R) φ.unop.hom A f h

end FiniteTypeCommHopfAlgCat

end TauCeti
