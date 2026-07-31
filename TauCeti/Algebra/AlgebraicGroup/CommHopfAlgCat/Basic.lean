/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.AlgebraicGroup.PointsFunctor

/-!
# Commutative Hopf algebras and their functor of points

This file packages the contravariant functor that sends a commutative coordinate Hopf algebra
`H` over a commutative ring `R` to its group-valued functor of points `A ↦ Hom_R(H, A)`.

The category of commutative Hopf algebras is Mathlib's bundled `CommHopfAlgCat`; this file
adds the functor-of-points stack on top of it.

This is the categorical form of the first concrete target in the Tau Ceti reductive-groups
roadmap, Layer 0, "R-points as a group": for a commutative Hopf algebra representing an
affine group scheme, the functor of points is group-valued by convolution, and a morphism of
coordinate Hopf algebras acts on points by pre-composition.

## Main declarations

* `CommHopfAlgCat.mapPointsFunctor`: a coordinate morphism `H ⟶ K` induces a natural
  transformation from the points functor of `K` to the points functor of `H`.
* `CommHopfAlgCat.pointsFunctor`: the contravariant functor
  `(CommHopfAlgCat R)ᵒᵖ ⥤ CommAlgCat R ⥤ GrpCat`.

## References

The bundled category `CommHopfAlgCat`, its forgetful functor to `CommBialgCat`, and the
equivalence `CommHopfAlgCat.commHopfAlgCatEquivCogrpCommAlgCat` with cogroup objects in
commutative algebras are Mathlib's `Mathlib.Algebra.Category.CommHopfAlgCat`. The points
functoriality uses Mathlib's convolution monoid and bialgebra morphism API, in particular
`AlgHom.convMul_comp_bialgHom_distrib` from
`Mathlib.RingTheory.Bialgebra.Convolution`, through the Tau Ceti wrapper
`AlgHom.mapDomain`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u v w

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- A morphism of coordinate commutative Hopf algebras induces a natural transformation
between their group-valued points functors, contravariantly in the coordinate algebra.

At a commutative `R`-algebra `A`, this sends an `A`-valued point `f : K →ₐ[R] A` to
`f ∘ φ : H →ₐ[R] A`. -/
@[expose] noncomputable def mapPointsFunctor {H K : CommHopfAlgCat.{v} R} (φ : H ⟶ K) :
    HopfAlgebra.pointsFunctor (R := R) (H := K) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := H) where
  app A := GrpCat.ofHom
    (AlgHom.mapDomain (H₁ := H) (H₂ := K) (A := A) φ.hom)
  naturality {A B} ψ := by
    simp only [HopfAlgebra.pointsFunctor_map, HopfAlgebra.mapPoints]
    exact GrpCat.hom_ext (AlgHom.mapValue_mapDomain φ.hom ψ.hom)

/-- On points, `mapPointsFunctor φ` is pre-composition with `φ`. -/
@[simp]
lemma mapPointsFunctor_app_apply {H K : CommHopfAlgCat.{v} R} (φ : H ⟶ K)
    (A : CommAlgCat.{w} R) (f : HopfAlgebra.points (R := R) (H := K) A) :
    (mapPointsFunctor φ).app A f =
      toConv (f.ofConv.comp (φ.hom : H →ₐ[R] K)) := by
  exact AlgHom.mapDomain_apply (A := A) φ.hom f

/-- Pointwise form of `mapPointsFunctor_app_apply`. -/
lemma mapPointsFunctor_app_apply_apply {H K : CommHopfAlgCat.{v} R} (φ : H ⟶ K)
    (A : CommAlgCat.{w} R) (f : HopfAlgebra.points (R := R) (H := K) A) (h : H) :
    (((mapPointsFunctor φ).app A f).ofConv) h = f.ofConv (φ.hom h) := by
  exact AlgHom.mapDomain_apply_apply (A := A) φ.hom f h

/-- Naturality of the point map induced by a coordinate morphism, applied to a point. -/
lemma mapPointsFunctor_naturality_apply {H K : CommHopfAlgCat.{v} R} (φ : H ⟶ K)
    {A B : CommAlgCat.{w} R} (χ : A ⟶ B)
    (f : HopfAlgebra.points (R := R) (H := K) A) :
    HopfAlgebra.mapPoints (H := H) χ ((mapPointsFunctor φ).app A f) =
      (mapPointsFunctor φ).app B (HopfAlgebra.mapPoints (H := K) χ f) := by
  exact DFunLike.congr_fun (AlgHom.mapValue_mapDomain φ.hom χ.hom).symm f

/-- Pre-composition with a surjective coordinate morphism is injective on points. -/
lemma mapPointsFunctor_app_injective_of_surjective {H K : CommHopfAlgCat.{v} R}
    (φ : H ⟶ K) (hφ : Function.Surjective φ.hom) (A : CommAlgCat.{w} R) :
    Function.Injective ((mapPointsFunctor φ).app A) := by
  intro f g hfg
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro k
  obtain ⟨h, rfl⟩ := hφ k
  exact congrArg (fun p : HopfAlgebra.points (R := R) (H := H) A => p.ofConv h) hfg

/-- `mapPointsFunctor` sends the identity coordinate morphism to the identity natural
transformation. -/
@[simp]
lemma mapPointsFunctor_id (H : CommHopfAlgCat.{v} R) :
    mapPointsFunctor (𝟙 H) =
      𝟙 (HopfAlgebra.pointsFunctor (R := R) (H := H) :
        CommAlgCat.{w} R ⥤ GrpCat.{max v w}) := by
  ext A f
  -- `mapPointsFunctor (𝟙 H)` precomposes each point with the identity coordinate morphism, so
  -- both sides are the same map on `A`-points by construction; after the bump no `simp` lemma
  -- spans the `GrpCat.Hom.hom` wrapper the `ext` leaves behind.
  rfl

/-- `mapPointsFunctor` sends coordinate-algebra composition to reverse composition of natural
transformations. -/
lemma mapPointsFunctor_comp {H K L : CommHopfAlgCat.{v} R} (φ : H ⟶ K) (ψ : K ⟶ L) :
    mapPointsFunctor (φ ≫ ψ) =
      mapPointsFunctor ψ ≫ mapPointsFunctor φ := by
  ext A f
  -- as in `mapPointsFunctor_id`: precomposition with `φ ≫ ψ` is precomposition with `ψ` then
  -- with `φ` by associativity of `AlgHom.comp`, which holds definitionally, and the residual
  -- `GrpCat.Hom.hom` wrapper has no rewrite lemma after the bump.
  rfl

/-- The contravariant functor assigning to a commutative Hopf algebra its group-valued
functor of points.

A coordinate Hopf algebra `H` is sent to the functor `A ↦ WithConv (H →ₐ[R] A)`. A morphism
`φ : H ⟶ K` is sent contravariantly to the natural transformation that pre-composes
`K`-points by `φ`. -/
@[expose] noncomputable def pointsFunctor :
    (CommHopfAlgCat.{v} R)ᵒᵖ ⥤ CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj H := HopfAlgebra.pointsFunctor (R := R) (H := H.unop)
  map φ := mapPointsFunctor φ.unop
  map_id H := mapPointsFunctor_id (R := R) H.unop
  map_comp φ ψ := mapPointsFunctor_comp (R := R) ψ.unop φ.unop

/-- The object part of `pointsFunctor` is the points functor of the underlying commutative
Hopf algebra. -/
lemma pointsFunctor_obj (H : (CommHopfAlgCat.{v} R)ᵒᵖ) :
    (pointsFunctor (R := R)).obj H =
      HopfAlgebra.pointsFunctor (R := R) (H := H.unop) :=
  rfl

/-- The morphism part of `pointsFunctor` is pre-composition in the coordinate commutative
Hopf algebra. -/
lemma pointsFunctor_map {H K : (CommHopfAlgCat.{v} R)ᵒᵖ} (φ : H ⟶ K) :
    (pointsFunctor (R := R)).map φ =
      mapPointsFunctor φ.unop :=
  rfl

/-- Pointwise form of the morphism part of `pointsFunctor`. -/
@[simp]
lemma pointsFunctor_map_app_apply_apply {H K : (CommHopfAlgCat.{v} R)ᵒᵖ}
    (φ : H ⟶ K) (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := H.unop) A) (h : K.unop) :
    ((((pointsFunctor (R := R)).map φ).app A f).ofConv) h =
      f.ofConv (φ.unop.hom h) := by
  rw [pointsFunctor_map]
  exact mapPointsFunctor_app_apply_apply (R := R) φ.unop A f h

end CommHopfAlgCat

-- Deprecated declarations.
--
-- The declarations below were part of Tau Ceti's hand-rolled `CommHopfAlgCat`, which was a
-- `CategoryTheory.ObjectProperty.FullSubcategory` of `HopfAlgCat R`. The category is now
-- Mathlib's bundled `CommHopfAlgCat`, so the Tau Ceti-local surface is kept here only as
-- deprecated wrappers forwarding to Mathlib's bundled category and its lemmas, so that
-- existing references continue to resolve.

/-- Deprecated: the Tau Ceti-local category alias forwards to Mathlib's bundled `CommHopfAlgCat`. -/
@[deprecated _root_.CommHopfAlgCat (since := "2026-06-19")]
abbrev CommHopfAlgCat.{u', v'} (R : Type u') [CommRing R] : Type _ := _root_.CommHopfAlgCat.{v'} R

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- Deprecated. The underlying ring of an object of `CommHopfAlgCat R` is commutative; this is
now provided directly by Mathlib's bundled `CommHopfAlgCat`. -/
@[deprecated "Provided by Mathlib's bundled CommHopfAlgCat" (since := "2026-06-19")]
abbrev commRing (H : CommHopfAlgCat.{u, v} R) : CommRing H := inferInstance

/-- Deprecated. The underlying type of an object of `CommHopfAlgCat R` is a Hopf algebra; this
is now provided directly by Mathlib's bundled `CommHopfAlgCat`. -/
@[deprecated "Provided by Mathlib's bundled CommHopfAlgCat" (since := "2026-06-19")]
abbrev hopfAlgebra (H : CommHopfAlgCat.{u, v} R) : _root_.HopfAlgebra R H := inferInstance

/-- Deprecated: use `φ.hom`. Turn a morphism in `CommHopfAlgCat` back into a bialgebra
morphism; this is Mathlib's `CommHopfAlgCat.Hom.hom`. -/
@[deprecated _root_.CommHopfAlgCat.Hom.hom (since := "2026-06-19")]
abbrev toBialgHom {H K : CommHopfAlgCat.{u, v} R} (φ : H ⟶ K) : H →ₐc[R] K :=
  φ.hom

variable (R) in
/-- Deprecated: use `CommHopfAlgCat.of`. Build a bundled commutative Hopf algebra from the
usual unbundled typeclasses. -/
@[deprecated _root_.CommHopfAlgCat.of (since := "2026-06-19")]
abbrev of (H : Type v) [CommRing H] [_root_.HopfAlgebra R H] : CommHopfAlgCat.{u, v} R :=
  _root_.CommHopfAlgCat.of R H

/-- Deprecated: use `CommHopfAlgCat.ofHom`. Typecheck a bialgebra morphism as a morphism in
`CommHopfAlgCat`. -/
@[deprecated _root_.CommHopfAlgCat.ofHom (since := "2026-06-19")]
abbrev ofHom {H K : Type v} [CommRing H] [CommRing K]
    [_root_.HopfAlgebra R H] [_root_.HopfAlgebra R K] (φ : H →ₐc[R] K) :
    of R H ⟶ of R K :=
  _root_.CommHopfAlgCat.ofHom φ

/-- Deprecated: `toBialgHom (𝟙 H) = BialgHom.id R H`; use `CommHopfAlgCat.hom_id`. -/
@[deprecated _root_.CommHopfAlgCat.hom_id (since := "2026-06-19")]
lemma toBialgHom_id {H : CommHopfAlgCat.{u, v} R} :
    toBialgHom (𝟙 H : H ⟶ H) = BialgHom.id R H := by
  ext x
  exact DFunLike.congr_fun (_root_.CommHopfAlgCat.hom_id (A := H)) x

/-- Deprecated: `toBialgHom (φ ≫ ψ) = (toBialgHom ψ).comp (toBialgHom φ)`; use
`CommHopfAlgCat.hom_comp`. -/
@[deprecated _root_.CommHopfAlgCat.hom_comp (since := "2026-06-19")]
lemma toBialgHom_comp {H K L : CommHopfAlgCat.{u, v} R} (φ : H ⟶ K) (ψ : K ⟶ L) :
    toBialgHom (φ ≫ ψ) = (toBialgHom ψ).comp (toBialgHom φ) :=
  _root_.CommHopfAlgCat.hom_comp φ ψ

/-- Deprecated: `ofHom (toBialgHom φ) = φ`; use `CommHopfAlgCat.ofHom_hom`. -/
@[deprecated _root_.CommHopfAlgCat.ofHom_hom (since := "2026-06-19")]
lemma ofHom_toBialgHom {H K : CommHopfAlgCat.{u, v} R} (φ : H ⟶ K) :
    _root_.CommHopfAlgCat.ofHom (toBialgHom φ) = φ :=
  _root_.CommHopfAlgCat.ofHom_hom φ

/-- Deprecated: `toBialgHom (ofHom φ) = φ`; use `CommHopfAlgCat.hom_ofHom`. -/
@[deprecated _root_.CommHopfAlgCat.hom_ofHom (since := "2026-06-19")]
lemma toBialgHom_ofHom {H K : Type v} [CommRing H] [CommRing K]
    [_root_.HopfAlgebra R H] [_root_.HopfAlgebra R K] (φ : H →ₐc[R] K) :
    toBialgHom (_root_.CommHopfAlgCat.ofHom (R := R) φ) = φ :=
  _root_.CommHopfAlgCat.hom_ofHom φ

/-- Deprecated: use `CommHopfAlgCat.hom_ext`. Two morphisms of commutative Hopf algebras are
equal when their underlying bialgebra morphisms are equal. -/
@[deprecated _root_.CommHopfAlgCat.hom_ext (since := "2026-06-19")]
lemma hom_ext {H K : CommHopfAlgCat.{u, v} R} {φ ψ : H ⟶ K}
    (h : φ.hom = ψ.hom) : φ = ψ :=
  _root_.CommHopfAlgCat.hom_ext h

/-- Deprecated: use `CommHopfAlgCat.hasForgetToCommBialgCat`. The forgetful functor from
commutative Hopf algebras to commutative bialgebras. -/
@[deprecated _root_.CommHopfAlgCat.hasForgetToCommBialgCat (since := "2026-06-19")]
abbrev hasForgetToCommBialgCat :
    HasForget₂ (CommHopfAlgCat.{u, v} R) (CommBialgCat.{v} R) :=
  _root_.CommHopfAlgCat.hasForgetToCommBialgCat

/-- Deprecated: use `CommHopfAlgCat.forget₂_commBialgCat_obj`. -/
@[deprecated _root_.CommHopfAlgCat.forget₂_commBialgCat_obj (since := "2026-06-19")]
lemma forget₂_commBialgCat_obj (H : CommHopfAlgCat.{u, v} R) :
    (forget₂ (CommHopfAlgCat.{u, v} R) (CommBialgCat.{v} R)).obj H = CommBialgCat.of R H :=
  _root_.CommHopfAlgCat.forget₂_commBialgCat_obj H

/-- Deprecated: use `CommHopfAlgCat.forget₂_commBialgCat_map`. -/
@[deprecated _root_.CommHopfAlgCat.forget₂_commBialgCat_map (since := "2026-06-19")]
lemma forget₂_commBialgCat_map {H K : CommHopfAlgCat.{u, v} R} (φ : H ⟶ K) :
    (forget₂ (CommHopfAlgCat.{u, v} R) (CommBialgCat.{v} R)).map φ = CommBialgCat.ofHom φ.hom :=
  _root_.CommHopfAlgCat.forget₂_commBialgCat_map φ

end CommHopfAlgCat

end TauCeti
