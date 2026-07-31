/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Basic

/-!
# Corepresentability of the functor of points

The underlying type-valued functor of points of a commutative Hopf algebra `H` is
corepresented by `H` as a commutative algebra. Concretely, a morphism
`CommAlgCat.of R H ⟶ A` is the same data as an `A`-valued point
`WithConv (H →ₐ[R] A)`.

This file packages that tautological equivalence as a `Functor.CorepresentableBy`, exposes
the resulting coyoneda isomorphism, and proves that the contravariant
`CommHopfAlgCat.pointsFunctor` is faithful. It concerns the underlying type-valued functor:
the later group-object Yoneda bridge will retain the group-valued structure and prove the
corresponding full-faithfulness and essential-image statements.

The corepresenting object and value algebras live in the same universe as `H`. Universe
transport for a points functor valued in a different universe is deliberately left to the
later universe-lifting bridge; `shrinkYonedaGrp` supplies only the group-valued hom-set
shrinking part.

## Main declarations

* `TauCeti.HopfAlgebra.pointsHomEquiv`: a morphism out of the coordinate algebra is the same
  data as a point, with the computation rules in both directions.
* `TauCeti.HopfAlgebra.pointsCorepresentableBy`: the underlying type-valued points functor is
  corepresented by the coordinate algebra.
* `TauCeti.HopfAlgebra.coyonedaObjIsoPointsFunctorForget`: the corresponding coyoneda
  isomorphism.
* `TauCeti.HopfAlgebra.pointsFunctorForget_isCorepresentable`: the discoverable
  corepresentability instance.
* `TauCeti.CommHopfAlgCat.pointsFunctor_faithful`: points distinguish coordinate Hopf
  algebra morphisms.

## References

This is the Yoneda/corepresentability step in `ReductiveGroups/README.md`, Layer 0,
"the functor of points and the three-way dictionary". It reuses Mathlib's
`Functor.CorepresentableBy`, `ConcreteCategory.homEquiv`, and `WithConv.equiv`. Stating the
corepresenting equivalence separately, at the type of points, follows Mathlib's
`CategoryTheory.Functor.RepresentableBy.homEquiv'`, which plays the same role for a
representable functor of the form `F ⋙ forget D`.
-/

public section

open CategoryTheory Opposite WithConv

namespace TauCeti

universe u v

section CorepresentableByToIso

universe u' v'

variable {C : Type u'} [Category.{v'} C] {F : C ⥤ Type v'} {X : C}

/-- Mathlib's `Functor.CorepresentableBy.toIso` is `Functor.corepresentableByEquiv`, whose
components are the isomorphisms `Equiv.toIso` attached to `homEquiv`. This local lemma is the
one place that unfolds that implementation, so the component lemmas below reduce to the
corepresenting equivalence. -/
private theorem corepresentableBy_toIso_hom_app (e : F.CorepresentableBy X) (Y : C)
    (f : X ⟶ Y) : e.toIso.hom.app Y f = e.homEquiv f := by
  simp only [Functor.CorepresentableBy.toIso, Functor.corepresentableByEquiv, Equiv.coe_fn_mk,
    NatIso.ofComponents_hom_app, Equiv.toIso_hom_hom_apply]

/-- The inverse form of `corepresentableBy_toIso_hom_app`, obtained from it by applying the
injective map `homEquiv`. -/
private theorem corepresentableBy_toIso_inv_app (e : F.CorepresentableBy X) (Y : C)
    (y : F.obj Y) : e.toIso.inv.app Y y = e.homEquiv.symm y :=
  e.homEquiv.injective <| by
    rw [← corepresentableBy_toIso_hom_app, Iso.inv_hom_id_app_apply, Equiv.apply_symm_apply]

end CorepresentableByToIso

namespace HopfAlgebra

variable {R : Type u} [CommRing R]

/-- The tautological equivalence between morphisms of commutative `R`-algebras
`CommAlgCat.of R H ⟶ A` and `A`-valued points of `H`: both are the algebra homomorphism
`H →ₐ[R] A` underlying the morphism.

This is the equivalence corepresenting the points functor, stated on its own rather than
only as a field of `pointsCorepresentableBy`, in the same way as Mathlib's
`Functor.RepresentableBy.homEquiv'`. It is what carries the computation rules: a left-hand
side mentioning the value `(pointsFunctor ⋙ forget GrpCat).obj A` of the corepresented
functor is not in `simp` normal form, since `Functor.comp_obj` rewrites that type. The
codomain is spelled as `WithConv (H →ₐ[R] A)`, the underlying type of `points A`, so that
the two sides of the rules below have the same type; `simp` does not use a rule whose sides
agree only definitionally. Only the commutative `R`-algebra structure of `H` is used here;
the Hopf structure enters when the codomain carries its convolution group structure. -/
noncomputable def pointsHomEquiv (H : Type v) [CommRing H] [Algebra R H]
    (A : CommAlgCat.{v} R) :
    (CommAlgCat.of R H ⟶ A) ≃ WithConv (H →ₐ[R] A) :=
  ConcreteCategory.homEquiv.trans (WithConv.equiv _).symm

/-- `pointsHomEquiv` regards a morphism of commutative `R`-algebras as an `A`-valued point. -/
@[simp]
theorem pointsHomEquiv_apply (H : Type v) [CommRing H] [Algebra R H]
    {A : CommAlgCat.{v} R} (f : CommAlgCat.of R H ⟶ A) :
    pointsHomEquiv H A f = toConv f.hom := by
  -- The defining equation of `pointsHomEquiv`: the two equivalences it composes are structures
  -- whose projections are `CommAlgCat.Hom.hom` and `toConv`. `ConcreteCategory.homEquiv` has no
  -- application lemma in Mathlib, so it is unfolded here and its `toFun` field read off by
  -- `Equiv.coe_fn_mk`. Everything below is derived from this lemma.
  rw [pointsHomEquiv, Equiv.trans_apply, WithConv.symm_equiv_apply, ConcreteCategory.homEquiv,
    Equiv.coe_fn_mk]

/-- The inverse of `pointsHomEquiv` forgets the convolution wrapper and bundles the resulting
algebra homomorphism as a morphism in `CommAlgCat`. -/
@[simp]
theorem pointsHomEquiv_symm_apply (H : Type v) [CommRing H] [Algebra R H]
    {A : CommAlgCat.{v} R} (p : WithConv (H →ₐ[R] A)) :
    (pointsHomEquiv H A).symm p = CommAlgCat.ofHom p.ofConv := by
  apply (pointsHomEquiv H A).injective
  rw [Equiv.apply_symm_apply, pointsHomEquiv_apply, CommAlgCat.hom_ofHom, WithConv.toConv_ofConv]

/-- Regarding a morphism as a point is natural in the value algebra: composing `f` with
`g : A ⟶ B` and taking the resulting `B`-valued point is the `A`-valued point of `f` pushed
forward along `g`. -/
private theorem toConv_hom_comp {H : Type v} [CommRing H] [_root_.HopfAlgebra R H]
    {A B : CommAlgCat.{v} R} (g : A ⟶ B) (f : CommAlgCat.of R H ⟶ A) :
    toConv (f ≫ g).hom =
      (pointsFunctor (R := R) (H := H) ⋙ forget GrpCat.{v}).map g (toConv f.hom) := by
  -- `Functor.comp_map` and the two `TypeCat` unwrapping lemmas turn the composite functor's
  -- action into `pointsFunctor.map g` applied to a point, so the naturality itself is proved
  -- pointwise, without unfolding anything.
  simp only [Functor.comp_map, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
  apply WithConv.ofConv_injective
  ext h
  rw [pointsFunctor_map_apply_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv,
    CommAlgCat.hom_comp, AlgHom.comp_apply]

/-- The underlying type-valued functor of points of a commutative Hopf algebra `H` is
corepresented by `H` as a commutative `R`-algebra. -/
noncomputable def pointsCorepresentableBy
    (H : Type v) [CommRing H] [_root_.HopfAlgebra R H] :
    (pointsFunctor (R := R) (H := H) ⋙ forget GrpCat.{v}).CorepresentableBy
      (CommAlgCat.of R H) where
  homEquiv {A} := pointsHomEquiv H A
  homEquiv_comp g f := by
    -- Computing both points with `pointsHomEquiv_apply` turns this field into
    -- `toConv_hom_comp`. Neither rule can be applied as a rewrite here: the field type demands
    -- the value type `(pointsFunctor ⋙ forget GrpCat).obj A`, which is the codomain
    -- `WithConv (H →ₐ[R] A)` of `pointsHomEquiv` only after unfolding the semireducible
    -- `Functor.comp`, `forget GrpCat` and `pointsFunctor`, and keyed matching does not see
    -- through them. The step is definitional, so `exact` performs it in one place.
    exact toConv_hom_comp g f

/-- The coyoneda functor corepresented by `H` is isomorphic to the underlying type-valued
functor of points of `H`. -/
noncomputable def coyonedaObjIsoPointsFunctorForget
    (H : Type v) [CommRing H] [_root_.HopfAlgebra R H] :
    coyoneda.obj (op (CommAlgCat.of R H)) ≅
      pointsFunctor (R := R) (H := H) ⋙ forget GrpCat.{v} :=
  (pointsCorepresentableBy (R := R) H).toIso

/-- The underlying type-valued functor of points is registered as corepresentable, so the
generic corepresentability API can recover a representing object and universal element. -/
instance pointsFunctorForget_isCorepresentable
    (H : Type v) [CommRing H] [_root_.HopfAlgebra R H] :
    (pointsFunctor (R := R) (H := H) ⋙ forget GrpCat.{v}).IsCorepresentable :=
  (pointsCorepresentableBy (R := R) H).isCorepresentable

-- The two component lemmas below are deliberately not `@[simp]`: their left-hand sides carry
-- the value type `(pointsFunctor ⋙ forget GrpCat).obj A` of the corepresented functor, which
-- `Functor.comp_obj` rewrites, so they are not in `simp` normal form. `pointsHomEquiv_apply`
-- and `pointsHomEquiv_symm_apply` are the corresponding simp rules.

/-- The forward map of `coyonedaObjIsoPointsFunctorForget` regards an algebra morphism as a
point. -/
theorem coyonedaObjIsoPointsFunctorForget_hom_app_apply
    (H : Type v) [CommRing H] [_root_.HopfAlgebra R H]
    (A : CommAlgCat.{v} R) (f : CommAlgCat.of R H ⟶ A) :
    (coyonedaObjIsoPointsFunctorForget (R := R) H).hom.app A f = toConv f.hom := by
  rw [coyonedaObjIsoPointsFunctorForget, corepresentableBy_toIso_hom_app]
  exact pointsHomEquiv_apply H f

/-- The inverse map of `coyonedaObjIsoPointsFunctorForget` bundles a point as a morphism in
`CommAlgCat`. -/
theorem coyonedaObjIsoPointsFunctorForget_inv_app_apply
    (H : Type v) [CommRing H] [_root_.HopfAlgebra R H]
    (A : CommAlgCat.{v} R) (p : points (R := R) (H := H) A) :
    (coyonedaObjIsoPointsFunctorForget (R := R) H).inv.app A p =
      CommAlgCat.ofHom p.ofConv := by
  rw [coyonedaObjIsoPointsFunctorForget]
  -- The two lemmas about the point `p` are chained as terms: as rewrites they would have to
  -- match `p`, whose type `points A` reaches the value type of the composite functor only
  -- through the semireducible `Functor.comp` and `pointsFunctor`.
  exact (corepresentableBy_toIso_inv_app (pointsCorepresentableBy (R := R) H) A p).trans
    (pointsHomEquiv_symm_apply H p)

end HopfAlgebra

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- The contravariant functor of points is faithful: a coordinate Hopf-algebra morphism is
recovered by evaluating its map on points at the identity point of its target algebra. -/
instance pointsFunctor_faithful :
    (pointsFunctor (R := R) :
      (_root_.CommHopfAlgCat.{v} R)ᵒᵖ ⥤ CommAlgCat.{v} R ⥤ GrpCat.{v}).Faithful where
  map_injective {H K} φ ψ hφψ := by
    apply Quiver.Hom.unop_inj
    apply _root_.CommHopfAlgCat.hom_ext
    ext k
    have hpoints := congrArg
      (fun α => α.app (CommAlgCat.of R H.unop)
        (toConv (AlgHom.id R H.unop))) hφψ
    have heval := congrArg (fun p => p.ofConv k) hpoints
    rw [pointsFunctor_map_app_apply_apply, pointsFunctor_map_app_apply_apply] at heval
    simpa only [AlgHom.id_apply] using heval

end CommHopfAlgCat

end TauCeti
