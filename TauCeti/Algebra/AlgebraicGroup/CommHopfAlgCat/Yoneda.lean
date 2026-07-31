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
`Functor.CorepresentableBy`, `ConcreteCategory.homEquiv`, and `WithConv.equiv`.
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
one place that unfolds that implementation, so the computation rules below can be stated
purely in terms of `homEquiv`. -/
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

/-- The underlying type-valued functor of points of a commutative Hopf algebra `H` is
corepresented by `H` as a commutative `R`-algebra. -/
noncomputable def pointsCorepresentableBy
    (H : Type v) [CommRing H] [_root_.HopfAlgebra R H] :
    (pointsFunctor (R := R) (H := H) ⋙ forget GrpCat.{v}).CorepresentableBy
      (CommAlgCat.of R H) where
  homEquiv := ConcreteCategory.homEquiv.trans (WithConv.equiv _).symm
  homEquiv_comp {A B} g f := by
    -- Unwrap the corepresenting equivalence: it sends `f` to the algebra homomorphism `f.hom`,
    -- regarded as a point. Both sides are then the composite `g.hom ∘ f.hom`.
    change toConv (f ≫ g).hom = (pointsFunctor (R := R) (H := H)).map g (toConv f.hom)
    apply WithConv.ofConv_injective
    ext h
    rw [pointsFunctor_map_apply_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv,
      CommAlgCat.hom_comp, AlgHom.comp_apply]

/-- The corepresenting equivalence sends a commutative-algebra morphism to the same algebra
homomorphism, regarded as a point. -/
@[simp]
theorem pointsCorepresentableBy_homEquiv_apply
    (H : Type v) [CommRing H] [_root_.HopfAlgebra R H]
    {A : CommAlgCat.{v} R} (f : CommAlgCat.of R H ⟶ A) :
    (pointsCorepresentableBy (R := R) H).homEquiv f = toConv f.hom := by
  -- The corepresenting equivalence is `ConcreteCategory.homEquiv` followed by
  -- `(WithConv.equiv _).symm`, so both sides are literally `toConv f.hom`. The conversion has
  -- to be definitional: the value type `(pointsFunctor ⋙ forget GrpCat).obj A` becomes
  -- `WithConv (H →ₐ[R] A)` only after unfolding `Functor.comp` and `forget`, so rewriting with
  -- `WithConv.symm_equiv_apply` fails — its instance of `WithConv.equiv` does not even
  -- typecheck at the unreduced value type. This lemma is the single definitional step; every
  -- computation rule below is derived from it by rewriting.
  rfl

/-- The inverse corepresenting equivalence forgets the convolution wrapper and bundles the
resulting algebra homomorphism as a morphism in `CommAlgCat`. -/
@[simp]
theorem pointsCorepresentableBy_homEquiv_symm_apply
    (H : Type v) [CommRing H] [_root_.HopfAlgebra R H]
    {A : CommAlgCat.{v} R} (p : points (R := R) (H := H) A) :
    (pointsCorepresentableBy (R := R) H).homEquiv.symm p =
      CommAlgCat.ofHom p.ofConv := by
  apply (pointsCorepresentableBy (R := R) H).homEquiv.injective
  rw [Equiv.apply_symm_apply, pointsCorepresentableBy_homEquiv_apply,
    CommAlgCat.hom_ofHom, WithConv.toConv_ofConv]

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

/-- The forward map of `coyonedaObjIsoPointsFunctorForget` regards an algebra morphism as a
point. -/
@[simp]
theorem coyonedaObjIsoPointsFunctorForget_hom_app_apply
    (H : Type v) [CommRing H] [_root_.HopfAlgebra R H]
    (A : CommAlgCat.{v} R) (f : CommAlgCat.of R H ⟶ A) :
    (coyonedaObjIsoPointsFunctorForget (R := R) H).hom.app A f = toConv f.hom := by
  rw [coyonedaObjIsoPointsFunctorForget, corepresentableBy_toIso_hom_app,
    pointsCorepresentableBy_homEquiv_apply]

/-- The inverse map of `coyonedaObjIsoPointsFunctorForget` bundles a point as a morphism in
`CommAlgCat`. -/
@[simp]
theorem coyonedaObjIsoPointsFunctorForget_inv_app_apply
    (H : Type v) [CommRing H] [_root_.HopfAlgebra R H]
    (A : CommAlgCat.{v} R) (p : points (R := R) (H := H) A) :
    (coyonedaObjIsoPointsFunctorForget (R := R) H).inv.app A p =
      CommAlgCat.ofHom p.ofConv := by
  rw [coyonedaObjIsoPointsFunctorForget, corepresentableBy_toIso_inv_app,
    pointsCorepresentableBy_homEquiv_symm_apply]

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
