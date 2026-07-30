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
  change (ConcreteCategory.homEquiv.trans (WithConv.equiv _).symm) f = _
  simp only [Equiv.trans_apply, WithConv.symm_equiv_apply, ConcreteCategory.homEquiv,
    Equiv.coe_fn_mk]

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
  simp only [coyonedaObjIsoPointsFunctorForget, Functor.CorepresentableBy.toIso,
    Functor.corepresentableByEquiv, Equiv.coe_fn_mk, NatIso.ofComponents_hom_app,
    Equiv.toIso_hom_hom_apply]
  exact pointsCorepresentableBy_homEquiv_apply (R := R) H f

/-- The inverse map of `coyonedaObjIsoPointsFunctorForget` bundles a point as a morphism in
`CommAlgCat`. -/
@[simp]
theorem coyonedaObjIsoPointsFunctorForget_inv_app_apply
    (H : Type v) [CommRing H] [_root_.HopfAlgebra R H]
    (A : CommAlgCat.{v} R) (p : points (R := R) (H := H) A) :
    (coyonedaObjIsoPointsFunctorForget (R := R) H).inv.app A p =
      CommAlgCat.ofHom p.ofConv := by
  simp only [coyonedaObjIsoPointsFunctorForget, Functor.CorepresentableBy.toIso,
    Functor.corepresentableByEquiv, Equiv.coe_fn_mk, NatIso.ofComponents_inv_app,
    Equiv.toIso_inv_hom_apply]
  exact pointsCorepresentableBy_homEquiv_symm_apply (R := R) H p

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
