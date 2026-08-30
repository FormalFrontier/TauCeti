/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Basic
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Conjugation

/-!
# Yoneda theory for the functor of points

The underlying type-valued functor of points of a commutative Hopf algebra `H` is
corepresented by `H` as a commutative algebra. Concretely, a morphism
`CommAlgCat.of R H ⟶ A` is the same data as an `A`-valued point
`WithConv (H →ₐ[R] A)`.

This file packages that tautological equivalence as a `Functor.CorepresentableBy`, exposes
the resulting coyoneda isomorphism, and proves that the contravariant
`CommHopfAlgCat.pointsFunctor` is fully faithful. The group-valued result identifies the
points functor with group-object Yoneda, after transporting commutative Hopf algebras to
cogroup commutative algebras and removing a double opposite. Its essential image consists
exactly of the group-valued functors whose underlying type-valued functor is corepresentable.

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
* `TauCeti.HopfAlgebra.pointsGroupPresheaf` and `TauCeti.HopfAlgebra.pointsPresheaf`: the
  group- and type-valued points functors as presheaves on opposite commutative algebras.
* `TauCeti.CommHopfAlgCat.groupYonedaPointsFunctor`: the group-object Yoneda model of the
  functor of points.
* `TauCeti.CommHopfAlgCat.groupYonedaPointsHomEquiv`: the carrier equivalence from the opaque
  group-Yoneda model to algebra morphisms.
* `TauCeti.CommHopfAlgCat.grpObjPointsMulEquiv`: generalized points of the represented group
  object are its convolution points.
* `TauCeti.CommHopfAlgCat.grpObj_conj_unop_hom`: categorical conjugation unops to the coordinate
  conjugation algebra map.
* `TauCeti.CommHopfAlgCat.groupYonedaPointsFunctorIso`: the group-valued Yoneda model is
  naturally isomorphic to the existing points functor.
* `TauCeti.CommHopfAlgCat.pointsFunctor_faithful` and
  `TauCeti.CommHopfAlgCat.pointsFunctor_full`: points recover coordinate Hopf algebra
  morphisms.
* `TauCeti.CommHopfAlgCat.homOfPointsMap`: the coordinate morphism a natural map of points
  functors comes from, with `TauCeti.CommHopfAlgCat.mapPointsFunctor_homOfPointsMap` its
  defining property, `TauCeti.CommHopfAlgCat.homOfPointsMap_mapPointsFunctor` the converse
  recovery law, and `TauCeti.CommHopfAlgCat.homOfPointsMap_id` and
  `TauCeti.CommHopfAlgCat.homOfPointsMap_comp` its functoriality. This is the form in which
  fullness is used downstream, where a group-scheme morphism is built from its natural action
  on points.
* `TauCeti.CommHopfAlgCat.essImage_pointsFunctor`: the essential image consists exactly of
  group functors with corepresentable underlying functor.

## References

This is the Yoneda/corepresentability step in `ReductiveGroups/README.md`, Layer 0,
"the functor of points and the three-way dictionary". It reuses Mathlib's
`Functor.CorepresentableBy`, `ConcreteCategory.homEquiv`, and `WithConv.equiv`. Stating the
corepresenting equivalence separately, at the type of points, follows Mathlib's
`CategoryTheory.Functor.RepresentableBy.homEquiv'`, which plays the same role for a
representable functor of the form `F ⋙ forget D`. The group-valued result uses Mathlib's
Hopf-algebra/cogroup equivalence, `CategoryTheory.yonedaGrp`, and its essential-image theorem.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite WithConv
open scoped CategoryTheory.MonObj

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

/-- The group-valued presheaf of convolution points of a commutative Hopf algebra.

The double-opposite equivalence presents the covariant functor on `CommAlgCat R` as a presheaf on
the opposite category. -/
noncomputable abbrev pointsGroupPresheaf (H : _root_.CommHopfAlgCat.{v} R) :
    ((CommAlgCat.{v} R)ᵒᵖ)ᵒᵖ ⥤ GrpCat.{v} :=
  (opOpEquivalence (CommAlgCat.{v} R)).functor ⋙
    pointsFunctor (R := R) (H := H)

/-- The underlying type-valued presheaf of convolution points of a commutative Hopf algebra. -/
noncomputable abbrev pointsPresheaf (H : _root_.CommHopfAlgCat.{v} R) :
    ((CommAlgCat.{v} R)ᵒᵖ)ᵒᵖ ⥤ Type v :=
  pointsGroupPresheaf H ⋙ forget GrpCat

/-- Evaluating the points presheaf at an affine `R`-scheme gives its convolution group of
algebra-valued points, with the group structure forgotten. -/
theorem pointsPresheaf_obj (H : _root_.CommHopfAlgCat.{v} R)
    (A : ((CommAlgCat.{v} R)ᵒᵖ)ᵒᵖ) :
    (pointsPresheaf H).obj A = WithConv (H →ₐ[R] A.unop.unop) :=
  rfl

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

/-- The group-object Yoneda model of the same-universe functor of points.

The Hopf-algebra/cogroup equivalence sends an opposite commutative Hopf algebra to a group
object in opposite commutative algebras. Group-valued Yoneda then produces a functor on the
double opposite of `CommAlgCat`, and the final equivalence precomposes it with `opOp` to give
a covariant functor on commutative algebras. -/
noncomputable def groupYonedaPointsFunctor :
    (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u} :=
  (commHopfAlgCatEquivCogrpCommAlgCat R).leftOp.functor ⋙
    yonedaGrp (C := (CommAlgCat.{u} R)ᵒᵖ) ⋙
      (opOpEquivalence (CommAlgCat.{u} R)).congrLeft.functor

/-- The carrier of the group-Yoneda model at a Hopf algebra `H` and value algebra `A` is
canonically the type of algebra morphisms `H ⟶ A`. This equivalence is the narrow carrier API
for the otherwise opaque composite `groupYonedaPointsFunctor`. -/
noncomputable def groupYonedaPointsHomEquiv
    (H : (_root_.CommHopfAlgCat.{u} R)ᵒᵖ) (A : CommAlgCat.{u} R) :
    ((groupYonedaPointsFunctor (R := R)).obj H).obj A ≃
      (CommAlgCat.of R H.unop ⟶ A) := by
  unfold groupYonedaPointsFunctor
  exact opEquiv _ _

/-- Under a map of value algebras, the algebra morphism underlying a group-Yoneda element
is postcomposed with that map. -/
@[simp]
theorem groupYonedaPointsHomEquiv_map
    (H : (_root_.CommHopfAlgCat.{u} R)ᵒᵖ) {A B : CommAlgCat.{u} R}
    (g : A ⟶ B) (f : ((groupYonedaPointsFunctor (R := R)).obj H).obj A) :
    groupYonedaPointsHomEquiv H B
        (((groupYonedaPointsFunctor (R := R)).obj H).map g f) =
      groupYonedaPointsHomEquiv H A f ≫ g := by
  unfold groupYonedaPointsHomEquiv groupYonedaPointsFunctor
  rfl

/-- Under a map of coordinate Hopf algebras, the algebra morphism underlying a
group-Yoneda element is precomposed with that map. -/
@[simp]
theorem groupYonedaPointsHomEquiv_map_app
    {H K : (_root_.CommHopfAlgCat.{u} R)ᵒᵖ} (f : H ⟶ K) (A : CommAlgCat.{u} R)
    (p : ((groupYonedaPointsFunctor (R := R)).obj H).obj A) :
    groupYonedaPointsHomEquiv K A
        (((groupYonedaPointsFunctor (R := R)).map f).app A p) =
      CommAlgCat.ofHom (f.unop.hom : K.unop →ₐ[R] H.unop) ≫
        groupYonedaPointsHomEquiv H A p := by
  unfold groupYonedaPointsHomEquiv groupYonedaPointsFunctor
  rfl

/-- Generalized points of the group object represented by `H` are the convolution group of
algebra-valued points of `H`. It sends the categorical multiplication `lift f g ≫ μ` to
the convolution product of the underlying algebra morphisms. -/
noncomputable def grpObjPointsMulEquiv (H : _root_.CommHopfAlgCat.{u} R)
    (X : (CommAlgCat.{u} R)ᵒᵖ) :
    (X ⟶ grpObj H) ≃* HopfAlgebra.points (R := R) (H := H) X.unop where
  toEquiv := (opEquiv X (grpObj H)).trans (HopfAlgebra.pointsHomEquiv H X.unop)
  map_mul' f g := by
    apply WithConv.ofConv_injective
    -- Exposing the hom type also exposes the group-object multiplication induced by the Hopf
    -- comultiplication.
    change (CartesianMonoidalCategory.lift f g ≫ μ).unop.hom =
      (toConv f.unop.hom * toConv g.unop.hom).ofConv
    apply AlgHom.ext
    intro h
    simp only [unop_comp, CommAlgCat.hom_comp, CommAlgCat.lift_unop_hom,
      AlgHom.comp_apply, AlgHom.convMul_apply]
    exact congrArg _ (Bialgebra.comulAlgHom_apply R H h)

/-- The group-object point equivalence regards a categorical point as the convolution wrapper of
its underlying algebra morphism. -/
@[simp]
theorem grpObjPointsMulEquiv_apply (H : _root_.CommHopfAlgCat.{u} R)
    (X : (CommAlgCat.{u} R)ᵒᵖ) (g : X ⟶ grpObj H) :
    grpObjPointsMulEquiv H X g = toConv g.unop.hom := by
  exact HopfAlgebra.pointsHomEquiv_apply H g.unop

/-- Unopping categorical conjugation on the represented group object gives the coordinate
conjugation algebra map. -/
theorem grpObj_conj_unop_hom (H : _root_.CommHopfAlgCat.{u} R) :
    (GrpObj.conj (grpObj H)).unop.hom =
      HopfAlgebra.conjugationAlgHom (R := R) (H := H) := by
  apply WithConv.toConv_injective
  calc
    WithConv.toConv (GrpObj.conj (grpObj H)).unop.hom =
        grpObjPointsMulEquiv H (grpObj H ⊗ grpObj H) (GrpObj.conj (grpObj H)) := by
      rw [grpObjPointsMulEquiv_apply]
    _ = grpObjPointsMulEquiv H (grpObj H ⊗ grpObj H) (fst (grpObj H) (grpObj H)) *
        grpObjPointsMulEquiv H (grpObj H ⊗ grpObj H) (snd (grpObj H) (grpObj H)) *
        (grpObjPointsMulEquiv H (grpObj H ⊗ grpObj H) (fst (grpObj H) (grpObj H)))⁻¹ := by
      rw [GrpObj.conj, map_mul, map_mul, map_inv]
    _ = WithConv.toConv (HopfAlgebra.conjugationAlgHom (R := R) (H := H)) := by
      rw [grpObjPointsMulEquiv_apply,
        grpObjPointsMulEquiv_apply H (grpObj H ⊗ grpObj H) (snd (grpObj H) (grpObj H))]
      simpa only [CommAlgCat.fst_unop_hom, CommAlgCat.snd_unop_hom,
        Bialgebra.TensorProduct.includeLeft_toAlgHom,
        Bialgebra.TensorProduct.includeRight_toAlgHom] using
        (HopfAlgebra.toConv_conjugationAlgHom (R := R) (H := H)).symm

/-- The inverse point equivalence bundles a convolution point as a morphism in the opposite
category of commutative algebras. -/
@[simp]
theorem grpObjPointsMulEquiv_symm_apply (H : _root_.CommHopfAlgCat.{u} R)
    (X : (CommAlgCat.{u} R)ᵒᵖ) (p : HopfAlgebra.points (R := R) (H := H) X.unop) :
    (grpObjPointsMulEquiv H X).symm p =
      (opEquiv X (grpObj H)).symm (CommAlgCat.ofHom p.ofConv) := by
  -- The inverse of the composite carrier equivalence reduces definitionally to the composite
  -- of the inverse opposite-hom equivalence and `pointsHomEquiv.symm`.
  change (opEquiv X (grpObj H)).symm ((HopfAlgebra.pointsHomEquiv H X.unop).symm p) = _
  rw [HopfAlgebra.pointsHomEquiv_symm_apply]

/-- Under the group-object point equivalences, composition with the morphism represented by `f`
is precomposition of algebra-valued points with `f`. -/
@[simp]
theorem grpObjPointsMulEquiv_comp_grpObjMap {H K : _root_.CommHopfAlgCat.{u} R} (f : H ⟶ K)
    (X : (CommAlgCat.{u} R)ᵒᵖ) (q : X ⟶ grpObj K) :
    grpObjPointsMulEquiv H X (q ≫ grpObjMap f) =
      (mapPointsFunctor f).app X.unop (grpObjPointsMulEquiv K X q) := by
  apply WithConv.ofConv_injective
  -- The public application rules expose both categorical points as their underlying algebra
  -- morphisms before the functorial action is computed.
  change (q ≫ grpObjMap f).unop.hom =
    ((mapPointsFunctor f).app X.unop (toConv q.unop.hom)).ofConv
  rw [mapPointsFunctor_app_apply, WithConv.ofConv_toConv]
  rw [unop_comp, grpObjMap_unop, CommAlgCat.hom_comp]
  rfl

/-- The tautological carrier equivalence respects group-Yoneda multiplication: unopping
`lift f g ≫ μ` gives comultiplication followed by `f` and `g`, which is convolution. -/
private noncomputable def groupYonedaPointsMulEquiv
    (H : (_root_.CommHopfAlgCat.{u} R)ᵒᵖ) (A : CommAlgCat.{u} R) :
    ((groupYonedaPointsFunctor (R := R)).obj H).obj A ≃*
      ((pointsFunctor (R := R) :
        (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).obj H).obj A :=
  grpObjPointsMulEquiv H.unop (op A)

/-- The forward homomorphism of the pointwise group equivalence is computed by the carrier
equivalence followed by the convolution wrapper. -/
private theorem groupYonedaPointsMulEquiv_apply
    (H : (_root_.CommHopfAlgCat.{u} R)ᵒᵖ) (A : CommAlgCat.{u} R)
    (f : ((groupYonedaPointsFunctor (R := R)).obj H).obj A) :
    (groupYonedaPointsMulEquiv H A).toGrpIso.hom f =
      toConv ((groupYonedaPointsHomEquiv H A) f).hom := by
  exact grpObjPointsMulEquiv_apply H.unop (op A) f

/-- The pointwise group equivalences are natural in the value algebra. -/
private noncomputable def groupYonedaPointsObjIso
    (H : (_root_.CommHopfAlgCat.{u} R)ᵒᵖ) :
    (groupYonedaPointsFunctor (R := R)).obj H ≅
      (pointsFunctor (R := R) :
        (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).obj H :=
  NatIso.ofComponents
    (fun A ↦ MulEquiv.toGrpIso (groupYonedaPointsMulEquiv H A))
    (fun {A B} ψ ↦ by
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro f
      apply WithConv.ofConv_injective
      apply AlgHom.ext
      intro h
      rw [GrpCat.comp_apply, GrpCat.comp_apply,
        groupYonedaPointsMulEquiv_apply, groupYonedaPointsMulEquiv_apply,
        WithConv.ofConv_toConv, groupYonedaPointsHomEquiv_map,
        CommAlgCat.hom_comp, AlgHom.comp_apply]
      exact (HopfAlgebra.pointsFunctor_map_apply_apply ψ
        (toConv ((groupYonedaPointsHomEquiv H A) f).hom) h).symm)

/-- The objectwise natural isomorphism has the same carrier-level computation as its
pointwise group equivalence. -/
private theorem groupYonedaPointsObjIso_hom_app_apply
    (H : (_root_.CommHopfAlgCat.{u} R)ᵒᵖ) (A : CommAlgCat.{u} R)
    (f : ((groupYonedaPointsFunctor (R := R)).obj H).obj A) :
    (groupYonedaPointsObjIso H).hom.app A f =
      toConv ((groupYonedaPointsHomEquiv H A) f).hom :=
  groupYonedaPointsMulEquiv_apply H A f

/-- Group-object Yoneda, transported through the Hopf-algebra/cogroup and double-opposite
equivalences, is naturally isomorphic to the existing group-valued functor of points. -/
noncomputable def groupYonedaPointsFunctorIso :
    groupYonedaPointsFunctor (R := R) ≅
      (pointsFunctor (R := R) :
        (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}) :=
  NatIso.ofComponents (groupYonedaPointsObjIso (R := R))
    (fun {H K} φ ↦ by
      ext A f
      apply WithConv.ofConv_injective
      apply AlgHom.ext
      intro h
      simp only [NatTrans.comp_app, GrpCat.comp_apply, groupYonedaPointsObjIso_hom_app_apply,
        groupYonedaPointsHomEquiv_map_app, pointsFunctor_map_app_apply_apply,
        WithConv.ofConv_toConv, CommAlgCat.hom_comp, CommAlgCat.hom_ofHom,
        AlgHom.comp_apply, BialgHom.coe_toAlgHom])

/-- The forward map of `groupYonedaPointsFunctorIso` unops a Yoneda morphism and regards
its underlying algebra homomorphism as a convolution point. -/
@[simp]
theorem groupYonedaPointsFunctorIso_hom_app_app_apply
    (H : (_root_.CommHopfAlgCat.{u} R)ᵒᵖ) (A : CommAlgCat.{u} R)
    (f : ((groupYonedaPointsFunctor (R := R)).obj H).obj A) :
    ((groupYonedaPointsFunctorIso (R := R)).hom.app H).app A f =
      toConv ((groupYonedaPointsHomEquiv H A) f).hom := by
  exact groupYonedaPointsObjIso_hom_app_apply H A f

/-- The inverse map of `groupYonedaPointsFunctorIso` bundles a convolution point as a
commutative-algebra morphism and takes its opposite. -/
@[simp]
theorem groupYonedaPointsFunctorIso_inv_app_app_apply
    (H : (_root_.CommHopfAlgCat.{u} R)ᵒᵖ) (A : CommAlgCat.{u} R)
    (p : HopfAlgebra.points (R := R) (H := H.unop) A) :
    ((groupYonedaPointsFunctorIso (R := R)).inv.app H).app A p =
      (groupYonedaPointsHomEquiv H A).symm (CommAlgCat.ofHom p.ofConv) := by
  apply (groupYonedaPointsHomEquiv H A).injective
  rw [Equiv.apply_symm_apply]
  apply CommAlgCat.hom_ext
  rw [CommAlgCat.hom_ofHom]
  -- State the triangle identity at the opaque outer functor's value; its object is
  -- definitionally the displayed convolution-point type of `p`.
  let p' : ((pointsFunctor (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).obj H).obj A := p
  have hp :
      ((groupYonedaPointsFunctorIso (R := R)).hom.app H).app A
          (((groupYonedaPointsFunctorIso (R := R)).inv.app H).app A p') = p' := by
    rw [← GrpCat.comp_apply, Iso.inv_hom_id_app_app, GrpCat.id_apply]
  simpa only [p'] using congrArg WithConv.ofConv
    ((groupYonedaPointsFunctorIso_hom_app_app_apply H A
      (((groupYonedaPointsFunctorIso (R := R)).inv.app H).app A p')).symm.trans hp)

/-- The same-universe group-valued functor of points is full: every natural group
homomorphism between point functors is induced by a coordinate Hopf-algebra morphism. -/
instance pointsFunctor_full :
    (pointsFunctor (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).Full := by
  let : (groupYonedaPointsFunctor (R := R)).Full := by
    dsimp [groupYonedaPointsFunctor]
    infer_instance
  exact Functor.Full.of_iso (groupYonedaPointsFunctorIso (R := R))

/-- The coordinate Hopf-algebra morphism that a natural transformation of group-valued points
functors comes from, recovered by fullness of the functor of points.

Its direction is `K ⟶ H`, opposite to that of the natural map
`pointsFunctor H ⟶ pointsFunctor K` it is recovered from. -/
noncomputable def homOfPointsMap {H K : _root_.CommHopfAlgCat.{u} R}
    (α : HopfAlgebra.pointsFunctor (R := R) (H := H) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := K)) :
    K ⟶ H :=
  ((pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).preimage
    (X := op H) (Y := op K) α).unop

/-- Pre-composition by the recovered coordinate morphism is the natural points map it was
recovered from. This is the defining property of `TauCeti.CommHopfAlgCat.homOfPointsMap`, and
the only thing its users need. -/
@[simp]
theorem mapPointsFunctor_homOfPointsMap {H K : _root_.CommHopfAlgCat.{u} R}
    (α : HopfAlgebra.pointsFunctor (R := R) (H := H) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := K)) :
    (mapPointsFunctor (homOfPointsMap α) :
      HopfAlgebra.pointsFunctor (R := R) (H := H) ⟶
        HopfAlgebra.pointsFunctor (R := R) (H := K)) = α := by
  unfold homOfPointsMap
  rw [← pointsFunctor_map]
  exact Functor.map_preimage
    (pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}) _

/-- Recovering a coordinate morphism from the points map it induces returns that morphism.
With `TauCeti.CommHopfAlgCat.mapPointsFunctor_homOfPointsMap` this makes
`TauCeti.CommHopfAlgCat.homOfPointsMap` a two-sided inverse of
`TauCeti.CommHopfAlgCat.mapPointsFunctor`, and it is where faithfulness of the functor of
points is used rather than only its fullness. -/
@[simp]
theorem homOfPointsMap_mapPointsFunctor {H K : _root_.CommHopfAlgCat.{u} R} (φ : K ⟶ H) :
    homOfPointsMap (mapPointsFunctor φ) = φ := by
  -- `pointsFunctor.map ψ.op` and `mapPointsFunctor ψ` are definitionally but not syntactically
  -- equal, so `Functor.preimage_map` does not unify against the goal. This `have` is
  -- load-bearing: it restates the defining property in the functor's own spelling of the
  -- morphism part, which is the one `Functor.map_injective` unifies against.
  have h : (pointsFunctor.{u, u, u} (R := R) :
        (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).map
        (homOfPointsMap (mapPointsFunctor φ)).op =
      (pointsFunctor.{u, u, u} (R := R) :
        (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).map φ.op :=
    mapPointsFunctor_homOfPointsMap (mapPointsFunctor φ)
  exact Quiver.Hom.op_inj (Functor.map_injective _ h)

/-- The recovered coordinate morphism of an identity points map is the identity. -/
@[simp]
theorem homOfPointsMap_id (H : _root_.CommHopfAlgCat.{u} R) :
    homOfPointsMap (𝟙 (HopfAlgebra.pointsFunctor (R := R) (H := H) :
      CommAlgCat.{u} R ⥤ GrpCat.{u})) = 𝟙 H := by
  rw [← mapPointsFunctor_id (R := R) H, homOfPointsMap_mapPointsFunctor]

/-- The recovered coordinate morphism of a composite points map is the composite of the
recovered morphisms, in the opposite order: `TauCeti.CommHopfAlgCat.homOfPointsMap` is
contravariant, like `TauCeti.CommHopfAlgCat.mapPointsFunctor`. -/
@[simp]
theorem homOfPointsMap_comp {H K L : _root_.CommHopfAlgCat.{u} R}
    (α : HopfAlgebra.pointsFunctor (R := R) (H := H) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := K))
    (β : HopfAlgebra.pointsFunctor (R := R) (H := K) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := L)) :
    homOfPointsMap (α ≫ β) = homOfPointsMap β ≫ homOfPointsMap α := by
  -- As in `homOfPointsMap_mapPointsFunctor`, this `have` is load-bearing: it moves the goal into
  -- the functor's own spelling of the morphism part before appealing to faithfulness.
  have h : (pointsFunctor.{u, u, u} (R := R) :
        (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).map
        (homOfPointsMap (α ≫ β)).op =
      (pointsFunctor.{u, u, u} (R := R) :
        (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).map
        (homOfPointsMap β ≫ homOfPointsMap α).op := by
    change mapPointsFunctor (homOfPointsMap (α ≫ β)) =
      mapPointsFunctor (homOfPointsMap β ≫ homOfPointsMap α)
    simp only [mapPointsFunctor_comp, mapPointsFunctor_homOfPointsMap]
  exact Quiver.Hom.op_inj (Functor.map_injective _ h)

/-- Precomposition by `unopUnop` turns representability on a double opposite into
corepresentability. This is the type-valued variance correction underlying the essential-image
calculation below. -/
private theorem isRepresentable_unopUnop_comp_iff_isCorepresentable
    (F : CommAlgCat.{u} R ⥤ Type u) :
    (unopUnop (CommAlgCat.{u} R) ⋙ F).IsRepresentable ↔ F.IsCorepresentable := by
  constructor
  · rintro ⟨X, ⟨e⟩⟩
    let c : F.CorepresentableBy X.unop :=
      { homEquiv {Y} := (opEquiv (op Y) X).symm.trans e.homEquiv
        homEquiv_comp {Y Y'} g f := by
          -- The structure field is a composite equivalence. This conversion unfolds only
          -- `Equiv.trans` and the inverse application of `opEquiv`; `op_comp` and the
          -- `unopUnop ⋙ F` map rules below record the actual variance calculation.
          change e.homEquiv ((f ≫ g).op) = F.map g (e.homEquiv f.op)
          rw [op_comp, e.homEquiv_comp, Functor.comp_map, unopUnop_map,
            Quiver.Hom.unop_op, Quiver.Hom.unop_op] }
    exact c.isCorepresentable
  · rintro ⟨X, ⟨e⟩⟩
    let r : (unopUnop (CommAlgCat.{u} R) ⋙ F).RepresentableBy (op X) :=
      { homEquiv {Y} := (opEquiv Y (op X)).trans e.homEquiv
        homEquiv_comp {Y Y'} f g := by
          -- As above, this conversion unfolds only `Equiv.trans` and the forward application
          -- of `opEquiv`. The composite-functor map stays visible for the explicit variance
          -- rewrite rather than being discharged by definitional equality.
          change e.homEquiv ((f ≫ g).unop) =
            (unopUnop (CommAlgCat.{u} R) ⋙ F).map f.op (e.homEquiv g.unop)
          rw [unop_comp, e.homEquiv_comp, Functor.comp_map, unopUnop_map,
            Quiver.Hom.unop_op] }
    exact r.isRepresentable

/-- Presenting the corepresentable underlying points functor on the double opposite of
`CommAlgCat R` produces a representable presheaf on `(CommAlgCat R)ᵒᵖ`. -/
instance pointsFunctorForget_unopUnop_isRepresentable
    (H : Type u) [CommRing H] [_root_.HopfAlgebra R H] :
    (unopUnop (CommAlgCat.{u} R) ⋙
      (HopfAlgebra.pointsFunctor (R := R) (H := H) ⋙ forget GrpCat.{u})).IsRepresentable :=
  (isRepresentable_unopUnop_comp_iff_isCorepresentable
    (R := R) (HopfAlgebra.pointsFunctor (R := R) (H := H) ⋙
      forget GrpCat.{u})).mpr inferInstance

/-- Transport the generic essential image of group-object Yoneda across the double-opposite
equivalence. -/
private theorem essImage_yonedaGrp_doubleOp :
    (yonedaGrp (C := (CommAlgCat.{u} R)ᵒᵖ) ⋙
      ((opOpEquivalence (CommAlgCat.{u} R)).congrLeft (E := GrpCat.{u})).functor).essImage =
      fun F ↦ (F ⋙ forget GrpCat.{u}).IsCorepresentable := by
  let D := (opOpEquivalence (CommAlgCat.{u} R)).congrLeft (E := GrpCat.{u})
  ext F
  constructor
  · rintro ⟨G, ⟨i⟩⟩
    have hmem : (yonedaGrp (C := (CommAlgCat.{u} R)ᵒᵖ)).essImage (D.inverse.obj F) :=
      ⟨G, ⟨D.unitIso.app _ ≪≫ D.inverse.mapIso i⟩⟩
    rw [essImage_yonedaGrp] at hmem
    apply (isRepresentable_unopUnop_comp_iff_isCorepresentable
      (R := R) (F ⋙ forget GrpCat.{u})).mp
    exact hmem
  · intro h
    have hrep := (isRepresentable_unopUnop_comp_iff_isCorepresentable
      (R := R) (F ⋙ forget GrpCat.{u})).mpr h
    have hmem : (yonedaGrp (C := (CommAlgCat.{u} R)ᵒᵖ)).essImage (D.inverse.obj F) := by
      rw [essImage_yonedaGrp]
      exact hrep
    obtain ⟨G, ⟨i⟩⟩ := hmem
    exact ⟨G, ⟨D.functor.mapIso i ≪≫ D.counitIso.app F⟩⟩

/-- A same-universe group-valued functor on commutative `R`-algebras lies in the essential
image of the functor of points exactly when its underlying type-valued functor is
corepresentable. -/
theorem essImage_pointsFunctor :
    (pointsFunctor (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).essImage =
      fun F ↦ (F ⋙ forget GrpCat.{u}).IsCorepresentable := by
  rw [← Functor.essImage_eq_of_natIso (groupYonedaPointsFunctorIso (R := R)),
    groupYonedaPointsFunctor, Functor.essImage_comp_of_essSurj,
    essImage_yonedaGrp_doubleOp]

end CommHopfAlgCat

namespace HopfAlgebra

variable {R : Type u} [CommRing R]

/-- The type-valued points presheaf is represented by the coordinate algebra on the opposite
category. -/
instance pointsPresheaf_isRepresentable (H : _root_.CommHopfAlgCat.{u} R) :
    (pointsPresheaf H).IsRepresentable := by
  -- Unfolding the two presheaf abbreviations exposes the registered representability of the
  -- underlying points functor after precomposition by the double-opposite equivalence.
  change (unopUnop (CommAlgCat.{u} R) ⋙
    (pointsFunctor (R := R) (H := H) ⋙ forget GrpCat.{u})).IsRepresentable
  exact CommHopfAlgCat.pointsFunctorForget_unopUnop_isRepresentable H

end HopfAlgebra

end TauCeti
