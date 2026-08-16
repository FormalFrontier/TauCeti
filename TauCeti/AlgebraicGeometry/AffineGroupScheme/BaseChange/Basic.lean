/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Equivalence
public import TauCeti.AlgebraicGeometry.PullbackSpecMap

/-!
# Base change of affine group schemes

Pullback along `Spec S ⟶ Spec R` carries an affine group scheme over `Spec R` to an affine
group scheme over `Spec S`. This file bundles that construction on objects and morphisms as
`TauCeti.AffineGroupSchemeCat.baseChangeFunctor`, and records comparison isomorphisms for base
change along the identity ring map and along a composite ring map. The mutual coherence
conditions of those two comparisons — the unit and associativity constraints that would make
`R ↦ AffineGroupSchemeCat R` a pseudofunctor — are not proved here.

The group structure is transported by Mathlib's left-exact pullback functor on `Over` categories.
Affineness is preserved because the base `Spec R` is itself affine: a fibre product of affine
schemes over an affine base is again affine, so the fibre product of `G` with `Spec S` over
`Spec R` is affine. (Over a general base scheme this argument is unavailable, and a fibre product
of affine schemes need not be affine.) Thus the construction applies over general commutative
rings; no field or finite-type hypothesis is needed.

## Main declarations

* `TauCeti.AffineGroupSchemeCat.baseChange`: base change of one affine group scheme.
* `TauCeti.AffineGroupSchemeCat.baseChangeMap`: base change of a morphism.
* `TauCeti.AffineGroupSchemeCat.baseChangeFunctor`: functorial base change.
* `TauCeti.AffineGroupSchemeCat.baseChangeFunctorIdIso`,
  `TauCeti.AffineGroupSchemeCat.baseChangeFunctorCompIso`: base change along the identity ring
  map is the identity, and base change along a composite is the composite of base changes. Their
  components are computed by simp lemmas in terms of the underlying comparisons
  `TauCeti.AlgebraicGeometry.Over.pullbackSpecMapId` and
  `TauCeti.AlgebraicGeometry.Over.pullbackSpecMapComp` of pullback functors.
* `TauCeti.AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso` and
  `TauCeti.AffineGroupSchemeCat.hopfSpecBaseChangeIso`: base change of a Hopf spectrum agrees
  with scalar extension of its coordinate Hopf algebra, first for group objects and then through
  the affine-group-scheme anti-equivalence.

The comparison with base change of coordinate Hopf algebras is developed in
`TauCeti.AlgebraicGeometry.AffineGroupScheme.BaseChange.Coordinate`.

## References

The coordinate-algebra counterpart of this construction, base change of commutative Hopf
algebras, is `TauCeti.CommHopfAlgCat.baseChangeFunctor`; the two sides are related by the
anti-equivalence `TauCeti.commHopfAlgCatOpEquivAffineGroupSchemeCat`.
`hopfSpecBaseChangeIso` identifies their values on each Hopf algebra. Their natural compatibility
is developed in `TauCeti.AlgebraicGeometry.AffineGroupScheme.BaseChange.Coordinate` as
`TauCeti.AffineGroupSchemeCat.hopfSpecBaseChangeNatIso`.

## Roadmap

This supplies the scheme-side base-change operation required by Layer 9 of the ReductiveGroups
roadmap. The CFSGStatement roadmap's milestone L0 uses it to evaluate a pinned
Chevalley--Demazure group scheme over `ℤ` after extension to an algebraic closure of a finite
prime field.
-/

public section

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry.Over

namespace TauCeti

universe u

namespace AffineGroupSchemeCat

variable {R S T : CommRingCat.{u}}

/-- Base change of an affine group scheme along a morphism `f : R ⟶ S` of commutative rings.

Its underlying scheme is the fibre product with `Spec S` over `Spec R`, and its group-object
structure is the one transported by pullback. -/
noncomputable abbrev baseChange (f : R ⟶ S) (G : AffineGroupSchemeCat R) :
    AffineGroupSchemeCat S :=
  ⟨(Over.pullback (Spec.map f)).mapGrp.obj G.obj, by
    rw [affineGroupSchemeProperty_iff]
    -- unfold the pulled-back group object to its underlying fibre product `G ×[Spec R] Spec S`,
    -- which Mathlib knows to be affine because `G`, `Spec S` and `Spec R` all are
    simp only [Functor.mapGrp_obj_X, Over.pullback_obj_left]
    infer_instance⟩

/-- The underlying group object of a base-changed affine group scheme is obtained by applying
pullback to the original group object. -/
@[simp]
lemma baseChange_obj (f : R ⟶ S) (G : AffineGroupSchemeCat R) :
    (baseChange f G).obj = (Over.pullback (Spec.map f)).mapGrp.obj G.obj :=
  (rfl)

/-- The underlying object over `Spec S` of a base-changed affine group scheme is the pullback of
the original object over `Spec R`. -/
lemma baseChange_obj_X (f : R ⟶ S) (G : AffineGroupSchemeCat R) :
    (baseChange f G).obj.X = (Over.pullback (Spec.map f)).obj G.obj.X := by
  simp only [Functor.mapGrp_obj_X]

/-- The underlying scheme of a base-changed affine group scheme is the corresponding fibre
product. -/
lemma baseChange_obj_X_left (f : R ⟶ S) (G : AffineGroupSchemeCat R) :
    (baseChange f G).obj.X.left = Limits.pullback G.obj.X.hom (Spec.map f) := by
  simp only [Functor.mapGrp_obj_X, Over.pullback_obj_left]

/-- Base change of a morphism of affine group schemes. -/
noncomputable abbrev baseChangeMap (f : R ⟶ S) {G H : AffineGroupSchemeCat R} (g : G ⟶ H) :
    baseChange f G ⟶ baseChange f H :=
  ObjectProperty.homMk ((Over.pullback (Spec.map f)).mapGrp.map g.hom)

/-- The underlying group-object morphism of `baseChangeMap` is obtained by applying pullback. -/
@[simp]
lemma hom_baseChangeMap (f : R ⟶ S) {G H : AffineGroupSchemeCat R} (g : G ⟶ H) :
    (baseChangeMap f g).hom = (Over.pullback (Spec.map f)).mapGrp.map g.hom :=
  (rfl)

/-- Pullback along `Spec S ⟶ Spec R` defines a functor from affine group schemes over
`Spec R` to affine group schemes over `Spec S`. -/
-- `@[expose]` is forced by the public statements below: with the body hidden, the two sides of
-- `baseChangeFunctor_map` and of the component lemmas for the comparison isomorphisms are only
-- definitionally equal, so those statements no longer elaborate.
@[expose] noncomputable def baseChangeFunctor (f : R ⟶ S) :
    AffineGroupSchemeCat R ⥤ AffineGroupSchemeCat S :=
  (affineGroupSchemeProperty S).lift
    ((affineGroupSchemeProperty R).ι ⋙ (Over.pullback (Spec.map f)).mapGrp)
    fun G => (baseChange f G).property

/-- The object part of `baseChangeFunctor` is base change of affine group schemes. -/
@[simp]
lemma baseChangeFunctor_obj (f : R ⟶ S) (G : AffineGroupSchemeCat R) :
    (baseChangeFunctor f).obj G = baseChange f G :=
  (rfl)

/-- The morphism part of `baseChangeFunctor` is base change of affine-group-scheme morphisms. -/
@[simp]
lemma baseChangeFunctor_map (f : R ⟶ S) {G H : AffineGroupSchemeCat R} (g : G ⟶ H) :
    (baseChangeFunctor f).map g = baseChangeMap f g :=
  (rfl)

/-- Base change along the identity of `R` is the identity functor on affine group schemes over
`Spec R`. -/
noncomputable def baseChangeFunctorIdIso :
    baseChangeFunctor (𝟙 R) ≅ 𝟭 (AffineGroupSchemeCat R) :=
  NatIso.ofComponents
    (fun G => (affineGroupSchemeProperty R).isoMk
      ((Functor.mapGrpNatIso pullbackSpecMapId ≪≫ Functor.mapGrpIdIso).app G.obj))
    fun g => (affineGroupSchemeProperty R).ι.map_injective
      ((Functor.mapGrpNatIso pullbackSpecMapId ≪≫ Functor.mapGrpIdIso).hom.naturality g.hom)

/-- The morphism of objects over `Spec R` underlying `baseChangeFunctorIdIso.hom`. -/
@[simp]
lemma baseChangeFunctorIdIso_hom_app_hom_hom_hom (G : AffineGroupSchemeCat R) :
    (baseChangeFunctorIdIso.hom.app G).hom.hom.hom = pullbackSpecMapId.hom.app G.obj.X := by
  simp only [Functor.id_obj, baseChangeFunctorIdIso, ObjectProperty.isoMk, ObjectProperty.homMk,
    NatIso.trans_app, Iso.trans_hom, Iso.app_hom, NatIso.ofComponents_hom_app, Grp.comp',
    Mon.comp_hom', Functor.mapGrpNatIso_hom_app_hom_hom, Functor.mapGrpIdIso_hom_app_hom_hom]
  exact Category.comp_id _

/-- The morphism of objects over `Spec R` underlying `baseChangeFunctorIdIso.inv`. -/
@[simp]
lemma baseChangeFunctorIdIso_inv_app_hom_hom_hom (G : AffineGroupSchemeCat R) :
    (baseChangeFunctorIdIso.inv.app G).hom.hom.hom = pullbackSpecMapId.inv.app G.obj.X := by
  simp only [Functor.id_obj, baseChangeFunctorIdIso, ObjectProperty.isoMk, ObjectProperty.homMk,
    NatIso.trans_app, Iso.trans_inv, Iso.app_inv, NatIso.ofComponents_inv_app, Grp.comp',
    Mon.comp_hom', Functor.mapGrpIdIso_inv_app_hom_hom, Functor.mapGrpNatIso_inv_app_hom_hom]
  exact Category.id_comp _

/-- Base change along a composite `f ≫ g` of ring maps is base change along `f` followed by base
change along `g`. -/
noncomputable def baseChangeFunctorCompIso (f : R ⟶ S) (g : S ⟶ T) :
    baseChangeFunctor (f ≫ g) ≅ baseChangeFunctor f ⋙ baseChangeFunctor g :=
  NatIso.ofComponents
    (fun G => (affineGroupSchemeProperty T).isoMk
      ((Functor.mapGrpNatIso (pullbackSpecMapComp f g) ≪≫ Functor.mapGrpCompIso).app G.obj))
    fun h => (affineGroupSchemeProperty T).ι.map_injective
      ((Functor.mapGrpNatIso (pullbackSpecMapComp f g) ≪≫
        Functor.mapGrpCompIso).hom.naturality h.hom)

/-- The morphism of objects over `Spec T` underlying `(baseChangeFunctorCompIso f g).hom`. -/
@[simp]
lemma baseChangeFunctorCompIso_hom_app_hom_hom_hom (f : R ⟶ S) (g : S ⟶ T)
    (G : AffineGroupSchemeCat R) :
    ((baseChangeFunctorCompIso f g).hom.app G).hom.hom.hom =
      (pullbackSpecMapComp f g).hom.app G.obj.X := by
  simp only [Functor.comp_obj, baseChangeFunctorCompIso, ObjectProperty.isoMk,
    ObjectProperty.homMk, NatIso.trans_app, Iso.trans_hom, Iso.app_hom,
    NatIso.ofComponents_hom_app, Grp.comp', Mon.comp_hom',
    Functor.mapGrpNatIso_hom_app_hom_hom, Functor.mapGrpCompIso_hom_app_hom_hom]
  exact Category.comp_id _

/-- The morphism of objects over `Spec T` underlying `(baseChangeFunctorCompIso f g).inv`. -/
@[simp]
lemma baseChangeFunctorCompIso_inv_app_hom_hom_hom (f : R ⟶ S) (g : S ⟶ T)
    (G : AffineGroupSchemeCat R) :
    ((baseChangeFunctorCompIso f g).inv.app G).hom.hom.hom =
      (pullbackSpecMapComp f g).inv.app G.obj.X := by
  simp only [Functor.comp_obj, baseChangeFunctorCompIso, ObjectProperty.isoMk,
    ObjectProperty.homMk, NatIso.trans_app, Iso.trans_inv, Iso.app_inv,
    NatIso.ofComponents_inv_app, Grp.comp', Mon.comp_hom',
    Functor.mapGrpCompIso_inv_app_hom_hom, Functor.mapGrpNatIso_inv_app_hom_hom]
  exact Category.id_comp _

end AffineGroupSchemeCat

namespace AffineGroupSchemeCat

section HopfSpec

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Pulling the Hopf spectrum of `H` from `Spec R` to `Spec S` gives the Hopf spectrum of the
scalar extension `S ⊗[R] H`, as group objects over `Spec S`.

The underlying scheme isomorphism first exchanges the two legs of the pullback and then applies
the affine comparison `pullbackSpecIso'`. Mathlib proves that this map preserves the unit and
multiplication of the Hopf spectra. -/
noncomputable def hopfSpecBaseChangeGrpIso
    (H : _root_.CommHopfAlgCat.{u} R) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.obj
        ((hopfSpec (CommRingCat.of R)).obj (.op H)) ≅
      (hopfSpec (CommRingCat.of S)).obj
        (.op (CommHopfAlgCat.baseChange (K := S) H)) := by
  let e := Limits.pullbackSymmetry
      (Spec (CommRingCat.of H) ↘ Spec (CommRingCat.of R))
      (Spec (CommRingCat.of S) ↘ Spec (CommRingCat.of R)) ≪≫ pullbackSpecIso' R S H
  let eOver := e.asOver (Spec (CommRingCat.of S))
  refine Grp.mkIso eOver ?_ ?_
  · exact IsMonHom.one_hom (e.hom.asOver (Spec (CommRingCat.of S)))
  · exact IsMonHom.mul_hom (e.hom.asOver (Spec (CommRingCat.of S)))

/-- The underlying scheme map of `hopfSpecBaseChangeGrpIso` is the standard affine pullback
comparison, after exchanging the two pullback legs. -/
@[simp]
lemma hopfSpecBaseChangeGrpIso_hom_hom_hom_left (H : _root_.CommHopfAlgCat.{u} R) :
    (hopfSpecBaseChangeGrpIso H).hom.hom.hom.left =
      (Limits.pullbackSymmetry
        (Spec (CommRingCat.of H) ↘ Spec (CommRingCat.of R))
        (Spec (CommRingCat.of S) ↘ Spec (CommRingCat.of R)) ≪≫
          pullbackSpecIso' R S H).hom := by
  rfl

/-- The inverse underlying scheme map of `hopfSpecBaseChangeGrpIso` is the inverse of the standard
affine pullback comparison. -/
@[simp]
lemma hopfSpecBaseChangeGrpIso_inv_hom_hom_left (H : _root_.CommHopfAlgCat.{u} R) :
    (hopfSpecBaseChangeGrpIso H).inv.hom.hom.left =
      (Limits.pullbackSymmetry
        (Spec (CommRingCat.of H) ↘ Spec (CommRingCat.of R))
        (Spec (CommRingCat.of S) ↘ Spec (CommRingCat.of R)) ≪≫
          pullbackSpecIso' R S H).inv := by
  rfl

/-- Base change of an affine group scheme represented by a commutative Hopf algebra is represented
by the scalar extension of that Hopf algebra. -/
noncomputable def hopfSpecBaseChangeIso (H : _root_.CommHopfAlgCat.{u} R) :
    baseChange (CommRingCat.ofHom (algebraMap R S))
        ((commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor.obj (.op H)) ≅
      (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of S)).functor.obj
        (.op (CommHopfAlgCat.baseChange (K := S) H)) :=
  (affineGroupSchemeProperty (CommRingCat.of S)).isoMk
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.mapIso
        ((commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
          (CommRingCat.of R)).app (.op H)) ≪≫
      hopfSpecBaseChangeGrpIso H ≪≫
      ((commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
        (CommRingCat.of S)).app
          (.op (CommHopfAlgCat.baseChange (K := S) H))).symm)

/-- The underlying group-scheme morphism of `hopfSpecBaseChangeIso` is the composite of the
anti-equivalence comparison at `R`, the direct Hopf-spectrum base-change comparison, and the
inverse anti-equivalence comparison at `S`. -/
@[simp]
lemma hopfSpecBaseChangeIso_hom_hom (H : _root_.CommHopfAlgCat.{u} R) :
    (hopfSpecBaseChangeIso H).hom.hom =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.map
          ((commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
            (CommRingCat.of R)).hom.app (.op H)) ≫
        (hopfSpecBaseChangeGrpIso H).hom ≫
        (commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
          (CommRingCat.of S)).inv.app
            (.op (CommHopfAlgCat.baseChange (K := S) H)) := by
  rfl

/-- The inverse underlying group-scheme morphism of `hopfSpecBaseChangeIso` is the reverse
composite of the three comparison isomorphisms. -/
@[simp]
lemma hopfSpecBaseChangeIso_inv_hom (H : _root_.CommHopfAlgCat.{u} R) :
    (hopfSpecBaseChangeIso H).inv.hom =
      (commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
          (CommRingCat.of S)).hom.app
            (.op (CommHopfAlgCat.baseChange (K := S) H)) ≫
        (hopfSpecBaseChangeGrpIso H).inv ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.map
          ((commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
            (CommRingCat.of R)).inv.app (.op H)) := by
  rfl

end HopfSpec

end AffineGroupSchemeCat

end TauCeti
