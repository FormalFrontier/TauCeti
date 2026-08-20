/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.FiniteType
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.FiniteType

/-!
# Diagonalizable group schemes

For a commutative ring `R` and a finitely generated commutative group `G`, the group algebra
`R[G]` is a finite-type commutative Hopf algebra. Applying relative spectrum gives the affine
group scheme

`D(G) = Spec R[G]`

over `Spec R`. A homomorphism `G ⟶ H` induces the coordinate morphism `R[G] ⟶ R[H]`,
so relative spectrum reverses its direction and gives `D(H) ⟶ D(G)`. This file packages
that assignment as a functor from the opposite of `FGCommGrpCat` to group objects in schemes
over `Spec R`.

Every resulting group scheme is affine and locally of finite type over the base. The functor
is faithful over a nontrivial base and full when the prime spectrum of the base is connected;
these facts are transported from the corresponding coordinate-ring results through the full
subcategory inclusion and Mathlib's fully faithful `hopfSpec` functor. In particular, it is
fully faithful over a base with connected prime spectrum.

The pinned `hopfSpec` construction requires its base ring and Hopf-algebra carrier to lie in
the same universe, so the scheme-level construction here uses `FGCommGrpCat.{u}` over a base
ring in `Type u`.

## Main declarations

* `TauCeti.DiagonalizableGroup.groupScheme`: the affine group scheme `D(G) = Spec R[G]`.
* `TauCeti.DiagonalizableGroup.groupScheme_one_left`,
  `TauCeti.DiagonalizableGroup.groupScheme_mul_left`, and
  `TauCeti.DiagonalizableGroup.groupScheme_inv_left`: the underlying scheme maps of its
  group operations.
* `TauCeti.DiagonalizableGroup.groupSchemeMap`: the contravariant group-scheme morphism
  induced by a homomorphism of finitely generated commutative groups.
* `TauCeti.DiagonalizableGroup.schemeFunctor`: the functor `FGCommGrpCatᵒᵖ ⟶
  Grp (Over (Spec R))`.
* `TauCeti.DiagonalizableGroup.schemeFunctorIsoHopfSpec`: its factorization through the
  coordinate-ring functor and relative spectrum.
* `TauCeti.DiagonalizableGroup.isAffine_groupScheme`: `D(G)` is affine.
* `TauCeti.DiagonalizableGroup.locallyOfFiniteType_groupScheme`: `D(G) ⟶ Spec R` is
  locally of finite type.
* `TauCeti.DiagonalizableGroup.finiteTypeGroupScheme`: `D(G)` bundled as a finite-type affine
  group scheme.
* `TauCeti.DiagonalizableGroup.finiteTypeGroupSchemeIso`: its comparison with the object produced
  by the finite-type Hopf/group-scheme anti-equivalence.
* `TauCeti.DiagonalizableGroup.schemeFunctor_faithful` and
  `TauCeti.DiagonalizableGroup.schemeFunctor_full`: faithfulness over a nontrivial base and
  fullness over a base with connected prime spectrum.
* `TauCeti.DiagonalizableGroup.fullyFaithfulSchemeFunctor`: the resulting fully faithful
  embedding over a base with connected prime spectrum.

## References

Milne, *Algebraic Groups*, Definition 12.7 and Theorems 12.8--12.9, describes diagonalizable
groups and their character groups. The affine group-scheme construction and its full
faithfulness use Mathlib's `AlgebraicGeometry.hopfSpec`; finite generation and the
coordinate-ring fullness and faithfulness are supplied by
`TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.FiniteType`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace DiagonalizableGroup

open AlgebraicGeometry MonObj MonoidalCategory

variable (R : Type u) [CommRing R]

/-- The affine group scheme `D(G) = Spec R[G]` represented by the group algebra of a finitely
generated commutative group `G`.

The same-universe restriction is imposed by Mathlib's current `hopfSpec` construction. -/
noncomputable def groupScheme (G : FGCommGrpCat.{u}) :
    Grp (Over (Spec (CommRingCat.of R))) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
    (Opposite.op (coordinateRing R G).obj)

/-- The diagonalizable group scheme is obtained by applying relative spectrum to its
coordinate Hopf algebra. -/
theorem groupScheme_def (G : FGCommGrpCat.{u}) :
    groupScheme R G =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
        (Opposite.op (coordinateRing R G).obj) := by
  rfl

/-- The scheme underlying `D(G)` is the spectrum of the group algebra `R[G]`. -/
@[simp]
lemma groupScheme_X_left (G : FGCommGrpCat.{u}) :
    (groupScheme R G).X.left = Spec (CommRingCat.of (MonoidAlgebra R G)) := by
  simpa only [groupScheme] using
    hopfSpec_obj_X_left R (coordinateRing R G).obj

/-- After identifying its source with `Spec R[G]`, the structural morphism of `D(G)` is
induced by the group-algebra structure map. -/
@[simp]
lemma groupScheme_X_hom (G : FGCommGrpCat.{u}) :
    (groupScheme R G).X.hom =
      eqToHom (groupScheme_X_left R G) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (MonoidAlgebra R G))) := by
  simpa only [groupScheme] using
    hopfSpec_obj_X_hom R (coordinateRing R G).obj

/-- The source scheme of multiplication on `D(G)` is the fibre product of two copies of
`Spec R[G]` over `Spec R`. -/
@[simp↓]
lemma groupScheme_tensor_X_left (G : FGCommGrpCat.{u}) :
    ((groupScheme R G).X ⊗ (groupScheme R G).X).left =
      Limits.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (MonoidAlgebra R G))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (MonoidAlgebra R G)))) := by
  simpa only [groupScheme] using
    hopfSpec_obj_tensor_X_left R (coordinateRing R G).obj

/-- The unit of `D(G)` is induced by the counit of the group algebra. -/
@[simp]
lemma groupScheme_one_left (G : FGCommGrpCat.{u}) :
    η[(groupScheme R G).X].left =
      Spec.map (CommRingCat.ofHom
        (Bialgebra.counitAlgHom R (MonoidAlgebra R G))) ≫
      eqToHom (groupScheme_X_left R G).symm := by
  unfold groupScheme
  convert hopfSpec_obj_one_left R (coordinateRing R G).obj using 1

/-- Multiplication on `D(G)` is induced by the comultiplication of the group algebra. The
first transport identifies its opaque product source with the standard affine fibre product. -/
@[simp]
lemma groupScheme_mul_left (G : FGCommGrpCat.{u}) :
    μ[(groupScheme R G).X].left =
      eqToHom (groupScheme_tensor_X_left R G) ≫
        (pullbackSpecIso R (MonoidAlgebra R G) (MonoidAlgebra R G)).hom ≫
        Spec.map (CommRingCat.ofHom
          (Bialgebra.comulAlgHom R (MonoidAlgebra R G))) ≫
        eqToHom (groupScheme_X_left R G).symm := by
  unfold groupScheme
  convert hopfSpec_obj_mul_left R (coordinateRing R G).obj using 1

/-- Inversion on `D(G)` is induced by the antipode of the group algebra. -/
@[simp]
lemma groupScheme_inv_left (G : FGCommGrpCat.{u}) :
    ι[(groupScheme R G).X].left =
      eqToHom (groupScheme_X_left R G) ≫
      Spec.map (CommRingCat.ofHom
        (HopfAlgebra.antipodeAlgHom R (MonoidAlgebra R G)).toRingHom) ≫
      eqToHom (groupScheme_X_left R G).symm := by
  unfold groupScheme
  convert hopfSpec_obj_inv_left R (coordinateRing R G).obj using 1

/-- A homomorphism `G ⟶ H` induces the contravariant group-scheme morphism
`D(H) ⟶ D(G)`. -/
noncomputable def groupSchemeMap {G H : FGCommGrpCat.{u}} (f : G ⟶ H) :
    groupScheme R H ⟶ groupScheme R G :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (coordinateMap R f).hom.op

/-- The morphism of diagonalizable group schemes is obtained by applying relative spectrum to
the coordinate Hopf-algebra morphism. -/
theorem groupSchemeMap_def {G H : FGCommGrpCat.{u}} (f : G ⟶ H) :
    groupSchemeMap R f =
      eqToHom (groupScheme_def R H) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (coordinateMap R f).hom.op ≫
        eqToHom (groupScheme_def R G).symm := by
  apply (conj_eqToHom_iff_heq _ _
    (groupScheme_def R H) (groupScheme_def R G)).2
  unfold groupSchemeMap
  rfl

/-- Under the identifications of its source and target with spectra, the scheme morphism
underlying `groupSchemeMap f` is induced by the coordinate Hopf-algebra morphism
`R[G] ⟶ R[H]`. -/
@[simp]
lemma groupSchemeMap_hom_left {G H : FGCommGrpCat.{u}} (f : G ⟶ H) :
    (groupSchemeMap R f).hom.hom.left =
      eqToHom (groupScheme_X_left R H) ≫
        Spec.map (CommRingCat.ofHom
          (FiniteTypeCommHopfAlgCat.toBialgHom (coordinateMap R f)).toAlgHom.toRingHom) ≫
        eqToHom (groupScheme_X_left R G).symm := by
  apply (conj_eqToHom_iff_heq _ _
    (groupScheme_X_left R H) (groupScheme_X_left R G)).2
  unfold groupSchemeMap
  -- `hopfSpec` is `(commHopfAlgCatEquivCogrpCommAlgCat R).functor.leftOp ⋙ (algSpec R).mapGrp`,
  -- so these two computation lemmas reduce the morphism to an `algSpec` image. Identifying that
  -- image with the coordinate algebra morphism is definitional: unlike its bialgebra counterpart
  -- `commBialgCatEquivComonCommAlgCat_functor_map_unop_hom`, the Hopf-algebra equivalence has no
  -- computation lemma for its morphism component.
  rw [Functor.comp_map, Functor.mapGrp_map_hom_hom]
  exact heq_of_eq (algSpec_map_left_ofAlgHom R
    (FiniteTypeCommHopfAlgCat.toBialgHom (coordinateMap R f)).toAlgHom)

/-- The group-scheme morphism induced by the identity homomorphism is the identity. -/
@[simp]
theorem groupSchemeMap_id (G : FGCommGrpCat.{u}) :
    groupSchemeMap R (𝟙 G) = 𝟙 (groupScheme R G) := by
  have h := congrArg
    (fun k : coordinateRing R G ⟶ coordinateRing R G ↦ k.hom.op)
    ((coordinateRingFunctor R).map_id G)
  simp only [coordinateRingFunctor_obj, coordinateRingFunctor_map,
    ObjectProperty.FullSubcategory.id_hom, op_id] at h
  unfold groupSchemeMap
  rw [h]
  simpa only [groupScheme] using
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map_id
      (Opposite.op (coordinateRing R G).obj)

/-- Composition of group homomorphisms becomes composition in the reverse order on their
diagonalizable group schemes. -/
@[simp]
theorem groupSchemeMap_comp {G H K : FGCommGrpCat.{u}} (f : G ⟶ H) (g : H ⟶ K) :
    groupSchemeMap R (f ≫ g) = groupSchemeMap R g ≫ groupSchemeMap R f := by
  have h := congrArg
    (fun k : coordinateRing R G ⟶ coordinateRing R K ↦ k.hom.op)
    ((coordinateRingFunctor R).map_comp f g)
  simp only [coordinateRingFunctor_obj, coordinateRingFunctor_map,
    ObjectProperty.FullSubcategory.comp_hom, op_comp] at h
  unfold groupSchemeMap
  rw [h, Functor.map_comp]
  rfl

/-- The diagonalizable group-scheme functor. It is contravariant in finitely generated
commutative groups and covariant on their opposite category. -/
noncomputable def schemeFunctor :
    (FGCommGrpCat.{u})ᵒᵖ ⥤ Grp (Over (Spec (CommRingCat.of R))) :=
  (coordinateRingFunctor R).op ⋙
    (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} R)
      (_root_.CommHopfAlgCat.{u} R)).op ⋙
    AlgebraicGeometry.hopfSpec (CommRingCat.of R)

/-- The diagonalizable group-scheme functor is the composite of the opposite coordinate-ring
functor, the inclusion from finite-type to unrestricted commutative Hopf algebras, and relative
spectrum. This is the categorical interface for factoring `schemeFunctor` without unfolding its
implementation. -/
noncomputable def schemeFunctorIsoHopfSpec :
    schemeFunctor R ≅
      (coordinateRingFunctor R).op ⋙
        (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} R)
          (_root_.CommHopfAlgCat.{u} R)).op ⋙
        AlgebraicGeometry.hopfSpec (CommRingCat.of R) :=
  Iso.refl _

/-- On objects, the diagonalizable group-scheme functor is `G ↦ Spec R[G]`. -/
@[simp]
theorem schemeFunctor_obj (G : (FGCommGrpCat.{u})ᵒᵖ) :
    (schemeFunctor R).obj G = groupScheme R G.unop :=
  -- Keep the defining reduction local, so both public definitions stay opaque to importers.
  by
    unfold schemeFunctor groupScheme
    rfl

/-- On morphisms, the diagonalizable group-scheme functor applies relative spectrum to the
coordinate map, reversing its direction. The object equalities transport the map between the
public descriptions of its source and target. -/
@[simp]
theorem schemeFunctor_map {G H : (FGCommGrpCat.{u})ᵒᵖ} (f : G ⟶ H) :
    (schemeFunctor R).map f =
      eqToHom (schemeFunctor_obj R G) ≫ groupSchemeMap R f.unop ≫
        eqToHom (schemeFunctor_obj R H).symm := by
  apply (conj_eqToHom_iff_heq _ _ (schemeFunctor_obj R G) (schemeFunctor_obj R H)).2
  unfold schemeFunctor groupSchemeMap
  simp only [Functor.comp_obj, Functor.comp_map, Functor.op_obj, Functor.op_map,
    coordinateRingFunctor_obj, coordinateRingFunctor_map]
  rw [Quiver.Hom.unop_op, FiniteTypeCommHopfAlgCat.forget₂_commHopfAlgCat_map]
  rfl

/-- Every diagonalizable group scheme `D(G)` constructed here is affine. -/
instance isAffine_groupScheme (G : FGCommGrpCat.{u}) :
    IsAffine (groupScheme R G).X.left := by
  rw [groupScheme_X_left]
  exact AlgebraicGeometry.isAffine_Spec _

/-- The structural morphism `D(G) ⟶ Spec R` is locally of finite type. -/
instance locallyOfFiniteType_groupScheme (G : FGCommGrpCat.{u}) :
    LocallyOfFiniteType (groupScheme R G).X.hom := by
  let : Algebra.FiniteType R (MonoidAlgebra R G) := (coordinateRing R G).property
  rw [groupScheme_X_hom]
  let : LocallyOfFiniteType (eqToHom (groupScheme_X_left R G)) :=
    locallyOfFiniteType_of_isOpenImmersion _
  let : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap R (MonoidAlgebra R G)))) := by
    rw [← AlgebraicGeometry.specOverSpec_over]
    infer_instance
  exact locallyOfFiniteType_comp _ _

/-- The diagonalizable group scheme `D(G)` bundled as a finite-type affine group scheme. -/
noncomputable def finiteTypeGroupScheme (G : FGCommGrpCat.{u}) :
    FiniteTypeAffineGroupSchemeCat (CommRingCat.of R) :=
  ⟨⟨groupScheme R G, (affineGroupSchemeProperty_iff _).2 inferInstance⟩,
    (finiteTypeAffineGroupSchemeProperty_iff _ _).2
      (locallyOfFiniteType_groupScheme R G)⟩

/-- The underlying group scheme of the bundled finite-type `D(G)` is `groupScheme R G`. -/
@[simp]
theorem finiteTypeGroupScheme_obj_obj (G : FGCommGrpCat.{u}) :
    (finiteTypeGroupScheme R G).obj.obj = groupScheme R G := by
  rfl

/-- The finite-type Hopf/group-scheme anti-equivalence sends the coordinate ring `R[G]` to the
bundled diagonalizable group scheme `D(G)`. -/
noncomputable def finiteTypeGroupSchemeIso (G : FGCommGrpCat.{u}) :
    (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat R).functor.obj
        (Opposite.op (coordinateRing R G)) ≅
      finiteTypeGroupScheme R G :=
  finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat.functorObjIso R
      (Opposite.op (coordinateRing R G)) ≪≫
    (finiteTypeAffineGroupSchemeProperty (CommRingCat.of R)).ι.preimageIso
      ((affineGroupSchemeProperty (CommRingCat.of R)).ι.preimageIso
        (eqToIso (groupScheme_def R G).symm))

/-- Every object produced by the diagonalizable group-scheme functor is affine. -/
instance isAffine_schemeFunctor_obj (G : (FGCommGrpCat.{u})ᵒᵖ) :
    IsAffine ((schemeFunctor R).obj G).X.left := by
  rw [schemeFunctor_obj]
  infer_instance

/-- Every structural morphism produced by the diagonalizable group-scheme functor is locally
of finite type. -/
instance locallyOfFiniteType_schemeFunctor_obj (G : (FGCommGrpCat.{u})ᵒᵖ) :
    LocallyOfFiniteType ((schemeFunctor R).obj G).X.hom := by
  rw [schemeFunctor_obj]
  infer_instance

/-- The diagonalizable group-scheme functor is faithful over a nontrivial base ring. -/
noncomputable instance schemeFunctor_faithful [Nontrivial R] :
    (schemeFunctor R).Faithful := by
  let : (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).Faithful :=
    (AlgebraicGeometry.hopfSpec.fullyFaithful (R := CommRingCat.of R)).faithful
  unfold schemeFunctor
  infer_instance

/-- The diagonalizable group-scheme functor is full when the prime spectrum of the base is
connected. -/
noncomputable instance schemeFunctor_full [ConnectedSpace (PrimeSpectrum R)] :
    (schemeFunctor R).Full := by
  let : (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} R)
      (_root_.CommHopfAlgCat.{u} R)).op.Full :=
    (finiteTypeCommHopfAlgProperty (R := R)).fullyFaithfulι.op.full
  let : (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).Full :=
    (AlgebraicGeometry.hopfSpec.fullyFaithful (R := CommRingCat.of R)).full
  unfold schemeFunctor
  infer_instance

/-- Over a base with connected prime spectrum, the diagonalizable group-scheme functor is
fully faithful. Connectedness includes nonemptiness, hence supplies the nontriviality needed
for faithfulness. -/
noncomputable def fullyFaithfulSchemeFunctor [ConnectedSpace (PrimeSpectrum R)] :
    (schemeFunctor R).FullyFaithful := by
  letI : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  exact Functor.FullyFaithful.ofFullyFaithful _

end DiagonalizableGroup

end TauCeti
