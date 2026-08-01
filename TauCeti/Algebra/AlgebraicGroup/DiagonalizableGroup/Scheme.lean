/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.FiniteType

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
* `TauCeti.DiagonalizableGroup.isAffine_groupScheme`: `D(G)` is affine.
* `TauCeti.DiagonalizableGroup.locallyOfFiniteType_groupScheme`: `D(G) ⟶ Spec R` is
  locally of finite type.
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

/-- The scheme underlying `D(G)` is the spectrum of the group algebra `R[G]`. -/
@[simp]
lemma groupScheme_X_left (G : FGCommGrpCat.{u}) :
    (groupScheme R G).X.left = Spec (CommRingCat.of (MonoidAlgebra R G)) := by
  unfold groupScheme
  rfl

/-- After identifying its source with `Spec R[G]`, the structural morphism of `D(G)` is
induced by the group-algebra structure map. -/
@[simp]
lemma groupScheme_X_hom (G : FGCommGrpCat.{u}) :
    (groupScheme R G).X.hom =
      eqToHom (groupScheme_X_left R G) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (MonoidAlgebra R G))) := by
  simpa only [eqToHom_refl, Category.comp_id] using
    (conj_eqToHom_iff_heq
      (groupScheme R G).X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R (MonoidAlgebra R G))))
      (groupScheme_X_left R G) rfl).2 (by
        unfold groupScheme
        exact heq_of_eq (AlgebraicGeometry.algSpec_obj_hom
          (R := CommRingCat.of R)
          (Opposite.op (CommAlgCat.of R (MonoidAlgebra R G)))))

/-- The source scheme of multiplication on `D(G)` is the fibre product of two copies of
`Spec R[G]` over `Spec R`. -/
@[simp↓]
lemma groupScheme_tensor_X_left (G : FGCommGrpCat.{u}) :
    ((groupScheme R G).X ⊗ (groupScheme R G).X).left =
      Limits.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (MonoidAlgebra R G))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (MonoidAlgebra R G)))) := by
  rw [Over.tensorObj_left]
  have h : (groupScheme R G).X.hom ≍
      Spec.map (CommRingCat.ofHom (algebraMap R (MonoidAlgebra R G))) := by
    rw [groupScheme_X_hom]
    exact eqToHom_comp_heq _ _
  cases groupScheme_X_left R G
  exact congrArg (fun k ↦ Limits.pullback k k) (eq_of_heq h)

/-- Specialize Mathlib's `algSpec_map_left` computation to an explicit algebra morphism.

This is the sole boundary where the `CommAlgCat`/under-category wrapper left in that public
computation lemma is reduced: `algSpec_map_left` phrases its answer through
`(commAlgCatEquivUnder R).functor.map`, and Mathlib provides no computation lemma for the
`Under.Hom.right` of that morphism, so the last step is definitional. Keeping it here avoids
proof-sensitive reductions at the public projection lemmas below. -/
private lemma algSpec_map_left_ofAlgHom {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    ((AlgebraicGeometry.algSpec (CommRingCat.of R)).map
      (CommAlgCat.ofHom f).op).left =
        Spec.map (CommRingCat.ofHom f.toRingHom) := by
  rw [AlgebraicGeometry.algSpec_map_left]
  rfl

/-- `D(G)` is Mathlib's group object `(Spec R[G]).asOver (Spec R)`.

`hopfSpec` builds `D(G)` as the `algSpec`-image of the cogroup algebra `R[G]`, and Mathlib's
`AlgebraicGeometry.instGrpObjSpecAsOverSpec` is defined to be exactly that image, so the two
group objects are equal by definition. Mathlib has no lemma identifying the two instance paths:
its computation lemmas for the operations of a functor image (`Functor.mapGrp_obj_grp_mul`,
`Functor.obj.ι_def`) are keyed on the `Functor.grpObjObj` instance, which `rw` cannot see
through the bundled `Grp` object here. This lemma is therefore the single place where that
identification is made, and the operation computations below rewrite with it instead of
reducing `hopfSpec` themselves. -/
private lemma groupScheme_eq_asOver (G : FGCommGrpCat.{u}) :
    groupScheme R G =
      Grp.mk ((Spec (CommRingCat.of (MonoidAlgebra R G))).asOver (Spec (CommRingCat.of R))) :=
  rfl

/-- The unit of `D(G)` is induced by the counit of the group algebra. -/
@[simp]
lemma groupScheme_one_left (G : FGCommGrpCat.{u}) :
    η[(groupScheme R G).X].left =
      Spec.map (CommRingCat.ofHom
        (Bialgebra.counitAlgHom R (MonoidAlgebra R G))) ≫
      eqToHom (groupScheme_X_left R G).symm := by
  simpa only [eqToHom_refl, Category.id_comp] using
    (conj_eqToHom_iff_heq
      η[(groupScheme R G).X].left
      (Spec.map (CommRingCat.ofHom
        (Bialgebra.counitAlgHom R (MonoidAlgebra R G))))
      rfl (groupScheme_X_left R G)).2 (by
        rw [groupScheme_eq_asOver]
        exact heq_of_eq (AlgebraicGeometry.one_spec_asOver_spec_left
          (R := CommRingCat.of R) (A := CommRingCat.of (MonoidAlgebra R G))))

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
  simpa only [Category.assoc] using
    (conj_eqToHom_iff_heq
      μ[(groupScheme R G).X].left
      ((pullbackSpecIso R (MonoidAlgebra R G) (MonoidAlgebra R G)).hom ≫
        Spec.map (CommRingCat.ofHom
          (Bialgebra.comulAlgHom R (MonoidAlgebra R G))))
      (groupScheme_tensor_X_left R G) (groupScheme_X_left R G)).2 (by
        rw [groupScheme_eq_asOver]
        exact heq_of_eq (AlgebraicGeometry.mul_spec_asOver_spec_left
          (R := CommRingCat.of R) (A := CommRingCat.of (MonoidAlgebra R G))))

/-- Inversion on `D(G)` is induced by the antipode of the group algebra. -/
@[simp]
lemma groupScheme_inv_left (G : FGCommGrpCat.{u}) :
    ι[(groupScheme R G).X].left =
      eqToHom (groupScheme_X_left R G) ≫
      Spec.map (CommRingCat.ofHom
        (HopfAlgebra.antipodeAlgHom R (MonoidAlgebra R G)).toRingHom) ≫
      eqToHom (groupScheme_X_left R G).symm := by
  apply (conj_eqToHom_iff_heq _ _
    (groupScheme_X_left R G) (groupScheme_X_left R G)).2
  -- Mathlib computes the unit and the multiplication of `(Spec A).asOver (Spec R)` but not its
  -- inverse, which is the `algSpec`-image of the antipode; `algSpec_map_left_ofAlgHom` turns
  -- that image into the expected `Spec.map`.
  rw [groupScheme_eq_asOver]
  exact heq_of_eq (algSpec_map_left_ofAlgHom R
    (HopfAlgebra.antipodeAlgHom R (MonoidAlgebra R G)))

/-- A homomorphism `G ⟶ H` induces the contravariant group-scheme morphism
`D(H) ⟶ D(G)`. -/
noncomputable def groupSchemeMap {G H : FGCommGrpCat.{u}} (f : G ⟶ H) :
    groupScheme R H ⟶ groupScheme R G :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (coordinateMap R f).hom.op

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
  letI : Algebra.FiniteType R (MonoidAlgebra R G) := (coordinateRing R G).property
  rw [groupScheme_X_hom]
  letI : LocallyOfFiniteType (eqToHom (groupScheme_X_left R G)) :=
    locallyOfFiniteType_of_isOpenImmersion _
  letI : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap R (MonoidAlgebra R G)))) := by
    -- `change` selects the `specOverSpec` instance path compatible with the finite-type
    -- coordinate algebra.
    change LocallyOfFiniteType
      (Spec (CommRingCat.of (MonoidAlgebra R G)) ↘ Spec (CommRingCat.of R))
    infer_instance
  exact locallyOfFiniteType_comp _ _

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
  letI : (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).Faithful :=
    (AlgebraicGeometry.hopfSpec.fullyFaithful (R := CommRingCat.of R)).faithful
  unfold schemeFunctor
  infer_instance

/-- The diagonalizable group-scheme functor is full when the prime spectrum of the base is
connected. -/
noncomputable instance schemeFunctor_full [ConnectedSpace (PrimeSpectrum R)] :
    (schemeFunctor R).Full := by
  letI : (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} R)
      (_root_.CommHopfAlgCat.{u} R)).op.Full :=
    (finiteTypeCommHopfAlgProperty (R := R)).fullyFaithfulι.op.full
  letI : (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).Full :=
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
