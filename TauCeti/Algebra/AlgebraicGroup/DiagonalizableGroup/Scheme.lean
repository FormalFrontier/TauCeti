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
* `TauCeti.DiagonalizableGroup.schemeFunctor_fullyFaithful`: the resulting fully faithful
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

open AlgebraicGeometry

variable (R : Type u) [CommRing R]

/-- The affine group scheme `D(G) = Spec R[G]` represented by the group algebra of a finitely
generated commutative group `G`.

The same-universe restriction is imposed by Mathlib's current `hopfSpec` construction. -/
noncomputable abbrev groupScheme (G : FGCommGrpCat.{u}) :
    Grp (Over (Spec (CommRingCat.of R))) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
    (Opposite.op (coordinateRing R G).obj)

/-- A homomorphism `G ⟶ H` induces the contravariant group-scheme morphism
`D(H) ⟶ D(G)`. -/
noncomputable def groupSchemeMap {G H : FGCommGrpCat.{u}} (f : G ⟶ H) :
    groupScheme R H ⟶ groupScheme R G :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (coordinateMap R f).hom.op

/-- The scheme morphism underlying `groupSchemeMap f` is the spectrum map induced by the
coordinate Hopf-algebra morphism `R[G] ⟶ R[H]`. -/
@[simp]
lemma groupSchemeMap_hom_left {G H : FGCommGrpCat.{u}} (f : G ⟶ H) :
    (groupSchemeMap R f).hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (FiniteTypeCommHopfAlgCat.toBialgHom (coordinateMap R f)).toAlgHom.toRingHom) := by
  rw [groupSchemeMap]
  rfl

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
  -- Parentheses keep this defining reduction local, so `schemeFunctor` stays opaque to importers.
  (rfl)

/-- On morphisms, the diagonalizable group-scheme functor applies relative spectrum to the
coordinate map, reversing its direction. The object equalities transport the map between the
public descriptions of its source and target. -/
@[simp]
theorem schemeFunctor_map {G H : (FGCommGrpCat.{u})ᵒᵖ} (f : G ⟶ H) :
    (schemeFunctor R).map f =
      eqToHom (schemeFunctor_obj R G) ≫ groupSchemeMap R f.unop ≫
        eqToHom (schemeFunctor_obj R H).symm :=
  (by
    apply (conj_eqToHom_iff_heq _ _ (schemeFunctor_obj R G) (schemeFunctor_obj R H)).2
    unfold schemeFunctor groupSchemeMap
    simp only [Functor.comp_obj, Functor.comp_map, Functor.op_obj, Functor.op_map,
      coordinateRingFunctor_obj, coordinateRingFunctor_map]
    rw [Quiver.Hom.unop_op, FiniteTypeCommHopfAlgCat.forget₂_commHopfAlgCat_map])

/-- Every diagonalizable group scheme `D(G)` constructed here is affine. -/
instance isAffine_groupScheme (G : FGCommGrpCat.{u}) :
    IsAffine (groupScheme R G).X.left := by
  exact AlgebraicGeometry.isAffine_Spec _

/-- The structural morphism `D(G) ⟶ Spec R` is locally of finite type. -/
instance locallyOfFiniteType_groupScheme (G : FGCommGrpCat.{u}) :
    LocallyOfFiniteType (groupScheme R G).X.hom := by
  letI : Algebra.FiniteType R (MonoidAlgebra R G) := (coordinateRing R G).property
  -- As for other uses of `hopfSpec`, `change` selects the `specOverSpec` instance path
  -- compatible with the finite-type coordinate algebra.
  change LocallyOfFiniteType
    (Spec (CommRingCat.of (MonoidAlgebra R G)) ↘ Spec (CommRingCat.of R))
  infer_instance

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
  letI : (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} R)
      (_root_.CommHopfAlgCat.{u} R)).op.Faithful :=
    (finiteTypeCommHopfAlgProperty (R := R)).fullyFaithfulι.op.faithful
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
noncomputable def schemeFunctor_fullyFaithful [ConnectedSpace (PrimeSpectrum R)] :
    (schemeFunctor R).FullyFaithful := by
  letI : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  exact Functor.FullyFaithful.ofFullyFaithful _

end DiagonalizableGroup

end TauCeti
