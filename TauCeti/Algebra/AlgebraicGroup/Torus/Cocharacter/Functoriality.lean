/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Torus.CharacterLattice.Functoriality
public import TauCeti.Algebra.AlgebraicGroup.Torus.Cocharacter.Basic
public import TauCeti.RepresentationTheory.GaloisLattice.Dual

/-!
# The cocharacter-lattice functor of tori

A morphism of coordinate Hopf algebras sends geometric characters forward. Precomposition with
that character map sends integral duals backward, and hence gives the contravariant map on
geometric cocharacters. This file proves that these maps are equivariant for the contragredient
absolute-Galois actions and assembles them into a functor from the opposite of the category of
torus coordinate rings to integral Galois lattices.

The character--cocharacter pairing is natural for these two variance conventions. Thus the two
lattice functors supply the functorial perfect pairing needed to form root data from a split pair.

## Main declarations

* `TauCeti.MultiplicativeTypeCommHopfAlgCat.cocharacterMap`: the contravariant map on geometric
  cocharacters induced by a coordinate Hopf-algebra morphism.
* `TauCeti.TorusCommHopfAlgCat.cocharacterLatticeFunctor`: the cocharacter-lattice functor from
  the opposite category of torus coordinate rings to integral Galois lattices.
* `TauCeti.MultiplicativeTypeCommHopfAlgCat.characterCocharacterPairing_map`: naturality of the
  perfect character--cocharacter pairing.

## References

See J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17, Theorem 12.23, and
Corollary 12.24.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace MultiplicativeTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- The contravariant map on geometric cocharacters induced by a morphism of coordinate Hopf
algebras. Under `X_*(T) ≃ Hom_ℤ(X^*(T), ℤ)`, it is precomposition with the covariant map
on geometric characters. -/
noncomputable def cocharacterMap {S T : MultiplicativeTypeCommHopfAlgCat k} (f : S ⟶ T) :
    cocharacterLattice T →ₗ[ℤ] cocharacterLattice S :=
  (cocharacterLatticeLinearEquivDual S).symm.toLinearMap.comp <|
    (CommHopfAlgCat.additiveCharacterMap f.hom.hom).dualMap.comp
      (cocharacterLatticeLinearEquivDual T).toLinearMap

/-- Mapping a cocharacter means precomposing its corresponding character functional with the
map on characters. -/
@[simp]
theorem cocharacterLatticeLinearEquivDual_cocharacterMap_apply
    {S T : MultiplicativeTypeCommHopfAlgCat k} (f : S ⟶ T) (y : cocharacterLattice T)
    (x : CommHopfAlgCat.additiveCharacterGroup S.obj.obj) :
    cocharacterLatticeLinearEquivDual S (cocharacterMap f y) x =
      cocharacterLatticeLinearEquivDual T y
        (CommHopfAlgCat.additiveCharacterMap f.hom.hom x) := by
  simp [cocharacterMap, LinearMap.dualMap_apply]

/-- The identity coordinate morphism induces the identity on cocharacters. -/
@[simp]
theorem cocharacterMap_id (T : MultiplicativeTypeCommHopfAlgCat k) :
    cocharacterMap (𝟙 T) = LinearMap.id := by
  apply LinearMap.ext
  intro y
  apply (cocharacterLatticeLinearEquivDual T).injective
  apply LinearMap.ext
  intro x
  simp

/-- Cocharacter maps reverse composition of coordinate morphisms. -/
@[simp]
theorem cocharacterMap_comp {S T U : MultiplicativeTypeCommHopfAlgCat k}
    (f : S ⟶ T) (g : T ⟶ U) :
    cocharacterMap (f ≫ g) = cocharacterMap f ∘ₗ cocharacterMap g := by
  apply LinearMap.ext
  intro y
  apply (cocharacterLatticeLinearEquivDual S).injective
  apply LinearMap.ext
  intro x
  simp

/-- The map on cocharacters is equivariant for the contragredient absolute-Galois actions. -/
@[simp]
theorem cocharacterMap_smul
    {S T : MultiplicativeTypeCommHopfAlgCat k} (f : S ⟶ T)
    (σ : Field.absoluteGaloisGroup k) (y : cocharacterLattice T) :
    cocharacterMap f (cocharacterGaloisRepresentation T σ y) =
      cocharacterGaloisRepresentation S σ (cocharacterMap f y) := by
  apply (cocharacterLatticeLinearEquivDual S).injective
  apply LinearMap.ext
  intro x
  rw [cocharacterLatticeLinearEquivDual_cocharacterMap_apply,
    cocharacterGaloisRepresentation_apply_apply,
    cocharacterGaloisRepresentation_apply_apply,
    cocharacterLatticeLinearEquivDual_cocharacterMap_apply,
    CommHopfAlgCat.additiveCharacterMap_smul]

/-- The character--cocharacter pairing is natural: mapping a character covariantly or mapping a
cocharacter contravariantly gives the same integer. -/
theorem characterCocharacterPairing_map {S T : MultiplicativeTypeCommHopfAlgCat k} (f : S ⟶ T)
    (x : CommHopfAlgCat.additiveCharacterGroup S.obj.obj) (y : cocharacterLattice T) :
    characterCocharacterPairing T (CommHopfAlgCat.additiveCharacterMap f.hom.hom x) y =
      characterCocharacterPairing S x (cocharacterMap f y) := by
  simp

end MultiplicativeTypeCommHopfAlgCat

namespace TorusCommHopfAlgCat

variable {k : Type u} [Field k]

/-- A morphism of torus coordinate rings, regarded as a morphism of coordinate rings of groups
of multiplicative type. -/
noncomputable abbrev toMultiplicativeTypeMap {S T : TorusCommHopfAlgCat k} (f : S ⟶ T) :
    toMultiplicativeTypeCommHopfAlgCat S ⟶ toMultiplicativeTypeCommHopfAlgCat T :=
  ObjectProperty.homMk f.hom

/-- The geometric cocharacter lattice of a torus with its contragredient absolute-Galois
representation. -/
noncomputable abbrev cocharacterLatticeRepresentation (T : TorusCommHopfAlgCat k) :
    Rep.{u} ℤ (Field.absoluteGaloisGroup k) :=
  Rep.of (MultiplicativeTypeCommHopfAlgCat.cocharacterGaloisRepresentation
    (toMultiplicativeTypeCommHopfAlgCat T))

/-- The cocharacter representation of a torus is a continuous integral Galois lattice. -/
private theorem cocharacterLatticeFunctor_mem (T : TorusCommHopfAlgCat k) :
    galoisLatticeProperty k (cocharacterLatticeRepresentation T) := by
  let _ : Module.Free ℤ (CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :=
    characterLattice_module_free_of_torus k T.obj T.property
  let _ : Module.Finite ℤ (CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :=
    characterLattice_module_finite_of_torus k T.obj T.property
  apply galoisLatticeProperty_contragredient
    (Representation.ofMulDistribMulAction (Field.absoluteGaloisGroup k)
      (CommHopfAlgCat.geometricCharacterGroup T.obj.obj))
    (MultiplicativeTypeCommHopfAlgCat.cocharacterGaloisRepresentation
      (toMultiplicativeTypeCommHopfAlgCat T))
    (MultiplicativeTypeCommHopfAlgCat.cocharacterLatticeLinearEquivDual
      (toMultiplicativeTypeCommHopfAlgCat T))
  · intro σ y x
    rw [MultiplicativeTypeCommHopfAlgCat.cocharacterGaloisRepresentation_apply_apply]
    rfl
  · intro x
    -- The generic continuity theorem states the goal through a representation, while the existing
    -- character theorem is phrased as openness of the corresponding action stabilizer.
    change IsOpen (↑(MulAction.stabilizer (Field.absoluteGaloisGroup k) x) :
      Set (Field.absoluteGaloisGroup k))
    exact CommHopfAlgCat.stabilizer_additiveGroupLike_isOpen x

/-- The equivariant map from the cocharacter representation of the target torus to that of the
source torus. -/
noncomputable def cocharacterLatticeRepresentationMap
    {S T : TorusCommHopfAlgCat k} (f : S ⟶ T) :
    cocharacterLatticeRepresentation T ⟶ cocharacterLatticeRepresentation S :=
  Rep.ofHom {
    toLinearMap := MultiplicativeTypeCommHopfAlgCat.cocharacterMap
      (toMultiplicativeTypeMap f)
    isIntertwining' := fun σ ↦ by
      apply LinearMap.ext
      intro y
      exact MultiplicativeTypeCommHopfAlgCat.cocharacterMap_smul
        (toMultiplicativeTypeMap f) σ y
  }

/-- Evaluation of the equivariant morphism induced on geometric cocharacters. -/
@[simp]
theorem cocharacterLatticeRepresentationMap_hom_apply
    {S T : TorusCommHopfAlgCat k} (f : S ⟶ T)
    (y : MultiplicativeTypeCommHopfAlgCat.cocharacterLattice
      (toMultiplicativeTypeCommHopfAlgCat T)) :
    (cocharacterLatticeRepresentationMap f).hom y =
      MultiplicativeTypeCommHopfAlgCat.cocharacterMap (toMultiplicativeTypeMap f) y := by
  rfl

/-- Cocharacter lattices and their Galois actions form a contravariant functor on coordinate
Hopf algebras of tori. -/
private noncomputable def cocharacterLatticeRepresentationFunctor :
    (TorusCommHopfAlgCat k)ᵒᵖ ⥤ Rep.{u} ℤ (Field.absoluteGaloisGroup k) where
  obj T := cocharacterLatticeRepresentation T.unop
  map f := cocharacterLatticeRepresentationMap f.unop
  map_id T := by
    apply Rep.hom_ext
    exact Representation.IntertwiningMap.ext
      (MultiplicativeTypeCommHopfAlgCat.cocharacterMap_id
        (toMultiplicativeTypeCommHopfAlgCat T.unop))
  map_comp f g := by
    apply Rep.hom_ext
    exact Representation.IntertwiningMap.ext
      (MultiplicativeTypeCommHopfAlgCat.cocharacterMap_comp
        (toMultiplicativeTypeMap g.unop) (toMultiplicativeTypeMap f.unop))

/-- The cocharacter-lattice functor from coordinate Hopf algebras of tori, contravariant as a
functor on coordinate rings, to continuous integral Galois lattices. -/
noncomputable def cocharacterLatticeFunctor :
    (TorusCommHopfAlgCat k)ᵒᵖ ⥤ GaloisLatticeCat k :=
  (galoisLatticeProperty k).lift cocharacterLatticeRepresentationFunctor
    (fun T ↦ cocharacterLatticeFunctor_mem T.unop)

/-- The object part of the cocharacter-lattice functor is the geometric cocharacter lattice with
its contragredient Galois action. -/
@[simp]
theorem cocharacterLatticeFunctor_obj_obj (T : (TorusCommHopfAlgCat k)ᵒᵖ) :
    ((cocharacterLatticeFunctor (k := k)).obj T).obj =
      cocharacterLatticeRepresentation T.unop := by
  -- Expose the full-subcategory inclusion so the generic object formula for `ObjectProperty.lift`
  -- applies without unfolding the Galois-lattice predicate.
  change (galoisLatticeProperty k).ι.obj
      ((cocharacterLatticeFunctor (k := k)).obj T) = _
  calc
    _ = cocharacterLatticeRepresentationFunctor.obj T := by
      simpa only [cocharacterLatticeFunctor] using
        ObjectProperty.ι_obj_lift_obj (galoisLatticeProperty k)
          cocharacterLatticeRepresentationFunctor
          (fun T ↦ cocharacterLatticeFunctor_mem T.unop) T
    _ = _ := rfl

/-- The map part of the cocharacter-lattice functor is the dual of the corresponding character
map, transported to geometric cocharacters. -/
@[simp]
theorem cocharacterLatticeFunctor_map_hom
    {S T : (TorusCommHopfAlgCat k)ᵒᵖ} (f : S ⟶ T) :
    ((cocharacterLatticeFunctor (k := k)).map f).hom =
      eqToHom (cocharacterLatticeFunctor_obj_obj S) ≫
        cocharacterLatticeRepresentationMap f.unop ≫
          eqToHom (cocharacterLatticeFunctor_obj_obj T).symm := by
  have hlift : ((cocharacterLatticeFunctor (k := k)).map f).hom =
      cocharacterLatticeRepresentationFunctor.map f := by
    simpa only [cocharacterLatticeFunctor, ObjectProperty.ι_map] using
      ObjectProperty.ι_obj_lift_map (galoisLatticeProperty k)
        cocharacterLatticeRepresentationFunctor
        (fun T ↦ cocharacterLatticeFunctor_mem T.unop) f
  rw [hlift]
  -- The remaining equality only erases the propositionally irrelevant object transports inserted
  -- by the lifted functor.
  rfl

/-- Evaluation of the cocharacter-lattice functor on a morphism of torus coordinate rings. -/
theorem cocharacterLatticeFunctor_map_hom_apply
    {S T : TorusCommHopfAlgCat k} (f : S ⟶ T)
    (y : MultiplicativeTypeCommHopfAlgCat.cocharacterLattice
      (toMultiplicativeTypeCommHopfAlgCat T)) :
    (eqToHom (cocharacterLatticeFunctor_obj_obj (Opposite.op S))).hom
        (((cocharacterLatticeFunctor (k := k)).map f.op).hom
          ((eqToHom (cocharacterLatticeFunctor_obj_obj (Opposite.op T)).symm).hom y)) =
      MultiplicativeTypeCommHopfAlgCat.cocharacterMap (toMultiplicativeTypeMap f) y := by
  rw [cocharacterLatticeFunctor_map_hom]
  rfl

end TorusCommHopfAlgCat

end TauCeti
