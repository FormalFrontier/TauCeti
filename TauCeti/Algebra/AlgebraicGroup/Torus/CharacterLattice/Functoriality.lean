/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice.Functoriality
public import TauCeti.Algebra.AlgebraicGroup.Torus.CharacterLattice.Basic
public import TauCeti.RepresentationTheory.GaloisLattice.Basic

/-!
# The character-lattice functor of tori

The character group of a torus is a finite free `ℤ`-module with a continuous action of the
absolute Galois group. Here continuity is expressed without choosing topology data on the
underlying module: every vector has an open stabilizer, which is the standard criterion for an
action on a discrete space.

These objects form the category `GaloisLatticeCat k`, defined in the generic representation-theory
module `TauCeti.RepresentationTheory.GaloisLattice.Basic`. The functorial geometric-character
construction restricts to a functor from coordinate Hopf algebras of tori to that category.
Because coordinate rings are contravariant in affine group schemes, this is the contravariant
character-lattice functor from tori themselves.

## Main declarations

* `TauCeti.TorusCommHopfAlgCat.characterLatticeFunctor`: the character-lattice functor on
  coordinate Hopf algebras of tori.

## References

See J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Corollary 12.24.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace TorusCommHopfAlgCat

variable {k : Type u} [Field k]

private theorem characterLatticeFunctor_mem (T : TorusCommHopfAlgCat k) :
    galoisLatticeProperty k
      (((torusCommHopfAlgProperty k).ι ⋙
        (finiteTypeCommHopfAlgProperty k).ι ⋙
          CommHopfAlgCat.geometricCharacterFunctor).obj T) := by
  simp only [Functor.comp_obj, ObjectProperty.ι_obj,
    CommHopfAlgCat.geometricCharacterFunctor_obj]
  let _ : Module.Free ℤ (CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :=
    characterLattice_module_free_of_torus k T.obj T.property
  let _ : Module.Finite ℤ (CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :=
    characterLattice_module_finite_of_torus k T.obj T.property
  apply galoisLatticeProperty_ofMulDistribMulAction k
    (CommHopfAlgCat.geometricCharacterGroup T.obj.obj)
  · exact fun sigma x ↦
      CommHopfAlgCat.geometricCharacterRepresentation_ρ_apply T.obj.obj sigma x
  · exact fun x ↦ CommHopfAlgCat.stabilizer_additiveGroupLike_isOpen x

/-- The character-lattice functor from coordinate Hopf algebras of tori to continuous integral
Galois lattices. On the corresponding affine group schemes this functor is contravariant. -/
noncomputable def characterLatticeFunctor :
    TorusCommHopfAlgCat k ⥤ GaloisLatticeCat k :=
  (galoisLatticeProperty k).lift
    ((torusCommHopfAlgProperty k).ι ⋙
      (finiteTypeCommHopfAlgProperty k).ι ⋙ CommHopfAlgCat.geometricCharacterFunctor)
    characterLatticeFunctor_mem

/-- The underlying integral representation of a torus's character lattice is its geometric
character group with the absolute-Galois action. -/
@[simp]
theorem characterLatticeFunctor_obj_obj
    (T : TorusCommHopfAlgCat k) :
    ((characterLatticeFunctor (k := k)).obj T).obj =
      CommHopfAlgCat.geometricCharacterRepresentation T.obj.obj :=
  by
    simpa only [characterLatticeFunctor, ObjectProperty.ι_obj, Functor.comp_obj,
      CommHopfAlgCat.geometricCharacterFunctor_obj] using
        ObjectProperty.ι_obj_lift_obj
          (galoisLatticeProperty k)
          ((torusCommHopfAlgProperty k).ι ⋙
            (finiteTypeCommHopfAlgProperty k).ι ⋙ CommHopfAlgCat.geometricCharacterFunctor)
          characterLatticeFunctor_mem T

/-- The morphism part of `characterLatticeFunctor` is the induced equivariant character map. -/
@[simp]
theorem characterLatticeFunctor_map_hom {S T : TorusCommHopfAlgCat k} (f : S ⟶ T) :
    ((characterLatticeFunctor (k := k)).map f).hom =
      eqToHom (characterLatticeFunctor_obj_obj S) ≫
        CommHopfAlgCat.geometricCharacterRepresentationMap f.hom.hom ≫
          eqToHom (characterLatticeFunctor_obj_obj T).symm := by
  have hlift : ((characterLatticeFunctor (k := k)).map f).hom =
      (((torusCommHopfAlgProperty k).ι ⋙
        (finiteTypeCommHopfAlgProperty k).ι ⋙
          CommHopfAlgCat.geometricCharacterFunctor).map f) := by
    simpa only [characterLatticeFunctor, ObjectProperty.ι_map] using
      ObjectProperty.ι_obj_lift_map
        (galoisLatticeProperty k)
        ((torusCommHopfAlgProperty k).ι ⋙
          (finiteTypeCommHopfAlgProperty k).ι ⋙
            CommHopfAlgCat.geometricCharacterFunctor)
        characterLatticeFunctor_mem f
  rw [hlift]
  simp only [Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.ι_obj,
    CommHopfAlgCat.geometricCharacterFunctor_map]
  rw [show CommHopfAlgCat.geometricCharacterFunctor_obj S.obj.obj =
      characterLatticeFunctor_obj_obj S from Subsingleton.elim _ _,
    show CommHopfAlgCat.geometricCharacterFunctor_obj T.obj.obj =
      characterLatticeFunctor_obj_obj T from Subsingleton.elim _ _]
  -- After explicitly identifying the two object-equality proofs, both composites are the same
  -- morphism definitionally.
  rfl

end TorusCommHopfAlgCat

end TauCeti
