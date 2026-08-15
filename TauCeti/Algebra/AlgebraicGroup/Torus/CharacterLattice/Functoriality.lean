/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
  rw [galoisLatticeProperty_iff]
  refine ⟨⟨characterLattice_module_free_of_torus k T.obj T.property,
    characterLattice_module_finite_of_torus k T.obj T.property⟩, ?_⟩
  refine fun x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj ↦ ?_
  -- Expose the representation abbreviation so the public action bridge can rewrite it.
  change IsOpen {sigma |
    Representation.ofMulDistribMulAction (Field.absoluteGaloisGroup k)
      (CommHopfAlgCat.geometricCharacterGroup T.obj.obj) sigma x = x}
  have hsetAction :
      {sigma | Representation.ofMulDistribMulAction (Field.absoluteGaloisGroup k)
        (CommHopfAlgCat.geometricCharacterGroup T.obj.obj) sigma x = x} =
        {sigma | sigma • x = x} := by
    ext sigma
    change Representation.ofMulDistribMulAction (Field.absoluteGaloisGroup k)
      (CommHopfAlgCat.geometricCharacterGroup T.obj.obj) sigma x = x ↔ sigma • x = x
    rw [CommHopfAlgCat.geometricCharacterRepresentation_ρ_apply T.obj.obj sigma x]
  rw [hsetAction]
  have hset : {sigma | sigma • x = x} =
      (MulAction.stabilizer (Field.absoluteGaloisGroup k) x :
        Set (Field.absoluteGaloisGroup k)) := by
    ext sigma
    exact MulAction.mem_stabilizer_iff.symm
  rw [hset]
  exact CommHopfAlgCat.stabilizer_additiveGroupLike_isOpen x

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
theorem characterLatticeFunctor_map {S T : TorusCommHopfAlgCat k} (f : S ⟶ T) :
    ((characterLatticeFunctor (k := k)).map f).hom =
      eqToHom (characterLatticeFunctor_obj_obj S) ≫
        CommHopfAlgCat.geometricCharacterRepresentationMap f.hom.hom ≫
          eqToHom (characterLatticeFunctor_obj_obj T).symm := by
  change
    (((torusCommHopfAlgProperty k).ι ⋙
      (finiteTypeCommHopfAlgProperty k).ι ⋙
        CommHopfAlgCat.geometricCharacterFunctor).map f) = _
  simp only [Functor.comp_map, ObjectProperty.ι_map,
    CommHopfAlgCat.geometricCharacterFunctor_map]
  congr 1

end TorusCommHopfAlgCat

end TauCeti
