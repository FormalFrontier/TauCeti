/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice.Functoriality
public import TauCeti.Algebra.AlgebraicGroup.Torus.CharacterLattice.Basic

/-!
# The character-lattice functor of tori

The character group of a torus is a finite free `ℤ`-module with a continuous action of the
absolute Galois group. Here continuity is expressed without choosing topology data on the
underlying module: every vector has an open stabilizer, which is the standard criterion for an
action on a discrete space.

These objects form the category `GaloisLatticeCat k`. The functorial geometric-character
construction restricts to a functor from coordinate Hopf algebras of tori to this category.
Because coordinate rings are contravariant in affine group schemes, this is the contravariant
character-lattice functor from tori themselves.

## Main declarations

* `TauCeti.galoisLatticeProperty`: finite free integral representations with open stabilizers.
* `TauCeti.GaloisLatticeCat`: the corresponding full subcategory of integral representations.
* `TauCeti.TorusCommHopfAlgCat.characterLatticeFunctor`: the character-lattice functor on
  coordinate Hopf algebras of tori.

## References

See J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Corollary 12.24.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-- The property of an integral representation of the absolute Galois group being a Galois
lattice: its module is finite free and every vector has an open stabilizer. -/
def galoisLatticeProperty (k : Type u) [Field k] :
    ObjectProperty (Rep.{u} ℤ (Field.absoluteGaloisGroup k)) :=
  fun M ↦ (∃ n : ℕ, Nonempty (M ≃+ (Fin n →₀ ℤ))) ∧
    ∀ x : M, IsOpen {sigma | M.ρ sigma x = x}

/-- Membership in the Galois-lattice property. -/
@[simp]
theorem galoisLatticeProperty_iff (k : Type u) [Field k]
    (M : Rep.{u} ℤ (Field.absoluteGaloisGroup k)) :
    galoisLatticeProperty k M ↔
      (∃ n : ℕ, Nonempty (M ≃+ (Fin n →₀ ℤ))) ∧
        ∀ x : M, IsOpen {sigma | M.ρ sigma x = x} :=
  Iff.rfl

/-- Being a Galois lattice is invariant under equivariant integral-linear isomorphisms. -/
instance (k : Type u) [Field k] :
    (galoisLatticeProperty k).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    rw [galoisLatticeProperty_iff] at hX ⊢
    -- `Rep` stores its `ℤ`-module instance, while an additive group also has a canonical one;
    -- select the stored instances so the underlying linear maps elaborate at the same types.
    let _ : Module ℤ X := X.hV2
    let _ : Module ℤ Y := Y.hV2
    obtain ⟨n, ⟨a⟩⟩ := hX.1
    let eAdd : Y ≃+ X :=
      { toFun := e.inv.hom
        invFun := e.hom.hom
        left_inv := Iso.inv_hom_id_apply e
        right_inv := Iso.hom_inv_id_apply e
        map_add' := e.inv.hom.toLinearMap.toAddHom.map_add }
    refine ⟨⟨n, ⟨eAdd.trans a⟩⟩, ?_⟩
    intro y
    let x : X := e.inv.hom y
    have hset : {sigma | Y.ρ sigma y = y} = {sigma | X.ρ sigma x = x} := by
      ext sigma
      constructor
      · intro hy
        calc
          X.ρ sigma x = e.inv.hom (Y.ρ sigma y) :=
            (Rep.hom_comm_apply e.inv sigma y).symm
          _ = e.inv.hom y := congrArg e.inv.hom hy
          _ = x := rfl
      · intro hx
        calc
          Y.ρ sigma y = Y.ρ sigma (e.hom.hom (e.inv.hom y)) :=
            congrArg (Y.ρ sigma) (Iso.inv_hom_id_apply e y).symm
          _ = e.hom.hom (X.ρ sigma x) :=
            (Rep.hom_comm_apply e.hom sigma x).symm
          _ = e.hom.hom x := congrArg e.hom.hom hx
          _ = y := Iso.inv_hom_id_apply e y
    rw [hset]
    exact hX.2 x

/-- The category of finite free integral representations of the absolute Galois group whose
vectors have open stabilizers. -/
abbrev GaloisLatticeCat (k : Type u) [Field k] :=
  (galoisLatticeProperty k).FullSubcategory

namespace TorusCommHopfAlgCat

variable {k : Type u} [Field k]

/-- The geometric-character representation functor restricted to coordinate Hopf algebras of
tori, before recording finite freeness and open stabilizers in its codomain. -/
noncomputable def characterRepresentationFunctor :
    TorusCommHopfAlgCat k ⥤ Rep.{u} ℤ (Field.absoluteGaloisGroup k) :=
  (torusCommHopfAlgProperty k).ι ⋙
    (finiteTypeCommHopfAlgProperty k).ι ⋙ CommHopfAlgCat.geometricCharacterFunctor

private theorem characterRepresentationFunctor_mem (T : TorusCommHopfAlgCat k) :
    galoisLatticeProperty k ((characterRepresentationFunctor (k := k)).obj T) := by
  simp only [characterRepresentationFunctor, Functor.comp_obj, ObjectProperty.ι_obj,
    CommHopfAlgCat.geometricCharacterFunctor_obj]
  refine ⟨exists_characterLattice_addEquiv_of_torus k T.obj T.property, ?_⟩
  -- The representation wrapper's action is the scalar action used by the open-stabilizer theorem.
  change ∀ x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj,
    IsOpen {sigma | sigma • x = x}
  intro x
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
  (galoisLatticeProperty k).lift (characterRepresentationFunctor (k := k))
    characterRepresentationFunctor_mem

/-- Forgetting that character lattices are finite free with open stabilizers recovers the
geometric-character representation functor restricted to tori. -/
noncomputable def characterLatticeFunctorCompιIso :
    characterLatticeFunctor (k := k) ⋙ (galoisLatticeProperty k).ι ≅
      characterRepresentationFunctor (k := k) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The underlying integral representation of a torus's character lattice is its geometric
character group with the absolute-Galois action. -/
@[simp]
theorem characterLatticeFunctor_obj
    (T : TorusCommHopfAlgCat k) :
    ((characterLatticeFunctor (k := k)).obj T).obj =
      CommHopfAlgCat.geometricCharacterRepresentation T.obj.obj :=
  by
    -- A lifted full-subcategory object has the original representation as its carrier object.
    change (characterRepresentationFunctor (k := k)).obj T = _
    rw [characterRepresentationFunctor, Functor.comp_obj, Functor.comp_obj,
      ObjectProperty.ι_obj, ObjectProperty.ι_obj,
      CommHopfAlgCat.geometricCharacterFunctor_obj]

end TorusCommHopfAlgCat

end TauCeti
