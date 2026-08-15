/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Integral Galois lattices

An integral Galois lattice over a field is a finite free `ℤ`-module equipped with an action of
the absolute Galois group for which every vector has an open stabilizer. This is the continuity
criterion when the module carries the discrete topology.

## Main declarations

* `TauCeti.galoisLatticeProperty`: integral representations that are finite free and have open
  stabilizers.
* `TauCeti.GaloisLatticeCat`: the corresponding full subcategory of integral representations.

## References

See J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-- The property of an integral representation of the absolute Galois group being a Galois
lattice: its module is finite free and every vector has an open stabilizer. -/
def galoisLatticeProperty (k : Type u) [Field k] :
    ObjectProperty (Rep.{u} ℤ (Field.absoluteGaloisGroup k)) :=
  fun M ↦ (Module.Free ℤ M ∧ Module.Finite ℤ M) ∧
    ∀ x : M, IsOpen {sigma | M.ρ sigma x = x}

/-- Membership in the Galois-lattice property. -/
@[simp]
theorem galoisLatticeProperty_iff (k : Type u) [Field k]
    (M : Rep.{u} ℤ (Field.absoluteGaloisGroup k)) :
    galoisLatticeProperty k M ↔
      (Module.Free ℤ M ∧ Module.Finite ℤ M) ∧
        ∀ x : M, IsOpen {sigma | M.ρ sigma x = x} :=
  Iff.rfl

/-- Being a Galois lattice is invariant under equivariant integral-linear isomorphisms. -/
instance (k : Type u) [Field k] :
    (galoisLatticeProperty k).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    rw [galoisLatticeProperty_iff] at hX ⊢
    -- A `Rep` stores a module structure, while Lean otherwise selects the canonical integer
    -- module. These structures are uniquely equal; transport finite freeness to the stored
    -- structures while applying Mathlib's equivariant linear equivalence, then transport back.
    let repModX : Module ℤ X := X.hV2
    let repModY : Module ℤ Y := Y.hV2
    have hmodX : repModX = AddCommGroup.toIntModule X := Subsingleton.elim _ _
    have hmodY : repModY = AddCommGroup.toIntModule Y := Subsingleton.elim _ _
    have hFreeX : @Module.Free ℤ X _ _ repModX := by
      rw [hmodX]
      exact hX.1.1
    have hFiniteX : @Module.Finite ℤ X _ _ repModX := by
      rw [hmodX]
      exact hX.1.2
    let _ : Module ℤ X := repModX
    let _ : Module ℤ Y := repModY
    let eRep := Representation.equivOfIso e
    have hFreeY : @Module.Free ℤ Y _ _ repModY :=
      Module.Free.of_equiv' hFreeX eRep.toLinearEquiv
    let _ : Module.Finite ℤ X := hFiniteX
    have hFiniteY : @Module.Finite ℤ Y _ _ repModY :=
      Module.Finite.equiv eRep.toLinearEquiv
    have hFreeY' : @Module.Free ℤ Y _ _ (AddCommGroup.toIntModule Y) := by
      rw [hmodY] at hFreeY
      exact hFreeY
    have hFiniteY' : @Module.Finite ℤ Y _ _ (AddCommGroup.toIntModule Y) := by
      rw [hmodY] at hFiniteY
      exact hFiniteY
    refine ⟨⟨hFreeY', hFiniteY'⟩, ?_⟩
    intro y
    let inv : Y →ₗ[ℤ] X := eRep.symm.toIntertwiningMap.toLinearMap
    have hinv : Function.Injective inv := by
      dsimp only [inv]
      rw [← eRep.symm.toLinearEquiv_toLinearMap]
      exact eRep.symm.toLinearEquiv.injective
    let x : X := inv y
    have hcomm (sigma : Field.absoluteGaloisGroup k) (z : Y) :
        inv (Y.ρ sigma z) = X.ρ sigma (inv z) := by
      simpa only [inv, LinearMap.comp_apply] using
        congrArg (fun q : Y →ₗ[ℤ] X ↦ q z)
          (eRep.symm.toIntertwiningMap.isIntertwining' sigma)
    -- After `ext sigma`, membership in each set reduces definitionally to its stabilizer
    -- equality. The `change` steps make that reduction explicit and also unfold the local
    -- abbreviation `x = inv y`, so equivariance and injectivity of `inv` apply directly.
    have hset : {sigma | Y.ρ sigma y = y} = {sigma | X.ρ sigma x = x} := by
      ext sigma
      constructor
      · intro hy
        change Y.ρ sigma y = y at hy
        change X.ρ sigma x = x
        calc
          X.ρ sigma x = inv (Y.ρ sigma y) := (hcomm sigma y).symm
          _ = inv y := congrArg inv hy
          _ = x := rfl
      · intro hx
        change X.ρ sigma x = x at hx
        change Y.ρ sigma y = y
        apply hinv
        rw [hcomm sigma y, hx]
    rw [hset]
    exact hX.2 x

/-- The category of finite free integral representations of the absolute Galois group whose
vectors have open stabilizers. -/
abbrev GaloisLatticeCat (k : Type u) [Field k] :=
  (galoisLatticeProperty k).FullSubcategory

end TauCeti
