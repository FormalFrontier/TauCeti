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
  fun M ↦ (@Module.Free ℤ M _ _ M.hV2 ∧ @Module.Finite ℤ M _ _ M.hV2) ∧
    ∀ x : M, IsOpen {sigma | M.ρ sigma x = x}

/-- Membership in the Galois-lattice property. -/
@[simp]
theorem galoisLatticeProperty_iff (k : Type u) [Field k]
    (M : Rep.{u} ℤ (Field.absoluteGaloisGroup k)) :
    galoisLatticeProperty k M ↔
      (@Module.Free ℤ M _ _ M.hV2 ∧ @Module.Finite ℤ M _ _ M.hV2) ∧
        ∀ x : M, IsOpen {sigma | M.ρ sigma x = x} :=
  Iff.rfl

/-- Build the Galois-lattice property for a representation induced from a multiplicative action,
using the usual stabilizer formulation of continuity. -/
theorem galoisLatticeProperty_ofMulDistribMulAction (k : Type u) [Field k]
    (G : Type u) [CommGroup G] [MulDistribMulAction (Field.absoluteGaloisGroup k) G]
    [DistribMulAction (Field.absoluteGaloisGroup k) (Additive G)]
    [free : Module.Free ℤ (Additive G)] [finite : Module.Finite ℤ (Additive G)]
    (hρ : ∀ (sigma : Field.absoluteGaloisGroup k) (x : Additive G),
      (Rep.ofMulDistribMulAction (Field.absoluteGaloisGroup k) G).ρ sigma x = sigma • x)
    (hopen : ∀ x : Additive G,
      IsOpen (MulAction.stabilizer (Field.absoluteGaloisGroup k) x :
        Set (Field.absoluteGaloisGroup k))) :
    galoisLatticeProperty k
      (Rep.ofMulDistribMulAction (Field.absoluteGaloisGroup k) G) := by
  rw [galoisLatticeProperty_iff]
  let M := Rep.ofMulDistribMulAction (Field.absoluteGaloisGroup k) G
  have hmod : M.hV2 = AddCommGroup.toIntModule (Additive G) := Subsingleton.elim _ _
  have hfree : @Module.Free ℤ (Additive G) _ _ M.hV2 := by
    rw [hmod]
    exact free
  have hfinite : @Module.Finite ℤ (Additive G) _ _ M.hV2 := by
    rw [hmod]
    exact finite
  refine ⟨⟨hfree, hfinite⟩, ?_⟩
  -- Expose the carrier of Mathlib's bundled representation so the supplied additive action and
  -- its stabilizer can be used directly.
  change ∀ x : Additive G, IsOpen {sigma |
    (Rep.ofMulDistribMulAction (Field.absoluteGaloisGroup k) G).ρ sigma x = x}
  intro x
  rw [show {sigma |
      (Rep.ofMulDistribMulAction (Field.absoluteGaloisGroup k) G).ρ sigma x = x} =
      (MulAction.stabilizer (Field.absoluteGaloisGroup k) x : Set _) from
    Set.ext fun sigma ↦ by
      simp only [Set.mem_ofPred_eq, hρ, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
      exact Iff.rfl]
  exact hopen x

private theorem module_free_of_repIso {G : Type u} [Monoid G] {X Y : Rep.{u} ℤ G}
    (e : X ≅ Y) (hX : @Module.Free ℤ X _ _ X.hV2) :
    @Module.Free ℤ Y _ _ Y.hV2 := by
  let _ : Module ℤ X := X.hV2
  let _ : Module ℤ Y := Y.hV2
  exact Module.Free.of_equiv' hX (Representation.equivOfIso e).toLinearEquiv

private theorem module_finite_of_repIso {G : Type u} [Monoid G] {X Y : Rep.{u} ℤ G}
    (e : X ≅ Y) (hX : @Module.Finite ℤ X _ _ X.hV2) :
    @Module.Finite ℤ Y _ _ Y.hV2 := by
  let _ : Module ℤ X := X.hV2
  let _ : Module ℤ Y := Y.hV2
  let _ : @Module.Finite ℤ X _ _ X.hV2 := hX
  exact Module.Finite.equiv (Representation.equivOfIso e).toLinearEquiv

private theorem isOpen_setOf_ρ_eq_of_iso {G : Type u} [Monoid G] [TopologicalSpace G]
    {X Y : Rep.{u} ℤ G} (e : X ≅ Y)
    (hX : ∀ x : X, IsOpen {g | X.ρ g x = x}) (y : Y) :
    IsOpen {g | Y.ρ g y = y} := by
  let _ : Module ℤ X := X.hV2
  let _ : Module ℤ Y := Y.hV2
  let inv : Y →ₗ[ℤ] X :=
    (Representation.equivOfIso e).symm.toIntertwiningMap.toLinearMap
  have hinv : Function.Injective inv := by
    dsimp only [inv]
    rw [← (Representation.equivOfIso e).symm.toLinearEquiv_toLinearMap]
    exact (Representation.equivOfIso e).symm.toLinearEquiv.injective
  have hcomm (g : G) (z : Y) : inv (Y.ρ g z) = X.ρ g (inv z) := by
    simpa only [inv, LinearMap.comp_apply] using
      congrArg (fun q : Y →ₗ[ℤ] X ↦ q z)
        ((Representation.equivOfIso e).symm.toIntertwiningMap.isIntertwining' g)
  rw [show {g | Y.ρ g y = y} = {g | X.ρ g (inv y) = inv y} from
    Set.ext fun g ↦ by
      simp only [Set.mem_ofPred_eq, ← hcomm g y, hinv.eq_iff]]
  exact hX (inv y)

/-- Being a Galois lattice is invariant under equivariant integral-linear isomorphisms. -/
instance (k : Type u) [Field k] :
    (galoisLatticeProperty k).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    rw [galoisLatticeProperty_iff] at hX ⊢
    exact ⟨⟨module_free_of_repIso e hX.1.1, module_finite_of_repIso e hX.1.2⟩,
      isOpen_setOf_ρ_eq_of_iso e hX.2⟩

/-- The category of finite free integral representations of the absolute Galois group whose
vectors have open stabilizers. -/
abbrev GaloisLatticeCat (k : Type u) [Field k] :=
  (galoisLatticeProperty k).FullSubcategory

namespace GaloisLatticeCat

/-- The stored integral module of a Galois lattice is free. -/
instance instStoredModuleFree (k : Type u) [Field k] (M : GaloisLatticeCat k) :
    @Module.Free ℤ M.obj _ _ M.obj.hV2 :=
  M.property.1.1

/-- The stored integral module of a Galois lattice is finite. -/
instance instStoredModuleFinite (k : Type u) [Field k] (M : GaloisLatticeCat k) :
    @Module.Finite ℤ M.obj _ _ M.obj.hV2 :=
  M.property.1.2

/-- The canonical integral module on the additive group underlying a Galois lattice is free. -/
instance instModuleFree (k : Type u) [Field k] (M : GaloisLatticeCat k) :
    Module.Free ℤ M.obj := by
  have hmod : M.obj.hV2 = AddCommGroup.toIntModule M.obj := Subsingleton.elim _ _
  rw [← hmod]
  exact M.property.1.1

/-- The canonical integral module on the additive group underlying a Galois lattice is finite. -/
instance instModuleFinite (k : Type u) [Field k] (M : GaloisLatticeCat k) :
    Module.Finite ℤ M.obj := by
  have hmod : M.obj.hV2 = AddCommGroup.toIntModule M.obj := Subsingleton.elim _ _
  rw [← hmod]
  exact M.property.1.2

/-- Every vector of a Galois lattice has an open stabilizer. -/
theorem isOpen_setOf_ρ_eq (k : Type u) [Field k] (M : GaloisLatticeCat k) (x : M.obj) :
    IsOpen {sigma | M.obj.ρ sigma x = x} :=
  M.property.2 x

end GaloisLatticeCat

end TauCeti
