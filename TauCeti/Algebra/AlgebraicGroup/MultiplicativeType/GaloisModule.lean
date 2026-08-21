/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice.Continuous
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Cocharacter

/-!
# Continuous Galois modules attached to a group of multiplicative type

The character and cocharacter groups of a group of multiplicative type carry mutually
contragredient actions of the absolute Galois group. The character action is already known to be
continuous for the Krull topology and the discrete topology on the group. This file proves the
corresponding statement for cocharacters.

The key point is finite generation. Choose a finite generating family of the character group. The
intersection of the open stabilizers of its generators fixes every character, hence fixes every
functional on the character group under the contragredient action. This open subgroup therefore
lies in the stabilizer of any prescribed cocharacter.

## Main declarations

* `TauCeti.MultiplicativeTypeCommHopfAlgCat.instDistribMulActionCocharacterLattice`: the
  contragredient absolute-Galois action on cocharacters.
* `TauCeti.MultiplicativeTypeCommHopfAlgCat.stabilizer_cocharacterLattice_isOpen`: every
  cocharacter has open stabilizer.
* `TauCeti.MultiplicativeTypeCommHopfAlgCat.instContinuousSMulCocharacterLattice`: the
  cocharacter group is a continuous discrete Galois module.

## References

See J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.

For a torus these groups are finite free lattices with a perfect pairing, so this completes the
continuous character--cocharacter Galois-module interface in Layer 4, "Tori: split and
non-split", of the ReductiveGroups roadmap. The later absolute root datum will use these two
continuous lattices together with their Galois-invariant perfect pairing.
-/

public section

namespace TauCeti

universe u

namespace MultiplicativeTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- The absolute Galois group acts on the cocharacter group through the contragredient
representation. -/
noncomputable instance instDistribMulActionCocharacterLattice
    (T : MultiplicativeTypeCommHopfAlgCat k) :
    DistribMulAction (Field.absoluteGaloisGroup k)
      (cocharacterLattice T) where
  smul σ f := cocharacterGaloisRepresentation T σ f
  one_smul f := by
    exact LinearMap.congr_fun
      (map_one (cocharacterGaloisRepresentation T)) f
  mul_smul σ τ f := by
    exact LinearMap.congr_fun
      (map_mul (cocharacterGaloisRepresentation T) σ τ) f
  smul_zero σ := LinearMap.map_zero _
  smul_add σ f g := LinearMap.map_add _ f g

/-- Scalar multiplication on the cocharacter lattice is the existing contragredient Galois
representation. -/
@[simp]
theorem cocharacterLattice_smul_def (T : MultiplicativeTypeCommHopfAlgCat k)
    (σ : Field.absoluteGaloisGroup k) (f : cocharacterLattice T) :
    σ • f = cocharacterGaloisRepresentation T σ f :=
  rfl

/-- The cocharacter lattice carries the discrete topology. -/
noncomputable instance instTopologicalSpaceCocharacterLattice
    (T : MultiplicativeTypeCommHopfAlgCat k) :
    TopologicalSpace (cocharacterLattice T) := ⊥

/-- The topology on the cocharacter lattice is discrete. -/
instance instDiscreteTopologyCocharacterLattice (T : MultiplicativeTypeCommHopfAlgCat k) :
    DiscreteTopology (cocharacterLattice T) := ⟨rfl⟩

/-- The stabilizer of every cocharacter of a group of multiplicative type is open in the absolute
Galois group. -/
theorem stabilizer_cocharacterLattice_isOpen (T : MultiplicativeTypeCommHopfAlgCat k)
    (f : cocharacterLattice T) :
    IsOpen (MulAction.stabilizer (Field.absoluteGaloisGroup k) f :
      Set (Field.absoluteGaloisGroup k)) := by
  let _ : Module.Finite ℤ (CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :=
    Module.Finite.iff_addGroup_fg.mpr <|
      CommHopfAlgCat.additiveCharacterGroup_fg_of_multiplicativeType T.obj T.property
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin
    (R := ℤ) (M := CommHopfAlgCat.additiveCharacterGroup T.obj.obj)
  let U : Subgroup (Field.absoluteGaloisGroup k) :=
    ⨅ i, MulAction.stabilizer (Field.absoluteGaloisGroup k) (s i)
  apply Subgroup.isOpen_mono (H₁ := U)
    (H₂ := MulAction.stabilizer (Field.absoluteGaloisGroup k) f)
  · intro σ hσ
    rw [Subgroup.mem_iInf] at hσ
    rw [MulAction.mem_stabilizer_iff]
    apply (cocharacterLatticeLinearEquivDual T).injective
    apply LinearMap.ext
    intro x
    rw [cocharacterLattice_smul_def, cocharacterGaloisRepresentation_apply_apply]
    -- `ofMulDistribMulAction_apply_apply` evaluates in `Additive` notation, whereas the
    -- character-group action uses scalar notation on that abbreviation. No public lemma bridges
    -- these definitionally equal forms, so the two `change`s below cross this type-tag boundary.
    have hlinear :
        Representation.ofMulDistribMulAction (Field.absoluteGaloisGroup k)
            (CommHopfAlgCat.geometricCharacterGroup T.obj.obj) σ⁻¹ =
          LinearMap.id := by
      apply LinearMap.ext_on hs
      rintro _ ⟨i, rfl⟩
      change σ⁻¹ • s i = s i
      exact inv_smul_eq_iff.mpr (MulAction.mem_stabilizer_iff.mp (hσ i)).symm
    have hx : σ⁻¹ • x = x := by
      change Representation.ofMulDistribMulAction (Field.absoluteGaloisGroup k)
        (CommHopfAlgCat.geometricCharacterGroup T.obj.obj) σ⁻¹ x = x
      exact LinearMap.congr_fun hlinear x
    rw [hx]
  · dsimp only [U]
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i ↦
      stabilizer_isOpen (Field.absoluteGaloisGroup k) (s i)

/-- The contragredient absolute-Galois action on the cocharacter lattice is continuous for the
Krull topology and the discrete topology on the lattice. -/
noncomputable instance instContinuousSMulCocharacterLattice
    (T : MultiplicativeTypeCommHopfAlgCat k) :
    ContinuousSMul (Field.absoluteGaloisGroup k)
      (cocharacterLattice T) :=
  continuousSMul_iff_stabilizer_isOpen.mpr (stabilizer_cocharacterLattice_isOpen T)

end MultiplicativeTypeCommHopfAlgCat

end TauCeti
