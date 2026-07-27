/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.ClassFunction
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The bilinear pairing of finite-group class functions

This file defines the normalized bilinear pairing on class functions of a finite group.  When
the coefficient field is algebraically closed and the group order is invertible, irreducible
characters are orthonormal for this pairing.

The pairing is bilinear, rather than Hermitian: complex conjugation enters only after restricting
to virtual characters.

## References

* [Character Theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md), Layer 0.
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 2.
-/

public section

namespace TauCeti

namespace ClassFunction

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G]

omit [Group G] in
private theorem card_inv_mul_sum_mul_smul (c : k) (f₁ f₂ : G → k) :
    (Nat.card G : k)⁻¹ * ∑ g : G, f₁ g * (c * f₂ g) =
      c * ((Nat.card G : k)⁻¹ * ∑ g : G, f₁ g * f₂ g) := by
  calc
    _ = (Nat.card G : k)⁻¹ * (c * ∑ g : G, f₁ g * f₂ g) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ = _ := by ring

/-- The normalized bilinear pairing of class functions on a finite group. -/
noncomputable def characterPairing :
    LinearMap.BilinForm k (ClassFunction k G) :=
  LinearMap.mk₂ k
    (fun f₁ f₂ => (Nat.card G : k)⁻¹ * ∑ g : G, f₁.1 g * f₂.1 g⁻¹)
    (by
      intro f₁ f₂ f₃
      simp [add_mul, Finset.sum_add_distrib, mul_add])
    (by
      intro c f₁ f₂
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        card_inv_mul_sum_mul_smul (G := G) c f₁.1 fun g => f₂.1 g⁻¹)
    (by
      intro f₁ f₂ f₃
      simp [mul_add, Finset.sum_add_distrib])
    (by
      intro c f₁ f₂
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      simpa using card_inv_mul_sum_mul_smul (G := G) c f₁.1 fun g => f₂.1 g⁻¹)

/-- The defining formula for the character pairing. -/
theorem characterPairing_apply (f₁ f₂ : ClassFunction k G) :
    characterPairing f₁ f₂ =
      (Nat.card G : k)⁻¹ * ∑ g : G, f₁.1 g * f₂.1 g⁻¹ :=
  (rfl)

/-- The character pairing is symmetric. -/
theorem characterPairing_symm (f₁ f₂ : ClassFunction k G) :
    characterPairing f₁ f₂ = characterPairing f₂ f₁ := by
  rw [characterPairing_apply, characterPairing_apply]
  have hsum : (∑ g : G, f₁.1 g * f₂.1 g⁻¹) = ∑ g : G, f₂.1 g * f₁.1 g⁻¹ := by
    calc
      _ = ∑ g : G, f₁.1 g⁻¹ * f₂.1 (g⁻¹)⁻¹ := by
        apply Fintype.sum_equiv (Equiv.inv G)
        intro g
        simp
      _ = _ := by simp [mul_comm]
  rw [hsum]

/-- The bilinear form underlying `characterPairing` is symmetric. -/
theorem characterPairing_isSymm :
    characterPairing (k := k) (G := G).IsSymm :=
  ⟨characterPairing_symm⟩

omit [Fintype G] in
private theorem isConj_inv_iff {x y : G} :
    IsConj x⁻¹ y⁻¹ ↔ IsConj x y := by
  constructor <;> intro h
  · obtain ⟨c, hc⟩ := isConj_iff.mp h
    apply isConj_iff.mpr
    refine ⟨c, ?_⟩
    have := congrArg Inv.inv hc
    simpa [mul_assoc] using this
  · obtain ⟨c, hc⟩ := isConj_iff.mp h
    apply isConj_iff.mpr
    refine ⟨c, ?_⟩
    have := congrArg Inv.inv hc
    simpa [mul_assoc] using this

private noncomputable def classIndicator (x : G) : ClassFunction k G := by
  classical
  exact equivConjClasses.symm (Pi.single (ConjClasses.mk x) 1)

open scoped Classical in
private theorem classIndicator_apply (x y : G) :
    (classIndicator (k := k) x).1 y =
      if ConjClasses.mk y = ConjClasses.mk x then 1 else 0 :=
  by
    classical
    rw [classIndicator, equivConjClasses_symm_apply, ofConjClasses_apply, Pi.single_apply]

omit [Fintype G] in
private theorem card_conjClass_dvd_card [Finite G] (x : G) :
    Nat.card (ConjClasses.mk x).carrier ∣ Nat.card G := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (ConjClasses.mk x).carrier := Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer (ConjAct G) x) := Fintype.ofFinite _
  letI : Fintype (MulAction.orbit (ConjAct G) x) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [ConjClasses.card_carrier]
  apply Nat.div_dvd_of_dvd
  refine ⟨Fintype.card (MulAction.orbit (ConjAct G) x), ?_⟩
  simpa [Nat.card_eq_fintype_card, Nat.mul_comm] using
    (MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) x).symm

omit [Fintype G] in
private theorem card_conjClass_cast_ne_zero [Finite G] [Invertible (Nat.card G : k)] (x : G) :
    (Nat.card (ConjClasses.mk x).carrier : k) ≠ 0 := by
  exact ne_zero_of_dvd_ne_zero (Invertible.ne_zero _)
    (Nat.cast_dvd_cast (α := k) (card_conjClass_dvd_card x))

/-- The character pairing is nondegenerate when the group order is invertible in the field. -/
theorem characterPairing_nondegenerate [Invertible (Nat.card G : k)] :
    characterPairing (k := k) (G := G).Nondegenerate := by
  classical
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (B := characterPairing (k := k) (G := G)) characterPairing_isSymm.isRefl).mpr ?_
  intro f hf
  apply Subtype.ext
  funext x
  by_contra hfx
  letI : Fintype (ConjClasses.mk x).carrier := Fintype.ofFinite _
  have hcarrier : (ConjClasses.mk x).carrier = {g | IsConj g x} := by
    ext g
    simp only [ConjClasses.mem_carrier_iff_mk_eq, Set.mem_setOf_eq]
    exact ConjClasses.mk_eq_mk_iff_isConj
  have hconj (g : G) :
      ConjClasses.mk g⁻¹ = ConjClasses.mk x⁻¹ ↔ IsConj g x := by
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_inv_iff]
  have hsum :
      (∑ g : G, f.1 g * (classIndicator (k := k) x⁻¹).1 g⁻¹) =
        Nat.card (ConjClasses.mk x).carrier * f.1 x := by
    calc
      _ = ∑ g : G, if IsConj g x then f.1 g else 0 := by
        apply Fintype.sum_congr
        intro g
        by_cases hg : IsConj g x
        · have h' := hconj g |>.mpr hg
          rw [classIndicator_apply, if_pos h', if_pos hg, mul_one]
        · have h' : ConjClasses.mk g⁻¹ ≠ ConjClasses.mk x⁻¹ := fun h => hg (hconj g |>.mp h)
          rw [classIndicator_apply, if_neg h', if_neg hg, mul_zero]
      _ = ∑ g ∈ Finset.univ.filter (fun g => IsConj g x), f.1 g := by
        rw [Finset.sum_filter]
      _ = ∑ _g ∈ Finset.univ.filter (fun g => IsConj g x), f.1 x := by
        apply Finset.sum_congr rfl
        intro g hg
        exact ClassFunction.eq_of_isConj f (by simpa using Finset.mem_filter.mp hg |>.2)
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        rw [hcarrier, Nat.card_eq_fintype_card]
        rw [(Fintype.card_ofFinset (p := {g | IsConj g x})
          (Finset.univ.filter fun g => IsConj g x) (by simp)).symm]
        rfl
  have hpair := hf (classIndicator (k := k) x⁻¹)
  rw [characterPairing_apply, hsum] at hpair
  exact (mul_ne_zero (inv_ne_zero (Invertible.ne_zero _))
    (mul_ne_zero (card_conjClass_cast_ne_zero (k := k) x) hfx)) hpair

/-- The pairing of two representation characters is Mathlib's normalized character sum. -/
theorem characterPairing_ofCharacter
    {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (σ : Representation k G W) :
    characterPairing (ofCharacter ρ) (ofCharacter σ) =
      (Nat.card G : k)⁻¹ * ∑ g : G, ρ.character g * σ.character g⁻¹ := by
  rw [characterPairing_apply]
  simp only [ofCharacter_apply]

/-- The pairing of two finite-dimensional representation characters is Mathlib's normalized
character sum. -/
theorem characterPairing_ofFDRep (V W : FDRep k G) :
    characterPairing (ofFDRep V) (ofFDRep W) =
      (Nat.card G : k)⁻¹ * ∑ g : G, V.character g * W.character g⁻¹ := by
  rw [characterPairing_apply]
  simp only [ofFDRep_apply]

/-- The character pairing computes the dimension of an intertwiner space. -/
theorem characterPairing_ofCharacter_eq_finrank {V W : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [Invertible (Nat.card G : k)] (ρ : Representation k G V) (σ : Representation k G W) :
    characterPairing (ofCharacter ρ) (ofCharacter σ) =
      Module.finrank k (Representation.IntertwiningMap σ ρ) := by
  rw [characterPairing_ofCharacter]
  exact Representation.card_inv_mul_sum_char_mul_char_eq_finrank σ ρ

open scoped Classical in
/-- The character pairing of irreducible characters is Kronecker orthonormal. -/
theorem characterPairing_ofCharacter_orthonormal {V W : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [Invertible (Nat.card G : k)] [IsAlgClosed k] (ρ : Representation k G V)
    (σ : Representation k G W) [ρ.IsIrreducible] [σ.IsIrreducible] :
    characterPairing (ofCharacter ρ) (ofCharacter σ) =
      if Nonempty (Representation.Equiv σ ρ) then (1 : k) else 0 := by
  rw [characterPairing_ofCharacter]
  exact Representation.char_orthonormal ρ σ

/-- The character pairing computes the dimension of a morphism space in `FDRep`. -/
theorem characterPairing_ofFDRep_eq_finrank [Invertible (Nat.card G : k)] (V W : FDRep k G) :
    characterPairing (ofFDRep V) (ofFDRep W) = Module.finrank k (W ⟶ V) := by
  rw [characterPairing_ofFDRep]
  exact FDRep.scalar_product_char_eq_finrank_equivariant W V

open scoped Classical in
/-- The character pairing of simple finite-dimensional representations is Kronecker orthonormal. -/
theorem characterPairing_ofFDRep_orthonormal [Invertible (Nat.card G : k)] [IsAlgClosed k]
    (V W : FDRep k G) [CategoryTheory.Simple V] [CategoryTheory.Simple W] :
    characterPairing (ofFDRep V) (ofFDRep W) =
      if Nonempty (V ≅ W) then (1 : k) else 0 := by
  rw [characterPairing_ofFDRep]
  exact FDRep.char_orthonormal V W

end ClassFunction

end TauCeti
