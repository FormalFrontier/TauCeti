/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter

/-!
# Real conjugacy classes and inversion-invariant rows of the character table

A conjugacy class of a group is **real** (`TauCeti.IsRealClass`, defined with the inversion
involution it is about in `TauCeti/Algebra/Group/Conj.lean`) when it contains an element conjugate
to its own inverse. A row of the character table is **inversion-invariant** when the character it
lists takes the same value at `g` and at `g⁻¹`; over `ℂ` that is exactly the row being real-valued,
because complex conjugation of a character value inverts the group element
(`TauCeti.conj_characterTable`).

This file proves that a finite group has as many inversion-invariant rows as real classes, and over
`ℂ` as many real-valued irreducible characters as real classes.

Both counts are read off the same quantity, `|G|⁻¹ ∑_g χᵢ(g)²`, summed over the whole table. Down
the columns it is the second orthogonality relation applied to a class and its inverse, and it
detects real classes. Along the rows it is the pairing of `χᵢ` with the twisted character
`g ↦ χᵢ(g⁻¹)`, and it detects inversion-invariant rows: the twist
`TauCeti.ClassFunction.invMap` is an isometry of the character pairing
(`TauCeti.ClassFunction.characterPairing_invMap_invMap`), so the twisted character still pairs to
`1` with itself, and it is a virtual character, being the character of the dual representation. A
virtual character of norm `1` is `±` a row of the character table
(`TauCeti.exists_eq_irreducibleCharacter_or_neg`), and the sign is fixed by the value at `1`, a
positive degree. So the twisted character is again one of the rows, and it is the `i`-th row
exactly when the `i`-th row is inversion-invariant.

That the twisted character is again an irreducible character is *proved* here rather than assumed:
no irreducibility of the dual representation is needed as an input.

## Main statements

* `TauCeti.card_inv_mul_sum_irreducibleCharacter_sq`: the row quantity `|G|⁻¹ ∑_g χᵢ(g)²` is `1`
  when the `i`-th row is inversion-invariant and `0` otherwise.
* `TauCeti.sum_characterTable_sq`: the column quantity `∑_i χᵢ(C)²` is `|G| / |C|` when `C` is
  real and `0` otherwise.
* `TauCeti.card_inversionInvariant_eq_card_realClasses`: the two counts agree over any
  algebraically closed field of characteristic zero.
* `TauCeti.card_realValued_eq_card_realClasses`: over `ℂ`, the rows of the character table fixed
  by complex conjugation are as many as the real conjugacy classes.

## References

* [Character Theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md), Layer 7.
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Theorem 6.32 and Problem 6.13.
* J.-P. Serre, *Linear Representations of Finite Groups* (1977), §13.2.
-/

public section

namespace TauCeti

universe u v

section Rows

open ClassFunction

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

open scoped Classical in
/-- **An irreducible character pairs with its own inversion to `1` or to `0`**, according as
inverting the group element leaves it unchanged or not. -/
theorem characterPairing_ofCharacter_invMap_self [CharZero k]
    (i : Fin (Nat.card (ConjClasses G))) :
    characterPairing (ofCharacter (irreducibleRepresentation k i))
        (invMap (ofCharacter (irreducibleRepresentation k i))) =
      if invMap (ofCharacter (irreducibleRepresentation k i)) =
        ofCharacter (irreducibleRepresentation k i) then 1 else 0 := by
  set f := invMap (ofCharacter (irreducibleRepresentation k i)) with hf
  -- the inverted character is the character of the dual representation, so a virtual character
  have hmem : (f : G → k) ∈ virtualCharacters k G := by
    have hdual : (f : G → k) = (FDRep.of (irreducibleRepresentation k i).dual).character := by
      rw [hf, invMap_ofCharacter]
      exact funext fun g => ofCharacter_apply _ g
    rw [hdual]
    exact character_mem_virtualCharacters _
  have hnorm : characterPairing f f = 1 := by
    rw [hf, characterPairing_invMap_invMap, characterPairing_ofCharacter_self]
  obtain ⟨j, hj⟩ := exists_eq_irreducibleCharacter_or_neg hmem hnorm
  have hone : (f : G → k) 1 = (characterDegree k i : k) := by rw [hf]; simp
  have hval : (f : G → k) = irreducibleCharacter k j := by
    refine hj.resolve_right fun h => absurd (characterDegree_pos k i) (Nat.not_lt.mpr ?_)
    rw [h] at hone
    have hcast : ((characterDegree k i + characterDegree k j : ℕ) : k) = ((0 : ℕ) : k) := by
      push_cast
      rw [← hone]
      simp
    have := Nat.cast_injective (R := k) hcast
    omega
  have hfj : f = ofCharacter (irreducibleRepresentation k j) :=
    Subtype.ext (hval.trans (funext fun g => by
      rw [ofCharacter_apply, character_irreducibleRepresentation]))
  rw [hfj, characterPairing_ofCharacter_irreducibleRepresentation_orthonormal]
  refine if_congr ⟨fun h => by rw [h], fun h => (irreducibleCharacter_injective k ?_).symm⟩ rfl rfl
  funext g
  have hg := congrFun (congrArg Subtype.val h) g
  rwa [ofCharacter_apply, ofCharacter_apply, character_irreducibleRepresentation,
    character_irreducibleRepresentation] at hg

open scoped Classical in
/-- **The row quantity of the character table.** For each irreducible character,
`|G|⁻¹ ∑_g χᵢ(g)²` is `1` when `χᵢ` is unchanged by inverting the group element, and `0`
otherwise. -/
theorem card_inv_mul_sum_irreducibleCharacter_sq [CharZero k]
    (i : Fin (Nat.card (ConjClasses G))) :
    (Nat.card G : k)⁻¹ * ∑ g : G, irreducibleCharacter k i g ^ 2 =
      if ∀ g : G, irreducibleCharacter k i g⁻¹ = irreducibleCharacter k i g then 1 else 0 := by
  have hval : characterPairing (ofCharacter (irreducibleRepresentation k i))
      (invMap (ofCharacter (irreducibleRepresentation k i))) =
      (Nat.card G : k)⁻¹ * ∑ g : G, irreducibleCharacter k i g ^ 2 := by
    rw [characterPairing_apply]
    congr 1
    exact Finset.sum_congr rfl fun g _ => by simp [pow_two]
  have hiff : (invMap (ofCharacter (irreducibleRepresentation k i)) =
      ofCharacter (irreducibleRepresentation k i)) ↔
      ∀ g : G, irreducibleCharacter k i g⁻¹ = irreducibleCharacter k i g := by
    rw [Subtype.ext_iff, funext_iff]
    simp
  by_cases hfix : ∀ g : G, irreducibleCharacter k i g⁻¹ = irreducibleCharacter k i g
  · rw [if_pos hfix, ← hval, characterPairing_ofCharacter_invMap_self, if_pos (hiff.mpr hfix)]
  · rw [if_neg hfix, ← hval, characterPairing_ofCharacter_invMap_self,
      if_neg fun h => hfix (hiff.mp h)]

end Rows

section Columns

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

open scoped Classical in
/-- **The column quantity of the character table.** Summing the squares of a column is the second
orthogonality relation applied to a class and its inverse: it is `|G| / |C|` when the class is
real, and `0` otherwise. -/
theorem sum_characterTable_sq (C : ConjClasses G) :
    ∑ i : Fin (Nat.card (ConjClasses G)), characterTable k G i C ^ 2 =
      if IsRealClass C then (Nat.card G : k) / Nat.card C.carrier else 0 := by
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  have h := sum_characterTable_mul_characterTable_inv (k := k) g g⁻¹
  rw [inv_inv] at h
  calc ∑ i : Fin (Nat.card (ConjClasses G)), characterTable k G i (ConjClasses.mk g) ^ 2
      = ∑ i : Fin (Nat.card (ConjClasses G)),
          characterTable k G i (ConjClasses.mk g) * characterTable k G i (ConjClasses.mk g) :=
        Finset.sum_congr rfl fun i _ => pow_two _
    _ = if IsConj g g⁻¹ then (Nat.card G : k) / Nat.card (ConjClasses.mk g).carrier else 0 := h
    _ = _ := if_congr isRealClass_mk_iff.symm rfl rfl

end Columns

section Counting

private theorem natCast_card_subtype {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (R : Type*) [Semiring R] :
    (Nat.card {a : α // p a} : R) = ∑ a : α, if p a then (1 : R) else 0 := by
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

open ClassFunction

variable (k : Type u) (G : Type v) [Field k] [CharZero k] [Group G] [Finite G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

/-- **A finite group has as many inversion-invariant rows in its character table as real conjugacy
classes.** -/
theorem card_inversionInvariant_eq_card_realClasses :
    Nat.card {i : Fin (Nat.card (ConjClasses G)) //
        ∀ C : ConjClasses G, characterTable k G i C⁻¹ = characterTable k G i C} =
      Nat.card {C : ConjClasses G // IsRealClass C} := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  have hG : (Nat.card G : k) ≠ 0 := Invertible.ne_zero _
  have hcolumn : ∀ i : Fin (Nat.card (ConjClasses G)),
      (∀ C : ConjClasses G, characterTable k G i C⁻¹ = characterTable k G i C) ↔
        ∀ g : G, irreducibleCharacter k i g⁻¹ = irreducibleCharacter k i g := by
    refine fun i => ⟨fun h g => by simpa using h (ConjClasses.mk g), fun h C => ?_⟩
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
    simpa using h g
  have hclass : ∀ i : Fin (Nat.card (ConjClasses G)),
      ∑ g : G, irreducibleCharacter k i g ^ 2 =
        ∑ C : ConjClasses G, (Nat.card C.carrier : k) * characterTable k G i C ^ 2 := by
    intro i
    have h := ClassFunction.sum_eq_sum_conjClasses
      (ofConjClasses (k := k) fun C => characterTable k G i C ^ 2)
    rw [toConjClasses_ofConjClasses] at h
    rw [← h]
    exact Finset.sum_congr rfl fun g _ => by
      simp only [ofConjClasses_apply, characterTable_apply]
  have key : ∑ i : Fin (Nat.card (ConjClasses G)),
        (if ∀ C : ConjClasses G, characterTable k G i C⁻¹ = characterTable k G i C then
          (1 : k) else 0) =
      ∑ C : ConjClasses G, (if IsRealClass C then (1 : k) else 0) :=
    calc ∑ i : Fin (Nat.card (ConjClasses G)),
          (if ∀ C : ConjClasses G, characterTable k G i C⁻¹ = characterTable k G i C then
            (1 : k) else 0)
        = ∑ i : Fin (Nat.card (ConjClasses G)),
            (Nat.card G : k)⁻¹ * ∑ g : G, irreducibleCharacter k i g ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [card_inv_mul_sum_irreducibleCharacter_sq]
          exact if_congr (hcolumn i) rfl rfl
      _ = (Nat.card G : k)⁻¹ * ∑ i : Fin (Nat.card (ConjClasses G)),
            ∑ C : ConjClasses G, (Nat.card C.carrier : k) * characterTable k G i C ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [hclass i]
      _ = (Nat.card G : k)⁻¹ * ∑ C : ConjClasses G,
            (Nat.card C.carrier : k) * ∑ i : Fin (Nat.card (ConjClasses G)),
              characterTable k G i C ^ 2 := by
          rw [Finset.sum_comm]
          exact congrArg (fun x => (Nat.card G : k)⁻¹ * x)
            (Finset.sum_congr rfl fun C _ => (Finset.mul_sum _ _ _).symm)
      _ = ∑ C : ConjClasses G, (if IsRealClass C then (1 : k) else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun C _ => ?_
          rw [sum_characterTable_sq]
          have hC : (Nat.card C.carrier : k) ≠ 0 := ConjClasses.card_carrier_cast_ne_zero C hG
          by_cases hR : IsRealClass C
          · rw [if_pos hR, if_pos hR]
            field_simp
          · rw [if_neg hR, if_neg hR, mul_zero, mul_zero]
  have hcast : ((Nat.card {i : Fin (Nat.card (ConjClasses G)) //
        ∀ C : ConjClasses G, characterTable k G i C⁻¹ = characterTable k G i C} : ℕ) : k) =
      ((Nat.card {C : ConjClasses G // IsRealClass C} : ℕ) : k) := by
    rw [natCast_card_subtype _ k, natCast_card_subtype _ k]
    exact key
  exact Nat.cast_injective hcast

/-- **A finite group has as many real-valued irreducible complex characters as real conjugacy
classes.**

A row of `TauCeti.characterTable ℂ G` is fixed by complex conjugation exactly when it is fixed by
inverting the class, because conjugating a character value inverts the group element. -/
theorem card_realValued_eq_card_realClasses (G : Type v) [Group G] [Finite G] :
    Nat.card {i : Fin (Nat.card (ConjClasses G)) //
        ∀ C : ConjClasses G, (starRingEnd ℂ) (characterTable ℂ G i C) = characterTable ℂ G i C} =
      Nat.card {C : ConjClasses G // IsRealClass C} := by
  rw [← card_inversionInvariant_eq_card_realClasses ℂ G]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun i =>
    forall_congr' fun C => by rw [conj_characterTable])

end Counting

end TauCeti
