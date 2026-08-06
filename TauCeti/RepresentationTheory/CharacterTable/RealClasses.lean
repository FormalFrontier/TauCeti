/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Table

/-!
# Real conjugacy classes and inversion-invariant rows of the character table

A conjugacy class of a group is **real** when it contains an element conjugate to its own inverse;
equivalently, when it is fixed by the inversion involution on `ConjClasses G`. A row of the
character table is **inversion-invariant** when the character it lists takes the same value at `g`
and at `g⁻¹`; over `ℂ` that is exactly the row being real-valued, because complex conjugation of a
character value inverts the group element.

This file proves that a finite group has as many inversion-invariant rows as real classes, and over
`ℂ` as many real-valued irreducible characters as real classes.

Both counts are read off the same quantity, `|G|⁻¹ ∑_g χᵢ(g)²`, summed over the whole table. Down
the columns it is the second orthogonality relation applied to a class and its inverse, and it
detects real classes. Along the rows it is the coefficient of `χᵢ` in the expansion of the twisted
character `g ↦ χᵢ(g⁻¹)`, and it detects inversion-invariant rows: the twist
`TauCeti.ClassFunction.invMap` is an isometry of the character pairing, so the twisted character
still pairs to `1` with itself, while all of its expansion coefficients are dimensions of
intertwiner spaces, hence natural numbers. A sum of squares of natural numbers equal to `1` has a
single nonzero term, so the twisted character is again one of the rows, and it is the `i`-th row
exactly when the `i`-th row is inversion-invariant.

That the twisted character is again an irreducible character is *proved* here rather than assumed:
no irreducibility of the dual representation is needed as an input.

## Main statements

* `TauCeti.IsRealClass`: a conjugacy class containing an element conjugate to its own inverse,
  with `TauCeti.isRealClass_iff_inv_eq` identifying it with being fixed by inversion.
* `TauCeti.characterPairing_self_eq_sum_sq`: Parseval for the character pairing against the rows
  of the character table, the expansion this file runs the argument through.
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

section RealClass

variable {G : Type v} [Group G]

/-- **A real conjugacy class**: one containing an element conjugate to its own inverse. -/
def IsRealClass (C : ConjClasses G) : Prop :=
  ∃ g : G, ConjClasses.mk g = C ∧ IsConj g g⁻¹

/-- **A class is real exactly when inversion fixes it.** -/
theorem isRealClass_iff_inv_eq {C : ConjClasses G} : IsRealClass C ↔ C⁻¹ = C := by
  constructor
  · rintro ⟨g, rfl, hg⟩
    rw [ConjClasses.inv_mk, ConjClasses.mk_eq_mk_iff_isConj]
    exact hg.symm
  · intro h
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
    rw [ConjClasses.inv_mk, ConjClasses.mk_eq_mk_iff_isConj] at h
    exact ⟨g, rfl, h.symm⟩

/-- The class of `g` is real exactly when `g` is conjugate to `g⁻¹`. -/
theorem isRealClass_mk_iff {g : G} : IsRealClass (ConjClasses.mk g) ↔ IsConj g g⁻¹ := by
  rw [isRealClass_iff_inv_eq, ConjClasses.inv_mk, ConjClasses.mk_eq_mk_iff_isConj]
  exact ⟨IsConj.symm, IsConj.symm⟩

/-- The class of the identity is real. -/
theorem isRealClass_one : IsRealClass (1 : ConjClasses G) :=
  isRealClass_iff_inv_eq.mpr ConjClasses.inv_one

end RealClass

section Rows

open ClassFunction

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

/-- **Parseval for the character pairing.** The rows of the character table are an orthonormal
basis of the class functions, so the self-pairing of a class function is the sum of the squares of
its expansion coefficients.

The pairing is bilinear rather than Hermitian, so the coefficients are squared, not multiplied by
their conjugates; over `ℂ` this is Parseval for the pairing `⟨f₁, f₂⟩ = |G|⁻¹ ∑_g f₁(g) f₂(g⁻¹)`. -/
theorem characterPairing_self_eq_sum_sq (f : ClassFunction k G) :
    characterPairing f f =
      ∑ i : Fin (Nat.card (ConjClasses G)),
        characterPairing (ofCharacter (irreducibleRepresentation k i)) f ^ 2 := by
  have hexp := sum_characterPairing_smul_ofCharacter (irreducibleRepresentation k)
    (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp) f
  calc characterPairing f f
      = characterPairing
          (∑ i, characterPairing (ofCharacter (irreducibleRepresentation k i)) f •
            ofCharacter (irreducibleRepresentation k i)) f := by rw [hexp]
    _ = ∑ i, characterPairing (ofCharacter (irreducibleRepresentation k i)) f ^ 2 := by
        rw [map_sum, LinearMap.sum_apply]
        exact Finset.sum_congr rfl fun i _ => by
          rw [map_smul, LinearMap.smul_apply, smul_eq_mul, sq]

/-- **The expansion coefficients of an inverted irreducible character are dimensions.** Inverting
the group element turns a character into the character of the dual representation, so the
coefficient of `χⱼ` is the dimension of a space of intertwiners, in particular a natural number. -/
theorem characterPairing_invMap_eq_finrank (i j : Fin (Nat.card (ConjClasses G))) :
    characterPairing (ofCharacter (irreducibleRepresentation k j))
        (invMap (ofCharacter (irreducibleRepresentation k i))) =
      Module.finrank k (Representation.IntertwiningMap (irreducibleRepresentation k i).dual
        (irreducibleRepresentation k j)) := by
  rw [invMap_ofCharacter, characterPairing_ofCharacter_eq_finrank]

/-- The squares of the expansion coefficients of an inverted irreducible character add up to `1`:
inversion is an isometry of the character pairing, so the inverted character still pairs to `1`
with itself. -/
private theorem sum_characterPairing_invMap_sq (i : Fin (Nat.card (ConjClasses G))) :
    ∑ j : Fin (Nat.card (ConjClasses G)),
        characterPairing (ofCharacter (irreducibleRepresentation k j))
          (invMap (ofCharacter (irreducibleRepresentation k i))) ^ 2 = 1 := by
  rw [← characterPairing_self_eq_sum_sq, characterPairing_invMap_invMap,
    characterPairing_ofCharacter_self]

open scoped Classical in
/-- **An irreducible character pairs with its own inversion to `1` or to `0`**, according as
inverting the group element leaves it unchanged or not.

This is the statement that carries the content: the coefficients of the inverted character are
natural numbers whose squares add up to `1`, so exactly one of them is `1` and the rest vanish.
The inverted character is therefore again one of the rows of the character table — a fact proved
here, not assumed — and it is the `i`-th row exactly when the `i`-th row is inversion-invariant. -/
theorem characterPairing_ofCharacter_invMap_self [CharZero k]
    (i : Fin (Nat.card (ConjClasses G))) :
    characterPairing (ofCharacter (irreducibleRepresentation k i))
        (invMap (ofCharacter (irreducibleRepresentation k i))) =
      if invMap (ofCharacter (irreducibleRepresentation k i)) =
        ofCharacter (irreducibleRepresentation k i) then 1 else 0 := by
  by_cases hfix : invMap (ofCharacter (irreducibleRepresentation k i)) =
      ofCharacter (irreducibleRepresentation k i)
  · rw [if_pos hfix, hfix, characterPairing_ofCharacter_self]
  rw [if_neg hfix]
  by_contra hne
  have hex : ∀ j : Fin (Nat.card (ConjClasses G)), ∃ n : ℕ,
      characterPairing (ofCharacter (irreducibleRepresentation k j))
        (invMap (ofCharacter (irreducibleRepresentation k i))) = n :=
    fun j => ⟨_, characterPairing_invMap_eq_finrank i j⟩
  choose m hm using hex
  have hsumk : ∑ j : Fin (Nat.card (ConjClasses G)), (m j : k) ^ 2 = 1 := by
    rw [← sum_characterPairing_invMap_sq i]
    exact Finset.sum_congr rfl fun j _ => by rw [hm j]
  have hsumn : ∑ j : Fin (Nat.card (ConjClasses G)), m j ^ 2 = 1 := by
    have hcast : ((∑ j : Fin (Nat.card (ConjClasses G)), m j ^ 2 : ℕ) : k) = ((1 : ℕ) : k) := by
      push_cast
      rw [hsumk]
    exact Nat.cast_injective hcast
  have hmi : m i ≠ 0 := fun h0 => hne (by rw [hm i, h0, Nat.cast_zero])
  have hle : m i ^ 2 ≤ 1 := hsumn ▸ Finset.single_le_sum
    (f := fun j : Fin (Nat.card (ConjClasses G)) => m j ^ 2)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hmi1 : m i = 1 :=
    le_antisymm ((Nat.le_self_pow two_ne_zero (m i)).trans hle) (Nat.one_le_iff_ne_zero.mpr hmi)
  have hzero : ∀ j : Fin (Nat.card (ConjClasses G)), j ≠ i → m j = 0 := by
    intro j hj
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun j : Fin (Nat.card (ConjClasses G)) => m j ^ 2) (Finset.mem_univ i)
    rw [hsumn, hmi1, one_pow] at hsplit
    have herase : ∑ l ∈ Finset.univ.erase i, m l ^ 2 = 0 := by omega
    have := (Finset.sum_eq_zero_iff.mp herase) j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
    simpa using this
  refine hfix ?_
  have hexp := sum_characterPairing_smul_ofCharacter (irreducibleRepresentation k)
    (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp)
    (invMap (ofCharacter (irreducibleRepresentation k i)))
  rw [← hexp, Finset.sum_eq_single i]
  · rw [hm i, hmi1, Nat.cast_one, one_smul]
  · exact fun j _ hj => by rw [hm j, hzero j hj, Nat.cast_zero, zero_smul]
  · exact fun h => absurd (Finset.mem_univ i) h

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

/-- **Complex conjugation of a character-table entry inverts the class**, in the class-indexed
form: `TauCeti.conj_characterTable_apply` is the same statement about a representative. -/
theorem conj_characterTable {G : Type v} [Group G] [Finite G]
    (i : Fin (Nat.card (ConjClasses G))) (C : ConjClasses G) :
    (starRingEnd ℂ) (characterTable ℂ G i C) = characterTable ℂ G i C⁻¹ := by
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  rw [ConjClasses.inv_mk, conj_characterTable_apply]

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
classes.**

Both counts are the total `|G|⁻¹ ∑_i ∑_g χᵢ(g)²` of the square of the table, read once along the
rows (`TauCeti.card_inv_mul_sum_irreducibleCharacter_sq`) and once down the columns
(`TauCeti.sum_characterTable_sq`). -/
theorem card_invariantRow_eq_card_realClasses :
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
  rw [← card_invariantRow_eq_card_realClasses ℂ G]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun i =>
    forall_congr' fun C => by rw [conj_characterTable])

end Counting

end TauCeti
