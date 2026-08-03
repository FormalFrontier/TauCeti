/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.GroupTheory.DoubleCoset
public import TauCeti.RepresentationTheory.CharacterTable.Pairing
public import TauCeti.RepresentationTheory.Induction.Permutation

/-!
# The pairing of two permutation characters counts double cosets

The character of a permutation representation `k[X]` counts fixed points, so the normalized
pairing of two permutation characters is the Burnside average
`|G|⁻¹ ∑ g, |X^g| · |Y^g|`, which counts the orbits of `G` on `X × Y`.  Taking `X = G ⧸ H` and
`Y = G ⧸ K` and identifying those orbits with double cosets gives

`⟨Ind_H^G 1, Ind_K^G 1⟩_G = #(H \ G / K)`,

the pairing of two induced trivial representations.

## Main statements

* `TauCeti.sum_character_ofMulAction_mul_character_ofMulAction`: Burnside's lemma as an unnormalized
  identity of character sums.
* `TauCeti.characterPairing_ofMulAction`: the pairing of two permutation characters is the number
  of orbits of `G` on the product.
* `TauCeti.characterPairing_ofMulAction_quotient`: the specialization to two coset spaces, whose
  value is the number of double cosets.
* `TauCeti.characterPairing_ind_trivial`: the same value for the pairing of two induced trivial
  representations.

## Implementation notes

All the identities are equalities in the coefficient field `k`, with the counts cast into `k`, and
the normalized ones assume `IsUnit (Nat.card G : k)` so that the `|G|⁻¹` in
`TauCeti.ClassFunction.characterPairing` is meaningful.  No algebraic closure and no orthogonality
of irreducible characters is used: the proof is Burnside's lemma, not a decomposition of the
permutation representation into irreducibles.  In particular the statements are valid in
characteristic `p` for `p ∤ |G|`, where the permutation representation need not be semisimple over
`k` as a module but its character still counts fixed points.

The pairing `⟨χ, ψ⟩ = |G|⁻¹ ∑ g, χ g * ψ g⁻¹` is bilinear rather than Hermitian, and the inversion
in its second argument is exactly what `MulAction.fixedBy_inv` absorbs.

## References

This is the "`⟨Ind_H^G 1, Ind_H^G 1⟩_G = #(H \ G / H)`" clause of the permutation-character item of
Layer 2 in `TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`, proved here for
two possibly different subgroups.

* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 7.3, Exercise 7.3.
-/

public section

open MulAction

namespace TauCeti

open ClassFunction

universe u v w

variable (k : Type u) {G : Type v} [Field k] [Group G]

/-- The character of a permutation representation at `g` is the number of points of the `G`-set
fixed by `g`, in the `MulAction.fixedBy` phrasing that Burnside's lemma uses. -/
private theorem char_ofMulAction_eq_card_fixedBy (X : Type w) [MulAction G X] [Finite X] (g : G) :
    (Representation.ofMulAction k G X).character g = Nat.card (fixedBy X g) :=
  char_ofMulAction k X g

/-- The character of an induced trivial representation is the coset permutation character. -/
private theorem ofCharacter_ind_trivial (H : Subgroup G) [Finite (G ⧸ H)] :
    ofCharacter ((Representation.trivial k H k).ind H.subtype) =
      ofCharacter (Representation.ofMulAction k G (G ⧸ H)) :=
  Subtype.ext (funext fun g => by
    rw [ofCharacter_apply, ofCharacter_apply, Representation.char_iso (indTrivialEquiv k H)])

section Fintype

variable [Fintype G] (X Y : Type w) [MulAction G X] [MulAction G Y] [Finite X] [Finite Y]

/-- **Burnside's lemma for two permutation characters.** The unnormalized sum
`∑ g, χ_X(g) · χ_Y(g⁻¹)` is the number of orbits of `G` on `X × Y` times the order of `G`.

This form carries no division, so it holds over any field. -/
theorem sum_character_ofMulAction_mul_character_ofMulAction :
    ∑ g : G, (Representation.ofMulAction k G X).character g *
        (Representation.ofMulAction k G Y).character g⁻¹ =
      (Nat.card (orbitRel.Quotient G (X × Y)) : k) * Nat.card G := by
  have hsum : ∀ g : G, (Representation.ofMulAction k G X).character g *
      (Representation.ofMulAction k G Y).character g⁻¹ =
      ((Nat.card (fixedBy X g) * Nat.card (fixedBy Y g) : ℕ) : k) := by
    intro g
    rw [char_ofMulAction_eq_card_fixedBy, char_ofMulAction_eq_card_fixedBy, fixedBy_inv,
      Nat.cast_mul]
  rw [Finset.sum_congr rfl fun g _ => hsum g, ← Nat.cast_sum,
    sum_card_fixedBy_mul_card_fixedBy X Y, Nat.cast_mul]

/-- **The pairing of two permutation characters counts orbits on the product.** For a finite group
`G` whose order is invertible in `k`, the normalized pairing of the characters of `k[X]` and `k[Y]`
is the number of orbits of `G` on `X × Y`. -/
theorem characterPairing_ofMulAction (hG : IsUnit (Nat.card G : k)) :
    characterPairing (ofCharacter (Representation.ofMulAction k G X))
        (ofCharacter (Representation.ofMulAction k G Y)) =
      (Nat.card (orbitRel.Quotient G (X × Y)) : k) := by
  rw [characterPairing_ofCharacter, sum_character_ofMulAction_mul_character_ofMulAction,
    mul_comm (Nat.card (orbitRel.Quotient G (X × Y)) : k), inv_mul_cancel_left₀ hG.ne_zero]

end Fintype

section Subgroups

variable [Fintype G] (H K : Subgroup G)

/-- **The pairing of two coset permutation characters counts double cosets.** For a finite group
`G` whose order is invertible in `k`, the normalized pairing of the characters of `k[G ⧸ H]` and
`k[G ⧸ K]` is the number of double cosets `H \ G / K`. -/
theorem characterPairing_ofMulAction_quotient (hG : IsUnit (Nat.card G : k)) :
    characterPairing (ofCharacter (Representation.ofMulAction k G (G ⧸ H)))
        (ofCharacter (Representation.ofMulAction k G (G ⧸ K))) =
      (Nat.card (DoubleCoset.Quotient (H : Set G) K) : k) := by
  rw [characterPairing_ofMulAction k (G ⧸ H) (G ⧸ K) hG, card_doubleCosetQuotient]

/-- **The pairing of two induced trivial representations counts double cosets.** For a finite
group `G` whose order is invertible in `k`, the pairing of the characters of `Ind_H^G 1` and
`Ind_K^G 1` is the number of double cosets `H \ G / K`.

For `K = H` this is the classical statement that `⟨Ind_H^G 1, Ind_H^G 1⟩_G` counts `H \ G / H`. -/
theorem characterPairing_ind_trivial (hG : IsUnit (Nat.card G : k)) :
    characterPairing (ofCharacter ((Representation.trivial k H k).ind H.subtype))
        (ofCharacter ((Representation.trivial k K k).ind K.subtype)) =
      (Nat.card (DoubleCoset.Quotient (H : Set G) K) : k) := by
  rw [ofCharacter_ind_trivial, ofCharacter_ind_trivial,
    characterPairing_ofMulAction_quotient k H K hG]

end Subgroups

end TauCeti
