/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.CentralCharacter
public import TauCeti.RepresentationTheory.CharacterTable.Values
public import TauCeti.RingTheory.RootsOfUnity.Complex

/-!
# Burnside's vanishing theorem for character values

Let `χ` be the character of an irreducible representation of a finite group `G`, and let `g` be an
element whose conjugacy class `C` has size coprime to the degree `χ(1)`. Then `χ(g)` is as far from
generic as it can be: either it vanishes, or it has the largest absolute value a character value
can have, namely `χ(1)`.

The proof has two halves.

*The arithmetic of the average.* Bézout writes `1 = a·|C| + b·χ(1)` with integers `a` and `b`, so

`χ(g) / χ(1) = a · (|C| χ(g) / χ(1)) + b · χ(g) = a · ωᵪ(K_C) + b · χ(g)`,

with `ωᵪ` the central character and `K_C` the class sum. Both `ωᵪ(K_C)` and `χ(g)` are algebraic
integers (`TauCeti.Representation.isIntegral_centralCharacter_classSumCenter` and
`TauCeti.Representation.isIntegral_char`), so the average `χ(g) / χ(1)` is one too. That is
`Representation.isIntegral_char_div_finrank`, proved over any algebraically closed field. This
first half is where the coprimality is spent.

*Kronecker's theorem.* Over `ℂ` the value `χ(g)` is a sum of `χ(1)` roots of unity, so once the
average is known to be an algebraic integer the dichotomy follows, with no arithmetic hypothesis of
its own: this is `TauCeti.sum_eq_zero_or_norm_sum_eq_card_of_isIntegral`.

The classical use of the dichotomy is Burnside's `pᵃqᵇ` theorem, which applies it to an element
whose class has prime-power size. Turning the second alternative `‖χ(g)‖ = χ(1)` into the
statement that `ρ g` is a scalar — the equality case of the triangle inequality for a sum of roots
of unity — is a separate step and is not proved here.

## Main statements

* `Representation.isIntegral_char_div_finrank` and its bundled form
  `FDRep.isIntegral_char_div_finrank`: when the class size and the degree are coprime, the average
  `χ(g) / χ(1)` is an algebraic integer.
* `Representation.char_eq_zero_or_norm_char_eq_finrank` and its bundled form
  `FDRep.char_eq_zero_or_norm_char_eq_finrank`: **Burnside's vanishing theorem**, the dichotomy
  `χ(g) = 0 ∨ ‖χ(g)‖ = χ(1)`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Theorem 3.8.
-/

public section

namespace TauCeti

open Module (finrank)

section Integrality

variable {k G V : Type*} [Field k] [IsAlgClosed k] [Group G] [Finite G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- **The average of an irreducible character over its degree is an algebraic integer**, whenever
the size of the conjugacy class of `g` is coprime to the degree.

Bézout splits `χ(g) / χ(1)` as an integer combination of the central-character value
`ωᵪ(K_C) = |C| χ(g) / χ(1)` and of `χ(g)`, both of which are algebraic integers. No hypothesis on
the characteristic is needed: if the degree happens to vanish in `k` the quotient is `0`, which is
an algebraic integer for the trivial reason. -/
theorem _root_.Representation.isIntegral_char_div_finrank (ρ : Representation k G V)
    [ρ.IsIrreducible] {g : G}
    (h : (Nat.card (ConjClasses.mk g).carrier).Coprime (finrank k V)) :
    IsIntegral ℤ (ρ.character g / (finrank k V : k)) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  rcases eq_or_ne (finrank k V : k) 0 with hd | hd
  · rw [hd, div_zero]
    exact isIntegral_zero
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have habk : (a : k) * (Nat.card (ConjClasses.mk g).carrier : k) + (b : k) * (finrank k V : k)
      = 1 := by
    have h' := congrArg (fun z : ℤ => (z : k)) hab
    push_cast at h'
    exact h'
  have hcentral :
      Representation.centralCharacter ρ (classSumCenter (ConjClasses.mk g)) * (finrank k V : k) =
        (Nat.card (ConjClasses.mk g).carrier : k) * ρ.character g := by
    rw [← ρ.char_one]
    exact Representation.centralCharacter_classSumCenter_mul_character_one ρ rfl
  have hexp : ρ.character g / (finrank k V : k) =
      (a : k) * Representation.centralCharacter ρ (classSumCenter (ConjClasses.mk g))
        + (b : k) * ρ.character g := by
    rw [div_eq_iff hd]
    calc ρ.character g
        = ((a : k) * (Nat.card (ConjClasses.mk g).carrier : k)
            + (b : k) * (finrank k V : k)) * ρ.character g := by rw [habk, one_mul]
      _ = (a : k) * ((Nat.card (ConjClasses.mk g).carrier : k) * ρ.character g)
            + ((b : k) * ρ.character g) * (finrank k V : k) := by ring
      _ = (a : k) * (Representation.centralCharacter ρ (classSumCenter (ConjClasses.mk g))
            * (finrank k V : k)) + ((b : k) * ρ.character g) * (finrank k V : k) := by
          rw [hcentral]
      _ = ((a : k) * Representation.centralCharacter ρ (classSumCenter (ConjClasses.mk g))
            + (b : k) * ρ.character g) * (finrank k V : k) := by ring
  have hchar : IsIntegral ℤ (ρ.character g) :=
    Representation.isIntegral_char ρ (isOfFinOrder_of_finite g).orderOf_pos.ne'
      (pow_orderOf_eq_one g)
  have hcast : ∀ m : ℤ, IsIntegral ℤ ((m : k)) := fun m => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := k) (x := m)
  rw [hexp]
  exact ((hcast a).mul
      (Representation.isIntegral_centralCharacter_classSumCenter ρ _)).add ((hcast b).mul hchar)

end Integrality

section Complex

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- **Burnside's vanishing theorem.** If the conjugacy class of `g` has size coprime to the degree
of an irreducible complex representation `ρ`, then its character either vanishes at `g` or attains
there the maximum absolute value `χ(1)` that any character value can have.

The average `χ(g) / χ(1)` is an algebraic integer (`Representation.isIntegral_char_div_finrank`)
and `χ(g)` is a sum of `χ(1)` roots of unity, so Kronecker's theorem leaves no other
possibility. -/
theorem _root_.Representation.char_eq_zero_or_norm_char_eq_finrank
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] {g : G}
    (h : (Nat.card (ConjClasses.mk g).carrier).Coprime (finrank ℂ V)) :
    ρ.character g = 0 ∨ ‖ρ.character g‖ = finrank ℂ V := by
  obtain ⟨s, hcard, hroot, hsum⟩ :=
    Representation.exists_multiset_rootsOfUnity_char_eq_sum ρ (pow_orderOf_eq_one g)
  have hint : IsIntegral ℤ (s.sum / (Multiset.card s : ℂ)) := by
    rw [← hsum, hcard]
    exact Representation.isIntegral_char_div_finrank ρ h
  rcases sum_eq_zero_or_norm_sum_eq_card_of_isIntegral
    (isOfFinOrder_of_finite g).orderOf_pos.ne' hroot hint with h0 | h1
  · exact Or.inl (hsum.trans h0)
  · exact Or.inr (by rw [hsum, h1, hcard])

end Complex

section Bundled

variable {G : Type*} [Group G] [Finite G]

/-- **The average of an irreducible character over its degree is an algebraic integer**, for a
bundled finite-dimensional representation over an algebraically closed field. -/
theorem _root_.FDRep.isIntegral_char_div_finrank {k : Type*} [Field k] [IsAlgClosed k]
    (X : FDRep k G) [_root_.Representation.IsIrreducible X.ρ] {g : G}
    (h : (Nat.card (ConjClasses.mk g).carrier).Coprime (finrank k X)) :
    IsIntegral ℤ (X.character g / (finrank k X : k)) :=
  Representation.isIntegral_char_div_finrank X.ρ h

/-- **Burnside's vanishing theorem**, for a bundled finite-dimensional complex representation. -/
theorem _root_.FDRep.char_eq_zero_or_norm_char_eq_finrank (X : FDRep ℂ G)
    [_root_.Representation.IsIrreducible X.ρ] {g : G}
    (h : (Nat.card (ConjClasses.mk g).carrier).Coprime (finrank ℂ X)) :
    X.character g = 0 ∨ ‖X.character g‖ = finrank ℂ X :=
  Representation.char_eq_zero_or_norm_char_eq_finrank X.ρ h

end Bundled

end TauCeti
