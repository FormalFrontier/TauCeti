/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.ClassEquation
public import TauCeti.RepresentationTheory.CharacterTable.Degree
public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Eigenrow

/-!
# Recovering the character of an irreducible representation from its central character

The central character `ωᵪ : Z(k[G]) →ₐ[k] k` of an irreducible representation is what the
Burnside--Dixon--Schneider algorithm computes: its row of values on the class sums,
`TauCeti.classSumRow`, is a normalized common left eigenrow of the class-multiplication matrices.
This file shows that the row determines the character it came from, so that the *central* character
table `Ω` determines the ordinary character table `X`.

Two identities do the work. The first is the division-free class-sum identity
`ωᵪ(K_C) · χ(1) = |C| · χ(g_C)` of
`TauCeti.Representation.centralCharacter_classSumCenter_mul_character_one`, which recovers the value
`χ(g_C)` from `ωᵪ(K_C)` *once the degree is known*. The second recovers the degree from the row
alone. Writing

`classRowNorm v = ∑_C v(C) v(C⁻¹) / |C|`

for the quantity Dixon divides by, substituting the first identity into first orthogonality — in the
form `χ(1) · ∑_C ωᵪ(K_C) χ(g_C⁻¹) = |G|` already proved as
`TauCeti.Representation.finrank_mul_sum_centralCharacter_eq_card` — gives

`χ(1)² · classRowNorm (C ↦ ωᵪ(K_C)) = |G|`.

Only the *square* of the degree is recovered this way; that the degree itself is the positive square
root is what the natural-number valuedness of `χ(1)` supplies, and it is why a specification of a
character table has to demand a natural degree rather than compute one.

Inversion of conjugacy classes, `TauCeti.instInvolutiveInvConjClasses`, enters through the second
factor `v(C⁻¹)`: the row is read both at `C` and at the inverse class, so the recovery is a
computation on `Ω` alone.

## Main definitions

* `TauCeti.classRowNorm`: the weighted self-pairing `∑_C v(C) v(C⁻¹) / |C|` of a row of scalars
  indexed by the conjugacy classes; the denominator in Dixon's degree formula.

## Main statements

* `TauCeti.Representation.finrank_sq_mul_classRowNorm_eq_card`: **degree recovery**,
  `χ(1)² · classRowNorm (C ↦ ωᵪ(K_C)) = |G|`, with
  `TauCeti.Representation.finrank_sq_eq_card_div_classRowNorm` the quotient form.
* `TauCeti.Representation.character_eq_finrank_mul_centralCharacter_div`: the character value
  `χ(g_C) = χ(1) · ωᵪ(K_C) / |C|` recovered from the central character.
* `TauCeti.Representation.finrank_eq_of_classSumRow_eq` and
  `TauCeti.Representation.character_eq_of_classSumRow_eq`: two irreducible representations whose
  central characters have the same row of values on the class sums have the same degree, and the
  same character.
* `TauCeti.Representation.classRowNorm_classSumRow_centralCharacter_trivial`: the worked case of the
  trivial representation, where degree recovery is the statement that the classes partition `G`.

## References

This proves the "normalization and degree recovery" item of Layer 5 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md).
See I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 3, and J. D. Dixon, *High speed
computation of group characters*, Numer. Math. **10** (1967), 446-450.
-/

public section

namespace TauCeti

open Module (finrank)
open scoped MonoidAlgebra

section ClassRowNorm

variable {k G : Type*} [DivisionSemiring k] [Group G] [Fintype (ConjClasses G)]

/-- The **class-row norm** of a row of scalars indexed by the conjugacy classes of `G`:
`∑_C v(C) v(C⁻¹) / |C|`, each term weighted by the reciprocal of the size of the class.

On the row `C ↦ ωᵪ(K_C)` of an irreducible central character this is the denominator of Dixon's
degree formula: `TauCeti.Representation.finrank_sq_eq_card_div_classRowNorm` divides `|G|` by it to
get the square of the degree. Because it is a function of the row, a degree read off it depends only
on the central character table `Ω`. -/
noncomputable def classRowNorm (v : ConjClasses G → k) : k :=
  ∑ C : ConjClasses G, v C * v C⁻¹ / (Nat.card C.carrier : k)

/-- The defining formula for `TauCeti.classRowNorm`. -/
theorem classRowNorm_def (v : ConjClasses G → k) :
    classRowNorm v = ∑ C : ConjClasses G, v C * v C⁻¹ / (Nat.card C.carrier : k) :=
  (rfl)

end ClassRowNorm

variable {k G : Type*} [Field k] [Group G] [Fintype G] [DecidableEq G]

namespace Representation

variable {V : Type*} [AddCommGroup V] [Module k V]
variable [IsAlgClosed k] [FiniteDimensional k V] (ρ : Representation k G V) [ρ.IsIrreducible]

/-- **The character value recovered from the central character.** On the class of `g`, the character
is the degree times the value of the central character on the class sum, divided by the size of the
class; the class size is assumed nonzero, which is all the division needs.

This is the conversion from a row of the central character table `Ω` to the corresponding row of the
ordinary character table `X`; the degree it needs is supplied by
`TauCeti.Representation.finrank_sq_mul_classRowNorm_eq_card`. When the order of the group is
invertible in `k`, the hypothesis on the class size comes from
`TauCeti.ConjClasses.card_carrier_cast_ne_zero`. -/
theorem character_eq_finrank_mul_centralCharacter_div {C : ConjClasses G} {g : G}
    (hg : ConjClasses.mk g = C) (hcard : (Nat.card C.carrier : k) ≠ 0) :
    ρ.character g =
      (finrank k V : k) * centralCharacter ρ (classSumCenter C) / (Nat.card C.carrier : k) := by
  have h := centralCharacter_classSumCenter_mul_character_one ρ hg
  rw [ρ.char_one] at h
  exact eq_div_of_mul_eq hcard (by linear_combination -h)

variable [Invertible (Nat.card G : k)]

/-- **Degree recovery.** The square of the degree of an irreducible representation, multiplied by
the class-row norm of its central character, is the group order:

`χ(1)² · ∑_C ωᵪ(K_C) ωᵪ(K_{C⁻¹}) / |C| = |G|`.

Substituting the class-sum identity `ωᵪ(K_{C⁻¹}) · χ(1) = |C| · χ(g_C⁻¹)` into first orthogonality,
collected one conjugacy class at a time as
`TauCeti.Representation.finrank_mul_sum_centralCharacter_eq_card`, replaces the character values by
central-character values at the cost of one further factor of the degree.

Only the square of the degree is recovered; see
`TauCeti.Representation.finrank_eq_of_classSumRow_eq` for the step that pins the degree itself. -/
theorem finrank_sq_mul_classRowNorm_eq_card :
    (finrank k V : k) ^ 2 * classRowNorm (classSumRow (centralCharacter ρ)) = Nat.card G := by
  have key : ∀ C : ConjClasses G, (finrank k V : k) * (classSumRow (centralCharacter ρ) C *
      classSumRow (centralCharacter ρ) C⁻¹ / (Nat.card C.carrier : k)) =
      centralCharacter ρ (classSumCenter C) *
        ClassFunction.toConjClasses (ClassFunction.ofCharacter ρ.dual) C := by
    intro C
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
    have hcard : (Nat.card (ConjClasses.mk g).carrier : k) ≠ 0 :=
      ConjClasses.card_carrier_cast_ne_zero _ (Invertible.ne_zero _)
    have hdual : ClassFunction.toConjClasses (ClassFunction.ofCharacter ρ.dual)
        (ConjClasses.mk g) = ρ.character g⁻¹ := by
      rw [ClassFunction.toConjClasses_mk, ClassFunction.ofCharacter_apply, ρ.char_dual]
    have hchar := character_eq_finrank_mul_centralCharacter_div ρ (ConjClasses.inv_mk g).symm
      (by rwa [ConjClasses.card_carrier_inv])
    rw [ConjClasses.card_carrier_inv] at hchar
    rw [hdual, hchar, classSumRow_apply, classSumRow_apply]
    field_simp
  calc (finrank k V : k) ^ 2 * classRowNorm (classSumRow (centralCharacter ρ))
      = (finrank k V : k) * ∑ C : ConjClasses G, (finrank k V : k) *
          (classSumRow (centralCharacter ρ) C * classSumRow (centralCharacter ρ) C⁻¹ /
            (Nat.card C.carrier : k)) := by
        rw [classRowNorm_def, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun C _ => by ring
    _ = (finrank k V : k) * ∑ C : ConjClasses G, centralCharacter ρ (classSumCenter C) *
          ClassFunction.toConjClasses (ClassFunction.ofCharacter ρ.dual) C := by
        rw [Finset.sum_congr rfl fun C _ => key C]
    _ = Nat.card G := finrank_mul_sum_centralCharacter_eq_card ρ

/-- The class-row norm of an irreducible central character is nonzero, so degree recovery may be
divided through by it: the group order is invertible, so the product it factors through cannot
vanish. -/
theorem classRowNorm_classSumRow_ne_zero :
    classRowNorm (classSumRow (centralCharacter ρ)) ≠ 0 := fun h => by
  have hrec := finrank_sq_mul_classRowNorm_eq_card ρ
  rw [h, mul_zero] at hrec
  exact Invertible.ne_zero (Nat.card G : k) hrec.symm

/-- **Degree recovery, in quotient form**: the square of the degree is the group order divided by
the class-row norm of the central character, a quantity read off the central character table
alone. -/
theorem finrank_sq_eq_card_div_classRowNorm :
    (finrank k V : k) ^ 2 =
      (Nat.card G : k) / classRowNorm (classSumRow (centralCharacter ρ)) :=
  eq_div_of_mul_eq (classRowNorm_classSumRow_ne_zero ρ) (finrank_sq_mul_classRowNorm_eq_card ρ)

/-! ### The trivial representation -/

section Trivial

variable (k G)

/-- **The worked case of the trivial representation.** Its central character sends a class sum to
the size of the class, so every term of the class-row norm is a class size, and the class-row norm
is the group order.

Degree recovery then reads `1² · |G| = |G|`: on the trivial representation the formula is exactly
the statement that the conjugacy classes partition the group. -/
@[simp]
theorem classRowNorm_classSumRow_centralCharacter_trivial :
    classRowNorm (classSumRow (centralCharacter (_root_.Representation.trivial k G k))) =
      Nat.card G := by
  have hpart : ∑ C : ConjClasses G, Nat.card C.carrier = Nat.card G := by
    rw [← Group.sum_card_conj_classes_eq_card G, finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun C _ => Nat.card_coe_set_eq C.carrier
  have hterm : ∀ C : ConjClasses G,
      classSumRow (centralCharacter (_root_.Representation.trivial k G k)) C *
          classSumRow (centralCharacter (_root_.Representation.trivial k G k)) C⁻¹ /
            (Nat.card C.carrier : k) = (Nat.card C.carrier : k) := fun C => by
    rw [classSumRow_apply, classSumRow_apply, centralCharacter_trivial_classSumCenter,
      centralCharacter_trivial_classSumCenter, ConjClasses.card_carrier_inv]
    exact mul_div_cancel_right₀ _
      (ConjClasses.card_carrier_cast_ne_zero C (Invertible.ne_zero _))
  rw [classRowNorm_def, Finset.sum_congr rfl fun C _ => hterm C, ← Nat.cast_sum, hpart]

end Trivial

end Representation

namespace Representation

variable {V W : Type*} [CharZero k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable [IsAlgClosed k] [FiniteDimensional k V] [FiniteDimensional k W]
  (ρ : Representation k G V) (σ : Representation k G W) [ρ.IsIrreducible] [σ.IsIrreducible]
variable (hρσ : classSumRow (centralCharacter ρ) = classSumRow (centralCharacter σ))

include hρσ

/-- **The degree of an irreducible representation is determined by its central character.** Degree
recovery gives the square of the degree as a function of the row of values of the central character
on the class sums, and a natural number is determined by its square. -/
theorem finrank_eq_of_classSumRow_eq : finrank k V = finrank k W := by
  have : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hsq : ((finrank k V ^ 2 : ℕ) : k) = ((finrank k W ^ 2 : ℕ) : k) := by
    push_cast
    rw [finrank_sq_eq_card_div_classRowNorm ρ, finrank_sq_eq_card_div_classRowNorm σ, hρσ]
  exact (pow_left_inj two_ne_zero).mp (Nat.cast_injective hsq)

/-- **The character of an irreducible representation is determined by its central character.** The
degree is determined by `TauCeti.Representation.finrank_eq_of_classSumRow_eq`, and the values follow
from it by `TauCeti.Representation.character_eq_finrank_mul_centralCharacter_div`.

This is what makes the central character table `Ω` a faithful record of the ordinary character
table `X`. -/
theorem character_eq_of_classSumRow_eq : ρ.character = σ.character := by
  have : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  funext g
  have hcard : (Nat.card (ConjClasses.mk g).carrier : k) ≠ 0 :=
    ConjClasses.card_carrier_cast_ne_zero _ (Invertible.ne_zero _)
  rw [character_eq_finrank_mul_centralCharacter_div ρ (rfl : ConjClasses.mk g = _) hcard,
    character_eq_finrank_mul_centralCharacter_div σ (rfl : ConjClasses.mk g = _) hcard,
    finrank_eq_of_classSumRow_eq ρ σ hρσ, ← classSumRow_apply, hρσ, classSumRow_apply]

end Representation

end TauCeti
