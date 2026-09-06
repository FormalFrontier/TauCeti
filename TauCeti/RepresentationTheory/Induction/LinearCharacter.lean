/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Character
public import TauCeti.RepresentationTheory.Induction.FiniteDimensional
public import TauCeti.RepresentationTheory.LinearCharacter

/-!
# Inducing a linear character

Two facts about `Ind_N^G` applied to a linear character, both independent of any irreducibility
question and so of the Mackey theory that the worked examples go on to use.

The first is a dimension count. Induction from a subgroup of finite index multiplies the dimension
by the index (`TauCeti.finrank_indFDRep`), and the representation carrying a linear character is a
line (`FDRep.finrank_ofLinearCharacter`), so what a linear character of `N` induces to has
dimension exactly `N.index`, whatever the group and whatever the character: this is the count every
worked example of induction from a linear character opens with.

The second is a character identity, for the special case of a linear character of `N` that extends
to the ambient group -- that is, one of the form `χ ∘ N.subtype` for `χ : G →* kˣ`. The induced
character formula sums `χ` over the conjugates `x⁻¹ g x` that land in `N`, and `χ` is a character
of the *whole* group, so every one of those summands is `χ g`: the sum only counts them.
Consequently the character of `Ind_N^G (Res_N χ)` is `χ` times the permutation character
`Ind_N^G 1`. This is the character-level shadow of the projection formula
`TauCeti.indProjection`, `Ind_N^G (A ⊗ Res_N B) ≅ Ind_N^G A ⊗ B`, read at `A` trivial and `B` the
line of `χ`; stating it directly on characters avoids transporting that isomorphism of `Rep k G`
across the finite-dimensional model `TauCeti.indFDRep`, and the character is what the consumers --
decompositions of small induced representations -- actually pair against.

## Main statements

* `TauCeti.finrank_indFDRep_ofLinearCharacter`: what a linear character induces to has the
  dimension of the index of the subgroup.
* `TauCeti.character_indFDRep_ofLinearCharacter_comp_subtype`: inducing the restriction of a
  linear character of the ambient group multiplies the permutation character by that character.
-/

public section

namespace TauCeti

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G] {N : Subgroup G} [N.FiniteIndex]

/-- **What a linear character induces to has the dimension of the index of the subgroup.**
Induction multiplies the dimension by the index, and the representation carrying a linear
character is a line. -/
theorem finrank_indFDRep_ofLinearCharacter (χ : N →* kˣ) :
    Module.finrank k (indFDRep (FDRep.ofLinearCharacter χ)) = N.index := by
  rw [finrank_indFDRep, FDRep.finrank_ofLinearCharacter, mul_one]

open scoped Classical in
/-- **Inducing the restriction of a linear character of the ambient group multiplies the
permutation character by that character.** The induced character at `g` averages the values of the
inducing character over the conjugates `x⁻¹ g x` lying in `N`; when that character is the
restriction of `χ : G →* kˣ`, each such value is `χ (x⁻¹ g x) = χ g`, so `χ g` factors out of the
average and what is left is the average of `1`, the character of `Ind_N^G 1`.

The subgroup order must be invertible in `k`, as it is for `TauCeti.character_ind`, both averages
dividing by it. -/
theorem character_indFDRep_ofLinearCharacter_comp_subtype [Finite G]
    (hN : IsUnit (Nat.card N : k)) (χ : G →* kˣ) (g : G) :
    (indFDRep (FDRep.ofLinearCharacter (χ.comp N.subtype))).character g =
      (χ g : k) * (indFDRep (FDRep.of (Representation.trivial k N k))).character g := by
  let _ : Fintype G := Fintype.ofFinite G
  have hterm : ∀ x : G, (if h : x⁻¹ * g * x ∈ N then
        (FDRep.ofLinearCharacter (χ.comp N.subtype)).character ⟨x⁻¹ * g * x, h⟩ else 0)
      = (χ g : k) * (if h : x⁻¹ * g * x ∈ N then
        (FDRep.of (Representation.trivial k N k)).character ⟨x⁻¹ * g * x, h⟩ else 0) := by
    intro x
    by_cases h : x⁻¹ * g * x ∈ N
    · -- `χ` is a character of `G`, so it does not see the conjugation.
      have hconj : χ (x⁻¹ * g * x) = χ g := by
        rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
      rw [dite_eq_left h, dite_eq_left h, FDRep.char_ofLinearCharacter,
        FDRep.character_of_trivial, mul_one]
      simp [hconj]
    · rw [dite_eq_right h, dite_eq_right h, mul_zero]
  rw [character_ind hN, character_ind hN, Finset.sum_congr rfl (fun x _ => hterm x),
    ← Finset.mul_sum]
  ring

end TauCeti
