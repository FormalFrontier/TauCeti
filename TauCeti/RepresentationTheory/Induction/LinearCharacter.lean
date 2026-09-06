/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Character
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

The second is a character identity, for a linear character of `N` that extends to the ambient
group -- that is, one of the form `χ ∘ N.subtype` for `χ : G →* kˣ`. The character of
`Ind_N^G (Res_N χ)` is then `χ` times the permutation character `Ind_N^G 1`. This is the
character-level form of the projection formula, `TauCeti.indClassFun_comp_subtype_mul` read on the
class function of `χ` against the constant function `1`; like that formula it holds over any field
and for any subgroup of finite index, with no hypothesis on the characteristic.

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

/-- **Inducing the restriction of a linear character of the ambient group multiplies the
permutation character by that character**: the character of `Ind_N^G (Res_N χ)` at `g` is `χ g`
times the character of `Ind_N^G 1` at `g`, for every `χ : G →* kˣ` and every `g`. A linear
character of `G` is in particular a class function on `G`, so this is the projection formula
`TauCeti.indClassFun_comp_subtype_mul` read on it and on the constant function `1`, and it inherits
that formula's absence of hypotheses on the characteristic. -/
theorem character_indFDRep_ofLinearCharacter_comp_subtype (χ : G →* kˣ) (g : G) :
    (indFDRep (FDRep.ofLinearCharacter (χ.comp N.subtype))).character g =
      (χ g : k) * (indFDRep (FDRep.of (Representation.trivial k N k))).character g := by
  have hχ : (fun x : G => (χ x : k)) ∈ ClassFunction k G := by
    refine ClassFunction.mem_iff.mpr fun x y => ?_
    have hconj : χ (y * x * y⁻¹) = χ x := by
      rw [map_mul, map_mul, map_inv, mul_comm (χ y) (χ x), mul_assoc, mul_inv_cancel, mul_one]
    exact congrArg (fun u : kˣ => (u : k)) hconj
  have hproj := congrFun (indClassFun_comp_subtype_mul (S := N) hχ
    (FDRep.of (Representation.trivial k N k)).character) g
  have hchar : (FDRep.ofLinearCharacter (χ.comp N.subtype)).character
      = (fun s : N => (χ (s : G) : k)) * (FDRep.of (Representation.trivial k N k)).character :=
    funext fun s => by simp
  rw [← indClassFun_ofFDRep_character, ← indClassFun_ofFDRep_character, hchar]
  exact hproj

end TauCeti
