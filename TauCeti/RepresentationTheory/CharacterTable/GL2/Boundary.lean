/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The three representations in the boundary splitting are defined here.
public import TauCeti.RepresentationTheory.CharacterTable.GL2.Linear
-- Equal characters determine isomorphic finite-group representations in characteristic zero.
import TauCeti.RepresentationTheory.CharacterTable.Determined
-- The fundamental theorem of algebra supplies the `IsAlgClosed ℂ` instance used only to promote
-- the character identity to an isomorphism.
import Mathlib.Analysis.Complex.Polynomial.Basic
-- Mathlib's character-norm criterion packages the irreducibility of the two constituents.
import Mathlib.RepresentationTheory.FinGroupCharZero
-- The class-function projection formula identifies the character of the determinant twist.
import TauCeti.RepresentationTheory.Induction.Character

/-!
# The boundary principal series of `GL₂` splits

For a finite field `F` and a multiplicative character `α : Fˣ → ℂˣ`, the principal series at
the repeated parameter `(α, α)` is reducible. This file identifies its two constituents:

```text
Ind_B^GL₂(α ⊗ α) ≅ (α ∘ det) ⊕ ((α ∘ det) ⊗ St).
```

The character identity is the projection formula for induction. The Borel character `α ⊗ α`
is the restriction of the determinant character `α ∘ det`, so its induction is the product of
that character with `Ind_B^GL₂(1)`. The latter is the permutation representation on the
projective line and has character `1 + χ_St`. Distributing the determinant character gives the
characters of `TauCeti.GL2Linear F α` and `TauCeti.GL2SteinbergTwist F α`. Character theory over
`ℂ` then promotes this identity to an isomorphism of representations.

This splitting separates the two boundary families in the character table of `GL₂(F)`: the
linear representations have dimension `1`, while their Steinberg twists have dimension
`Fintype.card F`.

## Main results

* `TauCeti.character_GL2PrincipalSeries_self_eq_mul`: the repeated-parameter principal-series
  character is the determinant character times the untwisted boundary character.
* `TauCeti.character_GL2PrincipalSeries_self_eq_add`: its two character constituents are the
  linear and Steinberg-twist characters.
* `TauCeti.simple_GL2Steinberg` and `TauCeti.simple_GL2SteinbergTwist`: the two Steinberg
  families are irreducible (for universe-small finite fields).
* `TauCeti.nonempty_iso_GL2PrincipalSeries_self`: the boundary principal series is the biproduct
  of those two representations.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42, §7.3.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe u

variable (F : Type u) [Field F] [Fintype F]

/-- **The boundary principal-series character is a determinant twist of the untwisted one.**
For `α : Fˣ → ℂˣ`, the equality
`χ(Ind_B^GL₂(α ⊗ α)) = (α ∘ det) · χ(Ind_B^GL₂(1 ⊗ 1))`
is the class-function projection formula, because `α ⊗ α` is the restriction of `α ∘ det` to
the Borel subgroup. -/
theorem character_GL2PrincipalSeries_self_eq_mul (α : Fˣ →* ℂˣ) :
    (GL2PrincipalSeries F α α).character =
      (GL2Linear F α).character * (GL2PrincipalSeries F 1 1).character := by
  rw [GL2PrincipalSeries_def, ← indClassFun_ofFDRep_character,
    GL2PrincipalSeries_def, ← indClassFun_ofFDRep_character]
  rw [← indClassFun_comp_subtype_mul
    (ClassFunction.mem_iff.mpr fun g x => (GL2Linear F α).char_conj g x)]
  congr 1
  funext b
  rw [Pi.mul_apply, character_GL2BorelRep, character_GL2BorelRep,
    GL2Borel.linearChar_self, character_GL2Linear]
  simp

/-- **The repeated-parameter principal series has the sum of the linear and Steinberg-twist
characters.** This is the character-theoretic two-constituent decomposition at the boundary of
the principal series. -/
theorem character_GL2PrincipalSeries_self_eq_add (α : Fˣ →* ℂˣ) :
    (GL2PrincipalSeries F α α).character =
      (GL2Linear F α).character + (GL2SteinbergTwist F α).character := by
  rw [character_GL2PrincipalSeries_self_eq_mul]
  ext g
  rw [Pi.mul_apply, character_GL2PrincipalSeries_one_one_eq_one_add]
  simp only [Pi.add_apply, character_GL2Linear,
    character_GL2SteinbergTwist]
  ring

/-! ### Irreducibility of the Steinberg constituents

Mathlib's character-norm criterion currently requires the coefficient field and the group in the
same universe. Accordingly these two packaging results use `F : Type`, as does the existing
irreducibility theorem for the non-boundary principal series. The representations and their
splitting above remain universe-polymorphic. -/

section SmallUniverse

variable (F : Type) [Field F] [Fintype F]

/-- **The Steinberg representation of `GL₂(F)` is irreducible.** Its character has norm one by
the Bruhat double-coset computation, and Mathlib's character-norm criterion converts that equality
to simplicity. -/
theorem simple_GL2Steinberg : Simple (GL2Steinberg F) := by
  classical
  apply (FDRep.simple_iff_char_is_norm_one (GL2Steinberg F)).mpr
  have h := characterPairing_GL2Steinberg_self F
  rw [ClassFunction.characterPairing_apply] at h
  have hcard : (Nat.card (GL (Fin 2) F) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp [hcard] at h
  simpa only [ClassFunction.ofFDRep_apply] using h

/-- **Every determinant twist of the Steinberg representation is irreducible.** Twisting its
character by `α ∘ det` preserves the character norm, since the values at `g` and `g⁻¹` are
mutual inverses. -/
theorem simple_GL2SteinbergTwist (α : Fˣ →* ℂˣ) : Simple (GL2SteinbergTwist F α) := by
  classical
  apply (FDRep.simple_iff_char_is_norm_one (GL2SteinbergTwist F α)).mpr
  have h := (FDRep.simple_iff_char_is_norm_one (GL2Steinberg F)).mp
    (simple_GL2Steinberg F)
  calc
    ∑ g : GL (Fin 2) F,
        (GL2SteinbergTwist F α).character g *
          (GL2SteinbergTwist F α).character g⁻¹ =
      ∑ g : GL (Fin 2) F,
        (GL2Steinberg F).character g * (GL2Steinberg F).character g⁻¹ := by
          apply Finset.sum_congr rfl
          intro g _
          simp only [character_GL2SteinbergTwist, map_inv]
          simp [mul_assoc, mul_left_comm]
    _ = Nat.card (GL (Fin 2) F) := h

end SmallUniverse

/-- **The boundary principal series splits into its linear and Steinberg constituents.** For a
multiplicative character `α : Fˣ → ℂˣ`,
`Ind_B^GL₂(α ⊗ α)` is isomorphic to the biproduct of the determinant character `α ∘ det` and its
Steinberg twist. -/
theorem nonempty_iso_GL2PrincipalSeries_self (α : Fˣ →* ℂˣ) :
    Nonempty (GL2PrincipalSeries F α α ≅ GL2Linear F α ⊞ GL2SteinbergTwist F α) := by
  apply FDRep.nonempty_iso_of_character_eq
  rw [FDRep.char_biprod]
  exact character_GL2PrincipalSeries_self_eq_add F α

end TauCeti
