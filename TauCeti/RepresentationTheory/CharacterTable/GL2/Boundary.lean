/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The three representations in the boundary splitting are defined here.
public import TauCeti.RepresentationTheory.CharacterTable.GL2.Linear
-- Non-public: the determinant twist of a principal-series character is the character identity the
-- splitting below is read off from, inside a proof only.
import TauCeti.RepresentationTheory.CharacterTable.GL2.PrincipalSeries.Twist
-- Equal characters determine isomorphic finite-group representations in characteristic zero.
import TauCeti.RepresentationTheory.CharacterTable.Determined
-- The fundamental theorem of algebra supplies the `IsAlgClosed ℂ` instance used both to promote
-- equal characters to an isomorphism and in the character-norm simplicity criterion.
import Mathlib.Analysis.Complex.Polynomial.Basic
-- Mathlib's character-norm criterion packages the irreducibility of the two constituents.
import Mathlib.RepresentationTheory.FinGroupCharZero

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

* `TauCeti.character_GL2PrincipalSeries_self_eq_add`: its two character constituents are the
  linear and Steinberg-twist characters.
* `TauCeti.simple_GL2Steinberg` and `TauCeti.simple_GL2SteinbergTwist`: the Steinberg
  representation and all its determinant twists are irreducible (for universe-small finite
  fields).
* `TauCeti.nonempty_iso_GL2PrincipalSeries_self`: the boundary principal series is the biproduct
  of those two representations.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42, Chapter 7 — cited only for the
  projection formula for induced characters, not for the `GL₂` decomposition itself, which is
  Fulton–Harris above.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe u

variable (F : Type u) [Field F] [Fintype F]

/-- **The repeated-parameter principal series has the sum of the linear and Steinberg-twist
characters.** This is the character-theoretic two-constituent decomposition at the boundary of
the principal series. -/
@[simp]
theorem character_GL2PrincipalSeries_self_eq_add (α : Fˣ →* ℂˣ) :
    (GL2PrincipalSeries F α α).character =
      (GL2Linear F α).character + (GL2SteinbergTwist F α).character := by
  have h := character_GL2PrincipalSeries_mul_eq_mul F α 1 1
  have hα : α * 1 = α := mul_one α
  rw [hα] at h
  rw [h]
  ext g
  rw [Pi.mul_apply, character_GL2PrincipalSeries_one_one_eq_one_add]
  simp only [Pi.add_apply, character_GL2Linear,
    character_GL2SteinbergTwist]
  ring

/-! ### Irreducibility of the constituents

Mathlib's character-norm criterion currently requires the coefficient field and the group in the
same universe. Accordingly the two Steinberg packaging results below use `F : Type`, as does the
existing irreducibility theorem for the non-boundary principal series. The representations, their
splitting, and the irreducibility of the linear constituent all remain universe-polymorphic. -/

section SmallUniverse

variable (F : Type) [Field F] [Fintype F]

/-- **The Steinberg representation of `GL₂(F)` is irreducible** for a universe-small finite
field `F`. -/
theorem simple_GL2Steinberg : Simple (GL2Steinberg F) := by
  classical
  apply (FDRep.simple_iff_char_is_norm_one (GL2Steinberg F)).mpr
  have h := characterPairing_GL2Steinberg_self F
  rw [ClassFunction.characterPairing_apply] at h
  have hcard : (Nat.card (GL (Fin 2) F) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp [hcard] at h
  simpa only [ClassFunction.ofFDRep_apply] using h

/-- **Every determinant twist of the Steinberg representation is irreducible** for a
universe-small finite field `F`. -/
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
