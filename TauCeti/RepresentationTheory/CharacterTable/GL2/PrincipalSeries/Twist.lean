/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The determinant character `TauCeti.GL2Linear` that the twist multiplies by, and, through it,
-- the principal series `TauCeti.GL2PrincipalSeries` the identity below is about.
public import TauCeti.RepresentationTheory.CharacterTable.GL2.Linear
-- Non-public: the projection formula `TauCeti.indClassFun_comp_subtype_mul` for induced class
-- functions is the whole proof.
import TauCeti.RepresentationTheory.Induction.ClassFunction
-- Non-public: `TauCeti.ClassFunction.mem_iff` supplies the class-function hypothesis that formula
-- takes, inside the proof only.
import TauCeti.RepresentationTheory.CharacterTable.ClassFunction

/-!
# Twisting the principal series of `GL₂(𝔽_q)` by a determinant character

Multiplying both parameters of the principal series by a character `γ : Fˣ →* ℂˣ` multiplies its
character by the determinant character `γ ∘ det`:

`χ(Ind_B^{GL₂}(γα ⊗ γβ)) = (γ ∘ det) · χ(Ind_B^{GL₂}(α ⊗ β))`.

This is the projection formula for induced class functions, because the Borel character
`γα ⊗ γβ` is the pointwise product of `α ⊗ β` with the restriction of `γ ∘ det` to the Borel
subgroup (`TauCeti.GL2LinearChar_comp_gl2BorelSubtype`).

At `α = β = 1` the identity turns the character of the permutation representation on the
projective line into the character of the principal series at the repeated parameter `(γ, γ)`,
which is how
`TauCeti/RepresentationTheory/CharacterTable/GL2/Boundary.lean` splits that principal series.

## Main statements

* `TauCeti.character_GL2PrincipalSeries_mul_eq_mul`: twisting both principal-series parameters by
  `γ` multiplies the induced character by the determinant character of `γ`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42, Chapter 7 — the projection
  formula for induced characters.
-/

public section

namespace TauCeti

universe u

variable (F : Type u) [Field F] [Fintype F]

/-- **Twisting both principal-series parameters multiplies the character by a determinant
character.** For `γ α β : Fˣ → ℂˣ`, the equality
`χ(Ind_B^GL₂(γα ⊗ γβ)) = (γ ∘ det) · χ(Ind_B^GL₂(α ⊗ β))`
is the class-function projection formula, because `γα ⊗ γβ` is the pointwise product of `α ⊗ β`
with the restriction of `γ ∘ det` to the Borel subgroup. -/
@[simp]
theorem character_GL2PrincipalSeries_mul_eq_mul (γ α β : Fˣ →* ℂˣ) :
    (GL2PrincipalSeries F (γ * α) (γ * β)).character =
      (GL2Linear F γ).character * (GL2PrincipalSeries F α β).character := by
  rw [GL2PrincipalSeries_def, ← indClassFun_ofFDRep_character,
    GL2PrincipalSeries_def, ← indClassFun_ofFDRep_character]
  rw [← indClassFun_comp_subtype_mul
    (ClassFunction.mem_iff.mpr fun g x => (GL2Linear F γ).char_conj g x)]
  congr 1
  funext b
  rw [Pi.mul_apply, character_GL2BorelRep, character_GL2BorelRep, character_GL2Linear,
    GL2Borel.det_diag, map_mul]
  simp [mul_mul_mul_comm]

end TauCeti
