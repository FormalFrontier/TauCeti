/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The untwisted Steinberg values and the four class representatives occur in the statements below,
-- and this module re-exports `Representation.ofLinearCharacter`, which the definitions below use.
public import TauCeti.RepresentationTheory.CharacterTable.GL2.CharacterValues

/-!
# Linear characters and Steinberg twists of `GL₂(𝔽_q)`

Every multiplicative character `α : Fˣ →* ℂˣ` gives a one-dimensional representation of
`GL₂(F)` by precomposition with the determinant. This file packages that representation as
`TauCeti.GL2Linear F α`, proves that distinct `α` give distinct character rows, and computes its
character on the four families of conjugacy classes.

Tensoring with `TauCeti.GL2Steinberg F` gives the corresponding Steinberg twist
`TauCeti.GL2SteinbergTwist F α`. Its character is the pointwise product of the determinant
character and the untwisted Steinberg character, so the four values are

`q α(a²)`, `α(ab)`, `0`, and `-α(N_{E/F}(x))`

on scalar, split semisimple, non-semisimple, and elliptic representatives. These are the two
expected boundary rows of the principal series `Ind_B^{GL₂}(α ⊗ α)`; this file does not prove the
representation-level splitting of that principal series.

## Main definitions

* `TauCeti.GL2LinearChar`: the character `α ∘ det` as a homomorphism to `ℂˣ`.
* `TauCeti.GL2LinearRep`: the corresponding representation on the line `ℂ`.
* `TauCeti.GL2Linear`: its one-dimensional representation.
* `TauCeti.GL2SteinbergTwist`: the determinant-character twist of the Steinberg representation.

## Main results

* `TauCeti.character_GL2Linear` and `TauCeti.character_GL2SteinbergTwist`: the character formulas
  at an arbitrary group element.
* `TauCeti.GL2LinearChar_comp_gl2BorelSubtype`: restriction to the Borel subgroup is the boundary
  character `α ⊗ α`.
* `TauCeti.GL2Linear_character_injective`: distinct multiplicative characters give distinct rows.
* The `_scalar`, `_diagGL`, `_jordanGL`, and `_gl2NonSplitTorusHom` theorems compute both families
  on the four class representatives.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 9, "The boundary: linear and Steinberg constituents" and "Character-value formulas".
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §5.2.
* C. Bonnafé, *Representations of `SL₂(𝔽_q)`* (2011), Chapter 5.
-/

public section

open Matrix
open CategoryTheory.MonoidalCategory

namespace TauCeti

universe u

section CommRing

variable {F : Type u} [CommRing F]

/-! ### The linear representations -/

/-- **The determinant character attached to `α`.** This is the multiplicative character of
`GL₂(F)` sending `g` to `α(det g)`. -/
def GL2LinearChar (α : Fˣ →* ℂˣ) : GL (Fin 2) F →* ℂˣ :=
  α.comp Matrix.GeneralLinearGroup.det

@[simp]
theorem GL2LinearChar_apply (α : Fˣ →* ℂˣ) (g : GL (Fin 2) F) :
    GL2LinearChar α g = α (Matrix.GeneralLinearGroup.det g) :=
  (rfl)

/-- **The one-dimensional representation `α ∘ det` of `GL₂(F)`.** -/
def GL2LinearRep (α : Fˣ →* ℂˣ) : Representation ℂ (GL (Fin 2) F) ℂ :=
  Representation.ofLinearCharacter (GL2LinearChar α)

/-- `TauCeti.GL2LinearRep` is the generic one-dimensional representation associated to
`TauCeti.GL2LinearChar`. -/
theorem GL2LinearRep_def (α : Fˣ →* ℂˣ) :
    GL2LinearRep α = Representation.ofLinearCharacter (GL2LinearChar α) :=
  (rfl)

/-- **The one-dimensional representation `α ∘ det` of `GL₂(F)`, bundled in `FDRep`.** -/
noncomputable def GL2Linear (F : Type u) [CommRing F] (α : Fˣ →* ℂˣ) :
    FDRep ℂ (GL (Fin 2) F) :=
  FDRep.of (GL2LinearRep α)

/-- `TauCeti.GL2Linear` is the one-dimensional representation associated to
`TauCeti.GL2LinearChar`. -/
theorem GL2Linear_def (α : Fˣ →* ℂˣ) :
    GL2Linear F α = FDRep.of (GL2LinearRep α) :=
  (rfl)

/-- The linear representation has dimension one. -/
@[simp]
theorem finrank_GL2Linear (α : Fˣ →* ℂˣ) :
    Module.finrank ℂ (GL2Linear F α) = 1 :=
  Module.finrank_self ℂ

/-- **The character of `TauCeti.GL2Linear F α` is `α ∘ det`.** -/
@[simp]
theorem character_GL2Linear (α : Fˣ →* ℂˣ) (g : GL (Fin 2) F) :
    (GL2Linear F α).character g = (α (Matrix.GeneralLinearGroup.det g) : ℂ) := by
  rw [GL2Linear_def, GL2LinearRep_def]
  -- the carrier of `FDRep.of ρ` is the module that `ρ` acts on, here `ℂ` itself
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character, GL2LinearChar_apply] using
    Representation.char_ofLinearCharacter (GL2LinearChar α) g

/-- **Determinant characters of `GL₂` remember their parameter.** Surjectivity of the determinant
shows that precomposition with it is injective. -/
theorem GL2LinearChar_injective : Function.Injective (GL2LinearChar (F := F)) := by
  intro α β h
  apply MonoidHom.ext
  intro a
  obtain ⟨g, hg⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin 2) a
  have := congrArg (fun χ : GL (Fin 2) F →* ℂˣ => χ g) h
  simpa [GL2LinearChar_apply, hg] using this

/-- **Distinct parameters give distinct linear character rows of `GL₂`.** -/
theorem GL2Linear_character_injective :
    Function.Injective fun α : Fˣ →* ℂˣ => (GL2Linear F α).character := by
  intro α β h
  apply GL2LinearChar_injective
  apply MonoidHom.ext
  intro g
  apply Units.ext
  have := congrFun h g
  simpa using this

/-- **The determinant character restricts to the boundary Borel character `α ⊗ α`.** -/
@[simp]
theorem GL2LinearChar_comp_gl2BorelSubtype (α : Fˣ →* ℂˣ) :
    (GL2LinearChar α).comp (GL2Borel F).subtype = GL2Borel.linearChar α α := by
  apply MonoidHom.ext
  intro g
  exact (GL2Borel.linearChar_self α g).symm

/-- **The linear representation restricts to the one-dimensional Borel representation at the
boundary pair `(α, α)`.** -/
@[simp]
theorem GL2LinearRep_comp_gl2BorelSubtype (α : Fˣ →* ℂˣ) :
    (GL2LinearRep α).comp (GL2Borel F).subtype = GL2Borel.linearRep α α := by
  rw [GL2LinearRep_def, Representation.ofLinearCharacter_comp,
    GL2LinearChar_comp_gl2BorelSubtype, GL2Borel.linearRep_def]

/-! ### The linear character row -/

/-- The linear character at a scalar matrix is `α(a²)`. -/
theorem character_GL2Linear_scalar (α : Fˣ →* ℂˣ) (a : Fˣ) :
    (GL2Linear F α).character (Matrix.GeneralLinearGroup.scalar (Fin 2) a) = (α (a ^ 2) : ℂ) := by
  rw [character_GL2Linear, Matrix.GeneralLinearGroup.det_scalar]
  norm_num

/-- The linear character at a split semisimple representative is `α(ab)`. The formula does not
need the usual `a ≠ b` hypothesis because it is an identity for every diagonal matrix. -/
theorem character_GL2Linear_diagGL (α : Fˣ →* ℂˣ) (a b : Fˣ) :
    (GL2Linear F α).character (diagGL ![a, b]) = (α (a * b) : ℂ) := by
  rw [character_GL2Linear, det_diagGL]
  simp [Fin.prod_univ_two]

/-- The linear character at a Jordan-form matrix `jordanGL a b` is `α(a²)`. The value does not
depend on the upper-right entry `b`, so no hypothesis on it is needed; the matrix represents the
non-semisimple family exactly when `b ≠ 0`. -/
theorem character_GL2Linear_jordanGL (α : Fˣ →* ℂˣ) (a : Fˣ) (b : F) :
    (GL2Linear F α).character (jordanGL a b) = (α (a ^ 2) : ℂ) := by
  rw [character_GL2Linear, det_jordanGL]

end CommRing

section Field

variable {F : Type u} [Field F]

section Elliptic

variable {E : Type*} [Field E] [Algebra F E] (hE : Module.finrank F E = 2)

/-- The linear character at a non-split-torus element is the character applied to its field norm. -/
theorem character_GL2Linear_gl2NonSplitTorusHom (α : Fˣ →* ℂˣ) (x : Eˣ) :
    (GL2Linear F α).character (GL2NonSplitTorusHom F E hE x) =
      (α (Algebra.normUnits F x) : ℂ) := by
  rw [character_GL2Linear, GL2NonSplitTorus.det_gl2NonSplitTorusHom]

end Elliptic

/-! ### The Steinberg twists -/

section FiniteField

variable [Fintype F]

/-- **The Steinberg representation twisted by `α ∘ det`.** These are the expected degree-`q`
boundary constituents of the principal series; that constituent relation is not proved here, only
the dimension and the character values below. -/
noncomputable def GL2SteinbergTwist (F : Type u) [Field F] [Fintype F] (α : Fˣ →* ℂˣ) :
    FDRep ℂ (GL (Fin 2) F) :=
  GL2Linear F α ⊗ GL2Steinberg F

/-- A Steinberg twist is the tensor product of the determinant character with the untwisted
Steinberg representation. -/
theorem GL2SteinbergTwist_def (α : Fˣ →* ℂˣ) :
    GL2SteinbergTwist F α = GL2Linear F α ⊗ GL2Steinberg F :=
  (rfl)

/-- The Steinberg twist has dimension `q`, being the tensor product of a line with the Steinberg
representation. -/
@[simp]
theorem finrank_GL2SteinbergTwist (α : Fˣ →* ℂˣ) :
    Module.finrank ℂ (GL2SteinbergTwist F α) = Fintype.card F := by
  -- The carrier of a tensor product in `FDRep` is the tensor product of the carriers.
  have hcarrier : Module.finrank ℂ (GL2SteinbergTwist F α) =
      Module.finrank ℂ (TensorProduct ℂ (GL2Linear F α) (GL2Steinberg F)) := rfl
  rw [hcarrier, Module.finrank_tensorProduct, finrank_GL2Linear, finrank_GL2Steinberg, one_mul]

/-- **The character of a Steinberg twist is the determinant character times the Steinberg
character.** -/
@[simp]
theorem character_GL2SteinbergTwist (α : Fˣ →* ℂˣ) (g : GL (Fin 2) F) :
    (GL2SteinbergTwist F α).character g =
      (α (Matrix.GeneralLinearGroup.det g) : ℂ) * (GL2Steinberg F).character g := by
  rw [GL2SteinbergTwist_def, congrFun (FDRep.char_tensor (GL2Linear F α) (GL2Steinberg F)) g,
    Pi.mul_apply, character_GL2Linear]

/-- The Steinberg twist at a scalar matrix is `q α(a²)`. -/
theorem character_GL2SteinbergTwist_scalar (α : Fˣ →* ℂˣ) (a : Fˣ) :
    (GL2SteinbergTwist F α).character (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      (Fintype.card F : ℂ) * α (a ^ 2) := by
  rw [character_GL2SteinbergTwist, Matrix.GeneralLinearGroup.det_scalar,
    character_GL2Steinberg_scalar]
  norm_num
  ring

/-- The Steinberg twist at a split semisimple representative is `α(ab)`. -/
theorem character_GL2SteinbergTwist_diagGL (α : Fˣ →* ℂˣ) {a b : Fˣ} (hab : a ≠ b) :
    (GL2SteinbergTwist F α).character (diagGL ![a, b]) = (α (a * b) : ℂ) := by
  rw [character_GL2SteinbergTwist, det_diagGL, character_GL2Steinberg_diagGL hab]
  simp [Fin.prod_univ_two]

/-- **Distinct parameters give distinct Steinberg-twist character rows.** At `diag(a, 1)` the
Steinberg character is `1` whenever `a ≠ 1`, so the row recovers `α(a)`; every character has value
`1` at the remaining element. -/
theorem GL2SteinbergTwist_character_injective :
    Function.Injective fun α : Fˣ →* ℂˣ => (GL2SteinbergTwist F α).character := by
  intro α β h
  apply MonoidHom.ext
  intro a
  apply Units.ext
  by_cases ha : a = 1
  · subst a
    simp
  · have hrow := congrFun h (diagGL ![a, 1])
    have hrow' : (GL2SteinbergTwist F α).character (diagGL ![a, 1]) =
        (GL2SteinbergTwist F β).character (diagGL ![a, 1]) := hrow
    rw [character_GL2SteinbergTwist_diagGL α ha,
      character_GL2SteinbergTwist_diagGL β ha] at hrow'
    simpa using hrow'

/-- The Steinberg twist vanishes at a non-semisimple representative. -/
theorem character_GL2SteinbergTwist_jordanGL (α : Fˣ →* ℂˣ) (a : Fˣ) {b : F}
    (hb : b ≠ 0) :
    (GL2SteinbergTwist F α).character (jordanGL a b) = 0 := by
  rw [character_GL2SteinbergTwist, character_GL2Steinberg_jordanGL a hb, mul_zero]

section Elliptic

variable {E : Type*} [Field E] [Algebra F E] (hE : Module.finrank F E = 2)

/-- The Steinberg twist at an elliptic element is the negative of `α` at its field norm. -/
theorem character_GL2SteinbergTwist_gl2NonSplitTorusHom (α : Fˣ →* ℂˣ) {x : Eˣ}
    (hx : (x : E) ∉ Set.range (algebraMap F E)) :
    (GL2SteinbergTwist F α).character (GL2NonSplitTorusHom F E hE x) =
      -(α (Algebra.normUnits F x) : ℂ) := by
  rw [character_GL2SteinbergTwist,
    GL2NonSplitTorus.det_gl2NonSplitTorusHom hE x,
    character_GL2Steinberg_gl2NonSplitTorusHom hE hx]
  ring

end Elliptic

end FiniteField

end Field

end TauCeti
