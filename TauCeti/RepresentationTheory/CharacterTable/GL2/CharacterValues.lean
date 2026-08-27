/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.GL2Steinberg` and `TauCeti.GL2PrincipalSeries` are the representations whose characters
-- are computed here.
public import TauCeti.RepresentationTheory.CharacterTable.GL2.Steinberg
-- The fixed-coset counts are the content of every proof below, and this module re-exports
-- `TauCeti.diagGL`, `TauCeti.jordanGL` and `TauCeti.GL2NonSplitTorusHom`, which occur in the
-- statements.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ProjectiveLine

/-!
# The Steinberg character of `GL₂(𝔽_q)` on the four families of conjugacy classes

`TauCeti.character_GL2Steinberg` computes the Steinberg character of `GL₂(𝔽_q)` at `g` as the
number of points of the projective line fixed by `g`, less one. The conjugacy classes of `GL₂(𝔽_q)`
fall into four families, and
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/ProjectiveLine.lean` counts the fixed points of a
representative of each: `q + 1` for a **central** scalar matrix, `2` for a **split semisimple**
diagonal matrix with distinct entries, `1` for a **non-semisimple** Jordan block, and `0` for an
**elliptic** element of the non-split torus that does not come from `F`. This file reads off the
resulting row of the character table,

`χ_St = q`, `1`, `0`, `-1`

on the four families, together with the row of the boundary principal series
`Ind_B^{GL₂}(1 ⊗ 1) = 1 + χ_St`, which is `q + 1`, `2`, `1`, `0` — the fixed-point counts
themselves, as they must be for a permutation character.

That these four values determine the Steinberg character outright is a statement about the
conjugacy classes, not about the representation: every element of `GL₂(𝔽_q)` is conjugate to one of
the four representatives (`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/ConjugacyClasses.lean`
classifies the classes by trace and determinant, and the elliptic normal form is the one that needs
the quadratic extension), and a character is a class function. That reduction is not carried out
here; the values below are stated at the normal forms themselves.

## Main results

* `TauCeti.character_GL2Steinberg_scalar`, `TauCeti.character_GL2Steinberg_diagGL`,
  `TauCeti.character_GL2Steinberg_jordanGL` and
  `TauCeti.character_GL2Steinberg_gl2NonSplitTorusHom`: the Steinberg character takes the values
  `q`, `1`, `0` and `-1` on the four families.
* `TauCeti.character_GL2PrincipalSeries_one_one_scalar` and its three companions: the character of
  the boundary principal series takes the values `q + 1`, `2`, `1` and `0`.

None of those eight values is a `simp` lemma. `TauCeti.character_GL2Steinberg` is itself `@[simp]`,
so `simp` rewrites the left-hand side of each of them to a fixed-coset count, and then, `F` being
finite, on to a `Fintype.card` by `Nat.card_eq_fintype_card`; so none of the eight is in
`simp`-normal form, and tagging any of them fails the `simpNF` linter.

## References

This supplies the Steinberg row of the character-value formulas of Layer 9 ("the representation
theory of `GL₂(𝔽_q)`") of
`TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md`. See also W. Fulton and J. Harris,
*Representation Theory: A First Course*, GTM 129, §5.2, and C. Bonnafé, *Representations of
`SL₂(𝔽_q)`* (2011), Chapter 5.
-/

public section

namespace TauCeti

open Matrix

universe u

variable {F : Type u} [Field F] [Fintype F]

/-! ### The Steinberg character -/

/-- **The Steinberg character at a central element is `q`.** A scalar matrix fixes every point of
the projective line, so the permutation character is `q + 1` and the invariant line accounts for
one of it. -/
theorem character_GL2Steinberg_scalar (u : Fˣ) :
    (GL2Steinberg F).character (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      (Fintype.card F : ℂ) := by
  rw [character_GL2Steinberg, GL2Borel.natCard_fixedCosets_scalar]
  push_cast
  ring

/-- **The Steinberg character at a split semisimple element is `1`.** A diagonal matrix with
distinct entries fixes exactly the two coordinate axes. -/
theorem character_GL2Steinberg_diagGL {a b : Fˣ} (hab : a ≠ b) :
    (GL2Steinberg F).character (diagGL ![a, b]) = 1 := by
  rw [character_GL2Steinberg, GL2Borel.natCard_fixedCosets_diagGL hab]
  norm_num

/-- **The Steinberg character at a non-semisimple element is `0`.** A Jordan block fixes exactly the
line of its single eigenvector, so the permutation character is `1` and the invariant line is all
of it. -/
theorem character_GL2Steinberg_jordanGL (a : Fˣ) {b : F} (hb : b ≠ 0) :
    (GL2Steinberg F).character (jordanGL a b) = 0 := by
  rw [character_GL2Steinberg, GL2Borel.natCard_fixedCosets_jordanGL a hb]
  norm_num

section Elliptic

variable {E : Type*} [Field E] [Algebra F E] (hE : Module.finrank F E = 2)

/-- **The Steinberg character at an elliptic element is `-1`.** An element of the non-split torus
coming from `E ∖ F` has no eigenline over `F`, so it fixes no point of the projective line at all
and only the invariant line contributes. -/
theorem character_GL2Steinberg_gl2NonSplitTorusHom {x : Eˣ}
    (hx : (x : E) ∉ Set.range (algebraMap F E)) :
    (GL2Steinberg F).character (GL2NonSplitTorusHom F E hE x) = -1 := by
  rw [character_GL2Steinberg, GL2Borel.natCard_fixedCosets_gl2NonSplitTorusHom hE hx]
  norm_num

end Elliptic

/-! ### The boundary principal series

At `α = β = 1` the principal series is the permutation representation of the projective line, so
its character is the fixed-point count itself: one more than the Steinberg value. -/

/-- The boundary principal series has character `q + 1` at a central element. -/
theorem character_GL2PrincipalSeries_one_one_scalar (u : Fˣ) :
    (GL2PrincipalSeries F 1 1).character (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      (Fintype.card F : ℂ) + 1 := by
  rw [character_GL2PrincipalSeries_one_one_eq_one_add, character_GL2Steinberg_scalar]
  ring

/-- The boundary principal series has character `2` at a split semisimple element. -/
theorem character_GL2PrincipalSeries_one_one_diagGL {a b : Fˣ} (hab : a ≠ b) :
    (GL2PrincipalSeries F 1 1).character (diagGL ![a, b]) = 2 := by
  rw [character_GL2PrincipalSeries_one_one_eq_one_add, character_GL2Steinberg_diagGL hab]
  norm_num

/-- The boundary principal series has character `1` at a non-semisimple element. -/
theorem character_GL2PrincipalSeries_one_one_jordanGL (a : Fˣ) {b : F} (hb : b ≠ 0) :
    (GL2PrincipalSeries F 1 1).character (jordanGL a b) = 1 := by
  rw [character_GL2PrincipalSeries_one_one_eq_one_add, character_GL2Steinberg_jordanGL a hb]
  ring

section Elliptic

variable {E : Type*} [Field E] [Algebra F E] (hE : Module.finrank F E = 2)

/-- The boundary principal series has character `0` at an elliptic element: no point of the
projective line is fixed, so the permutation character vanishes. -/
theorem character_GL2PrincipalSeries_one_one_gl2NonSplitTorusHom {x : Eˣ}
    (hx : (x : E) ∉ Set.range (algebraMap F E)) :
    (GL2PrincipalSeries F 1 1).character (GL2NonSplitTorusHom F E hE x) = 0 := by
  rw [character_GL2PrincipalSeries_one_one_eq_one_add,
    character_GL2Steinberg_gl2NonSplitTorusHom hE hx]
  ring

end Elliptic

end TauCeti
