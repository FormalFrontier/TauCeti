/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.GL2PrincipalSeries` and the Borel character `TauCeti.GL2BorelRep` it is induced from
-- are the subject.
public import TauCeti.RepresentationTheory.CharacterTable.GL2.PrincipalSeries.Basic
-- `TauCeti.indClassFun_ofFDRep_character` rewrites the character of an induced representation as
-- the induced class function, whose coset sum `TauCeti.indClassFun_eq_sum_of_smul_eq_self_mem`
-- then cuts down to the fixed cosets.
import TauCeti.RepresentationTheory.Induction.Character
-- The fixed-coset counts of the four families, and the representatives `TauCeti.diagGL`,
-- `TauCeti.jordanGL` and `TauCeti.GL2NonSplitTorusHom` at which they are stated.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ProjectiveLine
-- Non-public: that the Weyl element is the permutation matrix of the transposition is what
-- computes the second fixed coset of a split semisimple element, inside a proof only.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Bruhat

/-!
# The character of the principal series of `GL₂(𝔽_q)` on the four families of conjugacy classes

The conjugacy classes of `GL₂(𝔽_q)` fall into four families
(`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/ConjugacyClasses.lean`), with representatives
the **central** scalar `diag(a, a)`, the **split semisimple** `diag(a, b)` with `a ≠ b`, the
**non-semisimple** Jordan block `!![a, b; 0, a]` with `b ≠ 0`, and the **elliptic** image of an
element of `E ∖ F` under the non-split torus of a quadratic extension `E/F`. This file evaluates
the character of the principal series `Ind_B^{GL₂}(α ⊗ β)` at each of the four, giving the row

`χ_{α,β} = (q + 1) α(a) β(a)`, `α(a) β(b) + α(b) β(a)`, `α(a) β(a)`, `0`

of the character table of `GL₂(𝔽_q)`. At `α = β = 1` these are the fixed-point counts on the
projective line, which is the boundary case
`TauCeti/RepresentationTheory/CharacterTable/GL2/CharacterValues.lean` reads off.

The computation is the induced-character formula in the form
`TauCeti.indClassFun_eq_sum_of_smul_eq_self_mem`: the character of an induction at `g` is the sum
of the inducing character over the cosets of `B` that `g` fixes, evaluated at the conjugate of `g`
into `B` that each such coset exhibits. Which cosets are fixed is already known — a scalar fixes
all `q + 1` of them, a split semisimple element exactly `2`, a Jordan block exactly `1`, and an
elliptic element none
(`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/ProjectiveLine.lean`) — and those counts are
enough to *identify* the fixed cosets, because in each case a list of that many fixed cosets is at
hand: the trivial coset `B` and, for a split semisimple element, the coset of the Weyl element
`w = !![0, 1; 1, 0]`. Conjugating `diag(a, b)` by `w` swaps the two entries, which is where the
second summand `α(b) β(a)` comes from.

Only the central formula contains `q`, as the index `q + 1` of the Borel subgroup, and it is the
one whose fixed-coset count `TauCeti.GL2Borel.natCard_fixedCosets_scalar` is about a finite field.
The other three counts hold over any field; all four proofs still need `F` finite, because the
coset sum they run on is the one of a finite-index subgroup.

## Main results

* `TauCeti.character_GL2PrincipalSeries_scalar`, `TauCeti.character_GL2PrincipalSeries_diagGL`,
  `TauCeti.character_GL2PrincipalSeries_jordanGL` and
  `TauCeti.character_GL2PrincipalSeries_gl2NonSplitTorusHom`: the four values above.

## References

This supplies the principal-series row of the character-value formulas of Layer 9 ("the
representation theory of `GL₂(𝔽_q)`") of
`TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md`. See also W. Fulton and J. Harris,
*Representation Theory: A First Course*, GTM 129, §5.2, and C. Bonnafé, *Representations of
`SL₂(𝔽_q)`* (2011), Chapter 5.
-/

public section

namespace TauCeti

open _root_.Matrix

universe u

variable {F : Type u} [Field F]

/-- Conjugating a diagonal matrix by the Weyl element swaps its two entries. This is
`TauCeti.permutationGL_mul_diagGL_mul_inv` at the transposition, which
`TauCeti.gl2WeylElement_eq_permutationGL_swap` identifies the Weyl element with.

`TauCeti.GL2Borel.inv_weyl_mul_torusHom_mul_weyl` is the same fact for the split torus
`TauCeti.GL2Borel.torusHom` of the Borel subgroup rather than for `TauCeti.diagGL`. The two
presentations of a diagonal matrix are equal but not definitionally so, and the conjugacy-class
representatives of `GL₂(𝔽_q)` are stated with `TauCeti.diagGL`; nothing is recomputed here, the
general permutation lemma above does the work. -/
private theorem inv_gl2WeylElement_mul_diagGL_mul_gl2WeylElement (a b : Fˣ) :
    (GL2WeylElement F)⁻¹ * diagGL ![a, b] * GL2WeylElement F = diagGL ![b, a] := by
  have hinv : (permutationGL (k := F) (Equiv.swap (0 : Fin 2) 1))⁻¹ =
      permutationGL (k := F) (Equiv.swap (0 : Fin 2) 1) := by
    rw [← map_inv, Equiv.swap_inv]
  rw [gl2WeylElement_inv, gl2WeylElement_eq_permutationGL_swap]
  nth_rewrite 2 [← hinv]
  rw [permutationGL_mul_diagGL_mul_inv]
  exact congrArg diagGL (funext fun i => by fin_cases i <;> simp)

/-! ### The summands of the induced-character formula -/

variable (α β : Fˣ →* ℂˣ)

/-- The character of the Borel representation `α ⊗ β`, read off the two diagonal entries. -/
private theorem character_GL2BorelRep_eq (g : GL2Borel F) {a b : Fˣ}
    (h0 : ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = (a : F))
    (h1 : ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 = (b : F)) :
    (GL2BorelRep F α β).character g = (α a : ℂ) * (β b : ℂ) := by
  have ha : (GL2Borel.diag g).1 = a := Units.ext (by rw [GL2Borel.diag_fst_val]; exact h0)
  have hb : (GL2Borel.diag g).2 = b := Units.ext (by rw [GL2Borel.diag_snd_val]; exact h1)
  rw [character_GL2BorelRep, GL2Borel.linearChar_apply, ha, hb, Units.val_mul]

/-- The summand of the induced-character formula at a representative `x` whose conjugate
`x⁻¹ g x` is a named element `c` of the Borel subgroup with known diagonal entries. -/
private theorem indTerm_character_GL2BorelRep_eq (a b : Fˣ) {g x : GL (Fin 2) F} {c : GL2Borel F}
    (hc : x⁻¹ * g * x = (c : GL (Fin 2) F))
    (h0 : ((c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = (a : F))
    (h1 : ((c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 = (b : F)) :
    indTerm (GL2BorelRep F α β).character g x = (α a : ℂ) * (β b : ℂ) := by
  have hmem : x⁻¹ * g * x ∈ GL2Borel F := hc ▸ c.2
  -- After the case split, the summand is the Borel character at the *subgroup* element
  -- `⟨x⁻¹ * g * x, hmem⟩`, whereas `hc` equates underlying matrices.  Rewriting by `hc` there
  -- would have to move the membership proof `hmem` along with it, so it is the equality of
  -- subgroup elements, obtained from `hc` by `Subtype.ext`, that rewrites.
  have hsub : (⟨x⁻¹ * g * x, hmem⟩ : GL2Borel F) = c := Subtype.ext hc
  rw [indTerm_apply, dite_eq_left hmem, hsub, character_GL2BorelRep_eq α β c h0 h1]

/-- The character of the Borel representation is a class function, so its summands depend only on
the coset of their representative. -/
private theorem character_GL2BorelRep_mem_classFunction :
    (GL2BorelRep F α β).character ∈ ClassFunction ℂ (GL2Borel F) :=
  ClassFunction.mem_iff.mpr fun s t => (GL2BorelRep F α β).char_conj s t

/-- The summand may be computed at any representative of its coset, in particular at a chosen one
rather than at `Quotient.out`. -/
private theorem indTerm_out_eq (g x : GL (Fin 2) F) :
    indTerm (GL2BorelRep F α β).character g
        (Quotient.out (QuotientGroup.mk x : GL (Fin 2) F ⧸ GL2Borel F)) =
      indTerm (GL2BorelRep F α β).character g x :=
  indTerm_eq_of_mk_eq (character_GL2BorelRep_mem_classFunction α β) _ _ _
    (QuotientGroup.out_eq' _)

/-! ### The four values -/

section FiniteField

variable [Fintype F]

/-- The character of the principal series is the induced class function of the Borel character. -/
private theorem character_GL2PrincipalSeries_eq_indClassFun (g : GL (Fin 2) F) :
    (GL2PrincipalSeries F α β).character g =
      indClassFun (GL2Borel F) (GL2BorelRep F α β).character g := by
  rw [GL2PrincipalSeries_def, ← indClassFun_ofFDRep_character]

/-- **The principal series has character `(q + 1) α(a) β(a)` at a central element.** A scalar
matrix is central, so every one of the `q + 1` cosets of the Borel subgroup is fixed, and each
contributes the value of `α ⊗ β` at the scalar itself. -/
theorem character_GL2PrincipalSeries_scalar (u : Fˣ) :
    (GL2PrincipalSeries F α β).character (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      ((Fintype.card F : ℂ) + 1) * ((α u : ℂ) * (β u : ℂ)) := by
  classical
  let _ : Fintype (GL (Fin 2) F ⧸ GL2Borel F) := Fintype.ofFinite _
  have hterm : ∀ t : GL (Fin 2) F ⧸ GL2Borel F,
      indTerm (GL2BorelRep F α β).character (Matrix.GeneralLinearGroup.scalar (Fin 2) u)
        (Quotient.out t) = (α u : ℂ) * (β u : ℂ) := fun t =>
    indTerm_character_GL2BorelRep_eq α β u u (c := ⟨_, GL2Borel.scalar_mem F u⟩)
      (by rw [mul_assoc, Matrix.GeneralLinearGroup.scalar_commute, inv_mul_cancel_left])
      (by simp [Matrix.scalar_apply]) (by simp [Matrix.scalar_apply])
  have hcard : Fintype.card (GL (Fin 2) F ⧸ GL2Borel F) = Fintype.card F + 1 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, GL2Borel.index_eq]
  rw [character_GL2PrincipalSeries_eq_indClassFun,
    indClassFun_eq_sum_of_smul_eq_self_mem _ _ Finset.univ fun t _ => Finset.mem_univ t,
    Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_const, Finset.card_univ, hcard,
    nsmul_eq_mul]
  push_cast
  ring

/-- **The principal series has character `α(a) β(b) + α(b) β(a)` at a split semisimple element.**
A diagonal matrix with distinct entries fixes exactly two cosets of the Borel subgroup, the
trivial one and the one of the Weyl element; conjugating by the Weyl element swaps the two
diagonal entries, so the two cosets contribute `α(a) β(b)` and `α(b) β(a)`. -/
theorem character_GL2PrincipalSeries_diagGL {a b : Fˣ} (hab : a ≠ b) :
    (GL2PrincipalSeries F α β).character (diagGL ![a, b]) =
      (α a : ℂ) * (β b : ℂ) + (α b : ℂ) * (β a : ℂ) := by
  classical
  have hab' : diagGL ![a, b] ∈ GL2Borel F := GL2Borel.mem_iff.2 (by simp)
  have hba : diagGL ![b, a] ∈ GL2Borel F := GL2Borel.mem_iff.2 (by simp)
  have hconj := inv_gl2WeylElement_mul_diagGL_mul_gl2WeylElement a b
  have hne : (QuotientGroup.mk 1 : GL (Fin 2) F ⧸ GL2Borel F) ≠
      QuotientGroup.mk (GL2WeylElement F) := by
    rw [Ne, QuotientGroup.eq]
    simp
  -- both cosets below are fixed, and there are only two fixed cosets, so these are they
  have hsub : ({QuotientGroup.mk 1, QuotientGroup.mk (GL2WeylElement F)} :
      Set (GL (Fin 2) F ⧸ GL2Borel F)) ⊆ {t | diagGL ![a, b] • t = t} := by
    rintro t (rfl | rfl)
    · rw [Set.mem_ofPred_eq, smul_quotientGroup_mk_eq_self_iff]
      simp
    · rw [Set.mem_ofPred_eq, smul_quotientGroup_mk_eq_self_iff, hconj]
      exact hba
  have hfixed : ({QuotientGroup.mk 1, QuotientGroup.mk (GL2WeylElement F)} :
      Set (GL (Fin 2) F ⧸ GL2Borel F)) = {t | diagGL ![a, b] • t = t} :=
    Set.eq_of_subset_of_ncard_le hsub
      (by rw [Set.ncard_pair hne]; exact le_of_eq (GL2Borel.natCard_fixedCosets_diagGL hab))
      (Set.toFinite _)
  rw [character_GL2PrincipalSeries_eq_indClassFun,
    indClassFun_eq_sum_of_smul_eq_self_mem _ _
      ({QuotientGroup.mk 1, QuotientGroup.mk (GL2WeylElement F)} : Finset _)
      (fun t ht => by simpa using hfixed.ge ht),
    Finset.sum_pair hne, indTerm_out_eq, indTerm_out_eq,
    indTerm_character_GL2BorelRep_eq α β a b (c := ⟨_, hab'⟩) (by group) (by simp) (by simp),
    indTerm_character_GL2BorelRep_eq α β b a (c := ⟨_, hba⟩) hconj (by simp) (by simp)]

/-- **The principal series has character `α(a) β(a)` at a non-semisimple element.** A Jordan block
fixes exactly one coset of the Borel subgroup, the trivial one, and it is upper triangular with
both diagonal entries equal to `a`. -/
theorem character_GL2PrincipalSeries_jordanGL (a : Fˣ) {b : F} (hb : b ≠ 0) :
    (GL2PrincipalSeries F α β).character (jordanGL a b) = (α a : ℂ) * (β a : ℂ) := by
  classical
  have hmem : jordanGL a b ∈ GL2Borel F := jordanGL_mem_gl2Borel a b
  have hsub : ({QuotientGroup.mk 1} : Set (GL (Fin 2) F ⧸ GL2Borel F)) ⊆
      {t | jordanGL a b • t = t} := by
    rintro t rfl
    rw [Set.mem_ofPred_eq, smul_quotientGroup_mk_eq_self_iff]
    simp
  have hfixed : ({QuotientGroup.mk 1} : Set (GL (Fin 2) F ⧸ GL2Borel F)) =
      {t | jordanGL a b • t = t} :=
    Set.eq_of_subset_of_ncard_le hsub
      (by rw [Set.ncard_singleton]; exact le_of_eq (GL2Borel.natCard_fixedCosets_jordanGL a hb))
      (Set.toFinite _)
  rw [character_GL2PrincipalSeries_eq_indClassFun,
    indClassFun_eq_sum_of_smul_eq_self_mem _ _ ({QuotientGroup.mk 1} : Finset _)
      (fun t ht => by simpa using hfixed.ge ht),
    Finset.sum_singleton, indTerm_out_eq,
    indTerm_character_GL2BorelRep_eq α β a a (c := ⟨_, hmem⟩) (by group) (by simp) (by simp)]

section Elliptic

variable {E : Type*} [Field E] [Algebra F E] (hE : Module.finrank F E = 2)

/-- **The principal series vanishes at an elliptic element.** An element of the non-split torus
coming from `E ∖ F` has no eigenline over `F`, so it fixes no coset of the Borel subgroup and the
induced-character sum is empty. -/
theorem character_GL2PrincipalSeries_gl2NonSplitTorusHom {x : Eˣ}
    (hx : (x : E) ∉ Set.range (algebraMap F E)) :
    (GL2PrincipalSeries F α β).character (GL2NonSplitTorusHom F E hE x) = 0 := by
  classical
  rw [character_GL2PrincipalSeries_eq_indClassFun,
    indClassFun_eq_sum_of_smul_eq_self_mem _ _ (∅ : Finset _) fun t ht => ?_, Finset.sum_empty]
  have : Nonempty {c : GL (Fin 2) F ⧸ GL2Borel F //
      GL2NonSplitTorusHom F E hE x • c = c} := ⟨⟨t, ht⟩⟩
  have hpos := Nat.card_pos (α := {c : GL (Fin 2) F ⧸ GL2Borel F //
    GL2NonSplitTorusHom F E hE x • c = c})
  rw [GL2Borel.natCard_fixedCosets_gl2NonSplitTorusHom hE hx] at hpos
  exact absurd hpos (lt_irrefl 0)

end Elliptic

end FiniteField

end TauCeti
