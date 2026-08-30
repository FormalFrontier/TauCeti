/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.PointStabilizer
public import TauCeti.GroupTheory.GroupAction.Transitive
public import TauCeti.RepresentationTheory.Induction.DoubleCosetPairing
public import TauCeti.RepresentationTheory.Rep.OfMulAction
public import TauCeti.RepresentationTheory.Symmetric.Standard

/-!
# Inducing the trivial representation from a point stabilizer

Let `α` be a finite set and let `x₀ : α`.  The symmetric group `Equiv.Perm α` acts transitively on
`α`, so the coset space of the stabilizer of `x₀` is `α` itself, and inducing the trivial
representation of that stabilizer produces the permutation representation of `Equiv.Perm α` on
`α`.  This file makes that identification, reads off its character as the fixed-point count, and
computes the invariant the permutation representation is pinned down by: the double cosets of the
stabilizer, of which there are exactly two, and hence the self-pairing of the induced character.

The two double cosets are the source of everything else.  A permutation either fixes `x₀` or does
not, and each of the two possibilities is a single double coset, by
`TauCeti.card_doubleCosetQuotient_stabilizer`.  So `⟨Ind 1, Ind 1⟩ = 2` whenever `|Equiv.Perm α|`
is invertible in `k`, and the permutation representation then has exactly two constituents, each
with multiplicity one.  When moreover `(|α| : k) ≠ 0` those two constituents are named: the
trivial representation on the invariant line, split off by
`TauCeti.isCompl_invariantLine_augmentationSubrepresentation`, and the standard representation of
`TauCeti.RepresentationTheory.Symmetric.Standard`, which is irreducible under that same
hypothesis.  In the excluded characteristics the character identity
`TauCeti.char_ind_trivial_stabilizer_eq_one_add_char_standardRepresentation` still holds, but the
invariant line lies inside the standard representation instead of complementing it, so there is no
such splitting.

## Main definitions

* `TauCeti.indTrivialStabilizerEquiv` and `TauCeti.indTrivialStabilizerIso`: inducing the trivial
  representation of the stabilizer of `x₀` gives the permutation representation on `α`, as an
  equivalence of representations and as an isomorphism in `Rep k (Equiv.Perm α)`.  Both are read
  on generators by `TauCeti.indTrivialStabilizerEquiv_apply_mk` and
  `TauCeti.indTrivialStabilizerIso_hom_hom_mk`.

## Main statements

* `TauCeti.char_ind_trivial_stabilizer`: the character of the induced trivial representation at `σ`
  is the number of points fixed by `σ`, and `TauCeti.finrank_ind_trivial_stabilizer` says the
  representation has dimension `|α|`.
* `TauCeti.characterPairing_ind_trivial_stabilizer`: for `|Equiv.Perm α|` invertible in `k`, its
  self-pairing is `2`, the number of double cosets.
* `TauCeti.char_ind_trivial_stabilizer_eq_one_add_char_standardRepresentation`: the induced
  character is the trivial character plus the character of the standard representation.  This is
  an identity of characters and holds in every characteristic; it is a decomposition of
  representations only under the hypotheses of
  `TauCeti.isCompl_invariantLine_augmentationSubrepresentation`.
* `TauCeti.card_doubleCosetQuotient_stabilizer_fin_four`,
  `TauCeti.finrank_ind_trivial_stabilizer_fin_four`,
  `TauCeti.finrank_augmentationSubrepresentation_fin_four` and
  `TauCeti.isIrreducible_standardRepresentation_fin_four`: the `S₄` instance -- two double cosets,
  a `4`-dimensional induced representation, and a `3`-dimensional complement, irreducible when
  `4 ≠ 0` in `k`.

## Implementation notes

The two double cosets of the point stabilizer are counted in
`TauCeti.GroupTheory.DoubleCoset.PointStabilizer`, which is pure group theory, and the
identification of the coset space with `α` is `TauCeti.quotientStabilizerEquiv`, in
`TauCeti.GroupTheory.GroupAction.Transitive`.

The coefficient field and the acted-on set share a universe in the `Rep`-level isomorphism, since
that compares two objects of one category; the `Representation`-level statements, which is where
the characters are computed, carry no such constraint.

## References

This is the "Permutation characters and fixed points" worked example of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`: "For `G = S₄` and `H` a point
stabilizer `S₃`, `Ind_H^G(trivial)` is the natural permutation representation on `4` points; its
character at `g` is the number of fixed points of `g`, and `⟨Ind_H^G 1, Ind_H^G 1⟩ = #(H \ G / H) =
2`, the two double cosets being the diagonal and off-diagonal `H`-orbits on the four points, so it
splits as `trivial ⊕ (standard 3-dimensional)`."

* J.-P. Serre, *Linear Representations of Finite Groups*, §2.3 and §7.3.
-/

public section

open MulAction

namespace TauCeti

open ClassFunction

universe u v

/-! ### The induced representation is the permutation representation on the points -/

section Equivalence

variable (k : Type u) [CommRing k] {α : Type v} (x₀ : α)

/-- **Inducing the trivial representation of a point stabilizer.**  Because `Equiv.Perm α` acts
transitively on `α`, inducing the trivial representation of the stabilizer of `x₀` gives the
permutation representation of `Equiv.Perm α` on `α` itself. -/
noncomputable def indTrivialStabilizerEquiv :
    ((Representation.trivial k (stabilizer (Equiv.Perm α) x₀) k).ind
        (stabilizer (Equiv.Perm α) x₀).subtype).Equiv
      (Representation.ofMulAction k (Equiv.Perm α) α) :=
  (indTrivialEquiv k (stabilizer (Equiv.Perm α) x₀)).trans
    (ofMulActionEquivCongr k (quotientStabilizerEquiv (Equiv.Perm α) x₀)
      (quotientStabilizerEquiv_smul (Equiv.Perm α) x₀))

/-- The generator computation rule for `TauCeti.indTrivialStabilizerEquiv`: the generator carried
by `σ` goes to the basis vector of the point `σ⁻¹ x₀`.  Not a `simp` lemma, for the reason
`TauCeti.indTrivialEquiv_apply_mk` is not: `simp` unfolds the reducible
`Representation.IndV.mk`. -/
theorem indTrivialStabilizerEquiv_apply_mk (σ : Equiv.Perm α) (a : k) :
    indTrivialStabilizerEquiv k x₀
        (Representation.IndV.mk (stabilizer (Equiv.Perm α) x₀).subtype
          (Representation.trivial k (stabilizer (Equiv.Perm α) x₀) k) σ a) =
      MonoidAlgebra.single (σ⁻¹ x₀) a := by
  rw [indTrivialStabilizerEquiv, Representation.Equiv.trans_apply, indTrivialEquiv_apply_mk,
    ofMulActionEquivCongr_apply_single, quotientStabilizerEquiv_mk, Equiv.Perm.smul_def]

end Equivalence

section Induced

variable (k : Type u) [Field k] {α : Type v} (x₀ : α)

/-- **The permutation character.**  The character at `σ` of the trivial representation of the
stabilizer of `x₀` induced up to `Equiv.Perm α` is the number of points of `α` fixed by `σ`.

Not a `simp` lemma: the general `TauCeti.char_ind_trivial` is one, and it already rewrites this
left-hand side -- to the number of fixed *cosets* -- so tagging this specialisation fails the
`simpNF` linter. -/
theorem char_ind_trivial_stabilizer [Finite α] (σ : Equiv.Perm α) :
    ((Representation.trivial k (stabilizer (Equiv.Perm α) x₀) k).ind
        (stabilizer (Equiv.Perm α) x₀).subtype).character σ = Nat.card {x : α // σ x = x} := by
  rw [Representation.char_iso (indTrivialStabilizerEquiv k x₀), char_ofMulAction]
  simp only [Equiv.Perm.smul_def]

/-- The induced representation has dimension the number of points. -/
theorem finrank_ind_trivial_stabilizer [Fintype α] :
    Module.finrank k (Representation.IndV (stabilizer (Equiv.Perm α) x₀).subtype
        (Representation.trivial k (stabilizer (Equiv.Perm α) x₀) k)) = Fintype.card α := by
  rw [(indTrivialStabilizerEquiv k x₀).toLinearEquiv.finrank_eq,
    Module.finrank_eq_card_basis (MonoidAlgebra.basis α k)]

/-- **The self-pairing of the permutation character is `2`**, the number of double cosets of the
point stabilizer.  So the permutation representation has exactly two irreducible constituents, each
occurring once. -/
theorem characterPairing_ind_trivial_stabilizer [Fintype α] [DecidableEq α] [Nontrivial α]
    (hG : IsUnit (Nat.card (Equiv.Perm α) : k)) :
    characterPairing
        (ofCharacter ((Representation.trivial k (stabilizer (Equiv.Perm α) x₀) k).ind
          (stabilizer (Equiv.Perm α) x₀).subtype))
        (ofCharacter ((Representation.trivial k (stabilizer (Equiv.Perm α) x₀) k).ind
          (stabilizer (Equiv.Perm α) x₀).subtype)) = 2 := by
  rw [characterPairing_ind_trivial_eq_card_doubleCosetQuotient k
    (stabilizer (Equiv.Perm α) x₀) (stabilizer (Equiv.Perm α) x₀) hG,
    card_doubleCosetQuotient_stabilizer x₀]
  norm_num

/-- **The permutation character is the trivial character plus the standard one.**  This is an
identity of characters, and it needs no hypothesis on the characteristic of `k`.  It becomes the
decomposition `Ind_H^G 1 ≅ trivial ⊕ standard` when `(Fintype.card α : k) ≠ 0`: that is the
hypothesis under which `TauCeti.isCompl_invariantLine_augmentationSubrepresentation` splits the
invariant line off the permutation representation and
`TauCeti.isIrreducible_standardRepresentation` makes the remaining constituent irreducible.  When
`(Fintype.card α : k) = 0` and `3 ≤ |α|` the invariant line instead lies inside the standard
representation, and there is no such splitting. -/
theorem char_ind_trivial_stabilizer_eq_one_add_char_standardRepresentation [Finite α]
    (σ : Equiv.Perm α) :
    ((Representation.trivial k (stabilizer (Equiv.Perm α) x₀) k).ind
        (stabilizer (Equiv.Perm α) x₀).subtype).character σ =
      1 + (standardRepresentation k α).character σ := by
  have : Nonempty α := ⟨x₀⟩
  rw [char_standardRepresentation σ, char_ofMulAction, char_ind_trivial_stabilizer k x₀]
  simp only [Equiv.Perm.smul_def]
  ring

end Induced

/-! ### The `Rep`-level form

Objects of `Rep k G` live over one universe, so the isomorphism form of the identification
constrains the coefficient ring and the acted-on set to share a universe. -/

section RepIso

variable (k : Type u) [CommRing k] {α : Type u} (x₀ : α)

/-- **Inducing the trivial representation of a point stabilizer**, in `Rep k (Equiv.Perm α)`. -/
noncomputable def indTrivialStabilizerIso :
    Rep.ind (stabilizer (Equiv.Perm α) x₀).subtype
        (Rep.trivial k (stabilizer (Equiv.Perm α) x₀) k) ≅
      Rep.ofMulAction k (Equiv.Perm α) α :=
  Rep.mkIso (indTrivialStabilizerEquiv k x₀)

/-- The generator computation rule for `TauCeti.indTrivialStabilizerIso`: it is
`TauCeti.indTrivialStabilizerEquiv_apply_mk` read in `Rep k (Equiv.Perm α)`. -/
theorem indTrivialStabilizerIso_hom_hom_mk (σ : Equiv.Perm α) (a : k) :
    (indTrivialStabilizerIso k x₀).hom.hom
        (Representation.IndV.mk (stabilizer (Equiv.Perm α) x₀).subtype
          (Representation.trivial k (stabilizer (Equiv.Perm α) x₀) k) σ a) =
      MonoidAlgebra.single (σ⁻¹ x₀) a := by
  rw [indTrivialStabilizerIso, Rep.mkIso_hom_hom_apply]
  exact indTrivialStabilizerEquiv_apply_mk k x₀ σ a

end RepIso

/-! ### The `S₄` instance

`G = S₄` with `H` the stabilizer of a point is the worked example: the induced trivial
representation is the natural permutation representation on four points, there are two double
cosets, and over a field in which `4 ≠ 0` the representation splits as the trivial one plus a
three-dimensional irreducible. -/

section SymmetricFour

variable (k : Type u) [Field k] (x₀ : Fin 4)

/-- The stabilizer of a point of `Fin 4` has two double cosets in `S₄`: the two orbits of `S₄` on
ordered pairs of points, the diagonal and the off-diagonal one. -/
theorem card_doubleCosetQuotient_stabilizer_fin_four :
    Nat.card (DoubleCoset.Quotient (↑(stabilizer (Equiv.Perm (Fin 4)) x₀))
      (↑(stabilizer (Equiv.Perm (Fin 4)) x₀) : Set (Equiv.Perm (Fin 4)))) = 2 :=
  card_doubleCosetQuotient_stabilizer x₀

/-- `Ind_{S₃}^{S₄} 1` is four-dimensional: it is the permutation representation on four points. -/
theorem finrank_ind_trivial_stabilizer_fin_four :
    Module.finrank k (Representation.IndV (stabilizer (Equiv.Perm (Fin 4)) x₀).subtype
        (Representation.trivial k (stabilizer (Equiv.Perm (Fin 4)) x₀) k)) = 4 := by
  rw [finrank_ind_trivial_stabilizer k x₀]
  simp

/-- The complementary constituent of `Ind_{S₃}^{S₄} 1` is three-dimensional. -/
theorem finrank_augmentationSubrepresentation_fin_four :
    Module.finrank k
        (augmentationSubrepresentation k (Equiv.Perm (Fin 4)) (Fin 4)).toSubmodule = 3 := by
  simp

/-- The standard representation of `S₄` is irreducible over a field in which `4` is nonzero, so
`Ind_{S₃}^{S₄} 1` really is the trivial representation plus a three-dimensional irreducible. -/
theorem isIrreducible_standardRepresentation_fin_four (h : (4 : k) ≠ 0) :
    (standardRepresentation k (Fin 4)).IsIrreducible :=
  isIrreducible_standardRepresentation (by simp) (Or.inr (by simpa using h))

end SymmetricFour

end TauCeti
