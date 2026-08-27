/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
not, and each of the two possibilities is a single double coset: a permutation moving `x₀` to `y`
and one moving it to `y'` differ by the transposition of `y` and `y'`, which fixes `x₀`.  So
`⟨Ind 1, Ind 1⟩ = 2`, and the permutation representation has exactly two constituents, each with
multiplicity one: the trivial representation on the invariant line, and the standard
representation of `TauCeti.RepresentationTheory.Symmetric.Standard`, whose irreducibility is
proved there.

## Main definitions

* `TauCeti.indTrivialStabilizerEquiv` and `TauCeti.indTrivialStabilizerIso`: inducing the trivial
  representation of the stabilizer of `x₀` gives the permutation representation on `α`, as an
  equivalence of representations and as an isomorphism in `Rep k (Equiv.Perm α)`.

## Main statements

* `TauCeti.card_doubleCosetQuotient_stabilizer`: the stabilizer of a point of a nontrivial `α` has
  exactly two double cosets in `Equiv.Perm α`.
* `TauCeti.char_ind_trivial_stabilizer`: the character of the induced trivial representation at `σ`
  is the number of points fixed by `σ`, and `TauCeti.finrank_ind_trivial_stabilizer` says the
  representation has dimension `|α|`.
* `TauCeti.characterPairing_ind_trivial_stabilizer`: its self-pairing is `2`, the number of double
  cosets.
* `TauCeti.char_ind_trivial_stabilizer_eq_one_add_char_standardRepresentation`: the induced
  character is the trivial character plus the character of the standard representation.
* `TauCeti.card_doubleCosetQuotient_stabilizer_fin_four`,
  `TauCeti.finrank_ind_trivial_stabilizer_fin_four`,
  `TauCeti.finrank_augmentationSubrepresentation_fin_four` and
  `TauCeti.isIrreducible_standardRepresentation_fin_four`: the `S₄` instance -- two double cosets,
  a `4`-dimensional induced representation, and a `3`-dimensional irreducible complement.

## Implementation notes

The double-coset statements are proved on the relation `DoubleCoset.setoid` first and transported
to the quotient with `Quotient.sound'` and `Quotient.exact'`, because `DoubleCoset.Quotient` is a
plain definition that `rw` will not see through. They are proved by hand rather than through
`TauCeti.doubleCosetEquivOrbitQuotient`, which reads the same two classes as the two orbits of
`Equiv.Perm α` on ordered pairs of points: the transposition exhibiting the second class is
shorter than the transport.

The identification of the coset space with `α` is
`TauCeti.quotientStabilizerEquiv`, in `TauCeti.GroupTheory.GroupAction.Transitive`.

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

/-! ### The double cosets of a point stabilizer

A permutation either fixes `x₀` or does not, and each of the two possibilities is a single double
coset of the stabilizer. -/

section DoubleCosets

variable {α : Type v} (x₀ : α)

/-- A permutation is related to the identity by the double-coset relation of the stabilizer of `x₀`
exactly when it fixes `x₀`. -/
theorem doubleCoset_rel_stabilizer_one_iff {σ : Equiv.Perm α} :
    DoubleCoset.setoid (↑(stabilizer (Equiv.Perm α) x₀)) (↑(stabilizer (Equiv.Perm α) x₀)) σ 1 ↔
      σ x₀ = x₀ := by
  rw [DoubleCoset.rel_iff]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    have hax₀ : a x₀ = x₀ := mem_stabilizer_iff.mp ha
    have hbx₀ : b x₀ = x₀ := mem_stabilizer_iff.mp hb
    have happ := Equiv.Perm.ext_iff.mp hab.symm x₀
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hbx₀, Equiv.Perm.one_apply] at happ
    exact a.injective (happ.trans hax₀.symm)
  · intro hσ
    exact ⟨σ⁻¹, (stabilizer (Equiv.Perm α) x₀).inv_mem (mem_stabilizer_iff.mpr hσ), 1,
      (stabilizer (Equiv.Perm α) x₀).one_mem, by group⟩

/-- **The permutations moving `x₀` form a single double coset.**  If `σ` and `τ` both move `x₀`
then the transposition of `σ x₀` and `τ x₀` fixes `x₀` and carries the one onto the other. -/
theorem doubleCoset_rel_stabilizer_of_ne {σ τ : Equiv.Perm α} (hσ : σ x₀ ≠ x₀) (hτ : τ x₀ ≠ x₀) :
    DoubleCoset.setoid (↑(stabilizer (Equiv.Perm α) x₀)) (↑(stabilizer (Equiv.Perm α) x₀)) σ τ :=
    by
  classical
  have hax₀ : Equiv.swap (σ x₀) (τ x₀) x₀ = x₀ :=
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hσ) (Ne.symm hτ)
  have hinv : (Equiv.swap (σ x₀) (τ x₀))⁻¹ (τ x₀) = σ x₀ := by
    rw [Equiv.swap_inv]
    exact Equiv.swap_apply_right _ _
  rw [DoubleCoset.rel_iff]
  refine ⟨Equiv.swap (σ x₀) (τ x₀), mem_stabilizer_iff.mpr hax₀,
    σ⁻¹ * (Equiv.swap (σ x₀) (τ x₀))⁻¹ * τ, mem_stabilizer_iff.mpr ?_, by group⟩
  rw [Equiv.Perm.smul_def, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv,
    Equiv.Perm.inv_def, Equiv.symm_apply_apply]

/-- A double coset of the stabilizer of `x₀` is the identity one exactly when its permutations fix
`x₀`. -/
theorem doubleCoset_mk_stabilizer_eq_one_iff {σ : Equiv.Perm α} :
    DoubleCoset.mk (stabilizer (Equiv.Perm α) x₀) (stabilizer (Equiv.Perm α) x₀) σ =
        DoubleCoset.mk (stabilizer (Equiv.Perm α) x₀) (stabilizer (Equiv.Perm α) x₀) 1 ↔
      σ x₀ = x₀ :=
  ⟨fun h => (doubleCoset_rel_stabilizer_one_iff x₀).mp (Quotient.exact' h),
    fun h => Quotient.sound' ((doubleCoset_rel_stabilizer_one_iff x₀).mpr h)⟩

/-- **A point stabilizer has exactly two double cosets.**  The identity double coset is the
stabilizer itself, and every permutation moving `x₀` lies in the other one; a nontrivial `α`
supplies such a permutation. -/
theorem card_doubleCosetQuotient_stabilizer [Nontrivial α] :
    Nat.card (DoubleCoset.Quotient (↑(stabilizer (Equiv.Perm α) x₀))
      (↑(stabilizer (Equiv.Perm α) x₀) : Set (Equiv.Perm α))) = 2 := by
  classical
  obtain ⟨y, hy⟩ := exists_ne x₀
  have hswap : Equiv.swap x₀ y x₀ ≠ x₀ := by
    rw [Equiv.swap_apply_left]
    exact hy
  rw [Nat.card_eq_two_iff' (DoubleCoset.mk _ _ 1)]
  refine ⟨DoubleCoset.mk _ _ (Equiv.swap x₀ y),
    fun h => hswap ((doubleCoset_mk_stabilizer_eq_one_iff x₀).mp h), fun q hq => ?_⟩
  induction q using Quotient.inductionOn with
  | h σ =>
    exact Quotient.sound' (doubleCoset_rel_stabilizer_of_ne x₀
      (fun h => hq ((doubleCoset_mk_stabilizer_eq_one_iff x₀).mpr h)) hswap)

end DoubleCosets

/-! ### The induced representation is the permutation representation on the points -/

section Induced

variable (k : Type u) [Field k] {α : Type v} (x₀ : α)

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

/-- **The permutation character.**  The character at `σ` of the trivial representation of the
stabilizer of `x₀` induced up to `Equiv.Perm α` is the number of points of `α` fixed by `σ`. -/
theorem char_ind_trivial_stabilizer [Finite α] (σ : Equiv.Perm α) :
    ((Representation.trivial k (stabilizer (Equiv.Perm α) x₀) k).ind
        (stabilizer (Equiv.Perm α) x₀).subtype).character σ = Nat.card {x : α // σ x = x} := by
  rw [Representation.char_iso (indTrivialStabilizerEquiv k x₀), char_ofMulAction]
  rfl

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

/-- **The permutation representation is the trivial one plus the standard one**, read on
characters.  Together with `TauCeti.isCompl_invariantLine_augmentationSubrepresentation`, which
splits the invariant line off the permutation representation, and
`TauCeti.isIrreducible_standardRepresentation`, which says the remaining constituent is
irreducible, this is the decomposition `Ind_H^G 1 ≅ trivial ⊕ standard`. -/
theorem char_ind_trivial_stabilizer_eq_one_add_char_standardRepresentation [Finite α]
    [Nonempty α] (σ : Equiv.Perm α) :
    ((Representation.trivial k (stabilizer (Equiv.Perm α) x₀) k).ind
        (stabilizer (Equiv.Perm α) x₀).subtype).character σ =
      1 + (standardRepresentation k α).character σ := by
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
  indTrivialIso k (stabilizer (Equiv.Perm α) x₀) ≪≫
    ofMulActionIsoCongr k (quotientStabilizerEquiv (Equiv.Perm α) x₀)
      (quotientStabilizerEquiv_smul (Equiv.Perm α) x₀)

end RepIso

/-! ### The `S₄` instance

`G = S₄` with `H` the stabilizer of a point is the worked example: the induced trivial
representation is the natural permutation representation on four points, there are two double
cosets, and the representation splits as the trivial one plus a three-dimensional irreducible. -/

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
