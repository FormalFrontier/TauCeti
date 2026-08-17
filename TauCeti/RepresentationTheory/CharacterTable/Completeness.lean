/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.BlockRepresentation
public import TauCeti.RepresentationTheory.CharacterTable.Independence
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Completeness of the irreducible characters, and the second orthogonality relation

Let `G` be a finite group and `k` an algebraically closed field in which `|G|` is invertible. The
characters of pairwise inequivalent irreducible representations of `G` are orthonormal, hence
linearly independent, and there are at most as many of them as `G` has conjugacy classes
(`TauCeti/RepresentationTheory/CharacterTable/Independence.lean`). This file supplies the matching
lower bound and everything it unlocks.

The lower bound comes from the Wedderburn presentation of `k[G]`: its blocks are indexed by the
conjugacy classes and each carries an irreducible representation, pairwise inequivalent
(`TauCeti.exists_irreducible_family_conjClasses`). A family of that size therefore has linearly
independent characters in a space of exactly that dimension, so **the characters are a basis of the
class functions**: this is completeness, and `TauCeti.ClassFunction.le_span_irreducibleCharacters`
is the spanning statement it amounts to.

Expanding a class function in that basis is easy because the basis is orthonormal for
`TauCeti.ClassFunction.characterPairing`: the coefficient of `χᵢ` in `f` is `⟨χᵢ, f⟩`. Applying this
to the indicator function of a conjugacy class, whose pairings are computed by
`TauCeti.ClassFunction.characterPairing_classIndicator_inv`, gives the **second (column)
orthogonality relation** `|C_g| · ∑ᵢ χᵢ(g) χᵢ(h⁻¹) = |G|` or `0` according as `g` and `h` are
conjugate or not.

## Main statements

* `TauCeti.ClassFunction.basisOfIrreducibleCharacters`: **the characters of a family of pairwise
  inequivalent irreducible representations indexed by as many indices as `G` has conjugacy classes
  form a basis of the class functions**, with `TauCeti.ClassFunction.exists_basis_ofCharacter` the
  statement that such a family exists.
* `TauCeti.ClassFunction.le_span_irreducibleCharacters`: **completeness**, in the form that every
  class function lies in the span of the irreducible characters.
* `TauCeti.ClassFunction.sum_characterPairing_smul_ofCharacter`: the expansion of a class function
  in that basis, with coefficients the pairings against the irreducible characters.
* `TauCeti.ClassFunction.exists_nonempty_equiv`: **such a family is a complete list of the
  irreducibles**, every irreducible representation being equivalent to one of its members.
* `TauCeti.ClassFunction.card_conjClass_mul_sum_char_mul_char_inv`: **the second orthogonality
  relation**, in a form free of division, and `TauCeti.ClassFunction.sum_char_mul_char_inv` in the
  quotient form `|G| / |C_g|`.

## Implementation notes

The irreducibles are produced on the coordinate spaces `Fin n → k` rather than as simple objects of
`FDRep k G`, because a Wedderburn block is a matrix algebra acting on its column space, and because
`FDRep k G` carries only representations on types in the universe of `k`. Neither Mathlib nor this
repository relates `CategoryTheory.Simple` in `FDRep k G` to `Representation.IsIrreducible`, so the
`FDRep` mirrors of the statements below are not available; the `Representation`-level statements are
the ones the rest of the theory uses.

## References

This implements the completeness and second-orthogonality items of Layer 3 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
at the `Representation` level. Its `Suggested.lean` pins them as `irreducibleCharacters_span`, over
the simple objects of `FDRep k G`, and `char_column_orthogonality`, over the `ℂ`-valued character
table; the statements below are the prerequisites those two are read off from once Layer 2.5
supplies the dictionary between `CategoryTheory.Simple` in `FDRep k G` and
`Representation.IsIrreducible`, and neither roadmap name is claimed here.
See I. M. Isaacs, *Character Theory of Finite Groups* (1976), Theorem 2.18 and Corollary 2.14, or
J.-P. Serre, *Linear Representations of Finite Groups*, Sections 2.5 and 6.4.
-/

public section

namespace TauCeti

namespace ClassFunction

universe u v w

section Basis

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)] {ι : Type*} [Finite ι] {V : ι → Type w}
  [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)]
  (ρ : ∀ i, Representation k G (V i)) [∀ i, (ρ i).IsIrreducible]
  (hind : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)))
  (hcard : Nat.card ι = Nat.card (ConjClasses G))

include hind hcard

/-- **The irreducible characters are a basis of the class functions.** The characters of a family of
pairwise inequivalent irreducible representations are linearly independent, and if the family is
indexed by as many indices as `G` has conjugacy classes then there are as many of them as the
dimension of the class functions. -/
noncomputable def basisOfIrreducibleCharacters : Module.Basis ι k (ClassFunction k G) :=
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite ι
  basisOfLinearIndependentOfCardEqFinrank' (fun i => ofCharacter (ρ i))
    (linearIndependent_ofCharacter ρ hind)
    (by rw [finrank_eq_card_conjClasses, ← hcard, Nat.card_eq_fintype_card])

@[simp]
theorem coe_basisOfIrreducibleCharacters :
    ⇑(basisOfIrreducibleCharacters ρ hind hcard) = fun i => ofCharacter (ρ i) :=
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite ι
  coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _

theorem basisOfIrreducibleCharacters_apply (i : ι) :
    basisOfIrreducibleCharacters ρ hind hcard i = ofCharacter (ρ i) :=
  congrFun (coe_basisOfIrreducibleCharacters ρ hind hcard) i

/-- **Completeness**: the irreducible characters span the class functions. -/
theorem span_range_ofCharacter_eq_top :
    Submodule.span k (Set.range fun i => ofCharacter (ρ i)) =
      (⊤ : Submodule k (ClassFunction k G)) :=
  coe_basisOfIrreducibleCharacters ρ hind hcard ▸
    (basisOfIrreducibleCharacters ρ hind hcard).span_eq

end Basis

section Orthogonality

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)] {ι : Type*} [Fintype ι] {V : ι → Type w}
  [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)]
  (ρ : ∀ i, Representation k G (V i)) [∀ i, (ρ i).IsIrreducible]
  (hind : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)))
  (hcard : Nat.card ι = Nat.card (ConjClasses G))

include hind hcard

/-- **The expansion of a class function in the basis of irreducible characters.** The basis is
orthonormal for the character pairing, so the coefficient of `χᵢ` is the pairing `⟨χᵢ, f⟩`. -/
theorem sum_characterPairing_smul_ofCharacter (f : ClassFunction k G) :
    ∑ i, characterPairing (ofCharacter (ρ i)) f • ofCharacter (ρ i) = f := by
  classical
  set b := basisOfIrreducibleCharacters ρ hind hcard with hb
  have hbi : ∀ i, b i = ofCharacter (ρ i) := basisOfIrreducibleCharacters_apply ρ hind hcard
  have hrepr : ∀ j, characterPairing (ofCharacter (ρ j)) f = b.repr f j := by
    intro j
    conv_lhs => rw [← b.sum_repr f]
    rw [map_sum, Finset.sum_eq_single j]
    · rw [map_smul, hbi j, characterPairing_ofCharacter_self (ρ j), smul_eq_mul, mul_one]
    · intro i _ hij
      rw [map_smul, hbi i,
        characterPairing_ofCharacter_eq_zero (ρ j) (ρ i) (hind hij), smul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  calc ∑ i, characterPairing (ofCharacter (ρ i)) f • ofCharacter (ρ i)
      = ∑ i, b.repr f i • b i := Finset.sum_congr rfl fun i _ => by rw [hrepr i, hbi i]
    _ = f := b.sum_repr f

/-- The pointwise form of the expansion of a class function in the irreducible characters. -/
theorem apply_eq_sum_characterPairing_mul_character (f : ClassFunction k G) (y : G) :
    f.1 y = ∑ i, characterPairing (ofCharacter (ρ i)) f * (ρ i).character y := by
  conv_lhs => rw [← sum_characterPairing_smul_ofCharacter ρ hind hcard f]
  simp

open scoped Classical in
/-- **The second (column) orthogonality relation**, in a form free of division: the columns of the
character table at `g` and at `h`, weighted by the size of the class of `g`, sum to `|G|` when `g`
and `h` are conjugate and to `0` otherwise. -/
theorem card_conjClass_mul_sum_char_mul_char_inv (g h : G) :
    (Nat.card (ConjClasses.mk g).carrier : k) *
        ∑ i, (ρ i).character g * (ρ i).character h⁻¹ =
      if IsConj g h then (Nat.card G : k) else 0 := by
  classical
  have hval := apply_eq_sum_characterPairing_mul_character ρ hind hcard
    (classIndicator (k := k) g⁻¹) h⁻¹
  have hpair : ∀ i, characterPairing (ofCharacter (ρ i)) (classIndicator (k := k) g⁻¹) =
      (Nat.card G : k)⁻¹ * ((Nat.card (ConjClasses.mk g).carrier : k) * (ρ i).character g) := by
    intro i
    simpa using characterPairing_classIndicator_inv (ofCharacter (ρ i)) g
  have hiff : ConjClasses.mk h⁻¹ = ConjClasses.mk g⁻¹ ↔ IsConj g h := by
    rw [ConjClasses.mk_eq_mk_iff_isConj]
    exact ⟨fun hgh => (isConj_inv_iff.mp hgh).symm, fun hgh => isConj_inv_iff.mpr hgh.symm⟩
  have hlhs : (classIndicator (k := k) g⁻¹).1 h⁻¹ = if IsConj g h then (1 : k) else 0 := by
    rw [classIndicator_apply]
    exact if_congr hiff rfl rfl
  rw [hlhs] at hval
  have hsum : (if IsConj g h then (1 : k) else 0) =
      (Nat.card G : k)⁻¹ *
        ((Nat.card (ConjClasses.mk g).carrier : k) *
          ∑ i, (ρ i).character g * (ρ i).character h⁻¹) := by
    rw [hval, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hpair i]; ring
  have hG : (Nat.card G : k) ≠ 0 := Invertible.ne_zero _
  rw [eq_comm, inv_mul_eq_iff_eq_mul₀ hG] at hsum
  rw [hsum]
  split <;> simp

open scoped Classical in
/-- **The second (column) orthogonality relation** in its quotient form: the columns of the
character table at `g` and at `h` sum to `|G| / |C_g|` when `g` and `h` are conjugate, and to `0`
otherwise. -/
theorem sum_char_mul_char_inv (g h : G) :
    ∑ i, (ρ i).character g * (ρ i).character h⁻¹ =
      if IsConj g h then (Nat.card G : k) / Nat.card (ConjClasses.mk g).carrier else 0 := by
  have hgg := card_conjClass_mul_sum_char_mul_char_inv ρ hind hcard g g
  rw [ite_eq_left (IsConj.refl g)] at hgg
  have hc : (Nat.card (ConjClasses.mk g).carrier : k) ≠ 0 := fun h0 =>
    Invertible.ne_zero (Nat.card G : k) (by rw [← hgg, h0, zero_mul])
  have hgh := card_conjClass_mul_sum_char_mul_char_inv ρ hind hcard g h
  by_cases hconj : IsConj g h
  · rw [ite_eq_left hconj] at hgh ⊢
    rw [eq_div_iff hc, mul_comm]
    exact hgh
  · rw [ite_eq_right hconj] at hgh ⊢
    exact (mul_eq_zero.mp hgh).resolve_left hc

end Orthogonality

section Classification

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)] {ι : Type*} [Finite ι] {V : ι → Type w}
  [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)]
  (ρ : ∀ i, Representation k G (V i)) [∀ i, (ρ i).IsIrreducible]
  (hind : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)))
  (hcard : Nat.card ι = Nat.card (ConjClasses G))

include hind hcard

/-- **A complete family exhausts the irreducibles**: every finite-dimensional irreducible
representation of `G` is equivalent to a member of the family. Were it equivalent to none of them,
its character would be orthogonal to a basis of the class functions, hence zero; but an irreducible
character pairs to `1` with itself. -/
theorem exists_nonempty_equiv {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (σ : Representation k G W) [σ.IsIrreducible] : ∃ i, Nonempty (σ.Equiv (ρ i)) := by
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite ι
  by_contra hcon
  have hzero : ∀ i, characterPairing (ofCharacter (ρ i)) (ofCharacter σ) = 0 := fun i =>
    characterPairing_ofCharacter_eq_zero (ρ i) σ (not_nonempty_iff.mp fun hn => hcon ⟨i, hn⟩)
  have h0 : ofCharacter σ = (0 : ClassFunction k G) := by
    rw [← sum_characterPairing_smul_ofCharacter ρ hind hcard (ofCharacter σ)]
    simp [hzero]
  have h1 := characterPairing_ofCharacter_self σ
  rw [h0] at h1
  simp at h1

end Classification

section Existence

variable (k : Type u) (G : Type v) [Field k] [Group G] [Finite G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

/-- **The irreducible characters of a finite group are a basis of its class functions.** There is a
family of pairwise inequivalent irreducible representations of `G` indexed by the conjugacy classes
of `G`, and its characters are a basis of the class functions.

The count is sharp in both directions: no larger family of pairwise inequivalent irreducibles exists
by `TauCeti.ClassFunction.card_le_card_conjClasses`. -/
theorem exists_basis_ofCharacter :
    ∃ (d : ConjClasses G → ℕ) (ρ : ∀ C, Representation k G (Fin (d C) → k))
      (b : Module.Basis (ConjClasses G) k (ClassFunction k G)),
      (∀ C, (ρ C).IsIrreducible) ∧ ∀ C, b C = ofCharacter (ρ C) := by
  have : NeZero (Nat.card G : k) := ⟨Invertible.ne_zero _⟩
  obtain ⟨d, ρ, hirr, hind, -⟩ := exists_irreducible_family_conjClasses k G
  have := hirr
  exact ⟨d, ρ, basisOfIrreducibleCharacters ρ hind rfl, hirr,
    basisOfIrreducibleCharacters_apply ρ hind rfl⟩

/-- **Completeness**: every class function is a linear combination of irreducible characters.

Only this inclusion is stated: every character is itself a class function, so the span is contained
in `TauCeti.ClassFunction k G` for free, and the irreducible characters do not span all of `G → k`
unless `G` is abelian.

This is the `Representation`-level form, spanning by the characters of the irreducible
representations on the coordinate spaces `Fin n → k` that the Wedderburn blocks produce. It is a
prerequisite for, and not the same statement as, the roadmap's `irreducibleCharacters_span`, which
spans by the characters of the simple objects of `FDRep k G`: passing between the two needs the
dictionary between `CategoryTheory.Simple` in `FDRep k G` and `Representation.IsIrreducible`, which
is Layer 2.5 work and exists neither in Mathlib nor here. -/
theorem le_span_irreducibleCharacters :
    ClassFunction k G ≤ Submodule.span k
      {f : G → k | ∃ (n : ℕ) (ρ : Representation k G (Fin n → k)), ρ.IsIrreducible ∧
        ρ.character = f} := by
  classical
  let _ := Fintype.ofFinite (ConjClasses G)
  obtain ⟨d, ρ, b, hirr, hb⟩ := exists_basis_ofCharacter k G
  have hcoe : ∀ C, ((ofCharacter (ρ C) : ClassFunction k G) : G → k) = (ρ C).character :=
    fun C => funext fun x => ofCharacter_apply (ρ C) x
  intro f hf
  have hf' : f = ∑ C, b.repr ⟨f, hf⟩ C • (ρ C).character := by
    have hrepr := congrArg (fun F : ClassFunction k G => (F : G → k)) (b.sum_repr ⟨f, hf⟩)
    simpa [hb, hcoe] using hrepr.symm
  rw [hf']
  refine Submodule.sum_mem _ fun C _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨d C, ρ C, hirr C, rfl⟩

end Existence

end ClassFunction

end TauCeti
