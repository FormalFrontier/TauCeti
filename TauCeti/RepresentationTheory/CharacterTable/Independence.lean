/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Pairing
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Irreducible characters are linearly independent

Let `G` be a finite group and `k` an algebraically closed field in which `|G|` is invertible.
The characters of pairwise inequivalent irreducible representations of `G` are orthonormal for
`TauCeti.ClassFunction.characterPairing`, by Mathlib's first orthogonality relation. A family
that is orthogonal for a bilinear form and has nonzero self-pairings is linearly independent, so
those characters are linearly independent over `k`, both as class functions and as functions
on `G`.

Two consequences follow at once. An irreducible representation is determined by its character:
two irreducibles with the same character are equivalent, since otherwise a self pairing of `1`
would also have to be the cross pairing `0`. And a family of pairwise inequivalent irreducibles
has at most as many members as `G` has conjugacy classes, because the class functions have
exactly that dimension.

That last bound is in fact an equality, and the equality upgrades the linear independence proved
here to a basis of the class functions. Its other half runs through Wedderburn: the blocks of a
presentation of `k[G]` are as many as the conjugacy classes, and each carries an irreducible
representation, distinct blocks carrying inequivalent ones
(`TauCeti/RepresentationTheory/CharacterTable/BlockRepresentation.lean`). Completeness, the
resulting basis and the second orthogonality relation are proved in
`TauCeti/RepresentationTheory/CharacterTable/Completeness.lean`, downstream of this file; nothing
below uses them.

## Main results

* `TauCeti.ClassFunction.linearIndependent_ofCharacter` and
  `TauCeti.ClassFunction.linearIndependent_character`: **the characters of pairwise inequivalent
  irreducible representations are linearly independent**, as class functions and as functions
  on `G`; `TauCeti.ClassFunction.linearIndependent_ofFDRep` and
  `TauCeti.ClassFunction.linearIndependent_character_fdRep` are the `FDRep` mirrors.
* `TauCeti.Representation.nonempty_equiv_of_character_eq` and
  `TauCeti.FDRep.nonempty_iso_of_character_eq`: **an irreducible representation is determined by
  its character**.
* `TauCeti.ClassFunction.card_le_card_conjClasses` and
  `TauCeti.ClassFunction.card_le_card_conjClasses_fdRep`: **there are at most as many pairwise
  inequivalent irreducibles as there are conjugacy classes**.
* `TauCeti.Representation.nonempty_equiv_iff_eq`: inside a pairwise inequivalent family, two
  members are equivalent exactly when they are the same member. This one needs neither
  irreducibility nor any hypothesis on `k` and `G`; it is the form in which the
  pairwise-inequivalence hypothesis is used downstream.

## Implementation notes

Nothing here mentions `TauCeti.ClassFunction.characterPairing`, which is defined for a `Fintype`:
the pairing enters only through the split orthonormality lemmas of
`TauCeti/RepresentationTheory/CharacterTable/Pairing.lean`, so these statements ask for
`Finite G` and produce the `Fintype` inside their proofs.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md).
  Everything here is proved from Layer 0's `characterPairing` and its orthonormality, which are on
  `main`, together with Mathlib's `char_orthonormal`; no Layer 1, Layer 2 or Layer 3 material is
  used, and none is presupposed. What the file supplies is prerequisite material for the later
  layers: that a character determines its irreducible is the injectivity of the map
  `character : Irreps k G → ClassFunction k G` that Layer 2.5 asks for, and the cardinality bound
  is the `≤` half of Layer 2's count `Nat.card (Irreps k G) = Nat.card (ConjClasses G)`, obtained
  without Wedderburn. Layer 3's completeness item, the spanning statement and the orthonormal
  basis, is proved downstream in
  `TauCeti/RepresentationTheory/CharacterTable/Completeness.lean` from the linear independence
  proved here and the `≥` half of the count.
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Theorem 2.8 and Corollary 2.9.
-/

public section

namespace TauCeti

universe u v w

namespace ClassFunction

variable {k : Type u} {G : Type v} [Field k] [Group G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

/-! ### Linear independence -/

section Independence

variable [Finite G] {ι : Type*} {V : ι → Type w} [∀ i, AddCommGroup (V i)]
  [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)]

/-- **The characters of pairwise inequivalent irreducible representations are linearly
independent** as class functions: they are orthogonal for the character pairing, and each pairs
to `1` with itself. -/
theorem linearIndependent_ofCharacter (ρ : ∀ i, Representation k G (V i))
    [∀ i, (ρ i).IsIrreducible] (h : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j))) :
    LinearIndependent k fun i => ofCharacter (ρ i) := by
  let _ := Fintype.ofFinite G
  refine LinearMap.BilinForm.linearIndependent_of_iIsOrtho
    (LinearMap.BilinForm.iIsOrtho_def.mpr fun i j hij =>
      characterPairing_ofCharacter_eq_zero (ρ i) (ρ j) (h (Ne.symm hij))) fun i => ?_
  rw [characterPairing_ofCharacter_self (ρ i)]
  exact one_ne_zero

/-- The characters of pairwise inequivalent irreducible representations are linearly independent
as functions on `G`. -/
theorem linearIndependent_character (ρ : ∀ i, Representation k G (V i))
    [∀ i, (ρ i).IsIrreducible] (h : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j))) :
    LinearIndependent k fun i => (ρ i).character := by
  have hmap := (linearIndependent_ofCharacter ρ h).map' (ClassFunction k G).subtype
    (Submodule.ker_subtype _)
  have hcoe : ⇑(ClassFunction k G).subtype ∘ (fun i => ofCharacter (ρ i)) =
      fun i => (ρ i).character := by
    funext i g
    simp only [Function.comp_apply, Submodule.subtype_apply, ofCharacter_apply]
  rwa [hcoe] at hmap

/-- **The characters of pairwise non-isomorphic simple objects of `FDRep k G` are linearly
independent** as class functions. -/
theorem linearIndependent_ofFDRep (X : ι → FDRep k G) [∀ i, CategoryTheory.Simple (X i)]
    (h : Pairwise fun i j => IsEmpty (X i ≅ X j)) :
    LinearIndependent k fun i => ofFDRep (X i) := by
  let _ := Fintype.ofFinite G
  refine LinearMap.BilinForm.linearIndependent_of_iIsOrtho
    (LinearMap.BilinForm.iIsOrtho_def.mpr fun i j hij =>
      characterPairing_ofFDRep_eq_zero (X i) (X j) (h hij)) fun i => ?_
  rw [characterPairing_ofFDRep_self (X i)]
  exact one_ne_zero

/-- The characters of pairwise non-isomorphic simple objects of `FDRep k G` are linearly
independent as functions on `G`. -/
theorem linearIndependent_character_fdRep (X : ι → FDRep k G)
    [∀ i, CategoryTheory.Simple (X i)] (h : Pairwise fun i j => IsEmpty (X i ≅ X j)) :
    LinearIndependent k fun i => (X i).character := by
  have hmap := (linearIndependent_ofFDRep X h).map' (ClassFunction k G).subtype
    (Submodule.ker_subtype _)
  have hcoe : ⇑(ClassFunction k G).subtype ∘ (fun i => ofFDRep (X i)) =
      fun i => (X i).character := by
    funext i g
    simp only [Function.comp_apply, Submodule.subtype_apply, ofFDRep_apply]
  rwa [hcoe] at hmap

end Independence

end ClassFunction

/-! ### An irreducible representation is determined by its character -/

namespace Representation

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)] {V W : Type w} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- **An irreducible representation is determined by its character**: two irreducible
representations with the same character are equivalent. -/
theorem nonempty_equiv_of_character_eq (ρ : Representation k G V) (σ : Representation k G W)
    [ρ.IsIrreducible] [σ.IsIrreducible] (h : ρ.character = σ.character) :
    Nonempty (σ.Equiv ρ) := by
  let _ := Fintype.ofFinite G
  rw [← not_isEmpty_iff]
  intro hempty
  have hσρ : ClassFunction.ofCharacter σ = ClassFunction.ofCharacter ρ :=
    Subtype.ext <| funext fun g => by simp only [ClassFunction.ofCharacter_apply, h]
  have h0 := ClassFunction.characterPairing_ofCharacter_eq_zero ρ σ hempty
  rw [hσρ, ClassFunction.characterPairing_ofCharacter_self ρ] at h0
  exact one_ne_zero h0

/-! ### Members of a pairwise inequivalent family -/

section Pairwise

variable {k : Type u} {G : Type v} [Semiring k] [Monoid G] {ι : Type*} {V : ι → Type w}
  [∀ i, AddCommMonoid (V i)] [∀ i, Module k (V i)] (ρ : ∀ i, Representation k G (V i))
  (hind : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)))

include hind

/-- Inside a family of pairwise inequivalent representations, two members are equivalent exactly
when they are the same member. -/
@[simp]
theorem nonempty_equiv_iff_eq {i j : ι} : Nonempty ((ρ i).Equiv (ρ j)) ↔ i = j := by
  refine ⟨fun h => ?_, fun h => h ▸ ⟨_root_.Representation.Equiv.refl (ρ i)⟩⟩
  by_contra hij
  exact (hind hij).elim' h.some

end Pairwise

end Representation

namespace FDRep

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

/-- **A simple object of `FDRep k G` is determined by its character**: two simple objects with
the same character are isomorphic. -/
theorem nonempty_iso_of_character_eq (X Y : FDRep k G) [CategoryTheory.Simple X]
    [CategoryTheory.Simple Y] (h : X.character = Y.character) : Nonempty (X ≅ Y) := by
  let _ := Fintype.ofFinite G
  rw [← not_isEmpty_iff]
  intro hempty
  have hXY : ClassFunction.ofFDRep Y = ClassFunction.ofFDRep X :=
    Subtype.ext <| funext fun g => by simp only [ClassFunction.ofFDRep_apply, h]
  have h0 := ClassFunction.characterPairing_ofFDRep_eq_zero X Y hempty
  rw [hXY, ClassFunction.characterPairing_ofFDRep_self X] at h0
  exact one_ne_zero h0

end FDRep

namespace ClassFunction

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)] {ι : Type*} [Fintype ι] {V : ι → Type w}
  [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)]

/-! ### Counting irreducibles against conjugacy classes -/

section Counting

/-- **There are at most as many pairwise inequivalent irreducible representations as there are
conjugacy classes**: their characters are linearly independent in the space of class functions,
whose dimension is the number of conjugacy classes. -/
theorem card_le_card_conjClasses (ρ : ∀ i, Representation k G (V i))
    [∀ i, (ρ i).IsIrreducible] (h : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j))) :
    Fintype.card ι ≤ Nat.card (ConjClasses G) := by
  let _ := Fintype.ofFinite G
  have hle := (linearIndependent_ofCharacter ρ h).fintype_card_le_finrank
  rwa [finrank_eq_card_conjClasses] at hle

/-- There are at most as many pairwise non-isomorphic simple objects of `FDRep k G` as there are
conjugacy classes of `G`. -/
theorem card_le_card_conjClasses_fdRep (X : ι → FDRep k G) [∀ i, CategoryTheory.Simple (X i)]
    (h : Pairwise fun i j => IsEmpty (X i ≅ X j)) :
    Fintype.card ι ≤ Nat.card (ConjClasses G) := by
  let _ := Fintype.ofFinite G
  have hle := (linearIndependent_ofFDRep X h).fintype_card_le_finrank
  rwa [finrank_eq_card_conjClasses] at hle

end Counting

end ClassFunction

end TauCeti
