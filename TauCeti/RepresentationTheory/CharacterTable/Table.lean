/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Completeness
public import TauCeti.RepresentationTheory.CharacterTable.Degree

/-!
# The character table of a finite group

Let `G` be a finite group and `k` an algebraically closed field in which `|G|` is invertible. The
characters of the irreducible representations of `G` over `k` form a finite set
`TauCeti.irreducibleCharacters k G` of functions `G → k`, of size the number of conjugacy classes of
`G`: they are linearly independent, they span the class functions, and every irreducible
representation is equivalent to one that occurs in the complete family produced by the Wedderburn
decomposition of `k[G]`.

Choosing an enumeration of that set by `Fin r`, `r = |ConjClasses G|`, turns the irreducible
characters into the rows of a **square matrix**, the character table
`TauCeti.characterTable k G : Matrix (Fin r) (ConjClasses G) k`, whose `(i, C)` entry is the value
of the `i`-th irreducible character on the class `C`. Its columns are labelled by the actual
conjugacy classes of `G`; only the rows depend on the enumeration, and any two enumerations differ
by a permutation of them.

The two orthogonality relations become statements about the table: its rows are orthonormal for the
character pairing, and its columns are orthogonal with the class sizes as weights. Over `ℂ` both
take their familiar Hermitian form, because inversion conjugates character values
(`TauCeti.Representation.conj_char`).

## Main definitions

* `TauCeti.irreducibleCharacters`: the set of irreducible characters of `G` over `k`.
* `TauCeti.irreducibleCharacter`: the `i`-th irreducible character, for an enumeration of that set
  by `Fin (Nat.card (ConjClasses G))`, together with `TauCeti.irreducibleRepresentation`, an
  irreducible representation affording it, and `TauCeti.characterDegree`, its degree.
* `TauCeti.characterTable`: the character table of `G`.
* `TauCeti.basisIrreducibleCharacter`: its rows, as a basis of the class functions.

## Main results

* `TauCeti.card_irreducibleCharacters`: **`G` has as many irreducible characters as conjugacy
  classes**, so the table is square; `TauCeti.character_mem_irreducibleCharacters` is the statement
  that no irreducible character is missing from it.
* `TauCeti.characterTable_apply`: the entries of the table are the irreducible character values.
* `TauCeti.card_inv_mul_sum_characterTable_mul_characterTable_inv` and
  `TauCeti.card_inv_mul_sum_characterTable_mul_conj`: **first (row) orthogonality**, over `k` and in
  its Hermitian form over `ℂ`; `TauCeti.card_inv_mul_sum_card_conjClass_mul_characterTable_mul_conj`
  is the latter summed one column at a time, the form in which the roadmap's specification of a
  character table asks for it;
  `TauCeti.characterPairing_ofCharacter_irreducibleRepresentation_orthonormal` is the same relation
  phrased as orthonormality for the character pairing.
* `TauCeti.card_conjClass_mul_sum_characterTable_mul_characterTable_inv` and
  `TauCeti.sum_characterTable_mul_conj`: **second (column) orthogonality**, over `k` and in its
  Hermitian form over `ℂ`.
* `TauCeti.characterTable_one`: the identity-class column of the table lists the degrees, which are
  positive (`TauCeti.characterDegree_pos`) and have squares summing to `|G|`
  (`TauCeti.sum_characterDegree_sq_eq_card`); in characteristic zero they moreover divide `|G|`
  (`TauCeti.characterDegree_dvd_card`).

## Implementation notes

`TauCeti.irreducibleCharacters` is defined by the representations on the coordinate spaces
`Fin n → k`, the shape in which the Wedderburn blocks of `k[G]` produce them; this also keeps the
set free of a universe parameter beyond those of `k` and `G`. Nothing is lost:
`TauCeti.character_mem_irreducibleCharacters` puts the character of an irreducible representation on
*any* finite-dimensional space in the set, since it is equivalent to one of the coordinate ones.

The rows are indexed by `Fin (Nat.card (ConjClasses G))` rather than by a bare `Fin r`, so that the
squareness of the table is visible in its type.

The roadmap pins the character table over `ℂ`. Everything holds over any algebraically closed field
in which `|G|` is invertible except the Hermitian refinements, which are stated over `ℂ`, and the
divisibility of the degrees by `|G|`, which additionally assumes `CharZero k`. So the table is
defined over such a `k`, and `TauCeti.characterTable ℂ G` is the pinned object.

## References

This is Layer 3 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md):
the character table as an object, with its second orthogonality relation
(`char_column_orthogonality` in that roadmap's `Suggested.lean`) and the degrees in its
identity-class column.
See I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 2, or J.-P. Serre, *Linear
Representations of Finite Groups* (1977), Section 2.5.
-/

public section

namespace TauCeti

open Module

universe u v w

section Set

variable (k : Type u) (G : Type v) [Field k] [Group G]

/-- **The irreducible characters of `G` over `k`**: the set of characters of the irreducible
representations of `G` on the coordinate spaces `Fin n → k`.

Restricting to coordinate spaces costs nothing over an algebraically closed field in which `|G|` is
invertible: by `TauCeti.character_mem_irreducibleCharacters` the character of an irreducible
representation on any finite-dimensional space belongs to this set. -/
def irreducibleCharacters : Set (G → k) :=
  {f | ∃ (n : ℕ) (ρ : Representation k G (Fin n → k)), ρ.IsIrreducible ∧ ρ.character = f}

variable {k G}

/-- Membership in `TauCeti.irreducibleCharacters` unfolded. This is deliberately not `@[simp]`:
unfolding membership to the existential would put the left-hand side of the `@[simp]` lemma
`TauCeti.irreducibleCharacter_mem` out of simp normal form, and simp cannot discharge the
existential it produces. -/
theorem mem_irreducibleCharacters_iff {f : G → k} :
    f ∈ irreducibleCharacters k G ↔
      ∃ (n : ℕ) (ρ : Representation k G (Fin n → k)), ρ.IsIrreducible ∧ ρ.character = f :=
  Iff.rfl

variable [Finite G] [IsAlgClosed k] [Invertible (Nat.card G : k)]

/-- **Every irreducible character is an irreducible character**: the character of an irreducible
representation on an arbitrary finite-dimensional space lies in `TauCeti.irreducibleCharacters`,
because it is equivalent to one of the representations on a coordinate space. -/
@[simp]
theorem character_mem_irreducibleCharacters {V : Type w} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (σ : Representation k G V) [σ.IsIrreducible] :
    σ.character ∈ irreducibleCharacters k G := by
  have : NeZero (Nat.card G : k) := ⟨Invertible.ne_zero _⟩
  obtain ⟨d, ρ, hirr, hind, -⟩ := exists_irreducible_family_conjClasses k G
  have := hirr
  obtain ⟨C, ⟨e⟩⟩ := ClassFunction.exists_nonempty_equiv ρ hind rfl σ
  exact ⟨d C, ρ C, hirr C, (_root_.Representation.char_iso e).symm⟩

variable (k G)

/-- **The irreducible characters of `G` correspond to its conjugacy classes.** A complete family of
pairwise inequivalent irreducible representations is indexed by `ConjClasses G`, its characters are
distinct because they are linearly independent, and every irreducible character is one of them. -/
theorem nonempty_equiv_conjClasses_irreducibleCharacters :
    Nonempty (ConjClasses G ≃ irreducibleCharacters k G) := by
  have : NeZero (Nat.card G : k) := ⟨Invertible.ne_zero _⟩
  obtain ⟨d, ρ, hirr, hind, -⟩ := exists_irreducible_family_conjClasses k G
  have := hirr
  have hmem : ∀ C, (ρ C).character ∈ irreducibleCharacters k G := fun C => ⟨d C, ρ C, hirr C, rfl⟩
  refine ⟨Equiv.ofBijective (fun C => ⟨(ρ C).character, hmem C⟩) ⟨fun C D hCD => ?_, ?_⟩⟩
  · refine (ClassFunction.linearIndependent_ofCharacter ρ hind).injective (Subtype.ext ?_)
    exact funext fun g => by
      simpa using congrFun (congrArg Subtype.val hCD) g
  · rintro ⟨-, n, σ, hσ, rfl⟩
    have := hσ
    obtain ⟨C, ⟨e⟩⟩ := ClassFunction.exists_nonempty_equiv ρ hind rfl σ
    exact ⟨C, Subtype.ext (_root_.Representation.char_iso e).symm⟩

instance : Finite (irreducibleCharacters k G) :=
  Finite.of_equiv _ (nonempty_equiv_conjClasses_irreducibleCharacters k G).some

/-- **A finite group has as many irreducible characters as conjugacy classes.** -/
theorem card_irreducibleCharacters :
    Nat.card (irreducibleCharacters k G) = Nat.card (ConjClasses G) :=
  (Nat.card_congr (nonempty_equiv_conjClasses_irreducibleCharacters k G).some).symm

end Set

section Enumeration

variable (k : Type u) (G : Type v) [Field k] [Group G] [Finite G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

/-- An enumeration of the irreducible characters of `G` by `Fin (Nat.card (ConjClasses G))`, chosen
once and for all; it indexes the rows of the character table. -/
noncomputable def finEquivIrreducibleCharacters :
    Fin (Nat.card (ConjClasses G)) ≃ irreducibleCharacters k G :=
  (finCongr (card_irreducibleCharacters k G).symm).trans (Finite.equivFin _).symm

variable {G}

/-- The `i`-th irreducible character of `G`. -/
noncomputable def irreducibleCharacter (i : Fin (Nat.card (ConjClasses G))) : G → k :=
  finEquivIrreducibleCharacters k G i

/-- Every enumerated character is an irreducible character. -/
@[simp]
theorem irreducibleCharacter_mem (i : Fin (Nat.card (ConjClasses G))) :
    irreducibleCharacter k i ∈ irreducibleCharacters k G :=
  (finEquivIrreducibleCharacters k G i).2

/-- Distinct rows of the character table are distinct characters. -/
theorem irreducibleCharacter_injective :
    Function.Injective (irreducibleCharacter (G := G) k) :=
  Subtype.val_injective.comp (finEquivIrreducibleCharacters k G).injective

/-- **Every irreducible character is enumerated.** -/
theorem exists_irreducibleCharacter_eq {f : G → k} (hf : f ∈ irreducibleCharacters k G) :
    ∃ i, irreducibleCharacter k i = f :=
  ⟨(finEquivIrreducibleCharacters k G).symm ⟨f, hf⟩,
    congrArg Subtype.val ((finEquivIrreducibleCharacters k G).apply_symm_apply ⟨f, hf⟩)⟩

/-- **The degree of the `i`-th irreducible character**, the dimension of a representation affording
it. -/
noncomputable def characterDegree (i : Fin (Nat.card (ConjClasses G))) : ℕ :=
  (irreducibleCharacter_mem k i).choose

/-- An irreducible representation affording the `i`-th irreducible character. -/
noncomputable def irreducibleRepresentation (i : Fin (Nat.card (ConjClasses G))) :
    Representation k G (Fin (characterDegree k i) → k) :=
  (irreducibleCharacter_mem k i).choose_spec.choose

instance (i : Fin (Nat.card (ConjClasses G))) :
    (irreducibleRepresentation k i).IsIrreducible :=
  (irreducibleCharacter_mem k i).choose_spec.choose_spec.1

@[simp]
theorem character_irreducibleRepresentation (i : Fin (Nat.card (ConjClasses G))) :
    (irreducibleRepresentation k i).character = irreducibleCharacter k i :=
  (irreducibleCharacter_mem k i).choose_spec.choose_spec.2

/-- The representations affording the rows of the character table are pairwise inequivalent, their
characters being distinct. -/
theorem pairwise_isEmpty_equiv_irreducibleRepresentation :
    Pairwise fun i j : Fin (Nat.card (ConjClasses G)) =>
      IsEmpty ((irreducibleRepresentation k i).Equiv (irreducibleRepresentation k j)) :=
  fun i j hij =>
  ⟨fun e => hij (irreducibleCharacter_injective k (by
    rw [← character_irreducibleRepresentation k i, ← character_irreducibleRepresentation k j]
    exact _root_.Representation.char_iso e))⟩

/-- **An irreducible character takes its degree as its value at the identity.** -/
@[simp]
theorem irreducibleCharacter_one (i : Fin (Nat.card (ConjClasses G))) :
    irreducibleCharacter k i 1 = (characterDegree k i : k) := by
  rw [← character_irreducibleRepresentation k i, _root_.Representation.char_one]
  simp

/-- **The degree of an irreducible character is positive**: an irreducible representation is
nonzero, so the space affording the character has positive dimension. -/
theorem characterDegree_pos (i : Fin (Nat.card (ConjClasses G))) :
    0 < characterDegree k i := by
  have hsimple : Nontrivial (irreducibleRepresentation k i).asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra k G) _
  have : Nontrivial (Fin (characterDegree k i) → k) :=
    (irreducibleRepresentation k i).asModuleEquiv.symm.toEquiv.nontrivial
  simpa using Module.finrank_pos (R := k) (M := Fin (characterDegree k i) → k)

/-- **The sum of the squares of the degrees is the order of the group**, as an identity of natural
numbers. The representations affording the enumerated characters are pairwise inequivalent
irreducibles, and there are as many of them as `G` has conjugacy classes, so they are the blocks of
a Wedderburn presentation of `k[G]` up to a relabelling of the blocks; the squares of the block
dimensions add up to the dimension `|G|` of `k[G]`. -/
theorem sum_characterDegree_sq_eq_card :
    ∑ i : Fin (Nat.card (ConjClasses G)), characterDegree k i ^ 2 = Nat.card G := by
  classical
  have : NeZero (Nat.card G : k) := ⟨Invertible.ne_zero _⟩
  let _ : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  obtain ⟨d, ρ, hirr, hind, hsum⟩ := exists_irreducible_family_conjClasses k G
  have := hirr
  choose C hC using fun i : Fin (Nat.card (ConjClasses G)) =>
    ClassFunction.exists_nonempty_equiv ρ hind rfl (irreducibleRepresentation k i)
  have hdeg : ∀ i, characterDegree k i ^ 2 = d (C i) ^ 2 := fun i => by
    have := (hC i).some.toLinearEquiv.finrank_eq
    simp only [Module.finrank_fin_fun] at this
    rw [this]
  have hinj : Function.Injective C := by
    intro i j hij
    by_contra hne
    have e : (irreducibleRepresentation k i).Equiv (ρ (C j)) := hij ▸ (hC i).some
    exact (pairwise_isEmpty_equiv_irreducibleRepresentation k hne).elim
      (e.trans (hC j).some.symm)
  have hbij : Function.Bijective C :=
    (Fintype.bijective_iff_injective_and_card C).2
      ⟨hinj, by rw [Fintype.card_fin, Fintype.card_eq_nat_card]⟩
  rw [← hsum, finsum_eq_sum_of_fintype]
  exact Fintype.sum_bijective C hbij _ _ hdeg

/-- **The degree of an irreducible character divides the order of the group.** -/
theorem characterDegree_dvd_card [CharZero k] (i : Fin (Nat.card (ConjClasses G))) :
    characterDegree k i ∣ Nat.card G := by
  simpa using Representation.finrank_dvd_card (irreducibleRepresentation k i)

end Enumeration

section Table

variable (k : Type u) (G : Type v) [Field k] [Group G] [Finite G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

/-- **The character table of `G`**: the square matrix whose `(i, C)` entry is the value of the
`i`-th irreducible character of `G` on the conjugacy class `C`.

The rows are indexed by the chosen enumeration `TauCeti.finEquivIrreducibleCharacters` of the
irreducible characters and the columns by the conjugacy classes themselves, so the table is labelled
on its columns and determined up to a permutation of its rows. -/
noncomputable def characterTable :
    Matrix (Fin (Nat.card (ConjClasses G))) (ConjClasses G) k := fun i =>
  ClassFunction.toConjClasses (ClassFunction.ofCharacter (irreducibleRepresentation k i))

variable {k G}

/-- **The entries of the character table are the values of the irreducible characters**: the entry
in row `i` and the column of the class of `g` is the `i`-th irreducible character at `g`. -/
@[simp]
theorem characterTable_apply (i : Fin (Nat.card (ConjClasses G))) (g : G) :
    characterTable k G i (ConjClasses.mk g) = irreducibleCharacter k i g := by
  rw [characterTable, ClassFunction.toConjClasses_mk, ClassFunction.ofCharacter_apply,
    character_irreducibleRepresentation]

/-- The identity-class column of the character table lists the degrees of the irreducible
characters.

This is not a `simp` lemma: `TauCeti.characterTable_apply` already rewrites the left-hand side to
`TauCeti.irreducibleCharacter k i 1`, which `TauCeti.irreducibleCharacter_one` then evaluates. -/
theorem characterTable_one (i : Fin (Nat.card (ConjClasses G))) :
    characterTable k G i (ConjClasses.mk 1) = (characterDegree k i : k) := by
  rw [characterTable_apply, irreducibleCharacter_one]

variable (k G)

/-- **The rows of the character table are a basis of the class functions.** There are as many of
them as `G` has conjugacy classes, which is the dimension of the space of class functions, and they
are linearly independent. -/
noncomputable def basisIrreducibleCharacter :
    Module.Basis (Fin (Nat.card (ConjClasses G))) k (ClassFunction k G) :=
  ClassFunction.basisOfIrreducibleCharacters (irreducibleRepresentation k)
    (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp)

variable {k G}

@[simp]
theorem basisIrreducibleCharacter_apply (i : Fin (Nat.card (ConjClasses G))) (g : G) :
    (basisIrreducibleCharacter k G i).1 g = irreducibleCharacter k i g := by
  rw [basisIrreducibleCharacter, ClassFunction.basisOfIrreducibleCharacters_apply,
    ClassFunction.ofCharacter_apply, character_irreducibleRepresentation]

end Table

section RowOrthogonality

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

/-- **The rows of the character table are orthonormal**, read as class functions: the character
pairing of the representations affording the `i`-th and `j`-th irreducible characters is `1` when
`i = j` and `0` otherwise. This is the orthonormality of the irreducible characters
(`TauCeti.ClassFunction.characterPairing_ofCharacter_self` and
`TauCeti.ClassFunction.characterPairing_ofCharacter_eq_zero`) transported along the enumeration. -/
@[simp]
theorem characterPairing_ofCharacter_irreducibleRepresentation_orthonormal
    (i j : Fin (Nat.card (ConjClasses G))) :
    ClassFunction.characterPairing (ClassFunction.ofCharacter (irreducibleRepresentation k i))
        (ClassFunction.ofCharacter (irreducibleRepresentation k j)) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl]
    exact ClassFunction.characterPairing_ofCharacter_self _
  · rw [ite_eq_right hij]
    exact ClassFunction.characterPairing_ofCharacter_eq_zero _ _
      (pairwise_isEmpty_equiv_irreducibleRepresentation k (Ne.symm hij))

/-- **First (row) orthogonality on the character table**: distinct rows pair to `0` and each row
pairs to `1` with itself. -/
theorem card_inv_mul_sum_characterTable_mul_characterTable_inv
    (i j : Fin (Nat.card (ConjClasses G))) :
    (Nat.card G : k)⁻¹ * ∑ g : G, characterTable k G i (ConjClasses.mk g) *
        characterTable k G j (ConjClasses.mk g⁻¹) = if i = j then 1 else 0 := by
  have hchar : ∀ (l : Fin (Nat.card (ConjClasses G))) (g : G),
      characterTable k G l (ConjClasses.mk g) =
        (irreducibleRepresentation k l).character g := by simp
  simp only [hchar, ← ClassFunction.characterPairing_ofCharacter]
  exact characterPairing_ofCharacter_irreducibleRepresentation_orthonormal i j

end RowOrthogonality

section ColumnOrthogonality

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

open scoped Classical in
/-- **Second (column) orthogonality on the character table**, in a form free of division: the
columns at `g` and at `h`, weighted by the size of the class of `g`, sum to `|G|` when `g` and `h`
are conjugate and to `0` otherwise. -/
theorem card_conjClass_mul_sum_characterTable_mul_characterTable_inv (g h : G) :
    (Nat.card (ConjClasses.mk g).carrier : k) *
        ∑ i : Fin (Nat.card (ConjClasses G)),
          characterTable k G i (ConjClasses.mk g) * characterTable k G i (ConjClasses.mk h⁻¹) =
      if IsConj g h then (Nat.card G : k) else 0 := by
  let _ : Fintype G := Fintype.ofFinite G
  simpa using ClassFunction.card_conjClass_mul_sum_char_mul_char_inv
    (fun i : Fin (Nat.card (ConjClasses G)) => irreducibleRepresentation k i)
    (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp) g h

open scoped Classical in
/-- **Second (column) orthogonality on the character table**, in its quotient form. -/
theorem sum_characterTable_mul_characterTable_inv (g h : G) :
    ∑ i : Fin (Nat.card (ConjClasses G)),
        characterTable k G i (ConjClasses.mk g) * characterTable k G i (ConjClasses.mk h⁻¹) =
      if IsConj g h then (Nat.card G : k) / Nat.card (ConjClasses.mk g).carrier else 0 := by
  let _ : Fintype G := Fintype.ofFinite G
  simpa using ClassFunction.sum_char_mul_char_inv
    (fun i : Fin (Nat.card (ConjClasses G)) => irreducibleRepresentation k i)
    (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp) g h

end ColumnOrthogonality

section Complex

variable {G : Type v} [Group G] [Finite G]

/-- **Complex conjugation of an irreducible character value inverts the group element.** -/
@[simp]
theorem conj_irreducibleCharacter (i : Fin (Nat.card (ConjClasses G))) (g : G) :
    (starRingEnd ℂ) (irreducibleCharacter ℂ i g) = irreducibleCharacter ℂ i g⁻¹ := by
  rw [← character_irreducibleRepresentation ℂ i]
  exact Representation.conj_char _ g

/-- Complex conjugation of a character-table entry inverts the class.

This is not a `simp` lemma: `TauCeti.characterTable_apply` already rewrites the left-hand side to
`(starRingEnd ℂ) (TauCeti.irreducibleCharacter ℂ i g)`, which `TauCeti.conj_irreducibleCharacter`
then normalizes. -/
theorem conj_characterTable_apply (i : Fin (Nat.card (ConjClasses G))) (g : G) :
    (starRingEnd ℂ) (characterTable ℂ G i (ConjClasses.mk g)) =
      characterTable ℂ G i (ConjClasses.mk g⁻¹) := by
  rw [characterTable_apply, characterTable_apply, conj_irreducibleCharacter]

/-- **Complex conjugation of a character-table entry inverts the class**, in the class-indexed
form: `TauCeti.conj_characterTable_apply` is the same statement about a representative. -/
@[simp]
theorem conj_characterTable (i : Fin (Nat.card (ConjClasses G))) (C : ConjClasses G) :
    (starRingEnd ℂ) (characterTable ℂ G i C) = characterTable ℂ G i C⁻¹ := by
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  rw [ConjClasses.inv_mk, conj_characterTable_apply]

/-- **First (row) orthogonality over `ℂ`**, in its Hermitian form: the rows of the complex character
table are orthonormal for the Hermitian inner product on class functions. -/
theorem card_inv_mul_sum_characterTable_mul_conj [Fintype G]
    (i j : Fin (Nat.card (ConjClasses G))) :
    (Nat.card G : ℂ)⁻¹ * ∑ g : G, characterTable ℂ G i (ConjClasses.mk g) *
        (starRingEnd ℂ) (characterTable ℂ G j (ConjClasses.mk g)) = if i = j then 1 else 0 := by
  simp only [conj_characterTable_apply]
  exact card_inv_mul_sum_characterTable_mul_characterTable_inv i j

/-- **First (row) orthogonality over `ℂ`, summed one column at a time**: the Hermitian pairing of
two rows of the complex character table, collected over the conjugacy classes with the class sizes
as weights. This is the shape in which the roadmap's specification of a character table asks for row
orthonormality; `TauCeti.card_inv_mul_sum_characterTable_mul_conj` is the same statement summed over
the group.

The enumeration of the conjugacy classes is an explicit `Fintype` argument rather than a classical
one, so that the statement is about whichever enumeration the caller has in hand; a caller with
`[DecidableEq G]` has one, and a classical instance would not be defeq to it. -/
theorem card_inv_mul_sum_card_conjClass_mul_characterTable_mul_conj [Fintype (ConjClasses G)]
    (i j : Fin (Nat.card (ConjClasses G))) :
    (Nat.card G : ℂ)⁻¹ * ∑ C : ConjClasses G, (Nat.card C.carrier : ℂ) *
        characterTable ℂ G i C * (starRingEnd ℂ) (characterTable ℂ G j C) =
      if i = j then 1 else 0 := by
  let _ : Fintype G := Fintype.ofFinite G
  rw [← card_inv_mul_sum_characterTable_mul_conj i j]
  congr 1
  have hsum := ClassFunction.sum_eq_sum_conjClasses (ClassFunction.ofConjClasses
    (fun C => characterTable ℂ G i C * (starRingEnd ℂ) (characterTable ℂ G j C)))
  have hval : ∀ C : ConjClasses G, ClassFunction.toConjClasses (ClassFunction.ofConjClasses
      (fun C => characterTable ℂ G i C * (starRingEnd ℂ) (characterTable ℂ G j C))) C =
      characterTable ℂ G i C * (starRingEnd ℂ) (characterTable ℂ G j C) := by
    rintro C
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
    rw [ClassFunction.toConjClasses_mk, ClassFunction.ofConjClasses_apply]
  simp only [ClassFunction.ofConjClasses_apply, hval] at hsum
  rw [hsum]
  exact Finset.sum_congr rfl fun C _ => mul_assoc _ _ _

open scoped Classical in
/-- **Second (column) orthogonality over `ℂ`**, in its Hermitian form: two columns of the complex
character table are orthogonal unless they are the same class, in which case they pair to
`|G| / |C|`. -/
theorem sum_characterTable_mul_conj (C C' : ConjClasses G) :
    ∑ i : Fin (Nat.card (ConjClasses G)),
        characterTable ℂ G i C * (starRingEnd ℂ) (characterTable ℂ G i C') =
      if C = C' then (Nat.card G : ℂ) / Nat.card C.carrier else 0 := by
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  obtain ⟨h, rfl⟩ := ConjClasses.exists_rep C'
  simp only [conj_characterTable_apply]
  rw [sum_characterTable_mul_characterTable_inv]
  exact if_congr ConjClasses.mk_eq_mk_iff_isConj.symm rfl rfl

end Complex

end TauCeti
