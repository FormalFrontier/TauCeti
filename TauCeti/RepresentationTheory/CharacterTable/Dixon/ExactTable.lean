/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Specification
public import TauCeti.RepresentationTheory.CharacterTable.Table
public import TauCeti.RepresentationTheory.CharacterTable.Values
public import TauCeti.RingTheory.Cyclotomic.Basic

/-!
# The exact character table

The Burnside-Dixon-Schneider solver must return its output in an exact type: entries in the
computable ring `TauCeti.Cyclotomic (Monoid.exponent G)` of exact cyclotomic integers, never in
`ℂ`. This file defines that output type, `TauCeti.ExactCharTable`, together with the three facts
that make it the right one:

* **faithfulness** — the complex realization `TauCeti.ExactCharTable.embed` through the pinned
  embedding `TauCeti.Cyclotomic.complexEmbedding` is injective, so exact tables carry no less
  information than their complex images;
* **adequacy** — the character table of `G` itself lifts: some exact table embeds onto
  `TauCeti.characterTable ℂ G`, because every character value is an integer polynomial in the
  distinguished primitive root of unity of order `Monoid.exponent G`
  (`TauCeti.Representation.char_mem_adjoin_of_isPrimitiveRoot`);
* **labeled uniqueness at the exact level** — two exact tables whose complex realizations satisfy
  the Dixon-Schneider specification `TauCeti.IsCharacterTableSpec` agree up to a permutation of
  their rows, by injectivity and the complex-level uniqueness
  `TauCeti.characterTable_unique_rows`.

`ℂ` appears only through the pinned embedding, in the specification: this is the boundary the
character-theory roadmap prescribes for the executable deliverable, where the summit theorem
asserts that the embedded exact output satisfies the `ℂ`-valued checker. The eigenvector search
(`TauCeti.ClassData.centralCharacterSearch`), the refinement of its output to one-dimensional
common eigenspaces, and the assembled solver are separate milestones and are not touched here;
they will consume this type as their output interface.

## Main declarations

* `TauCeti.ExactCharTable`: the exact character table type, a class-indexed matrix of exact
  cyclotomic integers at the exponent of `G`.
* `TauCeti.ExactCharTable.embed`: its complex realization through the pinned embedding.
* `TauCeti.ExactCharTable.embed_injective`: the realization is injective.
* `TauCeti.ExactCharTable.exists_embed_eq_characterTable`: the character table lifts to an exact
  table.
* `TauCeti.ExactCharTable.eq_submatrix_of_isCharacterTableSpec`: exact tables satisfying the
  embedded specification are unique up to a row permutation.

## References

* J. D. Dixon, *High speed computation of group characters*, Numer. Math. 10 (1967), 446-450,
  for the exact-output discipline of the solver this type serves.
-/

public section

namespace TauCeti

universe v

variable {G : Type v} [Group G] [Fintype G]

variable (G) in
/-- **The exact character table type**: a matrix indexed like the character table of `G`, with
entries in the computable ring of exact cyclotomic integers at the exponent of `G`. Every value
of a complex character of `G` is an integer polynomial in a primitive root of unity of that
order, so this type loses nothing (`TauCeti.ExactCharTable.exists_embed_eq_characterTable`);
the solver returns it, and `ℂ` enters only through the pinned embedding. -/
abbrev ExactCharTable :=
  Matrix (Fin (Nat.card (ConjClasses G))) (ConjClasses G) (Cyclotomic (Monoid.exponent G))

namespace ExactCharTable

/-- The complex realization of an exact character table: apply the pinned embedding
`TauCeti.Cyclotomic.complexEmbedding` to every entry. -/
noncomputable def embed (T : ExactCharTable G) :
    Matrix (Fin (Nat.card (ConjClasses G))) (ConjClasses G) ℂ :=
  T.map Cyclotomic.complexEmbedding

@[simp]
theorem embed_apply (T : ExactCharTable G) (i : Fin (Nat.card (ConjClasses G)))
    (C : ConjClasses G) : T.embed i C = Cyclotomic.complexEmbedding (T i C) :=
  (rfl)

/-- Realizing a row-permuted exact table permutes the rows of the realization. -/
theorem embed_submatrix (T : ExactCharTable G)
    (σ : Fin (Nat.card (ConjClasses G)) → Fin (Nat.card (ConjClasses G))) :
    embed (T.submatrix σ id) = T.embed.submatrix σ id :=
  (rfl)

/-- **The complex realization is injective**: an exact character table carries exactly the
information of its complex image, by injectivity of the pinned embedding. -/
theorem embed_injective : Function.Injective (embed (G := G)) := fun _ _ h =>
  Matrix.ext fun i C =>
    Cyclotomic.complexEmbedding_injective (congrFun (congrFun h i) C)

variable (G) in
/-- **Adequacy of the exact type**: the character table of `G` lifts to an exact character
table. Every entry is a character value, hence lies in `ℤ[ζ]` for the distinguished primitive
root `ζ` of order `Monoid.exponent G`, which is exactly the image of the pinned embedding. -/
theorem exists_embed_eq_characterTable :
    ∃ T : ExactCharTable G, T.embed = characterTable ℂ G := by
  have hlift : ∀ i C, ∃ y : Cyclotomic (Monoid.exponent G),
      Cyclotomic.complexEmbedding y = characterTable ℂ G i C := by
    intro i C
    obtain ⟨g, rfl⟩ := C.exists_rep
    refine Cyclotomic.exists_complexEmbedding_eq_of_mem_adjoin ?_
    rw [characterTable_apply, ← character_irreducibleRepresentation]
    exact Representation.char_mem_adjoin_of_isPrimitiveRoot _
      Cyclotomic.isPrimitiveRoot_complexRoot (Monoid.pow_exponent_eq_one g)
  choose T hT using hlift
  exact ⟨Matrix.of T, by ext i C; rw [embed_apply]; exact hT i C⟩

variable (G) in
/-- **The embedded specification is satisfiable**: some exact character table embeds to a matrix
satisfying the Dixon-Schneider specification. This is the acceptance interface of the solver: it
must return an exact table in this set, and by
`TauCeti.ExactCharTable.eq_submatrix_of_isCharacterTableSpec` any member is the lift of the
character table up to a permutation of rows. -/
theorem exists_isCharacterTableSpec_embed [DecidableEq G] :
    ∃ T : ExactCharTable G, IsCharacterTableSpec G T.embed := by
  obtain ⟨T, hT⟩ := exists_embed_eq_characterTable G
  refine ⟨T, ?_⟩
  rw [hT]
  exact isCharacterTableSpec_characterTable G

/-- **Labeled uniqueness at the exact level**: two exact character tables whose complex
realizations satisfy the Dixon-Schneider specification agree up to a permutation of their rows.
The complex-level uniqueness identifies both realizations with the character table up to row
permutations, and injectivity of the realization transports the comparison back to the exact
tables themselves. -/
theorem eq_submatrix_of_isCharacterTableSpec [DecidableEq G] {T T' : ExactCharTable G}
    (hT : IsCharacterTableSpec G T.embed) (hT' : IsCharacterTableSpec G T'.embed) :
    ∃ σ : Equiv.Perm (Fin (Nat.card (ConjClasses G))), T' = T.submatrix σ id := by
  obtain ⟨σ, hσ⟩ := characterTable_unique_rows hT
  obtain ⟨σ', hσ'⟩ := characterTable_unique_rows hT'
  refine ⟨σ'.trans σ.symm, embed_injective ?_⟩
  rw [embed_submatrix, hσ, hσ', Matrix.submatrix_submatrix]
  refine Matrix.ext fun i C => ?_
  simp only [Matrix.submatrix_apply, Function.comp_apply, Equiv.trans_apply,
    Equiv.apply_symm_apply, id_eq]

end ExactCharTable

end TauCeti
