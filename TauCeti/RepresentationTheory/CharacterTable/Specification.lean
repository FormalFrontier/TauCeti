/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Eigenrow

/-!
# The specification a character table satisfies, and the labeled uniqueness it forces

Let `G` be a finite group. Its complex character table `TauCeti.characterTable ℂ G` is a square
matrix whose rows are indexed by an arbitrary enumeration of the irreducible characters and whose
columns are labeled by the conjugacy classes themselves. This file writes down a property
`TauCeti.IsCharacterTableSpec` of an *arbitrary* such matrix, proves that the character table has
it, and proves that it pins the character table down: **any matrix with this property is the
character table up to a permutation of its rows**.

The property is the checker of the Burnside--Dixon--Schneider algorithm. Its three ingredients are
the data that algorithm produces and can verify without knowing any representation theory:

* the identity column consists of positive integers dividing `|G|` whose squares sum to `|G|`;
* the rows are orthonormal for the class-size weighted Hermitian pairing;
* each **normalized row** `ω_i(K_C) = |C| · M i C / M i 1` (`TauCeti.centralCharacterRow`) is a
  common left eigenrow of the class-multiplication matrices, the eigenvalue at `C` being its own
  value there.

Uniqueness is the reason this is worth having: an algorithm that returns *a* matrix passing the
checker has returned *the* character table. The proof matches each normalized row with a row of the
central character table `Ω` (`TauCeti.isClassEigenrow_iff_exists_centralCharacterTable_eq`, which
identifies the normalized common left eigenrows with the central characters of the irreducibles),
recovers the degree of that irreducible from the self-pairing of the row, and reads the ordinary row
off `Ω` by `TauCeti.characterTable_eq_div`. Distinct rows of the matrix stay distinct because
orthonormality forbids repetitions, so the matching is a permutation.

## Main definitions

* `TauCeti.centralCharacterRow`: the normalized row `ω_i` of a candidate character table.
* `TauCeti.IsCharacterTableSpec`: the specification itself.

## Main results

* `TauCeti.isCharacterTableSpec_characterTable`: **the character table satisfies the
  specification**.
* `TauCeti.characterTable_unique_rows`: **labeled uniqueness**, a matrix satisfying the
  specification is the character table up to a permutation of rows. With
  `TauCeti.IsCharacterTableSpec.submatrix`, that a row permutation preserves the specification, this
  becomes the characterization `TauCeti.isCharacterTableSpec_iff_exists_perm` of the matrices
  satisfying it, and `TauCeti.IsCharacterTableSpec.exists_perm_eq`: any two of them differ by a
  permutation of rows.
* `TauCeti.IsCharacterTableSpec.exists_eq_characterTable`: the row-by-row form of uniqueness, that
  every row is a row of the character table.

## Implementation notes

The specification is stated over `ℂ`, where the roadmap pins it: its orthonormality condition is
the Hermitian one, which is the form the algorithm checks. The normalized row
`TauCeti.centralCharacterRow` needs no such restriction and is defined over any field, so that
`TauCeti.centralCharacterRow_characterTable` (the normalized rows of the character table are the
rows of the central character table) is available wherever the two tables are. Normalizing reads
only the row it is given, so it is also defined for a matrix with any row index type, and only
`TauCeti.centralCharacterRow_characterTable` and the specification itself ask for the character
table's.

The group is an explicit argument of `TauCeti.IsCharacterTableSpec`, as the roadmap pins it: the
specification is read as a statement about `G`, and `IsCharacterTableSpec G M` says what it says
without having to recover `G` from the type of `M`.

Three of the four conditions do the work in `TauCeti.characterTable_unique_rows`: the positivity
and integrality of the degrees, row orthonormality, and the eigenrow condition. The divisibility
`dᵢ ∣ |G|` and the identity `∑ dᵢ² = |G|` are part of the checker as the roadmap pins it, being
what the algorithm tests after the eigenvector search and before lifting; they are recorded here
because the character table satisfies them, not because uniqueness needs them.

## References

This is the specification and the labeled uniqueness of Layer 5 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md)
(`IsCharacterTableSpec`, `isCharacterTableSpec_characterTable` and `characterTable_unique_rows` in
that roadmap's `Suggested.lean`). See J. D. Dixon, *High speed computation of group characters*,
Numer. Math. 10 (1967) 446-450, and I. M. Isaacs, *Character Theory of Finite Groups* (1976),
Chapter 3.
-/

public section

namespace TauCeti

open scoped Matrix

universe u v

section Row

variable {ι : Type*} {k : Type u} {G : Type v} [Field k] [Group G]
  {M : Matrix ι (ConjClasses G) k} {i : ι}

/-- **The normalized row** `ω_i(K_C) = |C| · M i C / M i 1` of a candidate character table `M`.

For the character table itself this is the corresponding row of the central character table
(`TauCeti.centralCharacterRow_characterTable`), which is why the specification of a character table
asks for its normalized rows, rather than its rows, to be eigenrows of the class-multiplication
matrices. -/
noncomputable def centralCharacterRow (M : Matrix ι (ConjClasses G) k) (i : ι) (C : ConjClasses G) :
    k :=
  (Nat.card C.carrier : k) * M i C / M i (ConjClasses.mk 1)

/-- The normalized row, unfolded. The definition is not `@[expose]`d, so this is how it unfolds
outside this file; it is deliberately not `@[simp]`, because the specification and its consequences
are stated about `TauCeti.centralCharacterRow` as a whole, and unfolding it would take them out of
the shape in which the eigenrow API applies. -/
theorem centralCharacterRow_apply (M : Matrix ι (ConjClasses G) k) (i : ι) (C : ConjClasses G) :
    centralCharacterRow M i C = (Nat.card C.carrier : k) * M i C / M i (ConjClasses.mk 1) :=
  (rfl)

/-- The normalized row is normalized: it takes the value `1` on the class of the identity, whose
size is `1`. -/
@[simp]
theorem centralCharacterRow_mk_one (hM : M i (ConjClasses.mk 1) ≠ 0) :
    centralCharacterRow M i (ConjClasses.mk (1 : G)) = 1 := by
  rw [centralCharacterRow_apply, ConjClasses.card_carrier_mk_one, Nat.cast_one, one_mul,
    div_self hM]

/-- Normalizing a row, in the division-free form: `ω_i(K_C) · M i 1 = |C| · M i C`. -/
theorem centralCharacterRow_mul (hM : M i (ConjClasses.mk 1) ≠ 0) (C : ConjClasses G) :
    centralCharacterRow M i C * M i (ConjClasses.mk 1) = (Nat.card C.carrier : k) * M i C := by
  rw [centralCharacterRow_apply, div_mul_cancel₀ _ hM]

/-- Reindexing the rows of a matrix reindexes its normalized rows; in particular a permutation of
the rows permutes them. -/
@[simp]
theorem centralCharacterRow_submatrix {ι' : Type*} (M : Matrix ι (ConjClasses G) k) (e : ι' → ι)
    (i : ι') :
    centralCharacterRow (M.submatrix e id) i = centralCharacterRow M (e i) := by
  funext C
  rw [centralCharacterRow_apply, centralCharacterRow_apply, Matrix.submatrix_apply,
    Matrix.submatrix_apply, id_eq, id_eq]

variable [Fintype G] [DecidableEq G] [IsAlgClosed k] [Invertible (Nat.card G : k)]

/-- **The normalized rows of the character table are the rows of the central character table.**
Both say `ω_i(K_C) = |C| · χᵢ(g_C) / χᵢ(1)`; the hypothesis is that the degree `χᵢ(1)` does not
vanish in `k`, which holds automatically in characteristic zero. -/
theorem centralCharacterRow_characterTable {i : Fin (Nat.card (ConjClasses G))}
    (hdeg : (characterDegree k i : k) ≠ 0) :
    centralCharacterRow (characterTable k G) i = centralCharacterTable k G i := by
  funext C
  rw [centralCharacterRow_apply, characterTable_one, centralCharacterTable_eq_div i hdeg C]

end Row

section Spec

variable {G : Type v} [Group G] [Fintype G] [DecidableEq G]
  {M : Matrix (Fin (Nat.card (ConjClasses G))) (ConjClasses G) ℂ}

/-- **The specification of a complex character table.** A square matrix `M` whose columns are
labeled by the conjugacy classes of `G` satisfies it when

* its identity column consists of positive integers dividing `|G|`, whose squares sum to `|G|`;
* its rows are orthonormal for the class-size weighted Hermitian pairing on class functions;
* each of its normalized rows `TauCeti.centralCharacterRow` is a common left eigenrow of the
  class-multiplication matrices of `G` (`TauCeti.IsClassEigenrow`).

These are conditions on the structure constants of the class algebra and on the entries of `M`
alone, mentioning no representation, and they determine `M` up to a permutation of its rows
(`TauCeti.characterTable_unique_rows`). -/
structure IsCharacterTableSpec (G : Type v) [Group G] [Fintype G] [DecidableEq G]
    (M : Matrix (Fin (Nat.card (ConjClasses G))) (ConjClasses G) ℂ) : Prop where
  /-- The identity column consists of positive integers dividing the order of `G`. -/
  exists_degree : ∀ i, ∃ d : ℕ, 0 < d ∧ M i (ConjClasses.mk 1) = (d : ℂ) ∧ d ∣ Nat.card G
  /-- The squares of the identity column sum to the order of `G`. -/
  sum_degree_sq : ∑ i, M i (ConjClasses.mk 1) ^ 2 = (Nat.card G : ℂ)
  /-- The rows are orthonormal for the class-size weighted Hermitian pairing. -/
  row_orthonormal : ∀ i j, (Nat.card G : ℂ)⁻¹ * ∑ C : ConjClasses G,
      (Nat.card C.carrier : ℂ) * M i C * (starRingEnd ℂ) (M j C) = if i = j then 1 else 0
  /-- Each normalized row is a common left eigenrow of the class-multiplication matrices. -/
  row_eigen : ∀ i, IsClassEigenrow (centralCharacterRow M i)

/-- **The character table satisfies its specification.** The identity column lists the degrees,
which are positive and divide `|G|` and whose squares sum to `|G|`; the rows are orthonormal by the
first orthogonality relation; and the normalized rows are the rows of the central character table,
which are eigenrows because a central character is an algebra homomorphism out of the centre. -/
theorem isCharacterTableSpec_characterTable (G : Type v) [Group G] [Fintype G] [DecidableEq G] :
    IsCharacterTableSpec G (characterTable ℂ G) where
  exists_degree i :=
    ⟨characterDegree ℂ i, characterDegree_pos ℂ i, characterTable_one i,
      characterDegree_dvd_card ℂ i⟩
  sum_degree_sq := by
    simp only [characterTable_one]
    exact_mod_cast congrArg (Nat.cast (R := ℂ))
      (sum_characterDegree_sq_eq_card (k := ℂ) (G := G))
  row_orthonormal i j :=
    (card_inv_mul_sum_card_conjClass_mul_characterTable_mul_conj i j).trans
      (if_congr Iff.rfl rfl rfl)
  row_eigen i := by
    rw [centralCharacterRow_characterTable
      (Nat.cast_ne_zero.mpr (characterDegree_pos ℂ i).ne')]
    exact isClassEigenrow_centralCharacterTable i

namespace IsCharacterTableSpec

variable (hM : IsCharacterTableSpec G M) (i : Fin (Nat.card (ConjClasses G)))
include hM

/-- The identity column of a matrix satisfying the specification has no zero entry. -/
theorem apply_mk_one_ne_zero : M i (ConjClasses.mk 1) ≠ 0 := by
  obtain ⟨d, hd, hMd, -⟩ := hM.exists_degree i
  rw [hMd]
  exact_mod_cast hd.ne'

omit hM i in
/-- Two class functions proportional with constants `e` and `d` have weighted self-pairings
proportional with constants `e ^ 2` and `d ^ 2`. -/
private theorem sq_mul_sum_mul_conj_eq_of_mul_eq_mul {e d : ℕ} {r t : ConjClasses G → ℂ}
    (key : ∀ C, (e : ℂ) * r C = (d : ℂ) * t C) :
    (e : ℂ) ^ 2 * ∑ C : ConjClasses G, (Nat.card C.carrier : ℂ) * r C * (starRingEnd ℂ) (r C) =
      (d : ℂ) ^ 2 * ∑ C : ConjClasses G,
        (Nat.card C.carrier : ℂ) * t C * (starRingEnd ℂ) (t C) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  have hconj : (e : ℂ) * (starRingEnd ℂ) (r C) = (d : ℂ) * (starRingEnd ℂ) (t C) := by
    simpa using congrArg (starRingEnd ℂ) (key C)
  calc (e : ℂ) ^ 2 * ((Nat.card C.carrier : ℂ) * r C * (starRingEnd ℂ) (r C))
      = (Nat.card C.carrier : ℂ) * ((e : ℂ) * r C) * ((e : ℂ) * (starRingEnd ℂ) (r C)) := by ring
    _ = (Nat.card C.carrier : ℂ) * ((d : ℂ) * t C) *
          ((d : ℂ) * (starRingEnd ℂ) (t C)) := by rw [key C, hconj]
    _ = (d : ℂ) ^ 2 * ((Nat.card C.carrier : ℂ) * t C * (starRingEnd ℂ) (t C)) := by ring

omit hM in
/-- Given that the normalized row `i` of `M` is the central character row `j` (`hj`), and that its
identity entry is nonzero with value `d`, the row of `M` and row `j` of the character table are
proportional with those identity entries as the constants. The full specification
`IsCharacterTableSpec` never enters. -/
private theorem characterDegree_mul_apply_eq_mul_characterTable {d : ℕ}
    (hMi : M i (ConjClasses.mk 1) ≠ 0) (hMd : M i (ConjClasses.mk 1) = (d : ℂ))
    {j : Fin (Nat.card (ConjClasses G))}
    (hj : centralCharacterTable ℂ G j = centralCharacterRow M i) (C : ConjClasses G) :
    (characterDegree ℂ j : ℂ) * M i C = (d : ℂ) * characterTable ℂ G j C := by
  have hcard : (Nat.card (ConjClasses.carrier C) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ConjClasses.card_carrier_pos C).ne'
  have h₁ := centralCharacterRow_mul hMi C
  have h₂ := centralCharacterTable_mul_characterDegree (k := ℂ) j C
  rw [hMd] at h₁
  rw [hj] at h₂
  refine mul_left_cancel₀ hcard ?_
  calc (Nat.card C.carrier : ℂ) * ((characterDegree ℂ j : ℂ) * M i C)
      = (characterDegree ℂ j : ℂ) * ((Nat.card C.carrier : ℂ) * M i C) := by ring
    _ = (characterDegree ℂ j : ℂ) * (centralCharacterRow M i C * (d : ℂ)) := by rw [h₁]
    _ = (d : ℂ) * (centralCharacterRow M i C * (characterDegree ℂ j : ℂ)) := by ring
    _ = (d : ℂ) * ((Nat.card C.carrier : ℂ) * characterTable ℂ G j C) := by rw [h₂]
    _ = (Nat.card C.carrier : ℂ) * ((d : ℂ) * characterTable ℂ G j C) := by ring

/-- **Every row of a matrix satisfying the specification is a row of the character table.**

Its normalized row is a normalized common left eigenrow of the class-multiplication matrices, hence
the central character of some irreducible; the self-pairing of the row then forces the degree of
that irreducible to be the identity entry of the row, and the two rows agree class by class. -/
theorem exists_eq_characterTable : ∃ j, ∀ C, M i C = characterTable ℂ G j C := by
  obtain ⟨d, hdpos, hMd, -⟩ := hM.exists_degree i
  obtain ⟨j, hj⟩ := (isClassEigenrow_iff_exists_centralCharacterTable_eq
    (centralCharacterRow_mk_one (hM.apply_mk_one_ne_zero i))).mp (hM.row_eigen i)
  have he : (characterDegree ℂ j : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (characterDegree_pos ℂ j).ne'
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have key := characterDegree_mul_apply_eq_mul_characterTable i (hM.apply_mk_one_ne_zero i) hMd hj
  -- Both rows have self-pairing `1`, so the two constants of proportionality have equal squares.
  have hsum := sq_mul_sum_mul_conj_eq_of_mul_eq_mul (G := G) key
  have hMii := hM.row_orthonormal i i
  rw [ite_eq_left rfl] at hMii
  have hTjj := card_inv_mul_sum_card_conjClass_mul_characterTable_mul_conj j j
  rw [ite_eq_left rfl] at hTjj
  rw [((inv_mul_eq_one₀ hG).mp hMii).symm, ((inv_mul_eq_one₀ hG).mp hTjj).symm] at hsum
  have hsq : characterDegree ℂ j ^ 2 = d ^ 2 := by
    have := mul_right_cancel₀ hG hsum
    exact_mod_cast this
  have hdeg : (d : ℂ) = (characterDegree ℂ j : ℂ) := by
    exact_mod_cast ((Nat.pow_left_inj two_ne_zero).mp hsq).symm
  exact ⟨j, fun C => mul_left_cancel₀ he (by rw [key C, hdeg])⟩

/-- Permuting the rows of a matrix satisfying the specification gives a matrix satisfying it. -/
theorem submatrix (σ : Equiv.Perm (Fin (Nat.card (ConjClasses G)))) :
    IsCharacterTableSpec G (M.submatrix σ id) where
  exists_degree i := hM.exists_degree (σ i)
  sum_degree_sq := by
    rw [← hM.sum_degree_sq]
    exact Fintype.sum_equiv σ _ _ fun i => rfl
  row_orthonormal i j := by
    simp only [Matrix.submatrix_apply, id_eq]
    rw [hM.row_orthonormal (σ i) (σ j)]
    exact if_congr σ.apply_eq_iff_eq rfl rfl
  row_eigen i := by
    rw [centralCharacterRow_submatrix]
    exact hM.row_eigen (σ i)

end IsCharacterTableSpec

/-- **Labeled uniqueness of the character table.** With the columns labeled by the conjugacy
classes of `G`, a matrix satisfying the specification is the character table up to a permutation of
its rows, and of its rows only.

Each row is a row of the character table (`TauCeti.IsCharacterTableSpec.exists_eq_characterTable`),
and the assignment is injective because two equal rows would pair to `1` rather than to `0`; an
injective self-map of a finite type is a permutation. -/
theorem characterTable_unique_rows (hM : IsCharacterTableSpec G M) :
    ∃ σ : Equiv.Perm (Fin (Nat.card (ConjClasses G))),
      M = (characterTable ℂ G).submatrix σ id := by
  choose τ hτ using hM.exists_eq_characterTable
  have hinj : Function.Injective τ := by
    intro i j hij
    by_contra hne
    have hrow : M j = M i := funext fun C => by rw [hτ j C, hτ i C, hij]
    have h₀ := hM.row_orthonormal i j
    rw [ite_eq_right hne, hrow] at h₀
    have h₁ := hM.row_orthonormal i i
    rw [ite_eq_left rfl] at h₁
    exact one_ne_zero (h₁.symm.trans h₀)
  exact ⟨Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hinj),
    Matrix.ext fun i C => hτ i C⟩

/-- **The matrices satisfying the specification are exactly the row permutations of the character
table**: the specification recognizes the character table, and nothing else. -/
theorem isCharacterTableSpec_iff_exists_perm :
    IsCharacterTableSpec G M ↔ ∃ σ : Equiv.Perm (Fin (Nat.card (ConjClasses G))),
      M = (characterTable ℂ G).submatrix σ id :=
  ⟨characterTable_unique_rows, by
    rintro ⟨σ, rfl⟩
    exact (isCharacterTableSpec_characterTable G).submatrix σ⟩

/-- **Any two matrices satisfying the specification differ by a permutation of rows.** Both are the
character table up to such a permutation, so a solver that returns a matrix passing the checker has
returned the same table as any other. -/
theorem IsCharacterTableSpec.exists_perm_eq
    {N : Matrix (Fin (Nat.card (ConjClasses G))) (ConjClasses G) ℂ}
    (hM : IsCharacterTableSpec G M) (hN : IsCharacterTableSpec G N) :
    ∃ σ : Equiv.Perm (Fin (Nat.card (ConjClasses G))), M = N.submatrix σ id := by
  obtain ⟨σ, rfl⟩ := isCharacterTableSpec_iff_exists_perm.mp hM
  obtain ⟨τ, rfl⟩ := isCharacterTableSpec_iff_exists_perm.mp hN
  exact ⟨τ⁻¹ * σ, by ext i C; simp⟩

end Spec

end TauCeti
