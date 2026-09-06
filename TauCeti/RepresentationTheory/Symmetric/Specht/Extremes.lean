/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.Partition
public import TauCeti.RepresentationTheory.FDRep
public import TauCeti.RepresentationTheory.Subrepresentation
public import TauCeti.RepresentationTheory.Symmetric.Specht.Character

/-!
# The Specht modules of the one-row and the one-column shape

The two extreme partitions of `n` are the single row `(n)` and the single column `(1ⁿ)`, and their
Specht modules are the two representations of `Sₙ` that are visible without any representation
theory: the trivial one and the sign one.  This file proves that for the **polytabloid**
presentation `S^μ`, the span of the polytabloids inside the Young permutation module `M^μ`, and
then for the partition-indexed packaging `TauCeti.spechtModule` that the classification of the
irreducibles is stated in.  It also reads off the two rows `χ^{(n)} = 1` and `χ^{(1ⁿ)} = sgn` of
the integer character table of `Sₙ`.

The mechanism is the same on both shapes: the orbit of a single polytabloid `e_t` consists of
scalar multiples of `e_t`, so the Specht module is the line `ℚ ∙ e_t` and the symmetric group acts
on it through those scalars.  What differs is where the scalars come from.

* On a shape with **at most one row** the column group of `t` is trivial, so `e_t` is the bare
  tabloid `{t}` (`TauCeti.YoungTableau.polytabloid_eq_single_of_colSubgroup_eq_bot`); and the row
  group of `t` is everything, so every permutation fixes `{t}`, the row group being the stabilizer
  of a tabloid.  The scalars are all `1`.
* On a shape with **at most one column** the column group of `t` is everything, so every
  permutation is a column permutation of `t` and rescales `e_t` by its sign
  (`TauCeti.YoungTableau.polytabloid_relabel_of_mem_colSubgroup`).  The scalars are the signs.

The two shape hypotheses come in the two equivalent forms that
`TauCeti.YoungTableau.rowSubgroup_eq_top_iff` and `TauCeti.YoungTableau.colSubgroup_eq_top_iff`
relate.  A statement whose conclusion mentions a tableau `t` — the polytabloid identities, and the
description of the Specht module as the line through `e_t` — is stated on the row resp. column
group of that `t`, as in `TauCeti.RepresentationTheory.Symmetric.Specht.Ideal.Extremes`, which
proves the same two identifications for the left-ideal presentation `ℚ[Sₙ] c_t`.  A statement
about `spechtSubrepresentation μ` alone is stated on the diagram, as `μ.colLen 0 ≤ 1` resp.
`μ.rowLen 0 ≤ 1`, so that no tableau has to be produced to use it; the partition-level results
below feed those hypotheses with `TauCeti.colLen_diagramOf_indiscrete_le_one` and
`TauCeti.rowLen_diagramOf_ones_le_one`.  The two hypotheses are compatible rather than exclusive:
on the empty diagram both hold, and there `Sₙ` is trivial and so are both characters.

"Is the trivial representation" and "is the sign representation" are stated the way the ideal file
states them, as the action formula together with the dimension: a line on which `σ` acts by `1`
resp. by `sgn σ`.  No isomorphism with a separately constructed model object is built here.  The
third named small irreducible, the standard representation `S^{(n-1,1)}`, is not treated here
either; it is not a line and needs the tabloid combinatorics of the two-row shape.

## Main results

* `TauCeti.spechtSubrepresentation_toRepresentation_eq_trivial`: **`S^{(n)}` is the trivial
  representation**, and `TauCeti.finrank_spechtSubrepresentation_of_colLen_le_one` that it is a
  line.
* `TauCeti.spechtSubrepresentation_toRepresentation_apply_of_rowLen_le_one`: **`S^{(1ⁿ)}` is the
  sign representation**, and `TauCeti.finrank_spechtSubrepresentation_of_rowLen_le_one` that it too
  is a line.
* `TauCeti.spechtModule_indiscrete_ρ_apply`, `TauCeti.finrank_spechtModule_indiscrete`,
  `TauCeti.spechtModule_ones_ρ_apply` and `TauCeti.finrank_spechtModule_ones`: the same four
  statements for the partition-indexed Specht modules `S^{(n)}` and `S^{(1ⁿ)}`.
* `TauCeti.spechtChar_indiscrete` and `TauCeti.spechtChar_ones`: the two integer characters,
  `χ^{(n)} = 1` and `χ^{(1ⁿ)} = sgn`.
* `TauCeti.symmetricCharacterTable_indiscrete` and `TauCeti.symmetricCharacterTable_ones`: the two
  extreme rows of the character table of `Sₙ`, the all-ones row and the row of signs, the latter
  read off the number of parts of the cycle type.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 4.
* [W. Fulton, *Young Tableaux*][fulton1997], Section 7.2.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 4, "the named small irreducibles", and Layer 6, the special values of the Specht character.
-/

public section

namespace TauCeti

open Module

namespace YoungTableau

variable {μ : YoungDiagram}

/-! ## The polytabloids of the two extreme shapes -/

/-- Every permutation fixes the polytabloid of a tableau all of whose labels share a row: the
polytabloid is the bare tabloid, and the row group, which is everything, is its stabilizer. -/
@[simp]
theorem permutationModule_ρ_polytabloid_of_rowSubgroup_eq_top (t : YoungTableau μ)
    (h : rowSubgroup t = ⊤) (σ : Equiv.Perm (Fin μ.card)) :
    (permutationModule (shapePartition μ)).ρ σ (polytabloid t) = polytabloid t := by
  have hmem : σ ∈ rowSubgroup t := by rw [h]; exact Subgroup.mem_top σ
  rw [polytabloid_eq_single_of_colSubgroup_eq_bot t
      (colSubgroup_eq_bot_of_rowSubgroup_eq_top t h),
    Representation.ofMulAction_single, smul_tabloid_eq_self_iff.mpr hmem]

/-- Every permutation scales the polytabloid of a tableau all of whose labels share a column by its
sign: every permutation is then a column permutation of `t`. -/
@[simp]
theorem permutationModule_ρ_polytabloid_of_colSubgroup_eq_top (t : YoungTableau μ)
    (h : colSubgroup t = ⊤) (σ : Equiv.Perm (Fin μ.card)) :
    (permutationModule (shapePartition μ)).ρ σ (polytabloid t) =
      ((Equiv.Perm.sign σ : ℤ) : ℚ) • polytabloid t := by
  have hmem : σ ∈ colSubgroup t := by rw [h]; exact Subgroup.mem_top σ
  rw [← polytabloid_relabel σ t, polytabloid_relabel_of_mem_colSubgroup hmem]

end YoungTableau

open YoungTableau

variable {μ : YoungDiagram}

/-! ## A Specht module whose generating polytabloid is a group eigenvector

Both extreme shapes are instances of one situation: the polytabloid `e_t` is an eigenvector of
every group element, with eigenvalue `χ σ`.  Then the orbit of `e_t` spans the line through it, so
that line is the whole Specht module and the group acts on it through `χ`. -/

variable {χ : Equiv.Perm (Fin μ.card) → ℚ}

/-- If the group scales the polytabloid of `t`, the Specht module is the line through it: the
Specht module is the span of that orbit. -/
private theorem spechtSubrepresentation_toSubmodule_eq_span (t : YoungTableau μ)
    (h : ∀ σ, (permutationModule (shapePartition μ)).ρ σ (polytabloid t) = χ σ • polytabloid t) :
    (spechtSubrepresentation μ).toSubmodule = ℚ ∙ polytabloid t := by
  rw [spechtSubrepresentation_eq_span_orbit t]
  refine le_antisymm (Submodule.span_le.mpr (Set.range_subset_iff.mpr fun σ => ?_)) ?_
  · exact SetLike.mem_coe.mpr (Submodule.mem_span_singleton.mpr ⟨χ σ, (h σ).symm⟩)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.subset_span ⟨1, by simp⟩

/-- A Specht module generated by a group eigenvector is a line. -/
private theorem finrank_spechtSubrepresentation_eq_one (t : YoungTableau μ)
    (h : ∀ σ, (permutationModule (shapePartition μ)).ρ σ (polytabloid t) = χ σ • polytabloid t) :
    finrank ℚ (spechtSubrepresentation μ).toSubmodule = 1 := by
  rw [spechtSubrepresentation_toSubmodule_eq_span t h]
  exact finrank_span_singleton (polytabloid_ne_zero t)

/-- A Specht module generated by a group eigenvector carries the action by that eigenvalue. -/
private theorem spechtSubrepresentation_toRepresentation_apply (t : YoungTableau μ)
    (h : ∀ σ, (permutationModule (shapePartition μ)).ρ σ (polytabloid t) = χ σ • polytabloid t)
    (σ : Equiv.Perm (Fin μ.card)) (x : (spechtSubrepresentation μ).toSubmodule) :
    (spechtSubrepresentation μ).toRepresentation σ x = χ σ • x := by
  have hx : (x : (permutationModule (shapePartition μ)).V) ∈ ℚ ∙ polytabloid t := by
    rw [← spechtSubrepresentation_toSubmodule_eq_span t h]
    exact x.2
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  refine Subtype.ext ?_
  rw [Subrepresentation.toRepresentation_apply, LinearMap.coe_restrict_apply, Submodule.coe_smul,
    ← hc, map_smul, h σ, smul_comm]

/-! ## The one-row shape gives the trivial representation -/

/-- The Specht module of a shape with at most one row is the line through any of its
polytabloids. -/
theorem spechtSubrepresentation_toSubmodule_eq_span_of_rowSubgroup_eq_top (t : YoungTableau μ)
    (h : rowSubgroup t = ⊤) :
    (spechtSubrepresentation μ).toSubmodule = ℚ ∙ polytabloid t :=
  spechtSubrepresentation_toSubmodule_eq_span (χ := fun _ => 1) t fun σ => by
    rw [one_smul, permutationModule_ρ_polytabloid_of_rowSubgroup_eq_top t h]

/-- The Specht module of a shape with at most one row is a line. -/
theorem finrank_spechtSubrepresentation_of_colLen_le_one (h : μ.colLen 0 ≤ 1) :
    finrank ℚ (spechtSubrepresentation μ).toSubmodule = 1 := by
  obtain ⟨t⟩ := YoungTableau.nonempty μ
  exact finrank_spechtSubrepresentation_eq_one (χ := fun _ => 1) t fun σ => by
    rw [one_smul,
      permutationModule_ρ_polytabloid_of_rowSubgroup_eq_top t ((rowSubgroup_eq_top_iff t).mpr h)]

/-- The symmetric group fixes the Specht module of a shape with at most one row pointwise. -/
theorem spechtSubrepresentation_toRepresentation_apply_of_colLen_le_one (h : μ.colLen 0 ≤ 1)
    (σ : Equiv.Perm (Fin μ.card)) (x : (spechtSubrepresentation μ).toSubmodule) :
    (spechtSubrepresentation μ).toRepresentation σ x = x := by
  obtain ⟨t⟩ := YoungTableau.nonempty μ
  refine (spechtSubrepresentation_toRepresentation_apply (χ := fun _ => 1) t (fun σ => ?_) σ
    x).trans (one_smul ℚ x)
  rw [one_smul,
    permutationModule_ρ_polytabloid_of_rowSubgroup_eq_top t ((rowSubgroup_eq_top_iff t).mpr h)]

/-- **`S^{(n)}` is the trivial representation**: on a shape with at most one row the symmetric
group acts trivially on the span of the polytabloids.  Together with
`TauCeti.finrank_spechtSubrepresentation_of_colLen_le_one` this identifies it as the
one-dimensional trivial representation. -/
theorem spechtSubrepresentation_toRepresentation_eq_trivial (h : μ.colLen 0 ≤ 1) :
    (spechtSubrepresentation μ).toRepresentation =
      Representation.trivial ℚ (Equiv.Perm (Fin μ.card))
        (spechtSubrepresentation μ).toSubmodule := by
  refine DFunLike.ext _ _ fun σ => LinearMap.ext fun x => ?_
  rw [spechtSubrepresentation_toRepresentation_apply_of_colLen_le_one h,
    Representation.trivial_apply]

/-! ## The one-column shape gives the sign representation -/

/-- The Specht module of a shape with at most one column is the line through any of its
polytabloids. -/
theorem spechtSubrepresentation_toSubmodule_eq_span_of_colSubgroup_eq_top (t : YoungTableau μ)
    (h : colSubgroup t = ⊤) :
    (spechtSubrepresentation μ).toSubmodule = ℚ ∙ polytabloid t :=
  spechtSubrepresentation_toSubmodule_eq_span
    (χ := fun σ => ((Equiv.Perm.sign σ : ℤ) : ℚ)) t
    (permutationModule_ρ_polytabloid_of_colSubgroup_eq_top t h)

/-- The Specht module of a shape with at most one column is a line. -/
theorem finrank_spechtSubrepresentation_of_rowLen_le_one (h : μ.rowLen 0 ≤ 1) :
    finrank ℚ (spechtSubrepresentation μ).toSubmodule = 1 := by
  obtain ⟨t⟩ := YoungTableau.nonempty μ
  exact finrank_spechtSubrepresentation_eq_one
    (χ := fun σ => ((Equiv.Perm.sign σ : ℤ) : ℚ)) t
    (permutationModule_ρ_polytabloid_of_colSubgroup_eq_top t ((colSubgroup_eq_top_iff t).mpr h))

/-- **`S^{(1ⁿ)}` is the sign representation**: on a shape with at most one column the symmetric
group acts on the span of the polytabloids through the sign character.  Together with
`TauCeti.finrank_spechtSubrepresentation_of_rowLen_le_one` this identifies it as the
one-dimensional sign representation. -/
theorem spechtSubrepresentation_toRepresentation_apply_of_rowLen_le_one (h : μ.rowLen 0 ≤ 1)
    (σ : Equiv.Perm (Fin μ.card)) (x : (spechtSubrepresentation μ).toSubmodule) :
    (spechtSubrepresentation μ).toRepresentation σ x = ((Equiv.Perm.sign σ : ℤ) : ℚ) • x := by
  obtain ⟨t⟩ := YoungTableau.nonempty μ
  exact spechtSubrepresentation_toRepresentation_apply
    (χ := fun σ => ((Equiv.Perm.sign σ : ℤ) : ℚ)) t
    (permutationModule_ρ_polytabloid_of_colSubgroup_eq_top t ((colSubgroup_eq_top_iff t).mpr h))
    σ x

/-! ## The partition-indexed Specht modules of the two extreme partitions -/

/-- **`S^{(n)}` is a line.** -/
@[simp]
theorem finrank_spechtModule_indiscrete (n : ℕ) :
    finrank ℚ (spechtModule (Nat.Partition.indiscrete n)) = 1 :=
  finrank_spechtSubrepresentation_of_colLen_le_one (colLen_diagramOf_indiscrete_le_one n)

/-- **`S^{(n)}` is the trivial representation**: the symmetric group fixes it pointwise.

This is not a `simp` lemma: `TauCeti.spechtModule` is an `abbrev` for an `FDRep.of`, so
`FDRep.of_ρ'` already rewrites its left-hand side to the action of
`TauCeti.spechtSubrepresentation` along the relabelling. -/
theorem spechtModule_indiscrete_ρ_apply (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : spechtModule (Nat.Partition.indiscrete n)) :
    (spechtModule (Nat.Partition.indiscrete n)).ρ σ x = x :=
  spechtSubrepresentation_toRepresentation_apply_of_colLen_le_one
    (colLen_diagramOf_indiscrete_le_one n) _ x

/-- **`S^{(n)}` is the trivial representation**, in the extensional form its character is read
off. -/
theorem spechtModule_indiscrete_ρ_eq_trivial (n : ℕ) :
    (spechtModule (Nat.Partition.indiscrete n)).ρ =
      Representation.trivial ℚ (Equiv.Perm (Fin n))
        (spechtModule (Nat.Partition.indiscrete n)) :=
  DFunLike.ext _ _ fun σ => LinearMap.ext fun x => by
    rw [spechtModule_indiscrete_ρ_apply, Representation.trivial_apply]

/-- **`S^{(1ⁿ)}` is a line.** -/
@[simp]
theorem finrank_spechtModule_ones (n : ℕ) :
    finrank ℚ (spechtModule (Nat.Partition.ones n)) = 1 :=
  finrank_spechtSubrepresentation_of_rowLen_le_one (rowLen_diagramOf_ones_le_one n 0)

/-- **`S^{(1ⁿ)}` is the sign representation**: the symmetric group acts on it through the sign
character.  The sign is unchanged by the relabelling `Fin n ≃ Fin (diagramOf (1ⁿ)).card` that
`TauCeti.spechtModule` transports along.

This is not a `simp` lemma, for the reason given at
`TauCeti.spechtModule_indiscrete_ρ_apply`. -/
theorem spechtModule_ones_ρ_apply (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : spechtModule (Nat.Partition.ones n)) :
    (spechtModule (Nat.Partition.ones n)).ρ σ x = ((Equiv.Perm.sign σ : ℤ) : ℚ) • x := by
  have h := spechtSubrepresentation_toRepresentation_apply_of_rowLen_le_one
    (rowLen_diagramOf_ones_le_one n 0)
    ((finCongr (card_diagramOf (Nat.Partition.ones n)).symm).permCongrHom σ) x
  rwa [Equiv.permCongrHom_coe, Equiv.Perm.sign_permCongr] at h

/-! ## The two extreme rows of the character table of `Sₙ` -/

/-- **`χ^{(n)} = 1`**: the character of the trivial representation, whose value is the dimension of
its carrier. -/
@[simp]
theorem spechtChar_indiscrete (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    spechtChar (Nat.Partition.indiscrete n) σ = 1 := by
  have hcast : ((spechtChar (Nat.Partition.indiscrete n) σ : ℤ) : ℚ) = ((1 : ℤ) : ℚ) := by
    rw [spechtChar_cast, FDRep.character, spechtModule_indiscrete_ρ_eq_trivial]
    exact (Representation.char_trivial σ).trans (by
      rw [finrank_spechtModule_indiscrete]; norm_num)
  exact_mod_cast hcast

/-- **`χ^{(1ⁿ)} = sgn`**: the character of the sign representation. -/
@[simp]
theorem spechtChar_ones (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    spechtChar (Nat.Partition.ones n) σ = (Equiv.Perm.sign σ : ℤ) := by
  have hrho : ((spechtModule (Nat.Partition.ones n)).ρ σ :
      spechtModule (Nat.Partition.ones n) →ₗ[ℚ] spechtModule (Nat.Partition.ones n)) =
      ((Equiv.Perm.sign σ : ℤ) : ℚ) • LinearMap.id :=
    LinearMap.ext fun x => spechtModule_ones_ρ_apply n σ x
  have hcast : ((spechtChar (Nat.Partition.ones n) σ : ℤ) : ℚ) =
      (((Equiv.Perm.sign σ : ℤ) : ℤ) : ℚ) := by
    rw [spechtChar_cast, FDRep.character, hrho, map_smul, LinearMap.trace_id,
      finrank_spechtModule_ones]
    norm_num
  exact_mod_cast hcast

/-- **The `(n)` entry of the character table is `1` on every class**, the trivial character taking
that value everywhere. -/
@[simp]
theorem spechtCharValue_indiscrete (n : ℕ) (ν : n.Partition) :
    spechtCharValue (Nat.Partition.indiscrete n) ν = 1 := by
  obtain ⟨σ, hσ⟩ := ConjClasses.mk_surjective (partitionEquivConjClasses n ν)
  rw [spechtCharValue_eq_spechtChar _ _ hσ, spechtChar_indiscrete]

/-- **The `(1ⁿ)` entry of the character table is the sign of the class of cycle type `ν`**, read
off the number of parts of `ν` by `Equiv.Perm.sign_of_parts_partition`; the parts of
`Equiv.Perm.partition` include the fixed points, so the correction is the ambient `n`. -/
@[simp]
theorem spechtCharValue_ones (n : ℕ) (ν : n.Partition) :
    spechtCharValue (Nat.Partition.ones n) ν = (-1) ^ (n + Multiset.card ν.parts) := by
  obtain ⟨σ, hσ⟩ := ConjClasses.mk_surjective (partitionEquivConjClasses n ν)
  have hparts : Multiset.card σ.partition.parts = Multiset.card ν.parts := by
    have hcast : ∀ {m : ℕ} (e : n = m) (p : n.Partition),
        (Equiv.cast (congrArg Nat.Partition e) p).parts = p.parts := by
      rintro m rfl p
      rfl
    have hσpart : σ.partition =
        Equiv.cast (congrArg Nat.Partition (Fintype.card_fin n).symm) ν := by
      rw [← permConjClassPartition_mk, hσ, permConjClassPartition_partitionEquivConjClasses]
    rw [hσpart]
    exact congrArg Multiset.card (hcast (Fintype.card_fin n).symm ν)
  rw [spechtCharValue_eq_spechtChar _ _ hσ, spechtChar_ones,
    Equiv.Perm.sign_of_parts_partition, hparts, Fintype.card_fin]
  simp

/-- **The row of `(n)` in the character table of `Sₙ` is the all-ones row**, the trivial character
taking the value `1` on every conjugacy class.

This is not a `simp` lemma: `TauCeti.symmetricCharacterTable_apply` already rewrites its left-hand
side to `TauCeti.spechtCharValue`, where `TauCeti.spechtCharValue_indiscrete` finishes the
reduction. -/
theorem symmetricCharacterTable_indiscrete (n : ℕ) (ν : n.Partition) :
    symmetricCharacterTable n (Nat.Partition.indiscrete n) ν = 1 := by
  rw [symmetricCharacterTable_apply, spechtCharValue_indiscrete]

/-- **The row of `(1ⁿ)` in the character table of `Sₙ` is the row of signs**, the sign character
evaluated on the class of cycle type `ν`.

This is not a `simp` lemma, for the reason given at
`TauCeti.symmetricCharacterTable_indiscrete`. -/
theorem symmetricCharacterTable_ones (n : ℕ) (ν : n.Partition) :
    symmetricCharacterTable n (Nat.Partition.ones n) ν = (-1) ^ (n + Multiset.card ν.parts) := by
  rw [symmetricCharacterTable_apply, spechtCharValue_ones]

end TauCeti
