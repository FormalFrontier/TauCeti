/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.Partition.Conjugate
public import TauCeti.GroupTheory.QuotientGroup.Basic
public import TauCeti.RepresentationTheory.Symmetric.PermutationModule.Form
public import TauCeti.RepresentationTheory.Symmetric.Relabel
public import TauCeti.RepresentationTheory.Symmetric.TableauSubgroupConjugacy

/-!
# Polytabloids and the Specht module

The Young permutation module `M^μ` is the rational representation of `Sₙ` on the `μ`-tabloids,
which are the left cosets of the Young subgroup of the shape of `μ`.  A `μ`-tableau `t` names one
of them, its **tabloid** `{t}`, and antisymmetrizing that tabloid over the column group of `t`
produces the **polytabloid**

`e_t = b_t · {t} ∈ M^μ`.

The **Specht module** `S^μ` is the submodule of `M^μ` spanned by the polytabloids.  It is a
subrepresentation, because relabeling a tableau translates its polytabloid:
`e_{σt} = σ · e_t`.  Since the symmetric group acts transitively on tableaux, `S^μ` is in fact
the span of the orbit of a single polytabloid.

The conventions here are the ones the Schur-Weyl roadmap pins, and they have to be used
together: `M^μ` is a **left** module on the **left** cosets of the Young subgroup, the polytabloid
is the **column** antisymmetrization `b_t · {t}` of the tabloid, and the Young symmetrizer is
`c_t = a_t b_t`.  The opposite choices produce the dual Specht module.

The bridge between the two indexings is `rowYoungConjugator t`, the permutation carrying the
consecutive-block labeling of the shape of `μ` to the labeling of `t`: its coset is the tabloid of
`t`, and conjugation by it carries the Young subgroup onto the row group of `t`.  The tabloid of
`t` is therefore fixed exactly by the row group, which is what makes the polytabloid nonzero: the
column group meets the row group trivially, so the tabloids appearing in `e_t` are pairwise
distinct and the coefficient of `{t}` itself is `1`.

The identification of `S^μ` with the left ideal `ℚ[Sₙ] c_t` of
`TauCeti/RepresentationTheory/Symmetric/Specht/Ideal/Basic.lean` is a separate milestone and is not
proved here.  Neither is James's submodule theorem, which rests on the nonvanishing recorded below
and lives in `TauCeti/RepresentationTheory/Symmetric/Specht/SubmoduleTheorem.lean` together with
the irreducibility it yields.

## Main definitions

* `TauCeti.YoungTableau.tabloid`: the `μ`-tabloid of a tableau.
* `TauCeti.YoungTableau.polytabloid`: the polytabloid `e_t = b_t · {t}`.
* `TauCeti.spechtSubrepresentation`: the span of the polytabloids, as a subrepresentation of `M^μ`.
* `TauCeti.spechtModule`: the Specht module `S^μ` of a partition `μ` of `n`, that subrepresentation
  of the diagram of `μ` bundled as a finite-dimensional representation of `Sₙ`.

## Main results

* `TauCeti.YoungTableau.smul_tabloid_eq_self_iff`: the stabilizer of the tabloid of `t` is the row
  group of `t`.
* `TauCeti.YoungTableau.tabloid_eq_iff_rowIndex_eq`: two tableaux have the same tabloid exactly when
  they put every label in the same row.
* `TauCeti.YoungTableau.polytabloid_relabel`: relabeling translates the polytabloid.
* `TauCeti.YoungTableau.polytabloid_coeff_eq_zero_of_forall_ne`: only the tabloids reachable from
  `{t}` by a column permutation occur in `e_t`.
* `TauCeti.YoungTableau.polytabloid_ne_zero` and
  `TauCeti.YoungTableau.tabloidForm_polytabloid_self`: polytabloids are nonzero, and the tabloid
  form pairs one with itself to the order of the column group.
* `TauCeti.spechtSubrepresentation_eq_span_orbit` and `TauCeti.spechtSubrepresentation_ne_bot`: the
  Specht module is the span of the orbit of a single polytabloid, and it is nonzero.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapters 3 and 4.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 3, "Polytabloids and the Specht module".
-/

public section

namespace TauCeti

open scoped BigOperators

namespace YoungTableau

variable {μ : YoungDiagram}

/-! ## The tabloid of a tableau -/

/-- The **tabloid** `{t}` of a `μ`-tableau `t`: the row-equivalence class of `t`, presented as the
coset of the Young subgroup of the shape of `μ` given by `rowYoungConjugator t`. -/
noncomputable def tabloid (t : YoungTableau μ) :
    Equiv.Perm (Fin μ.card) ⧸ youngSubgroup (shapePartition μ) :=
  QuotientGroup.mk (rowYoungConjugator t)

theorem tabloid_def (t : YoungTableau μ) :
    tabloid t = QuotientGroup.mk (rowYoungConjugator t) :=
  (rfl)

/-- Relabeling a tableau translates its tabloid. -/
@[simp]
theorem tabloid_relabel (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) :
    tabloid (relabel σ t) = σ • tabloid t := by
  rw [tabloid_def, tabloid_def, rowYoungConjugator_relabel, MulAction.Quotient.smul_coe,
    smul_eq_mul]

/-- Every `μ`-tabloid is the tabloid of a tableau. -/
theorem tabloid_surjective : Function.Surjective (tabloid (μ := μ)) := by
  obtain ⟨t⟩ := YoungTableau.nonempty μ
  intro q
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨relabel (σ * (rowYoungConjugator t)⁻¹) t, ?_⟩
  rw [tabloid_def, rowYoungConjugator_relabel, inv_mul_cancel_right]

/-- **The stabilizer of a tabloid is the row group.** A permutation fixes the tabloid of `t`
exactly when it preserves the rows of `t`. -/
@[simp]
theorem smul_tabloid_eq_self_iff {t : YoungTableau μ} {σ : Equiv.Perm (Fin μ.card)} :
    σ • tabloid t = tabloid t ↔ σ ∈ rowSubgroup t := by
  -- the stabilizer of a coset is the conjugate subgroup, and that conjugate is the row group
  have h : MulAction.stabilizer (Equiv.Perm (Fin μ.card)) (tabloid t) = rowSubgroup t := by
    rw [tabloid_def, stabilizer_quotientGroup_mk]
    exact youngSubgroup_map_conj_eq_rowSubgroup t
  rw [← h, MulAction.mem_stabilizer_iff]

/-- Two permutations send the tabloid of `t` to the same tabloid exactly when they differ by an
element of the row group of `t`. -/
@[simp]
theorem smul_tabloid_eq_iff {t : YoungTableau μ} {σ τ : Equiv.Perm (Fin μ.card)} :
    σ • tabloid t = τ • tabloid t ↔ σ⁻¹ * τ ∈ rowSubgroup t := by
  rw [← smul_tabloid_eq_self_iff, mul_smul, inv_smul_eq_iff, eq_comm]

/-- **Two tableaux have the same tabloid exactly when they put every label in the same row.** -/
@[simp]
theorem tabloid_eq_iff_rowIndex_eq {t u : YoungTableau μ} :
    tabloid t = tabloid u ↔ rowIndex t = rowIndex u := by
  obtain ⟨σ, rfl⟩ := exists_relabel_eq t u
  rw [tabloid_relabel, eq_comm, smul_tabloid_eq_self_iff, mem_rowSubgroup]
  constructor
  · intro hσ
    funext k
    simpa using hσ (σ⁻¹ k)
  · intro hσ k
    have hk := congrFun hσ (σ k)
    rw [rowIndex_relabel] at hk
    simpa using hk

/-- Distinct elements of the column group of `t` move the tabloid of `t` to distinct tabloids: the
column group meets the row group, which is the stabilizer, only in the identity. -/
theorem smul_tabloid_injective (t : YoungTableau μ) :
    Function.Injective fun q : colSubgroup t => (q : Equiv.Perm (Fin μ.card)) • tabloid t := by
  intro q r h
  have hrow : (q : Equiv.Perm (Fin μ.card))⁻¹ * r ∈ rowSubgroup t := smul_tabloid_eq_iff.mp h
  have hcol : (q : Equiv.Perm (Fin μ.card))⁻¹ * r ∈ colSubgroup t :=
    mul_mem (inv_mem q.2) r.2
  have hmem : (q : Equiv.Perm (Fin μ.card))⁻¹ * r ∈ rowSubgroup t ⊓ colSubgroup t :=
    Subgroup.mem_inf.mpr ⟨hrow, hcol⟩
  rw [rowSubgroup_inf_colSubgroup_eq_bot t, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact Subtype.ext hmem

/-! ## Polytabloids -/

/-- Classical decidability of membership in the column group, used to form its finite sum, as in
`TauCeti/RepresentationTheory/Symmetric/Symmetrizer.lean`. -/
noncomputable local instance (t : YoungTableau μ) : DecidablePred (· ∈ colSubgroup t) :=
  Classical.decPred _

/-- The **polytabloid** `e_t = b_t · {t}`: the column antisymmetrizer of `t` acting on the tabloid
of `t` inside the Young permutation module of the shape of `μ`. -/
noncomputable def polytabloid (t : YoungTableau μ) :
    (permutationModule (shapePartition μ)).V :=
  (permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t)
    (MonoidAlgebra.single (tabloid t) 1)

/-- The polytabloid is the column antisymmetrizer applied to the tabloid. -/
theorem polytabloid_def (t : YoungTableau μ) :
    polytabloid t =
      (permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t)
        (MonoidAlgebra.single (tabloid t) 1) :=
  (rfl)

/-- The polytabloid is the signed sum of the tabloids obtained from `{t}` by the column group. -/
theorem polytabloid_eq_sum (t : YoungTableau μ) :
    polytabloid t =
      ∑ q : colSubgroup t,
        ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
          MonoidAlgebra.single ((q : Equiv.Perm (Fin μ.card)) • tabloid t) (1 : ℚ) := by
  rw [polytabloid, columnAntisymmetrizer_def]
  simp [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single]

/-- Relabeling a tableau translates its polytabloid: `e_{σt} = σ · e_t`. -/
@[simp]
theorem polytabloid_relabel (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) :
    polytabloid (relabel σ t) =
      (permutationModule (shapePartition μ)).ρ σ (polytabloid t) := by
  rw [polytabloid, polytabloid, columnAntisymmetrizer_relabel, map_mul, map_mul,
    Representation.asAlgebraHom_single_one, Representation.asAlgebraHom_single_one,
    tabloid_relabel]
  simp only [Module.End.mul_apply, Representation.ofMulAction_single, smul_smul,
    inv_mul_cancel, one_smul]

/-- The coefficient, in the polytabloid `e_t`, of the tabloid obtained from `{t}` by a column
permutation `q` of `t` is the sign of `q`. -/
@[simp]
theorem polytabloid_coeff_smul_tabloid (t : YoungTableau μ) (q : colSubgroup t) :
    (polytabloid t).coeff ((q : Equiv.Perm (Fin μ.card)) • tabloid t) =
      ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) := by
  classical
  rw [polytabloid_eq_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    Finset.sum_eq_single q]
  · simp [MonoidAlgebra.coeff_single]
  · intro r _ hr
    have hne : (r : Equiv.Perm (Fin μ.card)) • tabloid t ≠
        (q : Equiv.Perm (Fin μ.card)) • tabloid t := fun h =>
      hr (smul_tabloid_injective t h)
    simp [MonoidAlgebra.coeff_single, hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The coefficient of the tabloid `{t}` in the polytabloid `e_t` is `1`; in particular `e_t` is a
nonzero element of `M^μ`. -/
@[simp]
theorem polytabloid_coeff_tabloid (t : YoungTableau μ) :
    (polytabloid t).coeff (tabloid t) = 1 := by
  have h := polytabloid_coeff_smul_tabloid t 1
  simpa using h

/-- Only the tabloids reachable from `{t}` by a column permutation occur in the polytabloid
`e_t`. -/
theorem polytabloid_coeff_eq_zero_of_forall_ne (t : YoungTableau μ)
    {X : Equiv.Perm (Fin μ.card) ⧸ youngSubgroup (shapePartition μ)}
    (h : ∀ q ∈ colSubgroup t, q • tabloid t ≠ X) : (polytabloid t).coeff X = 0 := by
  classical
  rw [polytabloid_eq_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun q _ => ?_
  have hne := h (q : Equiv.Perm (Fin μ.card)) q.2
  simp [MonoidAlgebra.coeff_single, hne]

/-- Polytabloids are nonzero. -/
@[simp]
theorem polytabloid_ne_zero (t : YoungTableau μ) : polytabloid t ≠ 0 := by
  intro h
  have := polytabloid_coeff_tabloid t
  rw [h] at this
  simp at this

/-- **The tabloid form evaluates a polytabloid against itself to the order of the column group.**
This nonvanishing is the input that James's submodule theorem converts into irreducibility of the
Specht module. -/
theorem tabloidForm_polytabloid_self (t : YoungTableau μ) :
    tabloidForm (shapePartition μ) (polytabloid t) (polytabloid t) =
      (Nat.card (colSubgroup t) : ℚ) := by
  classical
  nth_rewrite 1 [polytabloid_eq_sum]
  rw [map_sum, LinearMap.sum_apply]
  have hterm : ∀ q : colSubgroup t,
      tabloidForm (shapePartition μ)
          (((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
            MonoidAlgebra.single ((q : Equiv.Perm (Fin μ.card)) • tabloid t) (1 : ℚ))
          (polytabloid t) = 1 := by
    intro q
    rw [map_smul, LinearMap.smul_apply, tabloidForm, permutationForm_single_left,
      polytabloid_coeff_smul_tabloid]
    rw [smul_eq_mul, one_mul, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  rw [Finset.sum_congr rfl fun q _ => hterm q, Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card, nsmul_eq_mul, mul_one]

end YoungTableau

/-! ## The Specht module -/

open YoungTableau

/-- The **Specht module** `S^μ`, in its concrete presentation: the subrepresentation of the Young
permutation module `M^μ` spanned by the polytabloids of the `μ`-tableaux.

It is stable under the symmetric group because relabeling a tableau translates its polytabloid,
and the polytabloids of the relabelings of a fixed tableau are all of them. -/
noncomputable def spechtSubrepresentation (μ : YoungDiagram) :
    Subrepresentation (permutationModule (shapePartition μ)).ρ where
  toSubmodule := Submodule.span ℚ (Set.range (polytabloid (μ := μ)))
  apply_mem_toSubmodule σ _ hv := by
    -- stability of a span is checked on its generators
    have h : Submodule.span ℚ (Set.range (polytabloid (μ := μ))) ≤
        (Submodule.span ℚ (Set.range (polytabloid (μ := μ)))).comap
          ((permutationModule (shapePartition μ)).ρ σ) := by
      rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      exact Submodule.subset_span ⟨relabel σ t, polytabloid_relabel σ t⟩
    exact h hv

/-- The underlying submodule of the Specht module is the span of the polytabloids. -/
@[simp]
theorem spechtSubrepresentation_toSubmodule (μ : YoungDiagram) :
    (spechtSubrepresentation μ).toSubmodule =
      Submodule.span ℚ (Set.range (polytabloid (μ := μ))) :=
  (rfl)

/-- Every polytabloid lies in the Specht module. -/
theorem polytabloid_mem_spechtSubrepresentation (t : YoungTableau μ) :
    polytabloid t ∈ spechtSubrepresentation μ :=
  Submodule.subset_span ⟨t, rfl⟩

/-- **The Specht module is cyclic.** It is the span of the orbit of a single polytabloid, because
the symmetric group permutes the `μ`-tableaux transitively. -/
theorem spechtSubrepresentation_eq_span_orbit (t : YoungTableau μ) :
    (spechtSubrepresentation μ).toSubmodule =
      Submodule.span ℚ
        (Set.range fun σ : Equiv.Perm (Fin μ.card) =>
          (permutationModule (shapePartition μ)).ρ σ (polytabloid t)) := by
  rw [spechtSubrepresentation_toSubmodule]
  congr 1
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨t', rfl⟩
    obtain ⟨σ, rfl⟩ := exists_relabel_eq t t'
    exact ⟨σ, (polytabloid_relabel σ t).symm⟩
  · rintro _ ⟨σ, rfl⟩
    exact ⟨relabel σ t, polytabloid_relabel σ t⟩

/-- The Specht module is nonzero. -/
@[simp]
theorem spechtSubrepresentation_ne_bot (μ : YoungDiagram) : spechtSubrepresentation μ ≠ ⊥ := by
  obtain ⟨t⟩ := YoungTableau.nonempty μ
  intro h
  have hmem : polytabloid t ∈ (⊥ : Subrepresentation (permutationModule (shapePartition μ)).ρ) :=
    h ▸ polytabloid_mem_spechtSubrepresentation t
  exact polytabloid_ne_zero t (Submodule.mem_bot ℚ |>.mp hmem)

/-- The Specht module is finite-dimensional, being a submodule of the finite-dimensional Young
permutation module.  This is what lets it be bundled as an `FDRep`. -/
instance (μ : YoungDiagram) :
    FiniteDimensional ℚ (spechtSubrepresentation μ).toSubmodule :=
  FiniteDimensional.finiteDimensional_submodule _

/-- The **Specht module** `S^μ` of a partition `μ` of `n`, bundled as a finite-dimensional
representation of `Sₙ`: the span of the polytabloids of the tableaux of the Young diagram
`diagramOf μ`, with the symmetric group on the `(diagramOf μ).card` entries of such a tableau
identified with `Sₙ` along `card_diagramOf`.

The tabloid combinatorics is indexed by a diagram, since a tableau is a filling of one, while the
classification the Specht modules feed is indexed by partitions; this is the partition-indexed
name.  Its representation unfolds to `spechtSubrepresentation (diagramOf μ)` by `FDRep.of_ρ'`, and
`spechtSubrepresentation_toSubmodule` identifies the underlying module with the span of the
polytabloids. -/
noncomputable abbrev spechtModule {n : ℕ} (μ : n.Partition) :
    FDRep ℚ (Equiv.Perm (Fin n)) :=
  FDRep.of ((spechtSubrepresentation (diagramOf μ)).toRepresentation.comp
    (finCongr (card_diagramOf μ).symm).permCongrHom.toMonoidHom)

/-- The Specht module is nontrivial, so it has positive dimension. -/
theorem finrank_spechtModule_pos {n : ℕ} (μ : n.Partition) :
    0 < Module.finrank ℚ (spechtModule μ) :=
  have : Nontrivial (spechtSubrepresentation (diagramOf μ)).toSubmodule :=
    Submodule.nontrivial_iff_ne_bot.mpr fun h =>
      spechtSubrepresentation_ne_bot _ (Subrepresentation.toSubmodule_injective h)
  Module.finrank_pos

end TauCeti
