/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Combinatorics.Young.Dominance
public import TauCeti.RepresentationTheory.Symmetric.PermutationModule.Basic
public import TauCeti.RepresentationTheory.Symmetric.Symmetrizer

/-!
# Dominance between the shape of a tableau and the shape of a tabloid

A `μ`-tabloid is a coset of the Young subgroup `youngSubgroup μ`, so it records a partition of the
labels into rows and nothing more.  This file compares such a tabloid with a tableau `t` of a
Young diagram `lam`, and proves **James's dominance lemma**: if the column antisymmetrizer `b_t`
does not annihilate the `μ`-tabloid `q` inside the Young permutation module `M^μ`, then the shape
of `t` dominates `μ` (`TauCeti.dominates_of_asAlgebraHom_columnAntisymmetrizer_ne_zero`).

The argument runs in three steps.  The tabloid `q = gH` has rows the fibers of
`youngBlock μ ∘ g⁻¹`, and its stabilizer is exactly the group of permutations preserving those
fibers (`TauCeti.stabilizer_mk_youngSubgroup`); counting the labels in the first `k` of those
rows recovers the partial sums of `μ` (`TauCeti.card_filter_youngBlock_lt`), which is what feeds
the counting core `TauCeti.YoungDiagram.card_filter_le_sum_take_rowLens` of
`TauCeti/Combinatorics/Young/Dominance.lean` and yields dominance from the row/column condition.
That condition is then supplied by the sign cancellation: if two labels sharing a column of `t`
lie in a common row of `q`, their transposition is an odd element of the column group fixing `q`,
and right translation by it flips every sign in `b_t · q` while permuting its terms, so
`b_t · q = 0`.

This is the shape-comparison half of the argument that the Specht modules are pairwise
non-isomorphic: a nonzero map `S^{lam} → M^μ` sends a polytabloid `b_t · {t}` to a combination of
the vectors `b_t · q`, so one of them survives.  Producing that map from an isomorphism of Specht
modules, which needs a complement to `S^{lam}` in `M^{lam}`, is a separate step and is not proved
here.

## Main results

* `TauCeti.stabilizer_mk_youngSubgroup`: the stabilizer of a tabloid is the subgroup preserving
  the fibers of the transported block map.
* `TauCeti.card_filter_youngBlock_lt`: the labels in the first `k` blocks of `μ` number the sum
  of the first `k` parts.
* `TauCeti.dominates_of_youngBlock_colIndex_injective`: dominance from the row/column condition.
* `TauCeti.dominates_of_forall_swap_smul_ne`: dominance from the absence of a column
  transposition fixing the tabloid.
* `TauCeti.asAlgebraHom_columnAntisymmetrizer_single_eq_zero` and
  `TauCeti.dominates_of_asAlgebraHom_columnAntisymmetrizer_ne_zero`: the sign cancellation, and
  James's dominance lemma itself.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Lemma 3.15.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 4, "Distinctness and completeness".
-/

public section

namespace TauCeti

open YoungTableau

/-- **The stabilizer of a tabloid.** A permutation fixes the coset `gH` of the Young subgroup of
`μ` exactly when it preserves every fiber of the block map transported by `g`, that is, when it
permutes the labels within the rows of the tabloid. -/
theorem stabilizer_mk_youngSubgroup {n : ℕ} (μ : n.Partition) (g : Equiv.Perm (Fin n)) :
    MulAction.stabilizer (Equiv.Perm (Fin n)) ((g : Equiv.Perm (Fin n) ⧸ youngSubgroup μ)) =
      fiberSubgroup fun x => youngBlock μ (g⁻¹ x) := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, mem_fiberSubgroup,
    show σ • (g : Equiv.Perm (Fin n) ⧸ youngSubgroup μ) = ((σ * g : Equiv.Perm (Fin n)) : _) from
      rfl,
    QuotientGroup.eq, ← Subgroup.inv_mem_iff, mem_youngSubgroup_iff]
  constructor
  · intro hσ x
    simpa using congrFun hσ (g⁻¹ x)
  · intro hσ
    funext a
    simpa using hσ (g a)

/-- The labels whose `μ`-block is among the first `k` are as many as the first `k` parts of `μ`
add up to. -/
theorem card_filter_youngBlock_lt {n : ℕ} (μ : n.Partition) (k : ℕ) :
    (Finset.univ.filter fun x : Fin n => (youngBlock μ x : ℕ) < k).card =
      ((μ.parts.sort (· ≥ ·)).take k).sum := by
  classical
  -- Each block of `μ` is the fiber of `youngBlock μ` over its label, and has the size of a part.
  have hfiber : ∀ i : ℕ, (Finset.univ.filter fun x : Fin n => (youngBlock μ x : ℕ) = i).card =
      (μ.parts.sort (· ≥ ·)).getD i 0 := by
    intro i
    by_cases hi : i < (μ.parts.sort (· ≥ ·)).length
    · rw [List.getD_eq_getElem _ _ hi, ← Fintype.card_subtype]
      refine (Fintype.card_congr ((youngBlockEquiv μ ⟨i, hi⟩).trans
        (Equiv.subtypeEquivRight fun x => ?_))).symm.trans (Fintype.card_fin _)
      exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi), Finset.card_eq_zero,
        Finset.filter_eq_empty_iff]
      exact fun x _ h => hi (h ▸ (youngBlock μ x).2)
  -- Split the labels into blocks, and the partial sum into parts.
  have hsplit := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter fun x : Fin n => (youngBlock μ x : ℕ) < k)
    (f := fun x : Fin n => (youngBlock μ x : ℕ)) (t := Finset.range k) fun x hx => by
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simpa using hx
  rw [hsplit]
  have hsum : ((μ.parts.sort (· ≥ ·)).take k).sum =
      ∑ i ∈ Finset.range k, (μ.parts.sort (· ≥ ·)).getD i 0 := by
    rw [← rowLens_diagramOf μ, YoungDiagram.sum_take_rowLens_eq_card_filter_fst,
      ← YoungDiagram.sum_range_rowLen_eq_card_filter_fst]
    exact Finset.sum_congr rfl fun i _ => by rw [← YoungDiagram.getD_rowLens, rowLens_diagramOf]
  rw [hsum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← hfiber i]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
  exact fun h => h ▸ Finset.mem_range.mp hi

/-- **The dominance lemma for a tableau and a tabloid.** If the labels of each row of the
`μ`-tabloid `gH` occupy pairwise distinct columns of the `lam`-tableau `t`, then the shape of `t`
dominates `μ`. -/
theorem dominates_of_youngBlock_colIndex_injective {lam : YoungDiagram} (t : YoungTableau lam)
    (μ : lam.card.Partition) (g : Equiv.Perm (Fin lam.card))
    (h : ∀ x y, youngBlock μ (g⁻¹ x) = youngBlock μ (g⁻¹ y) → colIndex t x = colIndex t y →
      x = y) :
    Dominates (shapePartition lam) μ := by
  classical
  refine dominates_iff.mpr fun k => ?_
  rw [shapePartition_parts_sort, ← card_filter_youngBlock_lt μ k]
  -- Transport the count along `g`, then feed it to the counting core.
  have hcard : (Finset.univ.filter fun x : Fin lam.card => (youngBlock μ x : ℕ) < k).card =
      (Finset.univ.filter fun x : Fin lam.card => (youngBlock μ (g⁻¹ x) : ℕ) < k).card :=
    Finset.card_equiv (g : Equiv.Perm (Fin lam.card)) fun x => by
      simp [Equiv.Perm.inv_def]
  rw [hcard]
  refine YoungDiagram.card_filter_le_sum_take_rowLens lam (fun x => (youngBlock μ (g⁻¹ x) : ℕ))
    (fun x => ((t.symm x : ↥lam.cells) : ℕ × ℕ)) (fun x => (t.symm x).2)
    (fun x y hxy => t.symm.injective (Subtype.ext hxy)) (fun x y hr hc => ?_) k
  exact h x y (Fin.ext hr) (by simpa only [colIndex_def] using hc)

/-- **The dominance lemma in its group-theoretic form.** If no transposition of two labels lying
in a common column of the `lam`-tableau `t` fixes the `μ`-tabloid `q`, then the shape of `t`
dominates `μ`.

This is the form the Specht-module argument uses: such a transposition is an odd element of the
column group of `t` fixing `q`, and its presence is exactly what makes the column antisymmetrizer
of `t` annihilate `q`. -/
theorem dominates_of_forall_swap_smul_ne {lam : YoungDiagram} (t : YoungTableau lam)
    (μ : lam.card.Partition) (q : Equiv.Perm (Fin lam.card) ⧸ youngSubgroup μ)
    (h : ∀ x y : Fin lam.card, x ≠ y → colIndex t x = colIndex t y → Equiv.swap x y • q ≠ q) :
    Dominates (shapePartition lam) μ := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine dominates_of_youngBlock_colIndex_injective t μ g fun x y hr hc => ?_
  by_contra hxy
  refine h x y hxy hc ?_
  -- the transposition preserves the rows of the tabloid, hence lies in its stabilizer
  have hmem : Equiv.swap x y ∈
      MulAction.stabilizer (Equiv.Perm (Fin lam.card))
        ((g : Equiv.Perm (Fin lam.card) ⧸ youngSubgroup μ)) := by
    rw [stabilizer_mk_youngSubgroup]
    exact swap_mem_fiberSubgroup hr
  exact MulAction.mem_stabilizer_iff.mp hmem

/-! ## The column antisymmetrizer acting on a tabloid -/

/-- Classical decidability of membership in the column group, used to form its finite sum, as in
`TauCeti/RepresentationTheory/Symmetric/Symmetrizer.lean`. -/
noncomputable local instance {lam : YoungDiagram} (t : YoungTableau lam) :
    DecidablePred (· ∈ colSubgroup t) :=
  Classical.decPred _

/-- The column antisymmetrizer of a `lam`-tableau `t` sends a `μ`-tabloid to the signed sum of
its translates under the column group of `t`. -/
theorem asAlgebraHom_columnAntisymmetrizer_single {lam : YoungDiagram} (t : YoungTableau lam)
    (μ : lam.card.Partition) (q : Equiv.Perm (Fin lam.card) ⧸ youngSubgroup μ) :
    (permutationModule μ).ρ.asAlgebraHom (columnAntisymmetrizer t)
        (MonoidAlgebra.single q 1) =
      ∑ c : colSubgroup t,
        ((Equiv.Perm.sign (c : Equiv.Perm (Fin lam.card)) : ℤ) : ℚ) •
          MonoidAlgebra.single ((c : Equiv.Perm (Fin lam.card)) • q) (1 : ℚ) := by
  rw [columnAntisymmetrizer_def]
  simp [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single]

/-- **The column antisymmetrizer kills a tabloid fixed by an odd column permutation.**  Right
translation by such a permutation is a bijection of the column group that flips every sign while
leaving the translated tabloids unchanged, so the signed sum is its own negative. -/
theorem asAlgebraHom_columnAntisymmetrizer_single_eq_zero {lam : YoungDiagram}
    (t : YoungTableau lam) (μ : lam.card.Partition)
    (q : Equiv.Perm (Fin lam.card) ⧸ youngSubgroup μ) {p : Equiv.Perm (Fin lam.card)}
    (hp : p ∈ colSubgroup t) (hsign : Equiv.Perm.sign p = -1) (hfix : p • q = q) :
    (permutationModule μ).ρ.asAlgebraHom (columnAntisymmetrizer t)
      (MonoidAlgebra.single q 1) = 0 := by
  classical
  set F : colSubgroup t → (permutationModule μ).V := fun c =>
    ((Equiv.Perm.sign (c : Equiv.Perm (Fin lam.card)) : ℤ) : ℚ) •
      MonoidAlgebra.single ((c : Equiv.Perm (Fin lam.card)) • q) (1 : ℚ) with hF
  have hterm : ∀ c : colSubgroup t, F (c * ⟨p, hp⟩) = -F c := by
    intro c
    rw [hF]
    simp only [Subgroup.coe_mul, map_mul, hsign, mul_smul, hfix, mul_neg, mul_one, Units.val_neg,
      Int.cast_neg, neg_smul]
  have hreindex : (∑ c : colSubgroup t, F (c * ⟨p, hp⟩)) = ∑ c : colSubgroup t, F c :=
    Fintype.sum_equiv (Equiv.mulRight (⟨p, hp⟩ : colSubgroup t)) _ _ fun _ => rfl
  have hzero : (∑ c : colSubgroup t, F c) + ∑ c : colSubgroup t, F c = 0 := by
    nth_rewrite 1 [← hreindex]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun c _ => by rw [hterm c, neg_add_cancel]
  rw [asAlgebraHom_columnAntisymmetrizer_single t μ q, ← hF]
  refine (smul_eq_zero.mp (show (2 : ℚ) • (∑ c : colSubgroup t, F c) = 0 from ?_)).resolve_left
    two_ne_zero
  rw [two_smul]
  exact hzero

/-- **James's dominance lemma.**  If the column antisymmetrizer of a `lam`-tableau `t` does not
annihilate the `μ`-tabloid `q`, then the shape of `t` dominates `μ`.

This is the statement the classification of the Specht modules consumes: a homomorphism
`M^{lam} → M^μ` that does not kill the polytabloid `b_t · {t}` carries it to a combination of the
vectors `b_t · q`, so one of those is nonzero and the shape of `t` dominates `μ`. -/
theorem dominates_of_asAlgebraHom_columnAntisymmetrizer_ne_zero {lam : YoungDiagram}
    (t : YoungTableau lam) (μ : lam.card.Partition)
    (q : Equiv.Perm (Fin lam.card) ⧸ youngSubgroup μ)
    (h : (permutationModule μ).ρ.asAlgebraHom (columnAntisymmetrizer t)
      (MonoidAlgebra.single q 1) ≠ 0) :
    Dominates (shapePartition lam) μ :=
  dominates_of_forall_swap_smul_ne t μ q fun _ _ hxy hcol hfix =>
    h (asAlgebraHom_columnAntisymmetrizer_single_eq_zero t μ q (swap_mem_colSubgroup hcol)
      (Equiv.Perm.sign_swap hxy) hfix)

end TauCeti
