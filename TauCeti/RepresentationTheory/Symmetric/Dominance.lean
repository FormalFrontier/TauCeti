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
fibers (`TauCeti.stabilizer_quotientGroup_mk_youngSubgroup`); counting the labels in the first `k`
of those rows recovers the partial sums of `μ` (`TauCeti.card_filter_youngBlock_lt`), which is
what feeds the counting core `YoungDiagram.card_filter_le_sum_take_rowLens` of
`TauCeti/Combinatorics/Young/Dominance.lean` and yields dominance from the row/column condition.
That condition is then supplied by the sign cancellation: if two labels sharing a column of `t`
lie in a common row of `q`, their transposition is an odd element of the column group fixing `q`,
which `b_t` absorbs at the cost of its sign while leaving `q` alone, so `b_t · q = 0`.

This is the shape-comparison half of the argument that the Specht modules are pairwise
non-isomorphic: a nonzero map `S^{lam} → M^μ` sends a polytabloid `b_t · {t}` to a combination of
the vectors `b_t · q`, so one of them survives.  Producing that map from an isomorphism of Specht
modules, which needs a complement to `S^{lam}` in `M^{lam}`, is a separate step and is not proved
here.

## Main results

* `TauCeti.dominates_of_youngBlock_colIndex_injective`: dominance from the row/column condition.
* `TauCeti.dominates_of_forall_swap_smul_ne`: dominance from the absence of a column
  transposition fixing the tabloid.
* `TauCeti.asAlgebraHom_columnAntisymmetrizer_single_eq_zero` and
  `TauCeti.dominates_of_asAlgebraHom_columnAntisymmetrizer_ne_zero`: the sign cancellation, and
  James's dominance lemma itself.
* `TauCeti.YoungTableau.asAlgebraHom_columnAntisymmetrizer_apply_eq_zero_of_not_dominates` and
  `TauCeti.YoungTableau.dominates_of_asAlgebraHom_columnAntisymmetrizer_apply_ne_zero`: the same
  lemma for an arbitrary vector of `M^μ` rather than a tabloid.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Lemma 3.15.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 4, "Distinctness and completeness".
-/

public section

namespace TauCeti

open YoungTableau

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
    rw [stabilizer_quotientGroup_mk_youngSubgroup]
    exact swap_mem_fiberSubgroup hr
  exact MulAction.mem_stabilizer_iff.mp hmem

/-! ## The column antisymmetrizer acting on a tabloid -/

/-- **The column antisymmetrizer kills a tabloid fixed by an odd column permutation.**  The
antisymmetrizer absorbs such a permutation up to its sign, which is `-1`, while the tabloid is
left alone, so the value is its own negative. -/
theorem asAlgebraHom_columnAntisymmetrizer_single_eq_zero {lam : YoungDiagram}
    (t : YoungTableau lam) (μ : lam.card.Partition)
    (q : Equiv.Perm (Fin lam.card) ⧸ youngSubgroup μ) {p : Equiv.Perm (Fin lam.card)}
    (hp : p ∈ colSubgroup t) (hsign : Equiv.Perm.sign p = -1) (hfix : p • q = q) :
    (permutationModule μ).ρ.asAlgebraHom (columnAntisymmetrizer t)
      (MonoidAlgebra.single q 1) = 0 := by
  have hfix' : (permutationModule μ).ρ p (MonoidAlgebra.single q (1 : ℚ)) =
      MonoidAlgebra.single q 1 := by
    rw [Representation.ofMulAction_single, hfix]
  have hneg : columnAntisymmetrizer t * MonoidAlgebra.single p (1 : ℚ) =
      -columnAntisymmetrizer t := by
    rw [mul_columnAntisymmetrizer_right t ⟨p, hp⟩, hsign]
    simp
  have key : (permutationModule μ).ρ.asAlgebraHom (columnAntisymmetrizer t)
        (MonoidAlgebra.single q 1) =
      -((permutationModule μ).ρ.asAlgebraHom (columnAntisymmetrizer t)
        (MonoidAlgebra.single q 1)) := by
    conv_lhs => rw [← hfix']
    rw [← Representation.asAlgebraHom_single_one (permutationModule μ).ρ,
      ← Module.End.mul_apply, ← map_mul, hneg, map_neg, LinearMap.neg_apply]
  have h2 : (2 : ℚ) • (permutationModule μ).ρ.asAlgebraHom (columnAntisymmetrizer t)
      (MonoidAlgebra.single q 1) = 0 := by
    rw [two_smul]
    nth_rewrite 2 [key]
    exact add_neg_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

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

namespace YoungTableau

/-- **The column antisymmetrizer of a non-dominating shape annihilates the whole permutation
module.**  James's dominance lemma says that `b_t` kills every `μ`-tabloid once the shape of `t`
fails to dominate `μ`; the tabloids span `M^μ`, so `b_t` kills all of it.

This is to `TauCeti.dominates_of_asAlgebraHom_columnAntisymmetrizer_ne_zero` what
`TauCeti.YoungTableau.exists_eq_smul_polytabloid` is to
`TauCeti.YoungTableau.exists_eq_smul_polytabloid_single`: the same statement, extended off the
tabloid basis by linearity. -/
theorem asAlgebraHom_columnAntisymmetrizer_apply_eq_zero_of_not_dominates {lam : YoungDiagram}
    (t : YoungTableau lam) (μ : lam.card.Partition) (h : ¬Dominates (shapePartition lam) μ)
    (x : (permutationModule μ).V) :
    (permutationModule μ).ρ.asAlgebraHom (columnAntisymmetrizer t) x = 0 := by
  have hx : x ∈ Submodule.span ℚ (Set.range (permutationModuleBasis μ)) := by
    rw [Module.Basis.span_eq]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨q, rfl⟩ := hw
    rw [MonoidAlgebra.basis_apply]
    by_contra hne
    exact h (dominates_of_asAlgebraHom_columnAntisymmetrizer_ne_zero t μ q hne)
  | zero => rw [map_zero]
  | add u v _ _ hu hv => rw [map_add, hu, hv, add_zero]
  | smul r u _ hu => rw [map_smul, hu, smul_zero]

/-- **James's dominance lemma for an arbitrary vector.**  If the column antisymmetrizer of a
`lam`-tableau does not annihilate some vector of `M^μ`, then the shape of `lam` dominates `μ`. -/
theorem dominates_of_asAlgebraHom_columnAntisymmetrizer_apply_ne_zero {lam : YoungDiagram}
    (t : YoungTableau lam) (μ : lam.card.Partition) {x : (permutationModule μ).V}
    (hx : (permutationModule μ).ρ.asAlgebraHom (columnAntisymmetrizer t) x ≠ 0) :
    Dominates (shapePartition lam) μ := by
  by_contra h
  exact hx (asAlgebraHom_columnAntisymmetrizer_apply_eq_zero_of_not_dominates t μ h x)

end YoungTableau

end TauCeti
