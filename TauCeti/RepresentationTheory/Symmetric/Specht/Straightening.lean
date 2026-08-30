/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.Specht.Garnir

/-!
# The Garnir element and the straightening step

The Garnir relation of `TauCeti/RepresentationTheory/Symmetric/Specht/Garnir.lean` says that the
signed sum

`∑_{σ} sgn(σ) e_{σt} = 0`

over the permutations `σ` supported in a set `X` whose labels cannot be spread over the rows
available to them vanishes.  As it stands the relation does not rewrite `e_t`: the permutations
that lie in the column group of `t` contribute further copies of `e_t` rather than of anything
else, so isolating the identity term rewrites `e_t` in terms of itself.  This file performs the
repackaging that Garnir's file leaves open, and states the result the straightening algorithm
consumes: **`e_t` is a rational combination of the polytabloids `e_{σt}` of those `σ` that do not
preserve the columns of `t`**.

## Splitting the relation

The whole content is that the terms of the relation indexed by the column group of `t` are all
equal to `e_t` on the nose.  A column permutation `q` scales the polytabloid by its sign
(`TauCeti.YoungTableau.polytabloid_relabel_of_mem_colSubgroup`), so its term
`sgn(q) e_{qt} = sgn(q)² e_t` is `e_t`.  Splitting the sum accordingly gives

`N · e_t + ∑_{σ ∉ colSubgroup t} sgn(σ) e_{σt} = 0`,

where `N` counts the permutations supported in `X` that preserve the columns of `t`; `N` is
positive because the identity is one of them, so `e_t` is `-1/N` times the second sum.  This is the
classical passage from the antisymmetrizer of `X` to the *Garnir element*, a signed sum over a
transversal of the internal permutations, written here without choosing a transversal: the terms
are constant on the cosets, so counting them suffices.

## Which permutations are internal

For the Garnir set `X` of `t` at a cell `(i, j)` -- the labels of `t` in column `j` from row `i`
down together with those in column `j + 1` from row `i` up -- the internal permutations are
exactly the ones preserving the column-`j` half `TauCeti.YoungTableau.garnirSetLeft`
(`TauCeti.YoungTableau.mem_colSubgroup_iff_image_garnirSetLeft_eq`), which is the classical
description of that subgroup as a product of the symmetric groups on the two halves.  The
straightening step therefore rewrites `e_t` in terms of the polytabloids of the tableaux obtained
by genuinely exchanging labels between the two columns, which is what makes it progress towards a
standard tableau.

## Main definitions

* `TauCeti.YoungTableau.garnirSetLeft`: the column-`j` half of the Garnir set of `t` at `(i, j)`.

## Main results

* `TauCeti.YoungTableau.card_nsmul_polytabloid_add_sum_sign_smul_polytabloid_relabel_eq_zero`: the
  Garnir relation with its column-group terms collected, **the Garnir element relation**.
* `TauCeti.YoungTableau.polytabloid_mem_span_polytabloid_relabel`: `e_t` lies in the span of the
  polytabloids of the relabelings of `t` by permutations supported in `X` that leave the column
  group.
* `TauCeti.YoungTableau.mem_colSubgroup_iff_image_garnirSetLeft_eq`: the internal permutations of
  a Garnir set are those preserving its left half.
* `TauCeti.YoungTableau.polytabloid_mem_span_polytabloid_relabel_garnirSet`: **the
  straightening step**, the previous three combined at a Garnir set.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Section 7.
* [B. E. Sagan, *The Symmetric Group*][sagan2001], Section 2.6.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 5, whose standard basis of the Specht module this step straightens towards.
-/

public section

namespace TauCeti

open scoped BigOperators

namespace YoungTableau

variable {μ : YoungDiagram}

/-- Classical decidability of membership in the column group, used to split a sum over the
permutations supported in a set according to whether they preserve the columns, as in
`TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean`. -/
noncomputable local instance decidablePredMemColSubgroupStraightening (t : YoungTableau μ) :
    DecidablePred (· ∈ colSubgroup t) :=
  Classical.decPred _

/-! ## Collecting the column-group terms of a Garnir relation -/

/-- A permutation fixing everything outside `X` maps `X` to itself: were `σ k` outside `X` for
some `k` of `X`, it would be fixed, forcing `σ k = k`. -/
private theorem apply_mem_of_forall_notMem {α : Type*} {X : Finset α} {σ : Equiv.Perm α}
    (hσ : ∀ k ∉ X, σ k = k) {k : α} (hk : k ∈ X) : σ k ∈ X := by
  by_contra h
  have h' : σ k = k := σ.injective (hσ (σ k) h)
  rw [h'] at h
  exact h hk

/-- **The Garnir element relation.**  Under the hypotheses of the Garnir relation
`TauCeti.YoungTableau.sum_sign_smul_polytabloid_relabel_eq_zero` -- every label of `X` lying in a
column of `μ` with at most `r` cells, and `X` having more than `r` elements -- the permutations
supported in `X` that preserve the columns of `t` contribute one copy of `e_t` each, so the
relation reads as a multiple of `e_t` cancelling against the remaining terms.

This is the form the straightening algorithm uses: the multiplicity `N` of `e_t` is the number of
internal permutations, and it is positive, the identity being one of them. -/
theorem card_nsmul_polytabloid_add_sum_sign_smul_polytabloid_relabel_eq_zero (t : YoungTableau μ)
    {X : Finset (Fin μ.card)} {r : ℕ} (hX : ∀ k ∈ X, μ.colLen (colIndex t k) ≤ r)
    (hcard : r < X.card)
    [DecidablePred fun σ : Equiv.Perm (Fin μ.card) => ∀ k ∉ X, σ k = k] :
    ({σ : Equiv.Perm (Fin μ.card) | (∀ k ∉ X, σ k = k) ∧ σ ∈ colSubgroup t} :
        Finset (Equiv.Perm (Fin μ.card))).card • polytabloid t +
      ∑ σ ∈ ({σ : Equiv.Perm (Fin μ.card) | (∀ k ∉ X, σ k = k) ∧ σ ∉ colSubgroup t} :
          Finset (Equiv.Perm (Fin μ.card))),
        ((Equiv.Perm.sign σ : ℤ) : ℚ) • polytabloid (relabel σ t) = 0 := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ({σ : Equiv.Perm (Fin μ.card) | ∀ k ∉ X, σ k = k} : Finset (Equiv.Perm (Fin μ.card)))
    (fun σ => σ ∈ colSubgroup t)
    (fun σ => ((Equiv.Perm.sign σ : ℤ) : ℚ) • polytabloid (relabel σ t))
  rw [sum_sign_smul_polytabloid_relabel_eq_zero t hX hcard, Finset.filter_filter,
    Finset.filter_filter] at hsplit
  -- an internal permutation scales `e_t` by its sign twice over, so contributes `e_t`
  have hconst : ∀ σ ∈ ({σ : Equiv.Perm (Fin μ.card) | (∀ k ∉ X, σ k = k) ∧ σ ∈ colSubgroup t} :
      Finset (Equiv.Perm (Fin μ.card))),
      ((Equiv.Perm.sign σ : ℤ) : ℚ) • polytabloid (relabel σ t) = polytabloid t := by
    intro σ hσ
    have hsq : ((Equiv.Perm.sign σ : ℤ) : ℚ) * ((Equiv.Perm.sign σ : ℤ) : ℚ) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [polytabloid_relabel_of_mem_colSubgroup (Finset.mem_filter.mp hσ).2.2, smul_smul, hsq,
      one_smul]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const] at hsplit
  exact hsplit

/-- **The straightening step, in the abstract.**  Under the hypotheses of the Garnir relation, the
polytabloid of `t` lies in the rational span of the polytabloids of the relabelings `σt` for the
permutations `σ` that are supported in `X` and do **not** preserve the columns of `t`.

This is the division-free reading of
`TauCeti.YoungTableau.card_nsmul_polytabloid_add_sum_sign_smul_polytabloid_relabel_eq_zero`, whose
multiple of `e_t` is nonzero. -/
theorem polytabloid_mem_span_polytabloid_relabel (t : YoungTableau μ) {X : Finset (Fin μ.card)}
    {r : ℕ} (hX : ∀ k ∈ X, μ.colLen (colIndex t k) ≤ r) (hcard : r < X.card) :
    polytabloid t ∈ Submodule.span ℚ
      ((fun σ => polytabloid (relabel σ t)) ''
        {σ : Equiv.Perm (Fin μ.card) | (∀ k ∉ X, σ k = k) ∧ σ ∉ colSubgroup t}) := by
  have hpos : 0 < ({σ : Equiv.Perm (Fin μ.card) | (∀ k ∉ X, σ k = k) ∧ σ ∈ colSubgroup t} :
      Finset (Equiv.Perm (Fin μ.card))).card :=
    Finset.card_pos.mpr ⟨1, by simp⟩
  have hne : (({σ : Equiv.Perm (Fin μ.card) | (∀ k ∉ X, σ k = k) ∧ σ ∈ colSubgroup t} :
      Finset (Equiv.Perm (Fin μ.card))).card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  refine (Submodule.smul_mem_iff _ hne).mp ?_
  rw [Nat.cast_smul_eq_nsmul, eq_neg_of_add_eq_zero_left
    (card_nsmul_polytabloid_add_sum_sign_smul_polytabloid_relabel_eq_zero t hX hcard)]
  refine neg_mem (Submodule.sum_mem _ fun σ hσ => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span ⟨σ, (Finset.mem_filter.mp hσ).2, rfl⟩

/-! ## The left half of a Garnir set -/

/-- The **left half of a Garnir set**: the labels of `t` lying in column `j` from row `i`
downwards.  The Garnir set of `t` at `(i, j)` is this set together with the labels in column
`j + 1` from row `i` upwards, and the permutations of the Garnir set that preserve the columns of
`t` are exactly those preserving this half
(`TauCeti.YoungTableau.mem_colSubgroup_iff_image_garnirSetLeft_eq`). -/
def garnirSetLeft (t : YoungTableau μ) (i j : ℕ) : Finset (Fin μ.card) :=
  {k | colIndex t k = j ∧ i ≤ rowIndex t k}

@[simp]
theorem mem_garnirSetLeft {t : YoungTableau μ} {i j : ℕ} {k : Fin μ.card} :
    k ∈ garnirSetLeft t i j ↔ colIndex t k = j ∧ i ≤ rowIndex t k := by
  simp [garnirSetLeft]

/-- The left half of a Garnir set is part of it, being the first of the two cases of its
definition. -/
theorem garnirSetLeft_subset_garnirSet (t : YoungTableau μ) (i j : ℕ) :
    garnirSetLeft t i j ⊆ garnirSet t i j := fun _ hk =>
  mem_garnirSet.mpr (Or.inl (mem_garnirSetLeft.mp hk))

/-- A label of a Garnir set outside its left half lies in column `j + 1`, the two halves being the
two cases of the definition of the Garnir set. -/
theorem colIndex_eq_of_mem_garnirSet_of_notMem_garnirSetLeft {t : YoungTableau μ} {i j : ℕ}
    {k : Fin μ.card} (hk : k ∈ garnirSet t i j) (hk' : k ∉ garnirSetLeft t i j) :
    colIndex t k = j + 1 := by
  rcases mem_garnirSet.mp hk with h | h
  · exact absurd (mem_garnirSetLeft.mpr h) hk'
  · exact h.1

/-- **The internal permutations of a Garnir set are those preserving its left half.**  A
permutation supported in the Garnir set of `t` at `(i, j)` preserves the columns of `t` exactly
when it maps the column-`j` half of that set onto itself; it then automatically preserves the
column-`(j + 1)` half as well, so the internal permutations are the product of the two symmetric
groups on the halves. -/
theorem mem_colSubgroup_iff_image_garnirSetLeft_eq {t : YoungTableau μ} {i j : ℕ}
    {σ : Equiv.Perm (Fin μ.card)} (hσ : ∀ k ∉ garnirSet t i j, σ k = k) :
    σ ∈ colSubgroup t ↔ (garnirSetLeft t i j).image σ = garnirSetLeft t i j := by
  constructor
  · intro hcol
    refine Finset.eq_of_subset_of_card_le ?_
      (le_of_eq (Finset.card_image_of_injective _ σ.injective).symm)
    intro k hk
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
    have hmem : σ l ∈ garnirSet t i j :=
      apply_mem_of_forall_notMem hσ (garnirSetLeft_subset_garnirSet t i j hl)
    have hcolσ : colIndex t (σ l) = j := by
      rw [mem_colSubgroup.mp hcol l]
      exact (mem_garnirSetLeft.mp hl).1
    rcases mem_garnirSet.mp hmem with ⟨-, hrow⟩ | ⟨hc, -⟩
    · exact mem_garnirSetLeft.mpr ⟨hcolσ, hrow⟩
    · exact absurd hc (by omega)
  · intro himg
    rw [mem_colSubgroup]
    intro k
    by_cases hk : k ∈ garnirSet t i j
    · by_cases hkl : k ∈ garnirSetLeft t i j
      · have hmem : σ k ∈ garnirSetLeft t i j := himg ▸ Finset.mem_image_of_mem σ hkl
        rw [(mem_garnirSetLeft.mp hmem).1, (mem_garnirSetLeft.mp hkl).1]
      · have hnot : σ k ∉ garnirSetLeft t i j := by
          intro h
          rw [← himg] at h
          obtain ⟨l, hl, hlk⟩ := Finset.mem_image.mp h
          exact hkl (σ.injective hlk ▸ hl)
        rw [colIndex_eq_of_mem_garnirSet_of_notMem_garnirSetLeft
            (apply_mem_of_forall_notMem hσ hk) hnot,
          colIndex_eq_of_mem_garnirSet_of_notMem_garnirSetLeft hk hkl]
    · rw [hσ k hk]

/-! ## The straightening step at a Garnir set -/

/-- **The straightening step.**  As soon as `(i, j + 1)` is a cell of `μ`, the polytabloid of `t`
lies in the rational span of the polytabloids of the relabelings `σt` by the permutations `σ` that
are supported in the Garnir set of `t` at `(i, j)` and move a label between its two halves, that
is between columns `j` and `j + 1`.

Applied at a cell where the rows of `t` fail to increase, this is the rewriting the straightening
algorithm performs on the way to the standard basis of the Specht module. -/
theorem polytabloid_mem_span_polytabloid_relabel_garnirSet (t : YoungTableau μ) {i j : ℕ}
    (h : (i, j + 1) ∈ μ) :
    polytabloid t ∈ Submodule.span ℚ
      ((fun σ => polytabloid (relabel σ t)) ''
        {σ : Equiv.Perm (Fin μ.card) | (∀ k ∉ garnirSet t i j, σ k = k) ∧
          (garnirSetLeft t i j).image σ ≠ garnirSetLeft t i j}) := by
  have hindex : {σ : Equiv.Perm (Fin μ.card) | (∀ k ∉ garnirSet t i j, σ k = k) ∧
        σ ∉ colSubgroup t} =
      {σ : Equiv.Perm (Fin μ.card) | (∀ k ∉ garnirSet t i j, σ k = k) ∧
        (garnirSetLeft t i j).image σ ≠ garnirSetLeft t i j} := by
    ext σ
    exact and_congr_right fun hσ => not_congr (mem_colSubgroup_iff_image_garnirSetLeft_eq hσ)
  rw [← hindex]
  exact polytabloid_mem_span_polytabloid_relabel t
    (fun _ hk => colLen_colIndex_le_colLen_of_mem_garnirSet hk)
    (by rw [card_garnirSet t h]; exact Nat.lt_succ_self _)

end YoungTableau

end TauCeti
