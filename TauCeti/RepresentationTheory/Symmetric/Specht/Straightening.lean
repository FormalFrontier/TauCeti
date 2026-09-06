/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.StandardTableau.Order
public import TauCeti.RepresentationTheory.Symmetric.Specht.Garnir
import TauCeti.Algebra.BigOperators.Finset.Swap
import TauCeti.Algebra.Order.BigOperators.SumLtSum

/-!
# The Garnir element and the straightening algorithm

The Garnir relation of `TauCeti/RepresentationTheory/Symmetric/Specht/Garnir.lean` says that the
signed sum

`∑_{σ} sgn(σ) e_{σt} = 0`

over the permutations `σ` supported in a set `X` whose labels cannot be spread over the rows
available to them vanishes.  As it stands the relation does not rewrite `e_t`: the permutations
that lie in the column group of `t` contribute further copies of `e_t` rather than of anything
else, so isolating the identity term rewrites `e_t` in terms of itself.  This file performs the
repackaging that Garnir's file leaves open -- **`e_t` is a rational combination of the polytabloids
`e_{σt}` of those `σ` that do not preserve the columns of `t`** -- and runs the resulting
straightening step to exhaustion: **every polytabloid is a rational combination of the
polytabloids of the standard tableaux of the same shape**, which is what makes the standard
polytabloids span the Specht module.

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
exactly the ones preserving the column-`j` half `TauCeti.YoungTableau.garnirSetLeft`, by
`TauCeti.YoungTableau.mem_colSubgroup_iff_image_garnirSetLeft_eq` of Garnir's file.  The
straightening step therefore rewrites `e_t` in terms of the polytabloids of the tableaux obtained
by genuinely exchanging labels between the two columns, which is what makes it progress towards a
standard tableau.

## The straightening algorithm

The straightening step is the second of two moves that rewrite an arbitrary polytabloid into
standard ones.  If two labels of one column of `t` are out of order, exchanging them is a
permutation of the column group of `t`, so it changes the polytabloid only by its sign
(`TauCeti.YoungTableau.polytabloid_relabel_of_mem_colSubgroup`).  If instead the columns of `t`
increase but two labels of one row are out of order, then two labels in *adjacent* columns of one
row are, and the straightening step at that cell writes `e_t` in terms of the polytabloids of the
relabelings by the permutations of the Garnir set that move a label between the two columns it
straddles.

Both moves increase a numerical measure of the tableau that is bounded above, so the rewriting
terminates.  The measure is built from the two moments `∑_k c_k · k` and `∑_k r_k · k`, weighting
each label by the index of its column, respectively of its row.  The first move fixes every label
in its column and raises the row moment, since it moves the smaller of the two labels up.  The
second move raises the column moment: because the columns of `t` increase and its row does not at
the chosen cell, every label of the Garnir set lying in the earlier column exceeds every label of
it lying in the later one, so a permutation of the set that does not preserve the columns
exchanges labels of the earlier column for strictly smaller ones.  Weighting the column moment
heavily enough that a gain in it outweighs any loss of row moment combines the two into one
measure.

A tableau on which neither move applies increases down its columns and along its rows, so it is
standard (`TauCeti.StandardYoungTableau.exists_toTableau_eq_iff`).

## Main results

* `TauCeti.YoungTableau.card_nsmul_polytabloid_add_sum_sign_smul_polytabloid_relabel_eq_zero`: the
  Garnir relation with its column-group terms collected, **the Garnir element relation**.
* `TauCeti.YoungTableau.polytabloid_mem_span_polytabloid_relabel`: `e_t` lies in the span of the
  polytabloids of the relabelings of `t` by permutations supported in `X` that leave the column
  group.
* `TauCeti.YoungTableau.polytabloid_mem_span_polytabloid_relabel_garnirSet`: **the
  straightening step**, the previous two combined at a Garnir set.
* `TauCeti.YoungTableau.polytabloid_mem_span_polytabloid_standard`: **the straightening
  algorithm**, every polytabloid is a rational combination of the standard ones.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Sections 7 and 8.
* [B. E. Sagan, *The Symmetric Group*][sagan2001], Sections 2.5 and 2.6.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 5, "The standard basis", which names the straightening algorithm as a target in its own
  right.
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

/-! ## The straightening measure -/
/-- The column moment of a tableau: every label weighted by the index of its column.  A Garnir
step at a row inversion increases it, because it moves the small labels of the Garnir set into the
earlier of the two columns the set straddles. -/
private def colMoment (t : YoungTableau μ) : ℕ := ∑ k : Fin μ.card, colIndex t k * (k : ℕ)

/-- The row moment of a tableau: every label weighted by the index of its row.  Exchanging two
labels of one column into increasing order increases it, and leaves the column moment alone. -/
private def rowMoment (t : YoungTableau μ) : ℕ := ∑ k : Fin μ.card, rowIndex t k * (k : ℕ)

/-- The measure both steps of the straightening algorithm increase: the column moment, weighted
heavily enough that a gain in it outweighs any loss of row moment, plus the row moment. -/
private def straightWeight (t : YoungTableau μ) : ℕ :=
  (μ.card ^ 3 + 1) * colMoment t + rowMoment t

/-- A bound for `straightWeight`, which is what makes the straightening algorithm terminate. -/
private def straightBound (μ : YoungDiagram) : ℕ := (μ.card ^ 3 + 1) * μ.card ^ 3 + μ.card ^ 3

private theorem rowIndex_le_card (t : YoungTableau μ) (k : Fin μ.card) :
    rowIndex t k ≤ μ.card := by
  refine le_of_lt ((rowIndex_lt_colLen_zero t k).trans_le ?_)
  rw [YoungDiagram.colLen_eq_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

private theorem colIndex_le_card (t : YoungTableau μ) (k : Fin μ.card) :
    colIndex t k ≤ μ.card := by
  refine le_of_lt ((colIndex_lt_rowLen t k).trans_le ?_)
  rw [YoungDiagram.rowLen_eq_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

private theorem colMoment_le (t : YoungTableau μ) : colMoment t ≤ μ.card ^ 3 :=
  calc colMoment t ≤ ∑ _k : Fin μ.card, μ.card * μ.card :=
        Finset.sum_le_sum fun k _ => Nat.mul_le_mul (colIndex_le_card t k) (le_of_lt k.isLt)
    _ = μ.card * (μ.card * μ.card) := by simp
    _ = μ.card ^ 3 := by ring

private theorem rowMoment_le (t : YoungTableau μ) : rowMoment t ≤ μ.card ^ 3 :=
  calc rowMoment t ≤ ∑ _k : Fin μ.card, μ.card * μ.card :=
        Finset.sum_le_sum fun k _ => Nat.mul_le_mul (rowIndex_le_card t k) (le_of_lt k.isLt)
    _ = μ.card * (μ.card * μ.card) := by simp
    _ = μ.card ^ 3 := by ring

private theorem straightWeight_le (t : YoungTableau μ) : straightWeight t ≤ straightBound μ :=
  Nat.add_le_add (Nat.mul_le_mul le_rfl (colMoment_le t)) (rowMoment_le t)

private theorem colMoment_relabel (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) :
    colMoment (relabel σ t) = ∑ k : Fin μ.card, colIndex t k * ((σ k : Fin μ.card) : ℕ) := by
  rw [colMoment]
  simp only [colIndex_relabel]
  rw [← Equiv.sum_comp σ fun k => colIndex t (σ⁻¹ k) * (k : ℕ)]
  simp

private theorem rowMoment_relabel (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) :
    rowMoment (relabel σ t) = ∑ k : Fin μ.card, rowIndex t k * ((σ k : Fin μ.card) : ℕ) := by
  rw [rowMoment]
  simp only [rowIndex_relabel]
  rw [← Equiv.sum_comp σ fun k => rowIndex t (σ⁻¹ k) * (k : ℕ)]
  simp

private theorem straightWeight_lt_of_colMoment_lt {t t' : YoungTableau μ}
    (h : colMoment t < colMoment t') : straightWeight t < straightWeight t' :=
  calc straightWeight t = (μ.card ^ 3 + 1) * colMoment t + rowMoment t := rfl
    _ < (μ.card ^ 3 + 1) * colMoment t + (μ.card ^ 3 + 1) :=
        Nat.add_lt_add_left (Nat.lt_succ_of_le (rowMoment_le t)) _
    _ = (μ.card ^ 3 + 1) * (colMoment t + 1) := (Nat.mul_succ _ _).symm
    _ ≤ (μ.card ^ 3 + 1) * colMoment t' := Nat.mul_le_mul le_rfl h
    _ ≤ straightWeight t' := Nat.le_add_right _ _

/-! ## Exchanging two labels of one column -/

/-- **Exchanging two labels of one column that are out of order increases the straightening
measure.**  The exchange leaves every label in its own column, so the column moment is unchanged,
while the smaller of the two labels moves to the earlier row and the row moment grows. -/
private theorem straightWeight_lt_of_swap {t : YoungTableau μ} {x y : Fin μ.card}
    (hcol : colIndex t x = colIndex t y) (hrow : rowIndex t x < rowIndex t y) (hyx : y < x) :
    straightWeight t < straightWeight (relabel (Equiv.swap x y) t) := by
  have hne : x ≠ y := fun h => absurd (congrArg (rowIndex t) h) hrow.ne
  have hc := sum_mul_swap (colIndex t) Fin.val (Finset.mem_univ x) (Finset.mem_univ y) hne
  have hr := sum_mul_swap (rowIndex t) Fin.val (Finset.mem_univ x) (Finset.mem_univ y) hne
  rw [hcol] at hc
  have hcol' : colMoment (relabel (Equiv.swap x y) t) = colMoment t := by
    rw [colMoment_relabel, colMoment]
    refine Nat.add_right_cancel (m := colIndex t y * (x : ℕ) + colIndex t y * (y : ℕ)) ?_
    rw [hc]
    ring
  have hrow' : rowMoment t < rowMoment (relabel (Equiv.swap x y) t) := by
    rw [rowMoment_relabel]
    have hstep : rowMoment t + (rowIndex t x * (x : ℕ) + rowIndex t y * (y : ℕ)) <
        rowMoment t + (rowIndex t x * (y : ℕ) + rowIndex t y * (x : ℕ)) :=
      Nat.add_lt_add_left (mul_add_mul_lt_mul_add_mul hrow (Fin.lt_def.mp hyx)) _
    rw [rowMoment] at hstep
    rw [← hr] at hstep
    exact lt_of_add_lt_add_right hstep
  rw [straightWeight, straightWeight, hcol']
  exact Nat.add_lt_add_left hrow' _

/-! ## The Garnir step increases the measure -/

/-- **The left half of a Garnir set carries larger labels than the right half**, at a cell where
the columns of `t` increase but its rows do not.  The left half sits in column `j` weakly below
row `i`, so its labels are at least the label at `(i, j)`; the right half sits in column `j + 1`
weakly above row `i`, so its labels are at most the label at `(i, j + 1)`; and the row inversion
puts the second of those below the first. -/
private theorem lt_of_mem_garnirSet {t : YoungTableau μ} {i j : ℕ} {x y : Fin μ.card}
    (hinc : ∀ p q : Fin μ.card, colIndex t p = colIndex t q → rowIndex t p < rowIndex t q → p < q)
    (hxr : rowIndex t x = i) (hxc : colIndex t x = j) (hyr : rowIndex t y = i)
    (hyc : colIndex t y = j + 1) (hyx : y < x) {a b : Fin μ.card}
    (ha : a ∈ garnirSetLeft t i j) (hb : b ∈ garnirSet t i j \ garnirSetLeft t i j) :
    b < a := by
  obtain ⟨hac, hai⟩ := mem_garnirSetLeft.mp ha
  obtain ⟨hbmem, hbnot⟩ := Finset.mem_sdiff.mp hb
  have hbc : colIndex t b = j + 1 :=
    colIndex_eq_of_mem_garnirSet_of_notMem_garnirSetLeft hbmem hbnot
  have hbi : rowIndex t b ≤ i := by
    rcases mem_garnirSet.mp hbmem with h | h
    · omega
    · exact h.2
  have hxa : x ≤ a := by
    rcases eq_or_lt_of_le hai with h | h
    · exact le_of_eq (rowIndex_colIndex_injective t (Prod.ext (hxr.trans h) (hxc.trans hac.symm)))
    · exact le_of_lt (hinc x a (by rw [hxc, hac]) (by omega))
  have hby : b ≤ y := by
    rcases eq_or_lt_of_le hbi with h | h
    · exact le_of_eq
        (rowIndex_colIndex_injective t (Prod.ext (h.trans hyr.symm) (hbc.trans hyc.symm)))
    · exact le_of_lt (hinc b y (by rw [hbc, hyc]) (by omega))
  exact lt_of_le_of_lt hby (lt_of_lt_of_le hyx hxa)

/-- Summing over a Garnir set against the column index only sees which of its two halves a label
lies in: the left half contributes the weight `j` and the right half the weight `j + 1`. -/
private theorem sum_colIndex_garnirSet (t : YoungTableau μ) (i j : ℕ) (g : Fin μ.card → ℕ) :
    ∑ k ∈ garnirSet t i j, colIndex t k * g k =
      j * (∑ k ∈ garnirSet t i j, g k) + ∑ k ∈ garnirSet t i j \ garnirSetLeft t i j, g k := by
  classical
  have hAX : garnirSetLeft t i j ⊆ garnirSet t i j := garnirSetLeft_subset_garnirSet t i j
  have hBc : ∀ k ∈ garnirSet t i j \ garnirSetLeft t i j,
      colIndex t k * g k = (j + 1) * g k := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_sdiff.mp hk
    rw [colIndex_eq_of_mem_garnirSet_of_notMem_garnirSetLeft hk1 hk2]
  have hAc : ∀ k ∈ garnirSetLeft t i j, colIndex t k * g k = j * g k := fun k hk => by
    rw [(mem_garnirSetLeft.mp hk).1]
  rw [← Finset.sum_sdiff hAX, ← Finset.sum_sdiff (f := g) hAX, Finset.sum_congr rfl hBc,
    Finset.sum_congr rfl hAc, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- **A Garnir permutation that does not preserve the columns increases the column moment.**  It
exchanges labels of the left half of the Garnir set for labels of the right half; the latter are
the smaller ones, and they move into the earlier column. -/
private theorem colMoment_lt_of_garnir {t : YoungTableau μ} {i j : ℕ}
    {σ : Equiv.Perm (Fin μ.card)} (hfix : ∀ k ∉ garnirSet t i j, σ k = k)
    (himg : (garnirSetLeft t i j).image σ ≠ garnirSetLeft t i j)
    (hlt : ∀ a ∈ garnirSetLeft t i j, ∀ b ∈ garnirSet t i j \ garnirSetLeft t i j,
      (b : ℕ) < (a : ℕ)) :
    colMoment t < colMoment (relabel σ t) := by
  classical
  have hAX : garnirSetLeft t i j ⊆ garnirSet t i j := garnirSetLeft_subset_garnirSet t i j
  -- `σ` permutes the Garnir set, since it fixes everything outside it
  have hmemX : ∀ k ∈ garnirSet t i j, σ k ∈ garnirSet t i j := by
    intro k hk
    by_contra hnot
    have heq : σ k = k := σ.injective (hfix _ hnot)
    rw [heq] at hnot
    exact hnot hk
  have hXimg : (garnirSet t i j).image σ = garnirSet t i j :=
    Finset.eq_of_subset_of_card_le
      (fun z hz => by obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz; exact hmemX k hk)
      (le_of_eq (Finset.card_image_of_injective _ σ.injective).symm)
  -- the labels outside the Garnir set contribute the same to both moments
  have hout : ∀ k ∈ (garnirSet t i j)ᶜ,
      colIndex t k * ((σ k : Fin μ.card) : ℕ) = colIndex t k * (k : ℕ) :=
    fun k hk => by rw [hfix k (Finset.mem_compl.mp hk)]
  have hsum : ∀ g : Fin μ.card → ℕ,
      ∑ k : Fin μ.card, colIndex t k * g k =
        (∑ k ∈ garnirSet t i j, colIndex t k * g k) +
          ∑ k ∈ (garnirSet t i j)ᶜ, colIndex t k * g k :=
    fun g => (Finset.sum_add_sum_compl _ _).symm
  have himage : ∑ k ∈ garnirSet t i j \ garnirSetLeft t i j, ((σ k : Fin μ.card) : ℕ) =
      ∑ z ∈ (garnirSet t i j \ garnirSetLeft t i j).image σ, (z : ℕ) :=
    (Finset.sum_image fun x _ y _ hxy => σ.injective hxy).symm
  have hfull : ∑ k ∈ garnirSet t i j, ((σ k : Fin μ.card) : ℕ) =
      ∑ k ∈ garnirSet t i j, (k : ℕ) := by
    have h : ∑ z ∈ (garnirSet t i j).image σ, (z : ℕ) =
        ∑ k ∈ garnirSet t i j, ((σ k : Fin μ.card) : ℕ) :=
      Finset.sum_image fun x _ y _ hxy => σ.injective hxy
    rw [hXimg] at h
    exact h.symm
  -- so the two moments differ only in the sum over the right half of the Garnir set
  have hkey := sum_lt_sum_image_sdiff Fin.val hAX hXimg himg hlt
  rw [colMoment_relabel, colMoment, hsum fun k => ((σ k : Fin μ.card) : ℕ),
    hsum fun k => (k : ℕ), Finset.sum_congr rfl hout,
    sum_colIndex_garnirSet t i j fun k => ((σ k : Fin μ.card) : ℕ),
    sum_colIndex_garnirSet t i j fun k => (k : ℕ), hfull, himage]
  omega

/-! ## The straightening algorithm -/

/-- **A row inversion produces one between adjacent columns.**  Walking rightwards from the
earlier of the two cells, the first step at which the label drops is such an inversion. -/
private theorem exists_adjacent_row_inversion (t : YoungTableau μ) :
    ∀ (n : ℕ) (x y : Fin μ.card), colIndex t y - colIndex t x ≤ n →
      rowIndex t x = rowIndex t y → colIndex t x < colIndex t y → y < x →
      ∃ u v : Fin μ.card,
        rowIndex t u = rowIndex t v ∧ colIndex t v = colIndex t u + 1 ∧ v < u := by
  intro n
  induction n with
  | zero =>
    intro x y hn _ hcol _
    omega
  | succ n ih =>
    intro x y hn hrow hcol hyx
    by_cases hadj : colIndex t y = colIndex t x + 1
    · exact ⟨x, y, hrow, hadj, hyx⟩
    · have hmem : (rowIndex t x, colIndex t x + 1) ∈ μ := by
        have hcell : (rowIndex t x, colIndex t y) ∈ μ := by
          rw [hrow]
          exact rowIndex_colIndex_mem t y
        exact μ.up_left_mem le_rfl (by omega) hcell
      obtain ⟨z, hzr, hzc⟩ := exists_rowIndex_colIndex t hmem
      rcases lt_trichotomy z x with hzx | hzx | hzx
      · exact ⟨x, z, hzr.symm, hzc, hzx⟩
      · exact absurd hzc (by rw [hzx]; omega)
      · refine ih z y ?_ (by rw [hzr, hrow]) ?_ (hyx.trans hzx)
        · omega
        · omega

/-- **A tableau that is not standard has its polytabloid in the span of heavier ones.**  If two
labels of one column are out of order, exchanging them is a column permutation, which changes the
polytabloid only by its sign; otherwise the rows fail to increase somewhere, and the Garnir
relation at that cell rewrites the polytabloid in terms of the relabelings that move a label
between the two columns concerned. -/
private theorem polytabloid_mem_span_of_lt (t : YoungTableau μ)
    (hns : ¬ ((∀ x y : Fin μ.card,
          colIndex t x = colIndex t y → rowIndex t x < rowIndex t y → x < y) ∧
        ∀ x y : Fin μ.card, rowIndex t x = rowIndex t y → colIndex t x < colIndex t y → x < y)) :
    polytabloid t ∈ Submodule.span ℚ
      {v | ∃ t' : YoungTableau μ, straightWeight t < straightWeight t' ∧ v = polytabloid t'} := by
  classical
  by_cases hinc : ∀ x y : Fin μ.card,
      colIndex t x = colIndex t y → rowIndex t x < rowIndex t y → x < y
  · -- the columns of `t` increase, so a row of `t` is out of order
    have hrowfail : ¬ ∀ x y : Fin μ.card,
        rowIndex t x = rowIndex t y → colIndex t x < colIndex t y → x < y :=
      fun h => hns ⟨hinc, h⟩
    push Not at hrowfail
    obtain ⟨x, y, hrow, hcol, hyx⟩ := hrowfail
    have hne : x ≠ y := fun h => absurd (congrArg (colIndex t) h) hcol.ne
    obtain ⟨u, v, huv, hadj, hvu⟩ := exists_adjacent_row_inversion t _ x y le_rfl hrow hcol
      (lt_of_le_of_ne hyx (Ne.symm hne))
    have hcell : (rowIndex t u, colIndex t u + 1) ∈ μ := by
      have h := rowIndex_colIndex_mem t v
      rwa [← huv, hadj] at h
    refine (Submodule.span_le.mpr ?_)
      (polytabloid_mem_span_polytabloid_relabel_garnirSet t hcell)
    rintro _ ⟨σ, ⟨hfix, himg⟩, rfl⟩
    refine Submodule.subset_span ⟨relabel σ t, ?_, rfl⟩
    refine straightWeight_lt_of_colMoment_lt (colMoment_lt_of_garnir hfix himg fun a ha b hb => ?_)
    exact Fin.lt_def.mp (lt_of_mem_garnirSet hinc rfl rfl huv.symm hadj hvu ha hb)
  · -- a column of `t` is out of order
    push Not at hinc
    obtain ⟨x, y, hcol, hrow, hyx⟩ := hinc
    have hne : x ≠ y := fun h => absurd (congrArg (rowIndex t) h) hrow.ne
    have hswap : Equiv.swap x y ∈ colSubgroup t := by
      rw [mem_colSubgroup]
      intro k
      rcases eq_or_ne k x with rfl | hkx
      · rw [Equiv.swap_apply_left, hcol]
      rcases eq_or_ne k y with rfl | hky
      · rw [Equiv.swap_apply_right, hcol]
      · rw [Equiv.swap_apply_of_ne_of_ne hkx hky]
    have hsign : polytabloid (relabel (Equiv.swap x y) t) = -polytabloid t := by
      rw [polytabloid_relabel_of_mem_colSubgroup hswap, Equiv.Perm.sign_swap hne]
      simp
    have hmem : polytabloid (relabel (Equiv.swap x y) t) ∈ Submodule.span ℚ
        {v | ∃ t' : YoungTableau μ,
          straightWeight t < straightWeight t' ∧ v = polytabloid t'} :=
      Submodule.subset_span
        ⟨_, straightWeight_lt_of_swap hcol hrow (lt_of_le_of_ne hyx (Ne.symm hne)), rfl⟩
    rw [hsign] at hmem
    simpa using neg_mem hmem

/-- **The straightening algorithm**: every polytabloid is a rational combination of the
polytabloids of the standard tableaux of the same shape.  The straightening measure increases at
every rewriting step and is bounded, so the rewriting terminates, and it terminates only at a
tableau increasing down its columns and along its rows. -/
theorem polytabloid_mem_span_polytabloid_standard (t : YoungTableau μ) :
    polytabloid t ∈ Submodule.span ℚ
      (Set.range fun T : StandardYoungTableau μ => polytabloid T.toTableau) := by
  classical
  suffices H : ∀ (N : ℕ) (t : YoungTableau μ), straightBound μ - straightWeight t ≤ N →
      polytabloid t ∈ Submodule.span ℚ
        (Set.range fun T : StandardYoungTableau μ => polytabloid T.toTableau) from
    H _ t le_rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro t ht
    by_cases hstd : (∀ x y : Fin μ.card,
          colIndex t x = colIndex t y → rowIndex t x < rowIndex t y → x < y) ∧
        ∀ x y : Fin μ.card, rowIndex t x = rowIndex t y → colIndex t x < colIndex t y → x < y
    · obtain ⟨T, rfl⟩ := (StandardYoungTableau.exists_toTableau_eq_iff t).mpr hstd
      exact Submodule.subset_span ⟨T, rfl⟩
    · refine (Submodule.span_le.mpr ?_) (polytabloid_mem_span_of_lt t hstd)
      rintro _ ⟨t', hlt, rfl⟩
      refine ih (straightBound μ - straightWeight t') ?_ t' le_rfl
      exact lt_of_lt_of_le
        (Nat.sub_lt_sub_left (lt_of_lt_of_le hlt (straightWeight_le t')) hlt) ht

end YoungTableau

end TauCeti
