/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.Specht.Module

/-!
# The Garnir relations

The polytabloids `e_t` of the `μ`-tableaux span the Specht module `S^μ`, and the standard basis
theorem says that the polytabloids of the *standard* tableaux already do.  The relations that the
straightening algorithm rewrites an arbitrary polytabloid with are the **Garnir relations**, and
this file proves them.

Write `A_X` for the signed sum `∑ sgn(σ) σ` over the permutations `σ` fixing every label outside a
finite set `X` (`TauCeti.antisymmetrizerOn`, defined with the other signed sums in
`TauCeti/RepresentationTheory/Symmetric/Symmetrizer.lean`).  The Garnir relation is

`A_X · e_t = 0`

whenever `X` is too large to be spread over the rows available to it: all the labels of `X` lie in
columns of `μ` of length at most `r`, and `X` has more than `r` elements
(`TauCeti.YoungTableau.asAlgebraHom_antisymmetrizerOn_polytabloid_eq_zero`).  Applied to the
polytabloid it reads as the vanishing of a signed sum of the polytabloids `e_{σt}`
(`TauCeti.YoungTableau.sum_sign_smul_polytabloid_relabel_eq_zero`).

Two facts drive the proof.

* **A signed sum kills whatever an odd permutation in it fixes.**  Absorbing an odd permutation
  supported in `X` turns `A_X` into its own negative, so `A_X` annihilates every vector that
  permutation fixes (`TauCeti.asAlgebraHom_antisymmetrizerOn_apply_eq_zero`).
* **Pigeonhole in the columns.**  A column permutation `q` of `t` moves a label only within its own
  column, so in the tabloid `q · {t}` the labels of `X` still lie in columns of length at most `r`,
  that is, in `r` rows.  As `X` has more than `r` elements, two of them share a row of `q · {t}`,
  and the transposition swapping those two fixes that tabloid.  Every tabloid occurring in `e_t` is
  of this form, so `A_X` kills them all.

The sets `X` the relation is applied to are the **Garnir sets** `TauCeti.YoungTableau.garnirSet t i
j`: the labels of `t` in column `j` from row `i` downwards together with those in column `j + 1`
from row `i` upwards.  As soon as `(i, j + 1)` is a cell of `μ` there are `μ.colLen j + 1` of them
(`TauCeti.YoungTableau.card_garnirSet`) while they occupy only the `μ.colLen j` rows of column `j`,
so the relation applies
(`TauCeti.YoungTableau.asAlgebraHom_antisymmetrizerOn_garnirSet_polytabloid_eq_zero`).
Those are the sets the straightening algorithm uses at a cell `(i, j)` where the rows of the
tableau fail to increase.

The straightening step itself is *not* proved here, and the relation as stated does not supply it.
The permutations `σ` supported in `X` that lie in the column group of `t` satisfy
`e_{σt} = sgn(σ) e_t`, so their terms in the signed sum are further copies of `e_t` rather than of
anything nearer to standard; simply isolating the identity term of the sum therefore rewrites `e_t`
in terms of itself.  The classical Garnir *element* avoids this by summing only over a transversal
of the permutations internal to the two halves of the set, so that `A_X` factors as the signed sum
over those internal permutations times the Garnir element, and the identity coset contributes `e_t`
alone.  That repackaging is left to the file that performs the straightening induction; here the
relation is proved, and stated, for the whole of `A_X`.

## Main definitions

* `TauCeti.YoungTableau.garnirSet`: the Garnir set of a tableau at a row and a column.

## Main results

* `TauCeti.YoungTableau.exists_ne_rowIndex_relabel_eq`: the pigeonhole step, two labels of an
  oversized set share a row after any column permutation.
* `TauCeti.YoungTableau.asAlgebraHom_antisymmetrizerOn_polytabloid_eq_zero`: **the Garnir
  relation**.
* `TauCeti.YoungTableau.sum_sign_smul_polytabloid_relabel_eq_zero`: the relation as the
  vanishing of a signed sum of polytabloids.
* `TauCeti.YoungTableau.card_garnirSet`: a Garnir set has one more element than the column it
  straddles has cells.
* `TauCeti.YoungTableau.asAlgebraHom_antisymmetrizerOn_garnirSet_polytabloid_eq_zero`: the Garnir
  relation at a Garnir set.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Section 7.
* [B. E. Sagan, *The Symmetric Group*][sagan2001], Section 2.6.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 5, whose standard basis of the Specht module these relations straighten towards.
-/

public section

namespace TauCeti

open scoped BigOperators

namespace YoungTableau

variable {μ : YoungDiagram}

/-! ## The Garnir relation -/

/-- **Pigeonhole in the columns.**  Suppose every label of `X` lies in a column of `μ` with at most
`r` cells, and `X` has more than `r` elements.  Then a column permutation `q` of `t` leaves two
distinct labels of `X` in a common row of `qt`: it moves each of them only inside its own column,
so all of them still lie in the top `r` rows. -/
theorem exists_ne_rowIndex_relabel_eq (t : YoungTableau μ) {X : Finset (Fin μ.card)} {r : ℕ}
    (hX : ∀ k ∈ X, μ.colLen (colIndex t k) ≤ r) (hcard : r < X.card)
    {q : Equiv.Perm (Fin μ.card)} (hq : q ∈ colSubgroup t) :
    ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ rowIndex (relabel q t) x = rowIndex (relabel q t) y := by
  have hmaps : ∀ k ∈ X, rowIndex (relabel q t) k ∈ Finset.range r := by
    intro k hk
    have hcol : colIndex t (q⁻¹ k) = colIndex t k := mem_colSubgroup.mp (inv_mem hq) k
    have hmem : (rowIndex t (q⁻¹ k), colIndex t (q⁻¹ k)) ∈ μ := rowIndex_colIndex_mem t (q⁻¹ k)
    have hlt : rowIndex t (q⁻¹ k) < μ.colLen (colIndex t (q⁻¹ k)) :=
      YoungDiagram.mem_iff_lt_colLen.mp hmem
    rw [Finset.mem_range, rowIndex_relabel]
    calc rowIndex t (q⁻¹ k) < μ.colLen (colIndex t (q⁻¹ k)) := hlt
      _ = μ.colLen (colIndex t k) := by rw [hcol]
      _ ≤ r := hX k hk
  exact Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by simpa using hcard) hmaps

/-- The antisymmetrizer of `X` annihilates every tabloid reachable from `{t}` by a column
permutation of `t`, because two labels of `X` share a row of that tabloid. -/
private theorem asAlgebraHom_antisymmetrizerOn_single_smul_tabloid_eq_zero (t : YoungTableau μ)
    {X : Finset (Fin μ.card)} {r : ℕ} (hX : ∀ k ∈ X, μ.colLen (colIndex t k) ≤ r)
    (hcard : r < X.card) {q : Equiv.Perm (Fin μ.card)} (hq : q ∈ colSubgroup t) :
    (permutationModule (shapePartition μ)).ρ.asAlgebraHom (antisymmetrizerOn X)
        (MonoidAlgebra.single (q • tabloid t) (1 : ℚ)) = 0 := by
  obtain ⟨x, hx, y, hy, hxy, hrow⟩ := exists_ne_rowIndex_relabel_eq t hX hcard hq
  refine asAlgebraHom_antisymmetrizerOn_apply_eq_zero _
    (fun k hk => Equiv.swap_apply_of_ne_of_ne (fun h => hk (h ▸ hx)) fun h => hk (h ▸ hy))
    (Equiv.Perm.sign_swap hxy) ?_
  rw [Representation.ofMulAction_single, ← tabloid_relabel]
  exact congrArg (MonoidAlgebra.single · (1 : ℚ))
    (smul_tabloid_eq_self_iff.mpr (swap_mem_rowSubgroup hrow))

/-- **The Garnir relation.**  If every label of the finite set `X` lies in a column of `μ` with at
most `r` cells and `X` has more than `r` elements, then the antisymmetrizer of `X` annihilates the
polytabloid of `t`.

The labels of `X` cannot be spread over the rows of those columns, so every tabloid occurring in
`e_t` has two of them in a common row and is killed by the signed sum. -/
theorem asAlgebraHom_antisymmetrizerOn_polytabloid_eq_zero (t : YoungTableau μ)
    {X : Finset (Fin μ.card)} {r : ℕ} (hX : ∀ k ∈ X, μ.colLen (colIndex t k) ≤ r)
    (hcard : r < X.card) :
    (permutationModule (shapePartition μ)).ρ.asAlgebraHom (antisymmetrizerOn X)
        (polytabloid t) = 0 := by
  rw [polytabloid_eq_sum, map_sum]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [map_smul, asAlgebraHom_antisymmetrizerOn_single_smul_tabloid_eq_zero t hX hcard q.2,
    smul_zero]

/-- **The Garnir relation, as a signed sum of polytabloids.**  Under the hypotheses of
`TauCeti.YoungTableau.asAlgebraHom_antisymmetrizerOn_polytabloid_eq_zero`, the signed sum of the
polytabloids of the relabelings `σt`, over the permutations `σ` supported in `X`, vanishes. -/
theorem sum_sign_smul_polytabloid_relabel_eq_zero (t : YoungTableau μ)
    {X : Finset (Fin μ.card)} {r : ℕ} (hX : ∀ k ∈ X, μ.colLen (colIndex t k) ≤ r)
    (hcard : r < X.card)
    [DecidablePred fun σ : Equiv.Perm (Fin μ.card) => ∀ k ∉ X, σ k = k] :
    ∑ σ ∈ {σ : Equiv.Perm (Fin μ.card) | ∀ k ∉ X, σ k = k},
        ((Equiv.Perm.sign σ : ℤ) : ℚ) • polytabloid (relabel σ t) = 0 := by
  rw [← asAlgebraHom_antisymmetrizerOn_polytabloid_eq_zero t hX hcard,
    asAlgebraHom_antisymmetrizerOn_apply]
  simp only [polytabloid_relabel]

/-! ## Garnir sets -/

/-- The **Garnir set** of a tableau `t` at row `i` and column `j`: the labels of `t` lying in
column `j` from row `i` downwards, together with those lying in column `j + 1` from row `i`
upwards.

When `(i, j + 1)` is a cell of `μ` this set has one element more than column `j` has cells, while
its labels stay in column `j` or `j + 1` under a column permutation of `t`; that is what makes the
Garnir relation apply to it. -/
def garnirSet (t : YoungTableau μ) (i j : ℕ) : Finset (Fin μ.card) :=
  {k | (colIndex t k = j ∧ i ≤ rowIndex t k) ∨ (colIndex t k = j + 1 ∧ rowIndex t k ≤ i)}

@[simp]
theorem mem_garnirSet {t : YoungTableau μ} {i j : ℕ} {k : Fin μ.card} :
    k ∈ garnirSet t i j ↔
      (colIndex t k = j ∧ i ≤ rowIndex t k) ∨ (colIndex t k = j + 1 ∧ rowIndex t k ≤ i) := by
  simp [garnirSet]

/-- Every label of a Garnir set at column `j` lies in a column with at most as many cells as column
`j` has, since columns of a Young diagram shorten to the right. -/
theorem colLen_colIndex_le_colLen_of_mem_garnirSet {t : YoungTableau μ} {i j : ℕ}
    {k : Fin μ.card} (hk : k ∈ garnirSet t i j) : μ.colLen (colIndex t k) ≤ μ.colLen j := by
  rcases mem_garnirSet.mp hk with ⟨hcol, -⟩ | ⟨hcol, -⟩
  · rw [hcol]
  · rw [hcol]
    exact μ.colLen_anti j (j + 1) (Nat.le_succ j)

/-- The cells occupied by a Garnir set: those of column `j` from row `i` down, and those of column
`j + 1` from row `i` up. -/
private theorem image_rowIndex_colIndex_garnirSet (t : YoungTableau μ) (i j : ℕ) :
    (garnirSet t i j).image (fun k => (rowIndex t k, colIndex t k)) =
      {c ∈ μ.cells | (c.2 = j ∧ i ≤ c.1) ∨ (c.2 = j + 1 ∧ c.1 ≤ i)} := by
  ext c
  simp only [Finset.mem_image, mem_garnirSet, Finset.mem_filter]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨rowIndex_colIndex_mem t k, hk⟩
  · rintro ⟨hmem, hc⟩
    refine ⟨t ⟨c, hmem⟩, ?_, ?_⟩ <;> simp [hc]

/-- The cells of column `j` from row `i` down are those of the whole column that the first `i`
rows leave over. -/
private theorem card_filter_cells_col (i j : ℕ) :
    {c ∈ μ.cells | c.2 = j ∧ i ≤ c.1}.card = μ.colLen j - i := by
  have htop : {c ∈ μ.col j | c.1 < i} = {c ∈ {c ∈ μ.cells | c.1 < i} | c.2 = j} := by
    simp [YoungDiagram.col, Finset.filter_filter, and_comm]
  have hbot : {c ∈ μ.col j | ¬ c.1 < i} = {c ∈ μ.cells | c.2 = j ∧ i ≤ c.1} := by
    simp [YoungDiagram.col, Finset.filter_filter]
  have hsplit := Finset.card_filter_add_card_filter_not (s := μ.col j)
    (p := fun c : ℕ × ℕ => c.1 < i)
  rw [htop, hbot, YoungDiagram.card_filter_fst_lt_filter_snd_eq, ← μ.colLen_eq_card] at hsplit
  omega

/-- The cells of column `j + 1` from row `i` up are those of that column in the first `i + 1`
rows, and `(i, j + 1) ∈ μ` says the column reaches that far. -/
private theorem card_filter_cells_col_succ {i j : ℕ} (h : (i, j + 1) ∈ μ) :
    {c ∈ μ.cells | c.2 = j + 1 ∧ c.1 ≤ i}.card = i + 1 := by
  have hlt : i < μ.colLen (j + 1) := YoungDiagram.mem_iff_lt_colLen.mp h
  -- the counting lemma filters the first `i + 1` rows before the column, so its nested filter
  -- has to be flattened into the single filter of the statement
  have hflat : {c ∈ {c ∈ μ.cells | c.1 < i + 1} | c.2 = j + 1} =
      {c ∈ μ.cells | c.2 = j + 1 ∧ c.1 ≤ i} := by
    simp [Finset.filter_filter, and_comm]
  have hcard := YoungDiagram.card_filter_fst_lt_filter_snd_eq μ (i + 1) (j + 1)
  rw [hflat] at hcard
  omega

/-- **A Garnir set is one bigger than the column it straddles.**  Column `j` contributes its cells
from row `i` down and column `j + 1` its cells from row `i` up, and `(i, j + 1) ∈ μ` makes both
counts available. -/
theorem card_garnirSet (t : YoungTableau μ) {i j : ℕ} (h : (i, j + 1) ∈ μ) :
    (garnirSet t i j).card = μ.colLen j + 1 := by
  classical
  have hij : (i, j) ∈ μ := μ.up_left_mem (le_refl i) (Nat.le_succ j) h
  have hi : i < μ.colLen j := YoungDiagram.mem_iff_lt_colLen.mp hij
  have hinj : Function.Injective fun k : Fin μ.card => (rowIndex t k, colIndex t k) :=
    rowIndex_colIndex_injective t
  have hcard := Finset.card_image_of_injective (garnirSet t i j) hinj
  rw [image_rowIndex_colIndex_garnirSet] at hcard
  have hdisj :
      Disjoint {c ∈ μ.cells | c.2 = j ∧ i ≤ c.1} {c ∈ μ.cells | c.2 = j + 1 ∧ c.1 ≤ i} := by
    rw [Finset.disjoint_left]
    rintro c h₁ h₂
    simp only [Finset.mem_filter] at h₁ h₂
    omega
  rw [← hcard, Finset.filter_or, Finset.card_union_of_disjoint hdisj, card_filter_cells_col,
    card_filter_cells_col_succ h]
  omega

/-- **The Garnir relation at a Garnir set.**  If `(i, j + 1)` is a cell of `μ`, the antisymmetrizer
of the Garnir set of `t` at `(i, j)` annihilates the polytabloid of `t`. -/
theorem asAlgebraHom_antisymmetrizerOn_garnirSet_polytabloid_eq_zero (t : YoungTableau μ) {i j : ℕ}
    (h : (i, j + 1) ∈ μ) :
    (permutationModule (shapePartition μ)).ρ.asAlgebraHom (antisymmetrizerOn (garnirSet t i j))
        (polytabloid t) = 0 :=
  asAlgebraHom_antisymmetrizerOn_polytabloid_eq_zero t
    (fun _ hk => colLen_colIndex_le_colLen_of_mem_garnirSet hk)
    (by rw [card_garnirSet t h]; exact Nat.lt_succ_self _)

end YoungTableau

end TauCeti
