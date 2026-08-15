/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Combinatorics.Enumerative.Partition.Conjugate
public import TauCeti.Combinatorics.Young.Diagram
public import TauCeti.Combinatorics.Young.Tableau

/-!
# The dominance lemma for tableaux

Two tableaux of different shapes can be compared by asking how the rows of one meet the columns
of the other.  The **dominance lemma** says that if the labels of each row of a `μ`-tableau `s`
land in pairwise distinct columns of a `ν`-tableau `t`, then `ν` dominates `μ`.

The proof is a double count.  Write the labels of the first `k` rows of `s` as a set `X`; it has
`μ₁ + ⋯ + μ_k` elements.  Inside a fixed column of `t` each of those `k` rows contributes at most
one label, so `X` meets that column in at most `k` labels, and of course in at most as many
labels as the column is long.  Summing over the columns of `t`, the cells of `ν` in its first `k`
rows -- of which there are exactly `min k (colLen j)` in column `j` -- already accommodate `X`,
so `μ₁ + ⋯ + μ_k ≤ ν₁ + ⋯ + ν_k`.

The counting core `YoungDiagram.card_filter_le_sum_take_rowLens` is stated for an
arbitrary finite index type carrying a row function and an injection into the cells: this is what
the tableau statement, where the index type is the set of labels, unfolds to, and it keeps the
counting free of any tableau bookkeeping.  The lemma is the combinatorial engine behind the
triangularity of the Specht modules in the dominance order: a homomorphism from the Specht module
`S^ν` into the permutation module `M^μ` is nonzero only when `ν` dominates `μ`, because the
column antisymmetrizer of a `ν`-tableau kills every `μ`-tabloid unless the row/column condition
below holds.

## Main results

* `YoungDiagram.card_filter_le_sum_take_rowLens`: the counting core.
* `TauCeti.YoungTableau.sum_take_rowLens_le_of_injective`: the dominance lemma for two tableaux.
* `TauCeti.dominates_of_rowIndex_colIndex_injective`: the dominance lemma for partitions.
* `TauCeti.exists_ne_rowIndex_eq_colIndex_eq_of_not_dominates`: its contrapositive, producing two
  distinct labels sharing a row of `s` and a column of `t` when dominance fails.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Lemma 3.15.
* B. E. Sagan, *The Symmetric Group*, 2nd edition (2001), Lemma 2.2.4.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 4, "Distinctness and completeness".
-/

public section

namespace YoungDiagram

/-- **The counting core of the dominance lemma.** Let the elements of a finite type `α` be
labelled by a *row* `r a : ℕ` and placed in the cells of a Young diagram `lam` by an injection
`f`, in such a way that the row of an element together with the column of its cell determines
the element.  Then the elements of row less than `k` are no more numerous than the cells of `lam`
in its first `k` rows.

The hypothesis `hcol` is the condition that elements sharing a row occupy pairwise distinct
columns; it is what bounds by `k` the number of elements landing in any one column. -/
theorem card_filter_le_sum_take_rowLens {α : Type*} [Fintype α] (lam : YoungDiagram)
    (r : α → ℕ) (f : α → ℕ × ℕ) (hmem : ∀ a, f a ∈ lam.cells) (hinj : Function.Injective f)
    (hcol : ∀ a b, r a = r b → (f a).2 = (f b).2 → a = b) (k : ℕ) :
    (Finset.univ.filter fun a => r a < k).card ≤ (lam.rowLens.take k).sum := by
  classical
  rw [sum_take_rowLens_eq_card_filter_fst]
  -- Every column index in sight is smaller than the length of the top row.
  have hlt : ∀ c ∈ lam.cells, c.2 ∈ Finset.range (lam.rowLen 0) := by
    intro c hc
    refine Finset.mem_range.mpr (lt_of_lt_of_le ?_ (lam.rowLen_anti 0 c.1 c.1.zero_le))
    exact _root_.YoungDiagram.mem_iff_lt_rowLen.mp ((_root_.YoungDiagram.mem_cells c).mp hc)
  -- Split both sides into their columns.
  rw [Finset.card_eq_sum_card_fiberwise (f := fun a => (f a).2)
      (t := Finset.range (lam.rowLen 0)) fun a _ => hlt _ (hmem a),
    Finset.card_eq_sum_card_fiberwise (f := fun c : ℕ × ℕ => c.2)
      (t := Finset.range (lam.rowLen 0)) fun c hc =>
      hlt c (Finset.mem_filter.mp hc).1]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [card_filter_fst_lt_filter_snd_eq lam k j]
  have hfib : ∀ a ∈ ((Finset.univ.filter fun a => r a < k).filter fun a => (f a).2 = j : Finset α),
      r a < k ∧ (f a).2 = j := by
    intro a ha
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ha
  -- In a fixed column, the elements are separated by their rows, and they fit in the column.
  refine le_min (le_of_le_of_eq ?_ (Finset.card_range k))
    (le_of_le_of_eq ?_ lam.colLen_eq_card.symm)
  · refine Finset.card_le_card_of_injOn r (fun a ha => ?_) fun a ha b hb hab => ?_
    · exact Finset.mem_range.mpr (hfib a ha).1
    · exact hcol a b hab (((hfib a ha).2).trans (hfib b hb).2.symm)
  · refine Finset.card_le_card_of_injOn f (fun a ha => ?_) hinj.injOn
    exact _root_.YoungDiagram.mem_col_iff.mpr
      ⟨(_root_.YoungDiagram.mem_cells _).mp (hmem a), (hfib a ha).2⟩

end YoungDiagram

namespace TauCeti

namespace YoungTableau

variable {lam m : YoungDiagram}

/-- **The dominance lemma.** Let `s` be an `m`-tableau and `t` a `lam`-tableau whose labels are
identified by `σ`.  If the labels of each row of `s` occupy pairwise distinct columns of `t`,
then every partial sum of the row lengths of `m` is at most the corresponding partial sum for
`lam`.

The hypothesis says that no row of `s` meets a column of `t` in two distinct labels, once the
labels are matched up by `σ`. -/
theorem sum_take_rowLens_le_of_injective (t : YoungTableau lam) (s : YoungTableau m)
    (σ : Fin m.card ≃ Fin lam.card)
    (h : ∀ x y, rowIndex s x = rowIndex s y → colIndex t (σ x) = colIndex t (σ y) → x = y)
    (k : ℕ) : (m.rowLens.take k).sum ≤ (lam.rowLens.take k).sum := by
  classical
  rw [← card_filter_rowIndex_lt s k]
  refine YoungDiagram.card_filter_le_sum_take_rowLens lam (rowIndex s)
    (fun x => ((t.symm (σ x) : ↥lam.cells) : ℕ × ℕ)) (fun x => (t.symm (σ x)).2)
    (fun x y hxy => σ.injective (t.symm.injective (Subtype.ext hxy))) (fun x y hr hc => ?_) k
  exact h x y hr (by simpa only [colIndex_def] using hc)

end YoungTableau

open YoungTableau in
/-- **The dominance lemma for partitions.** If the labels of each row of a `μ`-tableau `s` land
in pairwise distinct columns of a `ν`-tableau `t`, along an identification `σ` of their labels,
then `ν` dominates `μ`. -/
theorem dominates_of_rowIndex_colIndex_injective {n : ℕ} {μ ν : n.Partition}
    (t : YoungTableau (diagramOf ν)) (s : YoungTableau (diagramOf μ))
    (σ : Fin (diagramOf μ).card ≃ Fin (diagramOf ν).card)
    (h : ∀ x y, rowIndex s x = rowIndex s y → colIndex t (σ x) = colIndex t (σ y) → x = y) :
    Dominates ν μ := by
  refine dominates_iff.mpr fun k => ?_
  simpa only [rowLens_diagramOf] using sum_take_rowLens_le_of_injective t s σ h k

open YoungTableau in
/-- **The contrapositive of the dominance lemma.** When `ν` fails to dominate `μ`, every
`ν`-tableau has a column meeting a row of every `μ`-tableau in two distinct labels. -/
theorem exists_ne_rowIndex_eq_colIndex_eq_of_not_dominates {n : ℕ} {μ ν : n.Partition}
    (t : YoungTableau (diagramOf ν)) (s : YoungTableau (diagramOf μ))
    (σ : Fin (diagramOf μ).card ≃ Fin (diagramOf ν).card) (h : ¬Dominates ν μ) :
    ∃ x y, x ≠ y ∧ rowIndex s x = rowIndex s y ∧ colIndex t (σ x) = colIndex t (σ y) := by
  by_contra hcon
  refine h (dominates_of_rowIndex_colIndex_injective t s σ fun x y hr hc => ?_)
  by_contra hxy
  exact hcon ⟨x, y, hxy, hr, hc⟩

end TauCeti
