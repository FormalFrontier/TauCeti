/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.Young.SemistandardTableau
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.Combinatorics.Enumerative.Partition.Conjugate

/-!
# Kostka numbers

The *content* of a semistandard Young tableau records how often each natural number is used as an
entry, and the *Kostka number* `K_{μ w}` counts the semistandard tableaux of shape `μ` and content
`w`.  This file defines both, proves that the tableaux of a given content are finite, and
establishes the two facts that make the Kostka numbers a triangular array for the dominance order:
the tableau of shape `μ` whose `i`-th row consists of `i`s is the only one of content
`μ.rowLen` (so `K_{μ μ} = 1`), and a tableau of shape `μ` and content `w` forces every partial sum
`∑_{i < k} w i` to be at most the corresponding partial sum of the row lengths of `μ` (so
`K_{μ w} = 0` unless `μ` dominates `w`).

The mechanism behind both is a single observation, `TauCeti.SemistandardYoungTableau.le_entry`: the
entries of a semistandard tableau strictly increase down each column, so the entry in row `i` is at
least `i`, and therefore the cells carrying an entry smaller than `k` all lie in the first `k`
rows.

Mathlib's `SemistandardYoungTableau` fills the cells with natural numbers starting at `0`, so the
alphabet here is `0, 1, 2, …` rather than the classical `1, 2, 3, …` and the content of the
maximal tableau `SemistandardYoungTableau.highestWeight μ` is `μ.rowLen` on the nose.

## Main definitions

* `TauCeti.SemistandardYoungTableau.content`: the content (or weight) of a semistandard Young
  tableau, `content T i` being the number of cells filled with `i`.
* `TauCeti.kostkaNumber`: the number of semistandard Young tableaux of a given shape and content.
* `TauCeti.partitionKostkaNumber`: the Kostka number of two partitions of the same natural number,
  the shape and the content being read off their Young diagrams.

## Main results

* `TauCeti.SemistandardYoungTableau.sum_content_le_sum_take_rowLens`: the partial sums of the
  content of a tableau of shape `μ` are bounded by those of the row lengths of `μ`.
* `TauCeti.SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen`: a tableau of shape `μ`
  and content `μ.rowLen` is the maximal tableau.
* `TauCeti.SemistandardYoungTableau.finite_content_eq`: the tableaux of a fixed shape and content
  are finite, so the Kostka number counts them faithfully.
* `TauCeti.kostkaNumber_rowLen`: `K_{μ μ} = 1`.
* `TauCeti.partitionKostkaNumber_eq_zero_of_not_dominates`: `K_{μ ν} = 0` unless `μ` dominates `ν`.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 2.2.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 1.
-/

public section

namespace TauCeti

namespace SemistandardYoungTableau

variable {μ : YoungDiagram}

/-- The content, or weight, of a semistandard Young tableau: `content T i` is the number of cells
of the shape whose entry is `i`. -/
@[expose]
def content (T : _root_.SemistandardYoungTableau μ) (i : ℕ) : ℕ :=
  (μ.cells.filter fun c => T c.1 c.2 = i).card

/-- The content of a tableau counts the cells carrying a given entry. -/
theorem content_def (T : _root_.SemistandardYoungTableau μ) (i : ℕ) :
    content T i = (μ.cells.filter fun c => T c.1 c.2 = i).card :=
  rfl

/-- The entries of a tableau are exactly the values on which its content is nonzero. -/
theorem mem_image_iff_content_ne_zero (T : _root_.SemistandardYoungTableau μ) (i : ℕ) :
    i ∈ μ.cells.image (fun c => T c.1 c.2) ↔ content T i ≠ 0 := by
  rw [content_def, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  constructor
  · rintro hi
    obtain ⟨c, hc, hci⟩ := Finset.mem_image.mp hi
    exact ⟨c, Finset.mem_filter.mpr ⟨hc, hci⟩⟩
  · rintro ⟨c, hc⟩
    rw [Finset.mem_filter] at hc
    exact Finset.mem_image.mpr ⟨c, hc.1, hc.2⟩

/-- The content of a tableau is finitely supported: it spreads the cells of the shape over the
finitely many entries the tableau uses. -/
theorem finite_support_content (T : _root_.SemistandardYoungTableau μ) :
    (Function.support (content T)).Finite :=
  Set.Finite.subset (μ.cells.image fun c => T c.1 c.2).finite_toSet fun _ hi =>
    (mem_image_iff_content_ne_zero T _).mpr hi

/-- The entries of a semistandard Young tableau increase strictly down a column, so the entry in
row `i` is at least `i`. -/
theorem le_entry (T : _root_.SemistandardYoungTableau μ) {i j : ℕ} (h : (i, j) ∈ μ) :
    i ≤ T i j := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    have hm : (m, j) ∈ μ := μ.up_left_mem (Nat.le_succ m) le_rfl h
    exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih hm) (T.col_strict (Nat.lt_succ_self m) h))

/-- The cells carrying an entry smaller than `k` all lie in the first `k` rows. -/
theorem filter_entry_lt_subset_filter_fst_lt (T : _root_.SemistandardYoungTableau μ) (k : ℕ) :
    (μ.cells.filter fun c => T c.1 c.2 < k) ⊆ μ.cells.filter fun c => c.1 < k := by
  intro c hc
  rw [Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, lt_of_le_of_lt (le_entry T (by simpa using hc.1)) hc.2⟩

/-- The first `k` values of the content of a tableau count the cells carrying an entry smaller
than `k`. -/
theorem sum_content_eq_card_filter (T : _root_.SemistandardYoungTableau μ) (k : ℕ) :
    ∑ i ∈ Finset.range k, content T i = (μ.cells.filter fun c => T c.1 c.2 < k).card := by
  symm
  calc
    (μ.cells.filter fun c => T c.1 c.2 < k).card =
        ∑ i ∈ Finset.range k,
          ((μ.cells.filter fun c => T c.1 c.2 < k).filter fun c => T c.1 c.2 = i).card := by
      refine Finset.card_eq_sum_card_fiberwise fun c hc => ?_
      simp only [Finset.mem_coe, Finset.mem_filter] at hc
      exact Finset.mem_range.mpr hc.2
    _ = ∑ i ∈ Finset.range k, content T i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hik : i < k := Finset.mem_range.mp hi
      refine congrArg Finset.card (Finset.ext fun c => ?_)
      simp only [Finset.mem_filter, and_assoc]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.2 ▸ hik, h.2⟩⟩

/-- The content of a tableau of shape `μ` is a composition of the number of cells of `μ`, once the
range of summation covers all the entries. -/
theorem sum_content_eq_card {T : _root_.SemistandardYoungTableau μ} {N : ℕ}
    (hN : ∀ c ∈ μ.cells, T c.1 c.2 < N) :
    ∑ i ∈ Finset.range N, content T i = μ.card := by
  rw [sum_content_eq_card_filter, Finset.filter_true_of_mem hN]

/-- **Dominance bound for the content of a tableau**: the partial sums of the content of a
semistandard tableau of shape `μ` never exceed the partial sums of the row lengths of `μ`. -/
theorem sum_content_le_sum_take_rowLens (T : _root_.SemistandardYoungTableau μ) (k : ℕ) :
    ∑ i ∈ Finset.range k, content T i ≤ (μ.rowLens.take k).sum := by
  rw [sum_content_eq_card_filter, YoungDiagram.sum_take_rowLens_eq_card_filter_fst]
  exact Finset.card_le_card (filter_entry_lt_subset_filter_fst_lt T k)

/-- The maximal tableau, whose `i`-th row consists of `i`s, has content the row lengths of its
shape. -/
@[simp]
theorem content_highestWeight (μ : YoungDiagram) :
    content (_root_.SemistandardYoungTableau.highestWeight μ) = μ.rowLen := by
  funext i
  rw [content_def, μ.rowLen_eq_card]
  refine congrArg Finset.card (Finset.ext fun c => ?_)
  simp only [_root_.YoungDiagram.mem_row_iff,
    _root_.SemistandardYoungTableau.highestWeight_apply]
  aesop

/-- **Uniqueness of the maximal tableau**: a semistandard tableau of shape `μ` whose content is the
row lengths of `μ` has an `i` in every cell of row `i`, so it is
`SemistandardYoungTableau.highestWeight μ`.

Indeed the cells with entry smaller than `k` lie in the first `k` rows, and the two sets are
counted by the same partial sums, so they agree; taking `k = i + 1` at a cell of row `i` bounds its
entry by `i`, and `TauCeti.SemistandardYoungTableau.le_entry` bounds it below. -/
theorem eq_highestWeight_of_content_eq_rowLen {T : _root_.SemistandardYoungTableau μ}
    (h : content T = μ.rowLen) : T = _root_.SemistandardYoungTableau.highestWeight μ := by
  have key : ∀ i j : ℕ, (i, j) ∈ μ → T i j = i := by
    intro i j hij
    have hcards : (μ.cells.filter fun c => T c.1 c.2 < i + 1).card =
        (μ.cells.filter fun c => c.1 < i + 1).card := by
      rw [← sum_content_eq_card_filter, ← YoungDiagram.sum_range_rowLen_eq_card_filter_fst]
      exact Finset.sum_congr rfl fun k _ => congrFun h k
    have hsets := Finset.eq_of_subset_of_card_le
      (filter_entry_lt_subset_filter_fst_lt T (i + 1)) hcards.ge
    have hmem : ((i, j) : ℕ × ℕ) ∈ μ.cells.filter fun c => T c.1 c.2 < i + 1 := by
      rw [hsets, Finset.mem_filter]
      exact ⟨hij, Nat.lt_succ_self i⟩
    exact le_antisymm (Nat.lt_succ_iff.mp (Finset.mem_filter.mp hmem).2) (le_entry T hij)
  ext i j
  by_cases hij : (i, j) ∈ μ
  · rw [key i j hij, _root_.SemistandardYoungTableau.highestWeight_apply, if_pos hij]
  · rw [T.zeros hij, _root_.SemistandardYoungTableau.highestWeight_apply, if_neg hij]

/-- The semistandard tableaux of a fixed shape and content are finite: their entries all occur in
any one of them, so there are only finitely many values to fill the finitely many cells with. -/
instance finite_content_eq (μ : YoungDiagram) (w : ℕ → ℕ) :
    Finite {T : _root_.SemistandardYoungTableau μ // content T = w} := by
  by_cases hne : Nonempty {T : _root_.SemistandardYoungTableau μ // content T = w}
  swap
  · rw [not_nonempty_iff] at hne
    infer_instance
  obtain ⟨T₀, hT₀⟩ := hne.some
  have hmem : ∀ T : _root_.SemistandardYoungTableau μ, content T = w →
      ∀ c ∈ μ.cells, T c.1 c.2 ∈ μ.cells.image fun d => T₀ d.1 d.2 := by
    intro T hT c hc
    refine (mem_image_iff_content_ne_zero T₀ _).mpr ?_
    rw [congrFun hT₀ (T c.1 c.2), ← congrFun hT (T c.1 c.2)]
    exact (mem_image_iff_content_ne_zero T _).mp (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
  refine Finite.of_injective
    (fun (T : {T : _root_.SemistandardYoungTableau μ // content T = w}) (c : ↥μ.cells) =>
      (⟨T.1 (c : ℕ × ℕ).1 (c : ℕ × ℕ).2, hmem T.1 T.2 _ c.2⟩ :
        ↥(μ.cells.image fun d => T₀ d.1 d.2))) fun T T' hTT' => ?_
  refine Subtype.ext (_root_.SemistandardYoungTableau.ext fun i j => ?_)
  by_cases hij : (i, j) ∈ μ
  · exact congrArg Subtype.val (congrFun hTT' ⟨(i, j), hij⟩)
  · rw [T.1.zeros hij, T'.1.zeros hij]

end SemistandardYoungTableau

/-- The **Kostka number** `K_{μ w}`: the number of semistandard Young tableaux of shape `μ` whose
content is `w`. -/
noncomputable def kostkaNumber (μ : YoungDiagram) (w : ℕ → ℕ) : ℕ :=
  Nat.card {T : _root_.SemistandardYoungTableau μ // SemistandardYoungTableau.content T = w}

/-- **The diagonal Kostka number is `1`**: the maximal tableau is the only semistandard tableau of
shape `μ` whose content is the row lengths of `μ`. -/
@[simp]
theorem kostkaNumber_rowLen (μ : YoungDiagram) : kostkaNumber μ μ.rowLen = 1 := by
  rw [kostkaNumber, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun T T' => Subtype.ext ?_⟩,
    ⟨⟨_root_.SemistandardYoungTableau.highestWeight μ,
      SemistandardYoungTableau.content_highestWeight μ⟩⟩⟩
  rw [SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen T.2,
    SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen T'.2]

/-- **The Kostka numbers are supported on the dominance order**: a nonzero Kostka number
`K_{μ w}` forces every partial sum of `w` to be bounded by the corresponding partial sum of the
row lengths of `μ`. -/
theorem sum_le_sum_take_rowLens_of_kostkaNumber_ne_zero {μ : YoungDiagram} {w : ℕ → ℕ}
    (h : kostkaNumber μ w ≠ 0) (k : ℕ) :
    ∑ i ∈ Finset.range k, w i ≤ (μ.rowLens.take k).sum := by
  obtain ⟨T, hT⟩ := (Nat.card_ne_zero.mp h).1
  calc
    ∑ i ∈ Finset.range k, w i = ∑ i ∈ Finset.range k, SemistandardYoungTableau.content T i :=
      Finset.sum_congr rfl fun i _ => (congrFun hT i).symm
    _ ≤ (μ.rowLens.take k).sum := SemistandardYoungTableau.sum_content_le_sum_take_rowLens T k

/-- The row lengths of the Young diagram of a partition are its decreasingly sorted parts, padded
by zeros. -/
theorem rowLen_diagramOf {n : ℕ} (ν : n.Partition) (i : ℕ) :
    (diagramOf ν).rowLen i = (ν.parts.sort (· ≥ ·)).getD i 0 := by
  rw [← YoungDiagram.getD_rowLens, rowLens_diagramOf]

/-- The **Kostka number of two partitions** of the same natural number: the number of semistandard
tableaux of the shape of `μ` whose content is the row lengths of the diagram of `ν`, that is (by
`TauCeti.rowLen_diagramOf`), the tableaux using the entry `i` exactly as often as the `i`-th
largest part of `ν` prescribes. -/
noncomputable def partitionKostkaNumber {n : ℕ} (μ ν : n.Partition) : ℕ :=
  kostkaNumber (diagramOf μ) (diagramOf ν).rowLen

/-- A partition contributes exactly one tableau to its own Kostka number. -/
@[simp]
theorem partitionKostkaNumber_self {n : ℕ} (μ : n.Partition) : partitionKostkaNumber μ μ = 1 :=
  kostkaNumber_rowLen _

/-- **The Kostka numbers are triangular for the dominance order**: `K_{μ ν} ≠ 0` forces `μ` to
dominate `ν`. -/
theorem dominates_of_partitionKostkaNumber_ne_zero {n : ℕ} {μ ν : n.Partition}
    (h : partitionKostkaNumber μ ν ≠ 0) : Dominates μ ν := by
  refine dominates_iff.mpr fun k => ?_
  have hk := sum_le_sum_take_rowLens_of_kostkaNumber_ne_zero h k
  rwa [YoungDiagram.sum_range_rowLen_eq_card_filter_fst,
    ← YoungDiagram.sum_take_rowLens_eq_card_filter_fst, rowLens_diagramOf,
    rowLens_diagramOf] at hk

/-- **The Kostka numbers vanish off the dominance order**: there is no semistandard tableau of
shape `μ` and content `ν` unless `μ` dominates `ν`. -/
theorem partitionKostkaNumber_eq_zero_of_not_dominates {n : ℕ} {μ ν : n.Partition}
    (h : ¬ Dominates μ ν) : partitionKostkaNumber μ ν = 0 :=
  not_not.mp fun h' => h (dominates_of_partitionKostkaNumber_ne_zero h')

end TauCeti
