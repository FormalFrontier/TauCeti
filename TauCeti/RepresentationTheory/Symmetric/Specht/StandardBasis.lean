/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import TauCeti.Combinatorics.Young.StandardTableau.Order
public import TauCeti.RepresentationTheory.Symmetric.Specht.Straightening

/-!
# The standard basis of the Specht module

The polytabloid `e_t` of a `μ`-tableau `t` is the signed sum, over the column group of `t`, of the
tabloids `{q t}`, and the Specht module `S^μ` is the span of all of them.  This file proves that
the polytabloids of the **standard** tableaux -- those increasing along rows and down columns --
are a basis of `S^μ`, so that its dimension is the number `f^μ` of standard Young tableaux of
shape `μ`.

## Linear independence

The first half is the triangularity of the standard polytabloids against the tabloid basis.  Order
the tabloids by **dominance**: `{t}` dominates `{u}` when, for every `m` and every `i`, at least as
many of the labels below `m` sit in the first `i + 1` rows of `t` as sit in the first `i + 1` rows
of `u` (`TauCeti.YoungTableau.rowCount`, `TauCeti.YoungTableau.TabloidDominates`).  Two facts about
that order do the work.

* **The tabloid of a standard tableau is the largest one occurring in its polytabloid**
  (`TauCeti.YoungTableau.tabloidDominates_relabel_of_mem_colSubgroup`).  Fix a column `j` and a row
  bound `i`.  The labels of `T` in column `j` and in the first `i + 1` rows are, because `T`
  increases down its columns, exactly the smallest ones of that column, so no other set of that
  many labels of the column has more members below a given `m`.  A column permutation `q` replaces
  them by another such set, and summing the resulting inequality over the columns is the claim.
* **A standard tableau is determined by its tabloid**
  (`TauCeti.StandardYoungTableau.rowIndex_injective`), since a standard tableau writes the labels
  of each row in increasing order.

Dominance is only a partial order (antisymmetric up to equality of tabloids,
`TauCeti.YoungTableau.TabloidDominates.antisymm`), so the maximum is taken along a numerical
weight private to this file, the sum of all the counts in the range where they can differ:
dominance makes it larger, and a dominating tableau of no greater weight has every count equal,
which pins the rows down.  Taking the standard tableau of largest weight among those with a nonzero
coefficient, its tabloid can occur in no other standard polytabloid of the combination, and its
coefficient is the coefficient of that tabloid in the combination, hence zero.

## Spanning: the straightening algorithm

The second half rewrites an arbitrary polytabloid into standard ones by two moves, each of which
increases a numerical measure of the tableau that is bounded above, so that the rewriting
terminates.

* If two labels of one column of `t` are out of order, exchanging them is a permutation of the
  column group of `t`, so it changes the polytabloid only by its sign
  (`TauCeti.YoungTableau.polytabloid_relabel_of_mem_colSubgroup`).
* If the columns of `t` increase but two labels of one row are out of order, then two labels in
  *adjacent* columns of one row are, and at that cell the straightening step
  `TauCeti.YoungTableau.polytabloid_mem_span_polytabloid_relabel_garnirSet` writes `e_t` in terms
  of the polytabloids of the relabelings by the permutations of the Garnir set that move a label
  between the two columns it straddles.

The measure is the pair of moments `∑_k c_k · k` and `∑_k r_k · k`, weighting each label by the
index of its column, respectively of its row.  The first move fixes every label in its column and
raises the row moment, since it moves the smaller of the two labels up.  The second move raises the
column moment: because the columns of `t` increase and its row does not at the chosen cell, every
label of the Garnir set lying in the earlier column exceeds every label of it lying in the later
one, so a permutation of the set that does not preserve the columns exchanges labels of the earlier
column for strictly smaller ones.  Weighting the column moment heavily enough that a gain in it
outweighs any loss of row moment combines the two into one measure.

A tableau on which neither move applies increases down its columns and along its rows, so it is
standard (`TauCeti.StandardYoungTableau.exists_toTableau_eq_iff`).

## Main results

* `TauCeti.YoungTableau.TabloidDominates.antisymm`: dominance both ways is equality of tabloids.
* `TauCeti.YoungTableau.tabloidDominates_relabel_of_mem_colSubgroup`: a column permutation of a
  standard tableau lowers its tabloid.
* `TauCeti.linearIndependent_polytabloid`: the standard polytabloids are linearly independent.
* `TauCeti.YoungTableau.polytabloid_mem_span_polytabloid_standard`: **the straightening
  algorithm**, every polytabloid is a rational combination of the standard ones, and
  `TauCeti.spechtSubrepresentation_eq_span_standard`: they therefore span the Specht module.
* `TauCeti.standardPolytabloidBasis`: **the standard basis** of the Specht module.
* `TauCeti.finrank_spechtSubrepresentation` and `TauCeti.finrank_spechtModule`: **`dim S^μ = f^μ`.**

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Sections 7 and 8.
* [B. E. Sagan, *The Symmetric Group*][sagan2001], Sections 2.5 and 2.6.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 5, the standard basis of the Specht module.
-/

public section

namespace TauCeti

open scoped BigOperators

namespace YoungTableau

variable {μ : YoungDiagram}

/-! ### Counting the labels of a tableau by row -/

/-- The number of labels below `m` that the `μ`-tableau `t` places in one of its first `i + 1`
rows.  It depends on `t` only through its tabloid. -/
def rowCount (t : YoungTableau μ) (m i : ℕ) : ℕ :=
  (Finset.univ.filter fun k : Fin μ.card => (k : ℕ) < m ∧ rowIndex t k ≤ i).card

theorem rowCount_congr {t u : YoungTableau μ} (h : rowIndex t = rowIndex u) (m i : ℕ) :
    rowCount t m i = rowCount u m i := by
  rw [rowCount, rowCount, h]

/-- Passing from the labels below `k` to the labels below `k + 1` adds the label `k` itself. -/
theorem rowCount_succ (t : YoungTableau μ) (k : Fin μ.card) (i : ℕ) :
    rowCount t ((k : ℕ) + 1) i = rowCount t (k : ℕ) i + if rowIndex t k ≤ i then 1 else 0 := by
  classical
  have hsingle : (if rowIndex t k ≤ i then 1 else 0) =
      ∑ x : Fin μ.card, if x = k then (if rowIndex t x ≤ i then 1 else 0) else 0 := by
    simp
  rw [rowCount, rowCount, Finset.card_filter, Finset.card_filter, hsingle,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rcases lt_trichotomy (x : ℕ) (k : ℕ) with h | h | h
  · have hx : x ≠ k := fun he => absurd (congrArg Fin.val he) h.ne
    simp [h, Nat.lt_succ_of_lt h, hx]
  · have hx : x = k := Fin.ext h
    subst hx
    simp
  · have hx : x ≠ k := fun he => absurd (congrArg Fin.val he) h.ne'
    simp [Nat.not_lt.mpr h.le, Nat.not_lt.mpr h, hx]

/-- **The counts determine the rows.**  A tableau puts a label in the first row for which the
count jumps. -/
theorem rowIndex_eq_of_rowCount_eq {t u : YoungTableau μ}
    (h : ∀ m ≤ μ.card, ∀ i < μ.colLen 0, rowCount t m i = rowCount u m i) :
    rowIndex t = rowIndex u := by
  funext k
  have key : ∀ i < μ.colLen 0, (rowIndex t k ≤ i ↔ rowIndex u k ≤ i) := by
    intro i hi
    have h1 := h ((k : ℕ) + 1) k.isLt i hi
    rw [rowCount_succ, rowCount_succ, h (k : ℕ) k.isLt.le i hi] at h1
    have h2 : (if rowIndex t k ≤ i then 1 else 0) = if rowIndex u k ≤ i then (1 : ℕ) else 0 :=
      Nat.add_left_cancel h1
    constructor
    · intro hp
      by_contra hq
      rw [ite_eq_left hp, ite_eq_right hq] at h2
      exact absurd h2 one_ne_zero
    · intro hq
      by_contra hp
      rw [ite_eq_right hp, ite_eq_left hq] at h2
      exact absurd h2 zero_ne_one
  exact le_antisymm ((key (rowIndex u k) (rowIndex_lt_colLen_zero u k)).mpr le_rfl)
    ((key (rowIndex t k) (rowIndex_lt_colLen_zero t k)).mp le_rfl)

/-! ### The dominance order on tabloids -/

/-- **The dominance order on tabloids.** The tabloid of `t` dominates the tabloid of `u` when, for
every `m` and `i`, the labels below `m` that `t` puts in its first `i + 1` rows are at least as
many as those that `u` does. -/
def TabloidDominates (t u : YoungTableau μ) : Prop :=
  ∀ m i : ℕ, rowCount u m i ≤ rowCount t m i

theorem tabloidDominates_refl (t : YoungTableau μ) : TabloidDominates t t := fun _ _ => le_rfl

theorem TabloidDominates.trans {t u v : YoungTableau μ} (h : TabloidDominates t u)
    (h' : TabloidDominates u v) : TabloidDominates t v := fun m i => (h' m i).trans (h m i)

/-- **Dominance depends on the tableaux only through their tabloids.** -/
theorem tabloidDominates_congr {t t' u u' : YoungTableau μ} (ht : tabloid t = tabloid t')
    (hu : tabloid u = tabloid u') : TabloidDominates t u ↔ TabloidDominates t' u' := by
  rw [tabloid_eq_iff_rowIndex_eq] at ht hu
  exact forall_congr' fun m => forall_congr' fun i => by
    rw [rowCount_congr ht m i, rowCount_congr hu m i]

/-- **Dominance is antisymmetric up to equality of tabloids.** -/
theorem TabloidDominates.antisymm {t u : YoungTableau μ} (h : TabloidDominates t u)
    (h' : TabloidDominates u t) : tabloid t = tabloid u :=
  tabloid_eq_iff_rowIndex_eq.mpr
    (rowIndex_eq_of_rowCount_eq fun m _ i _ => le_antisymm (h' m i) (h m i))

/-- A numerical refinement of dominance: the total of all the counts that can differ.  Dominance
increases it, and a dominating tableau of no greater weight has the same rows
(`rowIndex_eq_of_tabloidDominates`). -/
private def rowWeight (t : YoungTableau μ) : ℕ :=
  ∑ m ∈ Finset.range (μ.card + 1), ∑ i ∈ Finset.range (μ.colLen 0), rowCount t m i

private theorem rowWeight_congr {t u : YoungTableau μ} (h : rowIndex t = rowIndex u) :
    rowWeight t = rowWeight u := by
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => rowCount_congr h m i

private theorem rowWeight_le_of_tabloidDominates {t u : YoungTableau μ} (h : TabloidDominates t u) :
    rowWeight u ≤ rowWeight t :=
  Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun i _ => h m i

/-- **Dominance with no gain of weight is equality of tabloids.** -/
private theorem rowIndex_eq_of_tabloidDominates {t u : YoungTableau μ} (h : TabloidDominates t u)
    (hw : rowWeight t ≤ rowWeight u) : rowIndex u = rowIndex t := by
  have hinner := (Finset.sum_eq_sum_iff_of_le
    fun m (_ : m ∈ Finset.range (μ.card + 1)) => Finset.sum_le_sum fun i _ => h m i).mp
      (le_antisymm (rowWeight_le_of_tabloidDominates h) hw)
  refine rowIndex_eq_of_rowCount_eq fun m hm i hi => ?_
  exact (Finset.sum_eq_sum_iff_of_le fun i _ => h m i).mp
    (hinner m (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))) i (Finset.mem_range.mpr hi)

/-! ### A column permutation lowers the tabloid of a standard tableau -/

/-- If `A` is a lower set of `S`, then no subset of `S` with at most as many members as `A` meets a
lower set `p` in more members than `A` does: either `p` contains all of `A`, and cardinality
settles it, or `p` misses a member of `A` and hence lies inside `A` already. -/
private theorem card_filter_le_of_isLowerSet {α : Type*} [LinearOrder α]
    {S A C : Finset α} {p : α → Prop} [DecidablePred p] (hCS : C ⊆ S) (hcard : C.card ≤ A.card)
    (hdown : ∀ x ∈ A, ∀ y ∈ S, y < x → y ∈ A) (hp : ∀ x y : α, y < x → p x → p y) :
    (C.filter p).card ≤ (A.filter p).card := by
  by_cases hall : ∀ x ∈ A, p x
  · rw [Finset.filter_true_of_mem hall]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans hcard
  · obtain ⟨a, ha, hpa⟩ : ∃ a ∈ A, ¬ p a := by
      by_contra hc
      exact hall fun x hx => not_not.mp fun hpx => hc ⟨x, hx, hpx⟩
    refine Finset.card_le_card fun y hy => ?_
    obtain ⟨hyC, hpy⟩ := Finset.mem_filter.mp hy
    have hlt : y < a := by
      rcases lt_trichotomy y a with h | h | h
      · exact h
      · exact absurd (h ▸ hpy) hpa
      · exact absurd (hp y a h hpy) hpa
    exact Finset.mem_filter.mpr ⟨hdown a ha y (hCS hyC) hlt, hpy⟩

/-- **A column permutation lowers the tabloid of a standard Young tableau.**  In each column of a
standard tableau the labels of the first rows are the smallest ones of the column, so moving them
about inside their columns can only push labels down. -/
theorem tabloidDominates_relabel_of_mem_colSubgroup (T : StandardYoungTableau μ)
    {q : Equiv.Perm (Fin μ.card)} (hq : q ∈ colSubgroup T.toTableau) :
    TabloidDominates T.toTableau (relabel q T.toTableau) := by
  classical
  have hcol : ∀ k, colIndex T.toTableau (q k) = colIndex T.toTableau k := mem_colSubgroup.mp hq
  intro m i
  -- index the labels of the relabelled tableau by their preimages
  have hreindex : rowCount (relabel q T.toTableau) m i =
      (Finset.univ.filter fun x : Fin μ.card =>
        ((q x : Fin μ.card) : ℕ) < m ∧ rowIndex T.toTableau x ≤ i).card := by
    refine Finset.card_equiv (q⁻¹ : Equiv.Perm (Fin μ.card)) fun k => ?_
    simp [rowIndex_relabel]
  -- both counts split over the columns of `T`
  have hmemJ : ∀ x : Fin μ.card,
      colIndex T.toTableau x ∈ Finset.image (colIndex T.toTableau) Finset.univ := fun x =>
    Finset.mem_image_of_mem _ (Finset.mem_univ x)
  rw [hreindex, rowCount,
    Finset.card_eq_sum_card_fiberwise (f := colIndex T.toTableau)
      (t := Finset.image (colIndex T.toTableau) Finset.univ) fun x _ => hmemJ x,
    Finset.card_eq_sum_card_fiberwise (f := colIndex T.toTableau)
      (t := Finset.image (colIndex T.toTableau) Finset.univ) fun x _ => hmemJ x]
  refine Finset.sum_le_sum fun j _ => ?_
  -- the labels of column `j` in the first `i + 1` rows, and their images under `q`
  set A : Finset (Fin μ.card) :=
    Finset.univ.filter fun x => colIndex T.toTableau x = j ∧ rowIndex T.toTableau x ≤ i with hA
  have hleft : ((Finset.univ.filter fun x : Fin μ.card =>
        ((q x : Fin μ.card) : ℕ) < m ∧ rowIndex T.toTableau x ≤ i).filter
      fun x => colIndex T.toTableau x = j) =
      A.filter fun x => ((q x : Fin μ.card) : ℕ) < m := by
    ext x
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hright : ((Finset.univ.filter fun x : Fin μ.card =>
        (x : ℕ) < m ∧ rowIndex T.toTableau x ≤ i).filter fun x => colIndex T.toTableau x = j) =
      A.filter fun x : Fin μ.card => (x : ℕ) < m := by
    ext x
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [hleft, hright]
  -- the image of `A` under `q` is another set of that many labels of the column
  have himage : (A.filter fun x : Fin μ.card => ((q x : Fin μ.card) : ℕ) < m).card =
      ((A.image q).filter fun y : Fin μ.card => (y : ℕ) < m).card := by
    rw [Finset.filter_image, Finset.card_image_of_injective _ q.injective]
  rw [himage]
  refine card_filter_le_of_isLowerSet (S := Finset.univ.filter fun x => colIndex T.toTableau x = j)
    (fun y hy => ?_) (le_of_eq (Finset.card_image_of_injective _ q.injective))
    (fun x hx y hy hlt => ?_) fun _ _ hxy hx => (Fin.lt_def.mp hxy).trans hx
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hcol x]
    exact hx.1
  · simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
    refine ⟨hy, le_of_lt (lt_of_lt_of_le ?_ hx.2)⟩
    exact (T.lt_iff_rowIndex_lt (hy.trans hx.1.symm)).mp hlt

end YoungTableau

/-! ### Linear independence of the standard polytabloids -/

open YoungTableau

/-- **The standard polytabloids are linearly independent.**  Among the standard tableaux carrying
a nonzero coefficient, one of largest weight has a tabloid that no other standard polytabloid of
the combination reaches, so its coefficient is read off the combination. -/
theorem linearIndependent_polytabloid (μ : YoungDiagram) :
    LinearIndependent ℚ fun T : StandardYoungTableau μ => polytabloid T.toTableau := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum T₁ hT₁
  by_contra hg
  obtain ⟨T₀, hT₀, hmax⟩ := Finset.exists_max_image (s.filter fun T => g T ≠ 0)
    (fun T => rowWeight T.toTableau) ⟨T₁, Finset.mem_filter.mpr ⟨hT₁, hg⟩⟩
  obtain ⟨hT₀s, hg₀⟩ := Finset.mem_filter.mp hT₀
  -- no other standard polytabloid of the combination reaches the tabloid of `T₀`
  have hzero : ∀ T ∈ s, T ≠ T₀ →
      (g T • polytabloid T.toTableau).coeff (tabloid T₀.toTableau) = 0 := by
    intro T hTs hTne
    rcases eq_or_ne (g T) 0 with h0 | h0
    · simp [h0]
    have hvanish : (polytabloid T.toTableau).coeff (tabloid T₀.toTableau) = 0 := by
      refine polytabloid_coeff_eq_zero_of_forall_ne _ fun q hq hcontra => hTne ?_
      have hdom : TabloidDominates T.toTableau (relabel q T.toTableau) :=
        tabloidDominates_relabel_of_mem_colSubgroup T hq
      have hrow : rowIndex (relabel q T.toTableau) = rowIndex T₀.toTableau := by
        rw [← tabloid_eq_iff_rowIndex_eq, tabloid_relabel, hcontra]
      have hw : rowWeight T.toTableau ≤ rowWeight (relabel q T.toTableau) := by
        rw [rowWeight_congr hrow]
        exact hmax T (Finset.mem_filter.mpr ⟨hTs, h0⟩)
      exact StandardYoungTableau.rowIndex_injective μ
        ((rowIndex_eq_of_tabloidDominates hdom hw).symm.trans hrow)
    simp [hvanish]
  -- so the coefficient of that tabloid in the combination is the coefficient of `T₀`
  have hcoeff : (∑ T ∈ s, g T • polytabloid T.toTableau).coeff (tabloid T₀.toTableau) = 0 := by
    rw [hsum]
    simp
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    Finset.sum_eq_single_of_mem T₀ hT₀s hzero] at hcoeff
  simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, polytabloid_coeff_tabloid,
    smul_eq_mul, mul_one] at hcoeff
  exact hg₀ hcoeff

/-! ### The straightening measure -/

namespace YoungTableau

variable {μ : YoungDiagram}

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

/-! ### Exchanging two labels of one column -/

private theorem sum_mul_swap (f : Fin μ.card → ℕ) {x y : Fin μ.card} (hne : x ≠ y) :
    (∑ k : Fin μ.card, f k * ((Equiv.swap x y k : Fin μ.card) : ℕ)) +
        (f x * (x : ℕ) + f y * (y : ℕ)) =
      (∑ k : Fin μ.card, f k * (k : ℕ)) + (f x * (y : ℕ) + f y * (x : ℕ)) := by
  classical
  have hsplit : ∀ g : Fin μ.card → ℕ,
      ∑ k : Fin μ.card, g k = g x + (g y + ∑ k ∈ (Finset.univ.erase x).erase y, g k) := by
    intro g
    rw [← Finset.add_sum_erase _ g (Finset.mem_univ x),
      ← Finset.add_sum_erase _ g (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ y⟩)]
  have htail : ∀ k ∈ (Finset.univ.erase x).erase y,
      f k * ((Equiv.swap x y k : Fin μ.card) : ℕ) = f k * (k : ℕ) := by
    intro k hk
    obtain ⟨hky, hk'⟩ := Finset.mem_erase.mp hk
    rw [Equiv.swap_apply_of_ne_of_ne (Finset.mem_erase.mp hk').1 hky]
  rw [hsplit fun k => f k * ((Equiv.swap x y k : Fin μ.card) : ℕ), hsplit fun k => f k * (k : ℕ),
    Finset.sum_congr rfl htail, Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

/-- **Exchanging two labels of one column that are out of order increases the straightening
measure.**  The exchange leaves every label in its own column, so the column moment is unchanged,
while the smaller of the two labels moves to the earlier row and the row moment grows. -/
private theorem straightWeight_lt_of_swap {t : YoungTableau μ} {x y : Fin μ.card}
    (hcol : colIndex t x = colIndex t y) (hrow : rowIndex t x < rowIndex t y) (hyx : y < x) :
    straightWeight t < straightWeight (relabel (Equiv.swap x y) t) := by
  have hne : x ≠ y := fun h => absurd (congrArg (rowIndex t) h) hrow.ne
  have hc := sum_mul_swap (colIndex t) hne
  have hr := sum_mul_swap (rowIndex t) hne
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

/-! ### The Garnir step increases the measure -/

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

/-- A set of labels every one of which is smaller than every label of a second set of the same
size has the smaller sum. -/
private theorem sum_lt_sum_of_forall_lt {U V : Finset (Fin μ.card)} (hcard : V.card = U.card)
    (hU : U.Nonempty) (hlt : ∀ u ∈ U, ∀ v ∈ V, (v : ℕ) < (u : ℕ)) :
    ∑ v ∈ V, (v : ℕ) < ∑ u ∈ U, (u : ℕ) := by
  classical
  have hV : V.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact Finset.card_pos.mpr hU)
  obtain ⟨w, hwV, hwm⟩ :=
    Finset.mem_image.mp ((V.image fun v : Fin μ.card => (v : ℕ)).max'_mem (hV.image _))
  have hVle : ∀ v ∈ V, (v : ℕ) ≤ (V.image fun v : Fin μ.card => (v : ℕ)).max' (hV.image _) :=
    fun v hv => Finset.le_max' _ _ (Finset.mem_image_of_mem _ hv)
  have hUge : ∀ u ∈ U,
      (V.image fun v : Fin μ.card => (v : ℕ)).max' (hV.image _) + 1 ≤ (u : ℕ) :=
    fun u hu => hwm ▸ hlt u hu w hwV
  calc ∑ v ∈ V, (v : ℕ)
      ≤ V.card * (V.image fun v : Fin μ.card => (v : ℕ)).max' (hV.image _) := by
        simpa [smul_eq_mul] using Finset.sum_le_card_nsmul V _ _ hVle
    _ < U.card * ((V.image fun v : Fin μ.card => (v : ℕ)).max' (hV.image _) + 1) := by
        rw [hcard]
        exact mul_lt_mul_of_pos_left (Nat.lt_succ_self _) (Finset.card_pos.mpr hU)
    _ ≤ ∑ u ∈ U, (u : ℕ) := by
        simpa [smul_eq_mul] using Finset.card_nsmul_le_sum U _ _ hUge

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

/-- **A permutation of a set that does not preserve a prescribed part increases the sum of the
other part.**  If every label of `A` exceeds every label of `X \ A`, and `σ` permutes `X` without
mapping `A` to itself, then `σ` moves some label of `A` into the image of `X \ A`, exchanging it
for a strictly smaller one, so that image has the larger sum. -/
private theorem sum_lt_sum_image_sdiff {X A : Finset (Fin μ.card)}
    {σ : Equiv.Perm (Fin μ.card)} (hAX : A ⊆ X) (hXimg : X.image σ = X)
    (himg : A.image σ ≠ A)
    (hlt : ∀ a ∈ A, ∀ b ∈ X \ A, (b : ℕ) < (a : ℕ)) :
    ∑ z ∈ X \ A, (z : ℕ) < ∑ z ∈ (X \ A).image σ, (z : ℕ) := by
  classical
  have hmemX : ∀ k ∈ X, σ k ∈ X := fun k hk => hXimg ▸ Finset.mem_image_of_mem σ hk
  have hXA : X \ (X \ A) = A := Finset.sdiff_sdiff_eq_self hAX
  have hcard : ((X \ A).image σ).card = (X \ A).card :=
    Finset.card_image_of_injective _ σ.injective
  have hBsub : (X \ A).image σ ⊆ X := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    exact hmemX k (Finset.sdiff_subset hk)
  -- the image of the second part is not the second part again, since `A` is not preserved
  have hne : (X \ A).image σ ≠ X \ A := by
    intro heq
    refine himg (Finset.eq_of_subset_of_card_le (fun z hz => ?_)
      (le_of_eq (Finset.card_image_of_injective _ σ.injective).symm))
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    have hnot : σ k ∉ X \ A := by
      intro hcontra
      obtain ⟨k', hk', hk'eq⟩ :=
        Finset.mem_image.mp (show σ k ∈ (X \ A).image σ by rw [heq]; exact hcontra)
      exact (Finset.mem_sdiff.mp hk').2 (σ.injective hk'eq ▸ hk)
    have hmem := Finset.mem_sdiff.mpr ⟨hmemX k (hAX hk), hnot⟩
    rwa [hXA] at hmem
  -- so the two differ, and what the image gains lies in `A`, above everything it loses
  have hUV : (((X \ A).image σ) \ (X \ A)).card = ((X \ A) \ ((X \ A).image σ)).card := by
    have h1 := Finset.card_sdiff_add_card_inter ((X \ A).image σ) (X \ A)
    have h2 := Finset.card_sdiff_add_card_inter (X \ A) ((X \ A).image σ)
    rw [Finset.inter_comm] at h2
    omega
  have hUne : (((X \ A).image σ) \ (X \ A)).Nonempty := by
    rw [Finset.sdiff_nonempty]
    exact fun hsub => hne (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm))
  have hUlt : ∀ u ∈ ((X \ A).image σ) \ (X \ A), ∀ v ∈ (X \ A) \ ((X \ A).image σ),
      (v : ℕ) < (u : ℕ) := by
    intro u hu v hv
    obtain ⟨huX, huB⟩ := Finset.mem_sdiff.mp hu
    refine hlt u ?_ v (Finset.mem_sdiff.mp hv).1
    have hmem := Finset.mem_sdiff.mpr ⟨hBsub huX, huB⟩
    rwa [hXA] at hmem
  have hlt' := sum_lt_sum_of_forall_lt hUV.symm hUne hUlt
  have hsd1 : (X \ A) \ ((X \ A) ∩ ((X \ A).image σ)) = (X \ A) \ ((X \ A).image σ) := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hsd2 : ((X \ A).image σ) \ ((X \ A) ∩ ((X \ A).image σ)) =
      ((X \ A).image σ) \ (X \ A) := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have h1 : (∑ z ∈ (X \ A) \ ((X \ A).image σ), (z : ℕ)) +
      ∑ z ∈ (X \ A) ∩ ((X \ A).image σ), (z : ℕ) = ∑ z ∈ X \ A, (z : ℕ) := by
    rw [← hsd1]
    exact Finset.sum_sdiff Finset.inter_subset_left
  have h2 : (∑ z ∈ ((X \ A).image σ) \ (X \ A), (z : ℕ)) +
      ∑ z ∈ (X \ A) ∩ ((X \ A).image σ), (z : ℕ) = ∑ z ∈ (X \ A).image σ, (z : ℕ) := by
    rw [← hsd2]
    exact Finset.sum_sdiff Finset.inter_subset_right
  omega

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
  have hkey := sum_lt_sum_image_sdiff hAX hXimg himg hlt
  rw [colMoment_relabel, colMoment, hsum fun k => ((σ k : Fin μ.card) : ℕ),
    hsum fun k => (k : ℕ), Finset.sum_congr rfl hout,
    sum_colIndex_garnirSet t i j fun k => ((σ k : Fin μ.card) : ℕ),
    sum_colIndex_garnirSet t i j fun k => (k : ℕ), hfull, himage]
  omega

/-! ### The straightening algorithm -/

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

/-! ### The standard basis of the Specht module -/

open YoungTableau

/-- **The standard polytabloids span the Specht module.**  The polytabloids span `S^μ` by
definition, and every one of them is a combination of the standard ones by
`TauCeti.YoungTableau.polytabloid_mem_span_polytabloid_standard`. -/
theorem spechtSubrepresentation_eq_span_standard (μ : YoungDiagram) :
    (spechtSubrepresentation μ).toSubmodule =
      Submodule.span ℚ (Set.range fun T : StandardYoungTableau μ => polytabloid T.toTableau) := by
  refine le_antisymm ?_ (Submodule.span_le.mpr ?_)
  · rw [spechtSubrepresentation_toSubmodule]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨t, rfl⟩
    exact polytabloid_mem_span_polytabloid_standard t
  · rintro _ ⟨T, rfl⟩
    exact polytabloid_mem_spechtSubrepresentation _

/-- **The standard basis theorem.**  The polytabloids of the standard `μ`-tableaux are a basis of
the Specht module `S^μ`: they are linearly independent by
`TauCeti.linearIndependent_polytabloid` and they span by
`TauCeti.spechtSubrepresentation_eq_span_standard`. -/
noncomputable def standardPolytabloidBasis (μ : YoungDiagram) :
    Module.Basis (StandardYoungTableau μ) ℚ (spechtSubrepresentation μ).toSubmodule :=
  (Module.Basis.span (linearIndependent_polytabloid μ)).map
    (LinearEquiv.ofEq _ _ (spechtSubrepresentation_eq_span_standard μ).symm)

@[simp]
theorem coe_standardPolytabloidBasis (μ : YoungDiagram) (T : StandardYoungTableau μ) :
    (standardPolytabloidBasis μ T : (permutationModule (shapePartition μ)).V) =
      polytabloid T.toTableau := by
  simp [standardPolytabloidBasis]

/-- **The dimension of the Specht module is the number of standard Young tableaux**, `dim S^μ =
f^μ`. -/
theorem finrank_spechtSubrepresentation (μ : YoungDiagram) :
    Module.finrank ℚ (spechtSubrepresentation μ).toSubmodule = standardCount μ := by
  rw [standardCount_def]
  exact Module.finrank_eq_card_basis (standardPolytabloidBasis μ)

/-- **The dimension of the Specht module `S^μ` of a partition `μ` of `n` is the number `f^μ` of
standard Young tableaux of shape `μ`.** -/
theorem finrank_spechtModule {n : ℕ} (μ : n.Partition) :
    Module.finrank ℚ (spechtModule μ) = standardCount (diagramOf μ) :=
  finrank_spechtSubrepresentation (diagramOf μ)

end TauCeti
