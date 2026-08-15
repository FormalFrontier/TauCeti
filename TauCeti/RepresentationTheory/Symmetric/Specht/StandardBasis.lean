/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Combinatorics.Young.StandardTableau.Order
public import TauCeti.RepresentationTheory.Symmetric.Specht.Module

/-!
# The standard polytabloids are linearly independent

The polytabloid `e_t` of a `μ`-tableau `t` is the signed sum, over the column group of `t`, of the
tabloids `{q t}`, and the Specht module `S^μ` is the span of all of them.  This file proves that
the polytabloids of the **standard** tableaux -- those increasing along rows and down columns --
are linearly independent (`TauCeti.linearIndependent_polytabloid`), so that

`f^μ = standardCount μ ≤ finrank ℚ S^μ`

(`TauCeti.standardCount_le_finrank_spechtModule`).  Together with the reverse inequality, which
needs the straightening algorithm and is not proved here, this is the standard basis theorem of
Layer 5 of the Schur--Weyl roadmap.

## The dominance order on tabloids

The argument is the triangularity of the standard polytabloids against the tabloid basis.  Order
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

## Main definitions

* `TauCeti.YoungTableau.rowCount`: how many of the first `m` labels lie in the first `i + 1` rows.
* `TauCeti.YoungTableau.TabloidDominates`: the dominance order on tabloids.

## Main results

* `TauCeti.YoungTableau.TabloidDominates.antisymm`: dominance both ways is equality of tabloids.
* `TauCeti.YoungTableau.tabloidDominates_relabel_of_mem_colSubgroup`: a column permutation of a
  standard tableau lowers its tabloid.
* `TauCeti.linearIndependent_polytabloid`: the standard polytabloids are linearly independent.
* `TauCeti.standardCount_le_finrank_spechtModule`: hence `f^μ ≤ dim S^μ`.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Section 8.
* [B. E. Sagan, *The Symmetric Group*][sagan2001], Section 2.5.
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

/-- **There are at least `f^μ` dimensions in the Specht module.**  Equality holds, but the reverse
inequality is the straightening algorithm and is not proved here. -/
theorem standardCount_le_finrank_spechtSubrepresentation (μ : YoungDiagram) :
    standardCount μ ≤ Module.finrank ℚ (spechtSubrepresentation μ).toSubmodule := by
  classical
  have hli : LinearIndependent ℚ fun T : StandardYoungTableau μ =>
      (⟨polytabloid T.toTableau, polytabloid_mem_spechtSubrepresentation T.toTableau⟩ :
        (spechtSubrepresentation μ).toSubmodule) :=
    LinearIndependent.of_comp (spechtSubrepresentation μ).toSubmodule.subtype
      (linearIndependent_polytabloid μ)
  simpa [standardCount_def] using hli.fintype_card_le_finrank

/-- **The number of standard Young tableaux of shape `μ` is at most the dimension of the Specht
module `S^μ`.** -/
theorem standardCount_le_finrank_spechtModule {n : ℕ} (μ : n.Partition) :
    standardCount (diagramOf μ) ≤ Module.finrank ℚ (spechtModule μ) :=
  standardCount_le_finrank_spechtSubrepresentation (diagramOf μ)

end TauCeti
