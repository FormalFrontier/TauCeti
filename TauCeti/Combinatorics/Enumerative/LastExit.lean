/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.SuccessorArray

/-!
# Last-exit reconstruction of a finite path

This file proves the finite combinatorial lemma behind the successor-array proof of the
Diaconis--Freedman theorem.  Fix a finite prefix of a path and reorder the successor entries used
by that prefix, separately within each row.  If each reordering preserves the used part of its row
and fixes its last entry, following the reordered successor rows produces another prefix with the
same endpoint and the same transition counts.

The fixed-last hypothesis is essential: it is the last-exit condition which prevents the
reconstructed path from closing a proper subtrail before all prescribed successor entries have
been used.  The proof follows Lemma 1(b) of Fortini, Ladelli, Petris, and Regazzini, *On mixtures
of distributions of Markov chains*, Stochastic Processes and their Applications 100 (2002),
147--165.

## Main definitions

* `TauCeti.reindexSuccessors`: rebuild a path after reindexing each row of its successor array.

## Main results

* `TauCeti.reindexSuccessors_endpoint` and `TauCeti.reindexSuccessors_transitionCount`: the
  last-exit reconstruction has the same endpoint and transition counts as the original prefix.

## References

* S. Fortini, L. Ladelli, G. Petris, and E. Regazzini, "On mixtures of distributions of Markov
  chains", *Stochastic Processes and their Applications* 100 (2002), 147--165, Lemma 1(b).
* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115--130.
* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 8, "Markov exchangeability".
-/

public section

noncomputable section

namespace TauCeti

variable {α : Type*}

attribute [local instance] Classical.decEq

/-- A visit index below the visit count at time `n` is realised strictly before `n`. -/
theorem visitTime_lt_of_lt_visitCount {x : ℕ → α} {a : α} {k n : ℕ}
    (h : k < visitCount x a n) : visitTime x a k < n := by
  classical
  rw [visitTime_def]
  apply Nat.nth_lt_of_lt_count
  simpa only [visitCount_eq_count] using h

/-- A visit index below the visit count at time `n` names a genuine visit. -/
theorem apply_visitTime_of_lt_visitCount {x : ℕ → α} {a : α} {k n : ℕ}
    (h : k < visitCount x a n) : x (visitTime x a k) = a := by
  classical
  have hcard : ∀ hf : {i | x i = a}.Finite, k < hf.toFinset.card := by
    intro hf
    exact h.trans_le (by rw [visitCount_eq_count]; exact Nat.count_le_card hf n)
  simpa only [visitTime_def] using Nat.nth_mem k hcard

/-- Before a realised visit indexed by `k`, there are exactly `k` earlier visits. -/
theorem visitCount_visitTime_of_lt_visitCount {x : ℕ → α} {a : α} {k n : ℕ}
    (h : k < visitCount x a n) : visitCount x a (visitTime x a k) = k := by
  classical
  have hcard : ∀ hf : {i | x i = a}.Finite, k < hf.toFinset.card := by
    intro hf
    exact h.trans_le (by rw [visitCount_eq_count]; exact Nat.count_le_card hf n)
  simpa only [visitCount_eq_count, visitTime_def] using Nat.count_nth hcard

/-- Rebuild `x` after reindexing the entries in each row of its successor array by `π`. -/
def reindexSuccessors (π : α → Equiv.Perm ℕ) (x : ℕ → α) : ℕ → α :=
  pathOfSuccessors (x 0) fun a k => successorArray x a (π a k)

-- The parentheses in `(rfl)` keep the definition sealed while exposing its computational API.
@[simp]
theorem reindexSuccessors_zero (π : α → Equiv.Perm ℕ) (x : ℕ → α) :
    reindexSuccessors π x 0 = x 0 := by
  rw [reindexSuccessors, pathOfSuccessors_zero]

/-- The recursion equation for a path rebuilt from reindexed successor rows. -/
theorem reindexSuccessors_succ (π : α → Equiv.Perm ℕ) (x : ℕ → α) (n : ℕ) :
    reindexSuccessors π x (n + 1) =
      successorArray x (reindexSuccessors π x n)
        (π (reindexSuccessors π x n)
          (visitCount (reindexSuccessors π x) (reindexSuccessors π x n) n)) := by
  rw [reindexSuccessors, pathOfSuccessors_succ]

/-- Reindexing every successor row by the identity leaves the path unchanged. -/
@[simp]
theorem reindexSuccessors_one (x : ℕ → α) :
    reindexSuccessors (fun _ => 1) x = x := by
  rw [reindexSuccessors]
  exact pathOfSuccessors_successorArray x

/-- Every entry already consumed by a rebuilt path is the corresponding entry of the supplied
successor rows. -/
theorem successorArray_pathOfSuccessors_of_lt_visitCount (a₀ : α) (s : α → ℕ → α)
    (a : α) (k n : ℕ) (hk : k < visitCount (pathOfSuccessors a₀ s) a n) :
    successorArray (pathOfSuccessors a₀ s) a k = s a k := by
  let y := pathOfSuccessors a₀ s
  have hy : y (visitTime y a k) = a := apply_visitTime_of_lt_visitCount hk
  have hcount : visitCount y a (visitTime y a k) = k :=
    visitCount_visitTime_of_lt_visitCount hk
  rw [successorArray_def]
  change y (visitTime y a k + 1) = s a k
  rw [show y (visitTime y a k + 1) =
      s (y (visitTime y a k))
        (visitCount y (y (visitTime y a k)) (visitTime y a k)) by
      exact pathOfSuccessors_succ a₀ s (visitTime y a k), hy, hcount]

/-- Every successor entry consumed by a reindexed reconstruction is the corresponding reindexed
entry of the original successor array. -/
theorem successorArray_reindexSuccessors_of_lt_visitCount (π : α → Equiv.Perm ℕ)
    (x : ℕ → α) (a : α) (k n : ℕ) (hk : k < visitCount (reindexSuccessors π x) a n) :
    successorArray (reindexSuccessors π x) a k = successorArray x a (π a k) := by
  exact successorArray_pathOfSuccessors_of_lt_visitCount (x 0)
    (fun b l => successorArray x b (π b l)) a k n hk

private theorem perm_apply_lt_of_fixed_of_lt (σ : Equiv.Perm ℕ) (q : ℕ)
    (hfix : ∀ k, q ≤ k → σ k = k) {k : ℕ} (hk : k < q) : σ k < q := by
  by_contra h
  have hsfix : σ (σ k) = σ k := hfix (σ k) (not_lt.mp h)
  have hsk : σ k = k := σ.injective hsfix
  exact (not_lt_of_ge ((not_lt.mp h).trans_eq hsk)) hk

private def reindexStepIndex (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m i : ℕ)
    (hki : visitCount (reindexSuccessors π x) (reindexSuccessors π x i) i <
      visitCount x (reindexSuccessors π x i) m)
    (hfix : ∀ a k, visitCount x a m ≤ k → π a k = k) : Fin m :=
  let y := reindexSuccessors π x
  let k := visitCount y (y i) i
  ⟨visitTime x (y i) (π (y i) k),
    visitTime_lt_of_lt_visitCount
      (perm_apply_lt_of_fixed_of_lt (π (y i)) _ (hfix (y i)) hki)⟩

private theorem reindexStepIndex_source (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m i : ℕ)
    (hki : visitCount (reindexSuccessors π x) (reindexSuccessors π x i) i <
      visitCount x (reindexSuccessors π x i) m)
    (hfix : ∀ a k, visitCount x a m ≤ k → π a k = k) :
    x (reindexStepIndex π x m i hki hfix) = reindexSuccessors π x i := by
  let y := reindexSuccessors π x
  let k := visitCount y (y i) i
  have hp : π (y i) k < visitCount x (y i) m :=
    perm_apply_lt_of_fixed_of_lt (π (y i)) _ (hfix (y i)) hki
  exact apply_visitTime_of_lt_visitCount hp

private theorem reindexStepIndex_target (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m i : ℕ)
    (hki : visitCount (reindexSuccessors π x) (reindexSuccessors π x i) i <
      visitCount x (reindexSuccessors π x i) m)
    (hfix : ∀ a k, visitCount x a m ≤ k → π a k = k) :
    x (reindexStepIndex π x m i hki hfix + 1) = reindexSuccessors π x (i + 1) := by
  let y := reindexSuccessors π x
  let k := visitCount y (y i) i
  change x (visitTime x (y i) (π (y i) k) + 1) = y (i + 1)
  calc
    x (visitTime x (y i) (π (y i) k) + 1) = successorArray x (y i) (π (y i) k) :=
      (successorArray_def x (y i) (π (y i) k)).symm
    _ = y (i + 1) := (reindexSuccessors_succ π x i).symm

private def reindexStepEmbedding (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m t : ℕ)
    (hused : ∀ i < t,
      visitCount (reindexSuccessors π x) (reindexSuccessors π x i) i <
        visitCount x (reindexSuccessors π x i) m)
    (hfix : ∀ a k, visitCount x a m ≤ k → π a k = k) : Fin t ↪ Fin m where
  toFun i := reindexStepIndex π x m i (hused i i.isLt) hfix
  inj' := by
    intro i j hij
    apply Fin.ext
    apply (visitCell_injective (reindexSuccessors π x))
    rw [visitCell_def, visitCell_def, Prod.mk.injEq]
    have hsource : reindexSuccessors π x i = reindexSuccessors π x j := by
      rw [← reindexStepIndex_source π x m i (hused i i.isLt) hfix,
        ← reindexStepIndex_source π x m j (hused j j.isLt) hfix]
      exact congrArg x (congrArg Fin.val hij)
    refine ⟨hsource, ?_⟩
    have hcounti := visitCount_visitTime_of_lt_visitCount
      (perm_apply_lt_of_fixed_of_lt (π (reindexSuccessors π x i)) _
        (hfix (reindexSuccessors π x i)) (hused i i.isLt))
    have hcountj := visitCount_visitTime_of_lt_visitCount
      (perm_apply_lt_of_fixed_of_lt (π (reindexSuccessors π x j)) _
        (hfix (reindexSuccessors π x j)) (hused j j.isLt))
    have hidx : (reindexStepIndex π x m i (hused i i.isLt) hfix).val =
        (reindexStepIndex π x m j (hused j j.isLt) hfix).val := congrArg Fin.val hij
    have hc : visitCount x (reindexSuccessors π x i)
          (reindexStepIndex π x m i (hused i i.isLt) hfix).val =
        visitCount x (reindexSuccessors π x j)
          (reindexStepIndex π x m j (hused j j.isLt) hfix).val := by
      rw [hsource, hidx]
    have hcounti' : visitCount x (reindexSuccessors π x i)
          (reindexStepIndex π x m i (hused i i.isLt) hfix).val =
        π (reindexSuccessors π x i)
          (visitCount (reindexSuccessors π x) (reindexSuccessors π x i) i) := by
      change visitCount x (reindexSuccessors π x i)
          (visitTime x (reindexSuccessors π x i)
            (π (reindexSuccessors π x i)
              (visitCount (reindexSuccessors π x) (reindexSuccessors π x i) i))) = _
      exact hcounti
    have hcountj' : visitCount x (reindexSuccessors π x j)
          (reindexStepIndex π x m j (hused j j.isLt) hfix).val =
        π (reindexSuccessors π x j)
          (visitCount (reindexSuccessors π x) (reindexSuccessors π x j) j) := by
      change visitCount x (reindexSuccessors π x j)
          (visitTime x (reindexSuccessors π x j)
            (π (reindexSuccessors π x j)
              (visitCount (reindexSuccessors π x) (reindexSuccessors π x j) j))) = _
      exact hcountj
    rw [hcounti', hcountj', hsource] at hc
    have hcounts := (π (reindexSuccessors π x j)).injective hc
    rw [hsource]
    exact hcounts

private theorem arrivalCount_add_start (z : ℕ → α) (b : α) (t : ℕ) :
    occCount (fun i : Fin t => z (i.val + 1)) b + (if z 0 = b then 1 else 0) =
      visitCount z b t + (if z t = b then 1 else 0) := by
  classical
  let w : Fin (t + 1) → α := fun i => z i.val
  have hfirst := occCount_comp_succ_add_zero w b
  have hlast := occCount_comp_castSucc_add_last w b
  have hbalance := hfirst.trans hlast.symm
  change occCount (fun i : Fin t => z (i.val + 1)) b + (if z 0 = b then 1 else 0) =
    occCount (fun i : Fin t => z i.val) b + (if z t = b then 1 else 0) at hbalance
  rw [visitCount_def]
  exact hbalance

private theorem arrivalCount_reindex_le (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m t : ℕ)
    (hused : ∀ i < t,
      visitCount (reindexSuccessors π x) (reindexSuccessors π x i) i <
        visitCount x (reindexSuccessors π x i) m)
    (hfix : ∀ a k, visitCount x a m ≤ k → π a k = k) (b : α) :
    occCount (fun i : Fin t => reindexSuccessors π x (i.val + 1)) b ≤
      occCount (fun i : Fin m => x (i.val + 1)) b := by
  classical
  rw [occCount_eq_card_filter, occCount_eq_card_filter]
  let e := reindexStepEmbedding π x m t hused hfix
  apply Finset.card_le_card_of_injOn e
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    change x ((reindexStepIndex π x m i (hused i i.isLt) hfix).val + 1) = b
    rw [reindexStepIndex_target π x m i (hused i i.isLt) hfix]
    exact hi.2
  · exact e.injective.injOn

private theorem departureCount_reindex_le (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m t : ℕ)
    (hused : ∀ i < t,
      visitCount (reindexSuccessors π x) (reindexSuccessors π x i) i <
        visitCount x (reindexSuccessors π x i) m)
    (hfix : ∀ a k, visitCount x a m ≤ k → π a k = k) (a : α) :
    visitCount (reindexSuccessors π x) a t ≤ visitCount x a m := by
  classical
  rw [visitCount_def, visitCount_def, occCount_eq_card_filter, occCount_eq_card_filter]
  let e := reindexStepEmbedding π x m t hused hfix
  apply Finset.card_le_card_of_injOn e
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [show e i = reindexStepIndex π x m i (hused i i.isLt) hfix from rfl,
      reindexStepIndex_source π x m i (hused i i.isLt) hfix]
    exact hi.2
  · exact e.injective.injOn

private theorem endpoint_eq_of_departureCount_eq (π : α → Equiv.Perm ℕ) (x : ℕ → α)
    (m t : ℕ)
    (hused : ∀ i < t,
      visitCount (reindexSuccessors π x) (reindexSuccessors π x i) i <
        visitCount x (reindexSuccessors π x i) m)
    (hfix : ∀ a k, visitCount x a m ≤ k → π a k = k)
    (hcount : visitCount (reindexSuccessors π x) (reindexSuccessors π x t) t =
      visitCount x (reindexSuccessors π x t) m) :
    reindexSuccessors π x t = x m := by
  classical
  let y := reindexSuccessors π x
  let b := y t
  have harr := arrivalCount_reindex_le π x m t hused hfix b
  have hy := arrivalCount_add_start y b t
  have hx := arrivalCount_add_start x b m
  have hy0 : y 0 = x 0 := reindexSuccessors_zero π x
  change occCount (fun i : Fin t => y (i.val + 1)) b ≤
    occCount (fun i : Fin m => x (i.val + 1)) b at harr
  by_contra hend
  change b ≠ x m at hend
  change visitCount y b t = visitCount x b m at hcount
  have hyt : y t = b := rfl
  have hxm : x m ≠ b := Ne.symm hend
  simp [hy0, hyt, hcount] at hy
  simp [hxm] at hx
  omega

private theorem arrivalCount_reindex_eq_of_departureCount_eq
    (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m t : ℕ) (b : α)
    (hcount : visitCount (reindexSuccessors π x) b t = visitCount x b m)
    (hend : reindexSuccessors π x t = x m) :
    occCount (fun i : Fin t => reindexSuccessors π x (i.val + 1)) b =
      occCount (fun i : Fin m => x (i.val + 1)) b := by
  classical
  let y := reindexSuccessors π x
  have hy := arrivalCount_add_start y b t
  have hx := arrivalCount_add_start x b m
  have hy0 : y 0 = x 0 := reindexSuccessors_zero π x
  change occCount (fun i : Fin t => y (i.val + 1)) b =
    occCount (fun i : Fin m => x (i.val + 1)) b
  change y t = x m at hend
  change visitCount y b t = visitCount x b m at hcount
  simp [hy0, hend, hcount] at hy
  omega

private theorem sum_occCount_eq_card {N : ℕ} (w : Fin N → α) (S : Finset α)
    (hS : ∀ i, w i ∈ S) : ∑ a ∈ S, occCount w a = N := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (f := w) (t := S)
    fun i _ => hS i
  simpa only [Finset.card_univ, Fintype.card_fin, occCount_eq_card_filter] using h.symm

private theorem arrivalCount_reindex_lt_of_omitted (π : α → Equiv.Perm ℕ) (x : ℕ → α)
    (m t r : ℕ) (hr : r < m)
    (hused : ∀ i < t,
      visitCount (reindexSuccessors π x) (reindexSuccessors π x i) i <
        visitCount x (reindexSuccessors π x i) m)
    (hfix : ∀ a k, visitCount x a m ≤ k → π a k = k)
    (homit : ∀ i : Fin t,
      (reindexStepEmbedding π x m t hused hfix i).val ≠ r) :
    occCount (fun i : Fin t => reindexSuccessors π x (i.val + 1)) (x (r + 1)) <
      occCount (fun i : Fin m => x (i.val + 1)) (x (r + 1)) := by
  classical
  rw [occCount_eq_card_filter, occCount_eq_card_filter]
  let e := reindexStepEmbedding π x m t hused hfix
  let A := Finset.univ.filter fun i : Fin t =>
    reindexSuccessors π x (i.val + 1) = x (r + 1)
  let B := Finset.univ.filter fun j : Fin m => x (j.val + 1) = x (r + 1)
  have himage : A.image e ⊆ B := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show e i = reindexStepIndex π x m i (hused i i.isLt) hfix from rfl,
      reindexStepIndex_target π x m i (hused i i.isLt) hfix]
    simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  have hrB : (⟨r, hr⟩ : Fin m) ∈ B := by simp [B]
  have hrnot : (⟨r, hr⟩ : Fin m) ∉ A.image e := by
    intro hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨i, _, hi⟩ := hmem
    exact homit i (congrArg Fin.val hi)
  have hstrict : A.image e ⊂ B := (Finset.ssubset_iff_of_subset himage).2
    ⟨⟨r, hr⟩, hrB, hrnot⟩
  calc
    A.card = (A.image e).card := (Finset.card_image_of_injective A e.injective).symm
    _ < B.card := Finset.card_lt_card hstrict

private theorem reindexSuccessors_uses_used_entries (π : α → Equiv.Perm ℕ) (x : ℕ → α)
    (m : ℕ) (hfix : ∀ a k, visitCount x a m ≤ k → π a k = k)
    (hlast : ∀ a, 0 < visitCount x a m →
      π a (visitCount x a m - 1) = visitCount x a m - 1) :
    ∀ i < m, visitCount (reindexSuccessors π x) (reindexSuccessors π x i) i <
      visitCount x (reindexSuccessors π x i) m := by
  intro i hi
  induction i using Nat.strong_induction_on with
  | h t ih =>
      let y := reindexSuccessors π x
      have hused : ∀ j < t, visitCount y (y j) j < visitCount x (y j) m := by
        intro j hj
        exact ih j hj (hj.trans hi)
      have hle := departureCount_reindex_le π x m t hused hfix (y t)
      apply lt_of_le_of_ne hle
      intro heq
      have hcount : visitCount y (y t) t = visitCount x (y t) m := by
        change visitCount y (y t) t = visitCount x (y t) m at heq
        exact heq
      have hend : y t = x m := endpoint_eq_of_departureCount_eq π x m t hused hfix hcount
      let S := Finset.univ.image fun j : Fin m => x j
      have hyS : ∀ j : Fin t, y j ∈ S := by
        intro j
        let e := reindexStepEmbedding π x m t hused hfix
        rw [show y j = x (e j) by
          rw [show e j = reindexStepIndex π x m j (hused j j.isLt) hfix from rfl,
            reindexStepIndex_source π x m j (hused j j.isLt) hfix]]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      have hxS : ∀ j : Fin m, x j ∈ S := fun j =>
        Finset.mem_image_of_mem _ (Finset.mem_univ j)
      have hsumy : ∑ a ∈ S, visitCount y a t = t := by
        simpa only [visitCount_def] using
          sum_occCount_eq_card (fun j : Fin t => y j) S hyS
      have hsumx : ∑ a ∈ S, visitCount x a m = m := by
        simpa only [visitCount_def] using
          sum_occCount_eq_card (fun j : Fin m => x j) S hxS
      let I := (Finset.range m).filter fun r => visitCount y (x r) t < visitCount x (x r) m
      have hI : I.Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        have hall : ∀ a ∈ S, visitCount y a t = visitCount x a m := by
          intro a ha
          rw [Finset.mem_image] at ha
          obtain ⟨j, _, rfl⟩ := ha
          apply Nat.le_antisymm (departureCount_reindex_le π x m t hused hfix (x j))
          apply not_lt.mp
          intro hlt
          change visitCount y (x j) t < visitCount x (x j) m at hlt
          have hjI : j.val ∈ I := by
            change j.val ∈ (Finset.range m).filter fun r =>
              visitCount y (x r) t < visitCount x (x r) m
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_range.mpr j.isLt, hlt⟩
          exact (Finset.ne_empty_of_mem hjI) hempty
        have : t = m := by
          have hsumEq : ∑ a ∈ S, visitCount y a t = ∑ a ∈ S, visitCount x a m :=
            Finset.sum_congr rfl fun a ha => hall a ha
          omega
        omega
      let r := I.max' hI
      have hrI : r ∈ I := I.max'_mem hI
      have hr : r < m := (Finset.mem_filter.mp hrI).1 |> Finset.mem_range.mp
      have hrinc : visitCount y (x r) t < visitCount x (x r) m :=
        (Finset.mem_filter.mp hrI).2
      have hlater : ∀ j, r < j → j < m →
          visitCount y (x j) t = visitCount x (x j) m := by
        intro j hrj hjm
        apply Nat.le_antisymm (departureCount_reindex_le π x m t hused hfix (x j))
        apply not_lt.mp
        intro hjinc
        change visitCount y (x j) t < visitCount x (x j) m at hjinc
        have hjI : j ∈ I := by
          change j ∈ (Finset.range m).filter fun q =>
            visitCount y (x q) t < visitCount x (x q) m
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_range.mpr hjm, hjinc⟩
        have := I.le_max' j hjI
        omega
      have hrle : r + 1 ≤ m := by omega
      let b := x (r + 1)
      have hbcount : visitCount y b t = visitCount x b m := by
        rcases hrle.eq_or_lt with hlastIndex | hbefore
        · change visitCount y (x (r + 1)) t = visitCount x (x (r + 1)) m
          rw [hlastIndex, ← hend]
          exact hcount
        · exact hlater (r + 1) (by omega) hbefore
      have hbarrival := arrivalCount_reindex_eq_of_departureCount_eq π x m t b hbcount hend
      have hnoLater : ∀ j, r < j → j < m → x j ≠ x r := by
        intro j hrj hjm hja
        have := hlater j hrj hjm
        rw [hja] at this
        omega
      have hq : visitCount x (x r) m = visitCount x (x r) r + 1 := by
        have hzero : visitCount (fun j => x (r + 1 + j)) (x r) (m - (r + 1)) = 0 := by
          apply visitCount_eq_zero_of_forall_ne
          intro j hj
          apply hnoLater (r + 1 + j) (by omega)
          omega
        calc
          visitCount x (x r) m = visitCount x (x r) ((r + 1) + (m - (r + 1))) := by
            rw [Nat.add_sub_of_le hrle]
          _ = visitCount x (x r) (r + 1) +
              visitCount (fun j => x (r + 1 + j)) (x r) (m - (r + 1)) :=
            visitCount_add x (x r) (r + 1) (m - (r + 1))
          _ = visitCount x (x r) r + 1 := by
            rw [hzero, Nat.add_zero, visitCount_succ_of_eq rfl]
      have hpositive : 0 < visitCount x (x r) m := by omega
      have homit : ∀ j : Fin t,
          (reindexStepEmbedding π x m t hused hfix j).val ≠ r := by
        intro j hej
        have hsource := reindexStepIndex_source π x m j (hused j j.isLt) hfix
        have hsource' : y j = x r := by
          change x (reindexStepIndex π x m j (hused j j.isLt) hfix) = y j at hsource
          rw [← hsource]
          exact congrArg x hej
        let k := visitCount y (y j) j
        have hklt : k < visitCount y (x r) t := by
          have hsucc : visitCount y (y j) (j.val + 1) = k + 1 :=
            visitCount_succ_of_eq rfl
          have hmono := visitCount_monotone y (y j) (show j.val + 1 ≤ t by omega)
          rw [hsource'] at hsucc hmono
          omega
        have hpcount := visitCount_visitTime_of_lt_visitCount
          (perm_apply_lt_of_fixed_of_lt (π (y j)) _ (hfix (y j)) (hused j j.isLt))
        have hp : π (x r) k = visitCount x (x r) r := by
          have hpcount' : visitCount x (y j)
                (reindexStepIndex π x m j (hused j j.isLt) hfix).val =
              π (y j) (visitCount y (y j) j) := by
            exact hpcount
          change (reindexStepIndex π x m j (hused j j.isLt) hfix).val = r at hej
          rw [hej, hsource'] at hpcount'
          have hkdef : k = visitCount y (x r) j := by
            change visitCount y (y j) j = visitCount y (x r) j
            rw [hsource']
          rw [hkdef]
          exact hpcount'.symm
        have hfixed : π (x r) (visitCount x (x r) r) = visitCount x (x r) r := by
          have hsub : visitCount x (x r) m - 1 = visitCount x (x r) r := by omega
          simpa only [hsub] using hlast (x r) hpositive
        have hk : k = visitCount x (x r) r := (π (x r)).injective (hp.trans hfixed.symm)
        omega
      have hblt := arrivalCount_reindex_lt_of_omitted π x m t r hr hused hfix homit
      change occCount (fun j : Fin t => y (j.val + 1)) b <
        occCount (fun j : Fin m => x (j.val + 1)) b at hblt
      exact (Nat.ne_of_lt hblt) hbarrival

private def reindexStepEquiv (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m : ℕ)
    (hfix : ∀ a k, visitCount x a m ≤ k → π a k = k)
    (hlast : ∀ a, 0 < visitCount x a m →
      π a (visitCount x a m - 1) = visitCount x a m - 1) : Fin m ≃ Fin m :=
  let hused := reindexSuccessors_uses_used_entries π x m hfix hlast
  let e := reindexStepEmbedding π x m m hused hfix
  Equiv.ofBijective e ⟨e.injective, Finite.injective_iff_surjective.mp e.injective⟩

private theorem reindexStepEquiv_source (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m : ℕ)
    (hfix : ∀ a k, visitCount x a m ≤ k → π a k = k)
    (hlast : ∀ a, 0 < visitCount x a m →
      π a (visitCount x a m - 1) = visitCount x a m - 1) (i : Fin m) :
    x (reindexStepEquiv π x m hfix hlast i) = reindexSuccessors π x i := by
  let hused := reindexSuccessors_uses_used_entries π x m hfix hlast
  exact reindexStepIndex_source π x m i (hused i i.isLt) hfix

private theorem reindexStepEquiv_target (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m : ℕ)
    (hfix : ∀ a k, visitCount x a m ≤ k → π a k = k)
    (hlast : ∀ a, 0 < visitCount x a m →
      π a (visitCount x a m - 1) = visitCount x a m - 1) (i : Fin m) :
    x (reindexStepEquiv π x m hfix hlast i + 1) = reindexSuccessors π x (i + 1) := by
  let hused := reindexSuccessors_uses_used_entries π x m hfix hlast
  exact reindexStepIndex_target π x m i (hused i i.isLt) hfix

/-- A last-exit reindexing uses each prescribed successor row exactly as often as the original
finite prefix. -/
theorem reindexSuccessors_visitCount (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m : ℕ)
    (hfix : ∀ a k, visitCount x a m ≤ k → π a k = k)
    (hlast : ∀ a, 0 < visitCount x a m →
      π a (visitCount x a m - 1) = visitCount x a m - 1) (a : α) :
    visitCount (reindexSuccessors π x) a m = visitCount x a m := by
  rw [visitCount_def, visitCount_def]
  rw [occCount_eq_card_filter, occCount_eq_card_filter,
    ← Fintype.card_coe, ← Fintype.card_coe]
  let e := reindexStepEquiv π x m hfix hlast
  apply Fintype.card_congr
  apply e.subtypeEquiv
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [reindexStepEquiv_source π x m hfix hlast i]

/-- A finite path reconstructed after last-exit reindexing has the same endpoint as the original
prefix. -/
theorem reindexSuccessors_endpoint (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m : ℕ)
    (hfix : ∀ a k, visitCount x a m ≤ k → π a k = k)
    (hlast : ∀ a, 0 < visitCount x a m →
      π a (visitCount x a m - 1) = visitCount x a m - 1) :
    reindexSuccessors π x m = x m := by
  let y := reindexSuccessors π x
  have hused := reindexSuccessors_uses_used_entries π x m hfix hlast
  apply endpoint_eq_of_departureCount_eq π x m m hused hfix
  exact reindexSuccessors_visitCount π x m hfix hlast (y m)

/-- A finite path reconstructed after last-exit reindexing has the same transition counts as the
original prefix. -/
theorem reindexSuccessors_transitionCount (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m : ℕ)
    (hfix : ∀ a k, visitCount x a m ≤ k → π a k = k)
    (hlast : ∀ a, 0 < visitCount x a m →
      π a (visitCount x a m - 1) = visitCount x a m - 1) (a b : α) :
    transitionCount (fun i : Fin (m + 1) => reindexSuccessors π x i) a b =
      transitionCount (fun i : Fin (m + 1) => x i) a b := by
  rw [transitionCount_eq_card_filter, transitionCount_eq_card_filter,
    ← Fintype.card_coe, ← Fintype.card_coe]
  let e := reindexStepEquiv π x m hfix hlast
  apply Fintype.card_congr
  apply e.subtypeEquiv
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change reindexSuccessors π x i = a ∧ reindexSuccessors π x (i + 1) = b ↔
    x (e i) = a ∧ x (e i + 1) = b
  rw [reindexStepEquiv_source π x m hfix hlast i,
    reindexStepEquiv_target π x m hfix hlast i]

end TauCeti

end

end
