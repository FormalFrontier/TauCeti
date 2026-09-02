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
Diaconis--Freedman theorem. Fix a finite prefix of a path and reorder the successor entries used
by that prefix, separately within each row. If each reordering permutes the used part of its row
among itself and fixes its last entry, following the reordered successor rows produces another
prefix with the same endpoint and the same transition counts.

The fixed-last hypothesis is essential: it is the last-exit condition which prevents the
reconstructed path from closing a proper subtrail before all prescribed successor entries have
been used. It enters exactly once, in
`TauCeti.visitCount_pathOfReindexedSuccessors_lt_visitCount`, where it rules out the maximal
deficient index being skipped. The proof follows Lemma 1(b) of Fortini, Ladelli, Petris, and
Regazzini, *On mixtures of distributions of Markov chains*, Stochastic Processes and their
Applications 100 (2002), 147--165.

## Main definitions

* `TauCeti.LastExitAdmissible`: packages the two hypotheses of finite last-exit reconstruction.
* `TauCeti.pathOfReindexedSuccessors`: the path rebuilt after reindexing each row of the successor
  array of the original path.

## Main results

* `TauCeti.lastExitAdmissible_of_support_lt_visitCount`: deterministic support criterion for
  last-exit admissibility.
* `TauCeti.visitCount_pathOfReindexedSuccessors_lt_visitCount`: the last-exit lemma — the
  reconstruction only ever consumes successor entries that the original prefix consumes too.
* `TauCeti.successorArray_pathOfReindexedSuccessors_of_lt_visitCount`: the entries it consumes are
  the prescribed reindexed ones.
* `TauCeti.visitCount_pathOfReindexedSuccessors`, `TauCeti.pathOfReindexedSuccessors_eq` and
  `TauCeti.transitionCount_pathOfReindexedSuccessors`: the last-exit reconstruction has the same
  visit counts, the same endpoint, and the same transition counts as the original prefix.

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

/-- A family of successor-row permutations is **last-exit admissible** for the prefix of `x`
before time `m` when it preserves every used row prefix and fixes the final used position in each
nonempty row.

These are exactly the two hypotheses needed by finite last-exit reconstruction: the first keeps
every reindexed successor entry inside the finite prefix, and the second prevents reconstruction
from closing a proper subtrail before all prescribed entries have been consumed. -/
def LastExitAdmissible (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m : ℕ) : Prop :=
  (∀ a k, k < visitCount x a m → π a k < visitCount x a m) ∧
    ∀ a, 0 < visitCount x a m →
      π a (visitCount x a m - 1) = visitCount x a m - 1

/-- The two conditions defining last-exit admissibility. -/
@[simp]
theorem lastExitAdmissible_iff {π : α → Equiv.Perm ℕ} {x : ℕ → α} {m : ℕ} :
    LastExitAdmissible π x m ↔
      (∀ a k, k < visitCount x a m → π a k < visitCount x a m) ∧
        ∀ a, 0 < visitCount x a m →
          π a (visitCount x a m - 1) = visitCount x a m - 1 :=
  Iff.rfl

/-- A last-exit-admissible permutation keeps every used row index inside the used prefix. -/
theorem LastExitAdmissible.maps_lt_visitCount
    {π : α → Equiv.Perm ℕ} {x : ℕ → α} {m : ℕ}
    (h : LastExitAdmissible π x m) {a : α} {k : ℕ} (hk : k < visitCount x a m) :
    π a k < visitCount x a m :=
  h.1 a k hk

/-- A last-exit-admissible permutation fixes the last used index of every nonempty row. -/
theorem LastExitAdmissible.apply_visitCount_sub_one {π : α → Equiv.Perm ℕ}
    {x : ℕ → α} {m : ℕ} (h : LastExitAdmissible π x m) {a : α}
    (ha : 0 < visitCount x a m) :
    π a (visitCount x a m - 1) = visitCount x a m - 1 :=
  h.2 a ha

/-- If every moved position lies strictly below the last used position of its row, then the row
permutations are last-exit admissible. -/
theorem lastExitAdmissible_of_support_lt_visitCount {π : α → Equiv.Perm ℕ}
    {x : ℕ → α} {m : ℕ}
    (h : ∀ a, 0 < visitCount x a m → ∀ k, π a k ≠ k → k + 1 < visitCount x a m) :
    LastExitAdmissible π x m := by
  rw [lastExitAdmissible_iff]
  constructor
  · intro a k hk
    by_cases hfix : π a k = k
    · simpa only [hfix] using hk
    · have himage : π a (π a k) ≠ π a k := by
        intro himage
        exact hfix ((π a).injective himage)
      have hlt := h a (Nat.zero_lt_of_lt hk) (π a k) himage
      omega
  · intro a ha
    by_contra hlast
    have hlt := h a ha (visitCount x a m - 1) hlast
    omega

/-- Rebuild `x` after reindexing the entries in each row of its successor array by `π`. -/
def pathOfReindexedSuccessors (π : α → Equiv.Perm ℕ) (x : ℕ → α) : ℕ → α :=
  pathOfSuccessors (x 0) fun a k => successorArray x a (π a k)

/-- The defining equation for reconstruction from reindexed successor rows. -/
theorem pathOfReindexedSuccessors_def (π : α → Equiv.Perm ℕ) (x : ℕ → α) :
    pathOfReindexedSuccessors π x =
      pathOfSuccessors (x 0) fun a k => successorArray x a (π a k) :=
  (rfl)

/-- A rebuilt path starts where the original does. -/
@[simp]
theorem pathOfReindexedSuccessors_zero (π : α → Equiv.Perm ℕ) (x : ℕ → α) :
    pathOfReindexedSuccessors π x 0 = x 0 := by
  rw [pathOfReindexedSuccessors, pathOfSuccessors_zero]

/-- The recursion equation for a path rebuilt from reindexed successor rows. -/
@[simp]
theorem pathOfReindexedSuccessors_succ (π : α → Equiv.Perm ℕ) (x : ℕ → α) (n : ℕ) :
    pathOfReindexedSuccessors π x (n + 1) =
      successorArray x (pathOfReindexedSuccessors π x n)
        (π (pathOfReindexedSuccessors π x n)
          (visitCount (pathOfReindexedSuccessors π x) (pathOfReindexedSuccessors π x n) n)) := by
  rw [pathOfReindexedSuccessors, pathOfSuccessors_succ]

/-- Reindexing every successor row by the identity leaves the path unchanged. -/
@[simp]
theorem pathOfReindexedSuccessors_one (x : ℕ → α) :
    pathOfReindexedSuccessors (1 : α → Equiv.Perm ℕ) x = x := by
  rw [pathOfReindexedSuccessors]
  exact pathOfSuccessors_successorArray x

/-- Every successor entry consumed by a reindexed reconstruction is the corresponding reindexed
entry of the original successor array. -/
theorem successorArray_pathOfReindexedSuccessors_of_lt_visitCount (π : α → Equiv.Perm ℕ)
    (x : ℕ → α) (a : α) {k n : ℕ}
    (hk : k < visitCount (pathOfReindexedSuccessors π x) a n) :
    successorArray (pathOfReindexedSuccessors π x) a k = successorArray x a (π a k) :=
  successorArray_pathOfSuccessors_of_lt_visitCount (a₀ := x 0)
    (s := fun b l => successorArray x b (π b l)) hk

/-- The time at which the original prefix consumes the successor entry that the reconstruction
consumes at time `i`: the visit of `x` to the state `pathOfReindexedSuccessors π x i` indexed by
the reindexed visit count. The hypothesis `hmaps` keeps that index below the number of visits `x`
makes before `m`, so the time is one of the first `m`. -/
private def reindexStepIndex (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m i : ℕ)
    (hki : visitCount (pathOfReindexedSuccessors π x) (pathOfReindexedSuccessors π x i) i <
      visitCount x (pathOfReindexedSuccessors π x i) m)
    (hmaps : ∀ a k, k < visitCount x a m → π a k < visitCount x a m) : Fin m :=
  ⟨visitTime x (pathOfReindexedSuccessors π x i)
      (π (pathOfReindexedSuccessors π x i)
        (visitCount (pathOfReindexedSuccessors π x) (pathOfReindexedSuccessors π x i) i)),
    visitTime_lt_of_lt_visitCount (hmaps _ _ hki)⟩

/-- The value of `TauCeti.reindexStepIndex`. This is the only place its body is unfolded. -/
private theorem reindexStepIndex_val (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m i : ℕ)
    (hki : visitCount (pathOfReindexedSuccessors π x) (pathOfReindexedSuccessors π x i) i <
      visitCount x (pathOfReindexedSuccessors π x i) m)
    (hmaps : ∀ a k, k < visitCount x a m → π a k < visitCount x a m) :
    (reindexStepIndex π x m i hki hmaps).val =
      visitTime x (pathOfReindexedSuccessors π x i)
        (π (pathOfReindexedSuccessors π x i)
          (visitCount (pathOfReindexedSuccessors π x) (pathOfReindexedSuccessors π x i) i)) :=
  rfl

/-- The original prefix visits the reconstruction's current state at the paired time. -/
private theorem reindexStepIndex_source (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m i : ℕ)
    (hki : visitCount (pathOfReindexedSuccessors π x) (pathOfReindexedSuccessors π x i) i <
      visitCount x (pathOfReindexedSuccessors π x i) m)
    (hmaps : ∀ a k, k < visitCount x a m → π a k < visitCount x a m) :
    x (reindexStepIndex π x m i hki hmaps) = pathOfReindexedSuccessors π x i := by
  rw [reindexStepIndex_val]
  exact apply_visitTime_of_lt_visitCount (hmaps _ _ hki)

/-- The original prefix moves to the reconstruction's next state at the paired time. -/
private theorem reindexStepIndex_target (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m i : ℕ)
    (hki : visitCount (pathOfReindexedSuccessors π x) (pathOfReindexedSuccessors π x i) i <
      visitCount x (pathOfReindexedSuccessors π x i) m)
    (hmaps : ∀ a k, k < visitCount x a m → π a k < visitCount x a m) :
    x (reindexStepIndex π x m i hki hmaps + 1) = pathOfReindexedSuccessors π x (i + 1) := by
  rw [reindexStepIndex_val, ← successorArray_def x, ← pathOfReindexedSuccessors_succ]

/-- By the paired time the original prefix has made exactly the reindexed number of visits. -/
private theorem visitCount_reindexStepIndex (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m i : ℕ)
    (hki : visitCount (pathOfReindexedSuccessors π x) (pathOfReindexedSuccessors π x i) i <
      visitCount x (pathOfReindexedSuccessors π x i) m)
    (hmaps : ∀ a k, k < visitCount x a m → π a k < visitCount x a m) :
    visitCount x (pathOfReindexedSuccessors π x i) (reindexStepIndex π x m i hki hmaps).val =
      π (pathOfReindexedSuccessors π x i)
        (visitCount (pathOfReindexedSuccessors π x) (pathOfReindexedSuccessors π x i) i) := by
  rw [reindexStepIndex_val]
  exact visitCount_visitTime_of_lt_visitCount (hmaps _ _ hki)

/-- The pairing of reconstruction times with original times, as an embedding. It is injective
because distinct reconstruction times use distinct cells of the successor array, and the paired
time determines both the state and the number of earlier visits to it. -/
private def reindexStepEmbedding (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m t : ℕ)
    (hused : ∀ i < t, visitCount (pathOfReindexedSuccessors π x)
      (pathOfReindexedSuccessors π x i) i < visitCount x (pathOfReindexedSuccessors π x i) m)
    (hmaps : ∀ a k, k < visitCount x a m → π a k < visitCount x a m) : Fin t ↪ Fin m where
  toFun i := reindexStepIndex π x m i (hused i i.isLt) hmaps
  inj' := by
    intro i j hij
    apply Fin.ext
    apply visitCell_injective (pathOfReindexedSuccessors π x)
    rw [visitCell_def, visitCell_def, Prod.mk.injEq]
    have hidx : (reindexStepIndex π x m i (hused i i.isLt) hmaps).val =
        (reindexStepIndex π x m j (hused j j.isLt) hmaps).val := congrArg Fin.val hij
    have hsource : pathOfReindexedSuccessors π x i = pathOfReindexedSuccessors π x j := by
      rw [← reindexStepIndex_source π x m i (hused i i.isLt) hmaps,
        ← reindexStepIndex_source π x m j (hused j j.isLt) hmaps, hidx]
    refine ⟨hsource, ?_⟩
    have hi := visitCount_reindexStepIndex π x m i (hused i i.isLt) hmaps
    have hj := visitCount_reindexStepIndex π x m j (hused j j.isLt) hmaps
    rw [hsource, hidx] at hi
    rw [hsource]
    exact (π (pathOfReindexedSuccessors π x j)).injective (hi.symm.trans hj)

/-- The value of `TauCeti.reindexStepEmbedding`. This is the only place its body is unfolded. -/
private theorem reindexStepEmbedding_apply (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m t : ℕ)
    (hused : ∀ i < t, visitCount (pathOfReindexedSuccessors π x)
      (pathOfReindexedSuccessors π x i) i < visitCount x (pathOfReindexedSuccessors π x i) m)
    (hmaps : ∀ a k, k < visitCount x a m → π a k < visitCount x a m) (i : Fin t) :
    reindexStepEmbedding π x m t hused hmaps i =
      reindexStepIndex π x m i (hused i i.isLt) hmaps :=
  rfl

/-- `TauCeti.reindexStepIndex_source`, read off the embedding. -/
private theorem reindexStepEmbedding_source (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m t : ℕ)
    (hused : ∀ i < t, visitCount (pathOfReindexedSuccessors π x)
      (pathOfReindexedSuccessors π x i) i < visitCount x (pathOfReindexedSuccessors π x i) m)
    (hmaps : ∀ a k, k < visitCount x a m → π a k < visitCount x a m) (i : Fin t) :
    x (reindexStepEmbedding π x m t hused hmaps i).val =
      pathOfReindexedSuccessors π x i.val := by
  rw [reindexStepEmbedding_apply]
  exact reindexStepIndex_source π x m i (hused i i.isLt) hmaps

/-- `TauCeti.reindexStepIndex_target`, read off the embedding. -/
private theorem reindexStepEmbedding_target (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m t : ℕ)
    (hused : ∀ i < t, visitCount (pathOfReindexedSuccessors π x)
      (pathOfReindexedSuccessors π x i) i < visitCount x (pathOfReindexedSuccessors π x i) m)
    (hmaps : ∀ a k, k < visitCount x a m → π a k < visitCount x a m) (i : Fin t) :
    x ((reindexStepEmbedding π x m t hused hmaps i).val + 1) =
      pathOfReindexedSuccessors π x (i.val + 1) := by
  rw [reindexStepEmbedding_apply]
  exact reindexStepIndex_target π x m i (hused i i.isLt) hmaps

/-- A reconstruction of length `t` arrives at each state at most as often as the original prefix
does over its whole length. -/
private theorem occCount_pathOfReindexedSuccessors_le (π : α → Equiv.Perm ℕ) (x : ℕ → α)
    (m t : ℕ)
    (hused : ∀ i < t, visitCount (pathOfReindexedSuccessors π x)
      (pathOfReindexedSuccessors π x i) i < visitCount x (pathOfReindexedSuccessors π x i) m)
    (hmaps : ∀ a k, k < visitCount x a m → π a k < visitCount x a m) (b : α) :
    occCount (fun i : Fin t => pathOfReindexedSuccessors π x (i.val + 1)) b ≤
      occCount (fun i : Fin m => x (i.val + 1)) b :=
  occCount_le_occCount_of_comp_eq (reindexStepEmbedding π x m t hused hmaps)
    (reindexStepEmbedding_target π x m t hused hmaps) b

/-- A reconstruction of length `t` departs from each state at most as often as the original prefix
does over its whole length. -/
private theorem visitCount_pathOfReindexedSuccessors_le (π : α → Equiv.Perm ℕ) (x : ℕ → α)
    (m t : ℕ)
    (hused : ∀ i < t, visitCount (pathOfReindexedSuccessors π x)
      (pathOfReindexedSuccessors π x i) i < visitCount x (pathOfReindexedSuccessors π x i) m)
    (hmaps : ∀ a k, k < visitCount x a m → π a k < visitCount x a m) (a : α) :
    visitCount (pathOfReindexedSuccessors π x) a t ≤ visitCount x a m := by
  rw [visitCount_def, visitCount_def]
  exact occCount_le_occCount_of_comp_eq (reindexStepEmbedding π x m t hused hmaps)
    (reindexStepEmbedding_source π x m t hused hmaps) a

/-- A reconstruction of length `t` that skips the original's step at time `r` arrives at
`x (r + 1)` strictly less often than the original prefix does. -/
private theorem occCount_pathOfReindexedSuccessors_lt (π : α → Equiv.Perm ℕ) (x : ℕ → α)
    (m t r : ℕ) (hr : r < m)
    (hused : ∀ i < t, visitCount (pathOfReindexedSuccessors π x)
      (pathOfReindexedSuccessors π x i) i < visitCount x (pathOfReindexedSuccessors π x i) m)
    (hmaps : ∀ a k, k < visitCount x a m → π a k < visitCount x a m)
    (homit : ∀ i : Fin t, (reindexStepEmbedding π x m t hused hmaps i).val ≠ r) :
    occCount (fun i : Fin t => pathOfReindexedSuccessors π x (i.val + 1)) (x (r + 1)) <
      occCount (fun i : Fin m => x (i.val + 1)) (x (r + 1)) :=
  occCount_lt_occCount_of_comp_eq (j := ⟨r, hr⟩) (reindexStepEmbedding π x m t hused hmaps)
    (reindexStepEmbedding_target π x m t hused hmaps) rfl fun i => Fin.ne_of_val_ne (homit i)

/-- **A reconstruction that has exhausted its current row ends where the original prefix does.**
The arrival/departure balance at the reconstruction's own endpoint forces it to coincide with the
original endpoint, because the reconstruction never arrives anywhere more often. -/
private theorem pathOfReindexedSuccessors_eq_of_visitCount_eq (π : α → Equiv.Perm ℕ) (x : ℕ → α)
    (m t : ℕ)
    (hused : ∀ i < t, visitCount (pathOfReindexedSuccessors π x)
      (pathOfReindexedSuccessors π x i) i < visitCount x (pathOfReindexedSuccessors π x i) m)
    (hmaps : ∀ a k, k < visitCount x a m → π a k < visitCount x a m)
    (hcount : visitCount (pathOfReindexedSuccessors π x) (pathOfReindexedSuccessors π x t) t =
      visitCount x (pathOfReindexedSuccessors π x t) m) :
    pathOfReindexedSuccessors π x t = x m := by
  classical
  have harr := occCount_pathOfReindexedSuccessors_le π x m t hused hmaps
    (pathOfReindexedSuccessors π x t)
  have hy := occCount_succ_add_zero_eq_visitCount_add_last (pathOfReindexedSuccessors π x)
    (pathOfReindexedSuccessors π x t) t
  have hx := occCount_succ_add_zero_eq_visitCount_add_last x (pathOfReindexedSuccessors π x t) m
  rw [pathOfReindexedSuccessors_zero, ite_eq_left rfl, hcount] at hy
  by_contra hend
  have hxm : ¬x m = pathOfReindexedSuccessors π x t := fun h => hend h.symm
  rw [ite_eq_right hxm] at hx
  omega

/-- **Matching departure counts at a common endpoint match the arrival counts too.** -/
private theorem occCount_pathOfReindexedSuccessors_eq_of_visitCount_eq (π : α → Equiv.Perm ℕ)
    (x : ℕ → α) (m t : ℕ) (b : α)
    (hcount : visitCount (pathOfReindexedSuccessors π x) b t = visitCount x b m)
    (hend : pathOfReindexedSuccessors π x t = x m) :
    occCount (fun i : Fin t => pathOfReindexedSuccessors π x (i.val + 1)) b =
      occCount (fun i : Fin m => x (i.val + 1)) b := by
  classical
  have hy := occCount_succ_add_zero_eq_visitCount_add_last (pathOfReindexedSuccessors π x) b t
  have hx := occCount_succ_add_zero_eq_visitCount_add_last x b m
  rw [pathOfReindexedSuccessors_zero, hend, hcount] at hy
  omega

/-- **A strictly shorter reconstruction is still deficient somewhere, and there is a last such
index.** If the reconstruction had already matched the original's visit count at every state the
original visits, summing the visit counts over the states used would force the two prefixes to have
the same length. -/
private theorem exists_maximal_visitCount_lt (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m t : ℕ)
    (hused : ∀ i < t, visitCount (pathOfReindexedSuccessors π x)
      (pathOfReindexedSuccessors π x i) i < visitCount x (pathOfReindexedSuccessors π x i) m)
    (hmaps : ∀ a k, k < visitCount x a m → π a k < visitCount x a m) (htm : t < m) :
    ∃ r < m, visitCount (pathOfReindexedSuccessors π x) (x r) t < visitCount x (x r) m ∧
      ∀ j, r < j → j < m →
        visitCount (pathOfReindexedSuccessors π x) (x j) t = visitCount x (x j) m := by
  classical
  have hnonempty : ((Finset.range m).filter fun r =>
      visitCount (pathOfReindexedSuccessors π x) (x r) t < visitCount x (x r) m).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    obtain ⟨S, hxS, hall⟩ : ∃ S : Finset α, (∀ j : Fin m, x j.val ∈ S) ∧
        ∀ a ∈ S, visitCount (pathOfReindexedSuccessors π x) a t = visitCount x a m := by
      refine ⟨Finset.image (fun j : Fin m => x j.val) Finset.univ,
        fun j => Finset.mem_image_of_mem _ (Finset.mem_univ j), ?_⟩
      intro a ha
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 ha
      refine Nat.le_antisymm
        (visitCount_pathOfReindexedSuccessors_le π x m t hused hmaps _) (not_lt.mp fun hlt => ?_)
      exact Finset.ne_empty_of_mem
        (Finset.mem_filter.2 ⟨Finset.mem_range.2 j.isLt, hlt⟩) hempty
    have hyS : ∀ j : Fin t, pathOfReindexedSuccessors π x j.val ∈ S := by
      intro j
      rw [← reindexStepEmbedding_source π x m t hused hmaps j]
      exact hxS _
    have hsumy : ∑ a ∈ S, visitCount (pathOfReindexedSuccessors π x) a t = t := by
      simpa only [visitCount_def] using
        sum_occCount_eq_card (fun j : Fin t => pathOfReindexedSuccessors π x j.val) hyS
    have hsumx : ∑ a ∈ S, visitCount x a m = m := by
      simpa only [visitCount_def] using sum_occCount_eq_card (fun j : Fin m => x j.val) hxS
    have hsumEq : ∑ a ∈ S, visitCount (pathOfReindexedSuccessors π x) a t =
        ∑ a ∈ S, visitCount x a m := Finset.sum_congr rfl hall
    omega
  obtain ⟨r, hrmem, hrmax⟩ :
      ∃ r ∈ (Finset.range m).filter fun q =>
          visitCount (pathOfReindexedSuccessors π x) (x q) t < visitCount x (x q) m,
        ∀ j ∈ (Finset.range m).filter fun q =>
          visitCount (pathOfReindexedSuccessors π x) (x q) t < visitCount x (x q) m, j ≤ r :=
    ⟨_, Finset.max'_mem _ hnonempty, fun j hj => Finset.le_max' _ j hj⟩
  rw [Finset.mem_filter, Finset.mem_range] at hrmem
  refine ⟨r, hrmem.1, hrmem.2, fun j hrj hjm => ?_⟩
  refine Nat.le_antisymm (visitCount_pathOfReindexedSuccessors_le π x m t hused hmaps (x j))
    (not_lt.mp fun hlt => ?_)
  have hle := hrmax j (Finset.mem_filter.2 ⟨Finset.mem_range.2 hjm, hlt⟩)
  omega

/-- **The reconstruction cannot consume a fixed last exit.** If `π` fixes the index of the last
visit of `x` to `x r` and the reconstruction has not yet used up that state's row, then no step of
the reconstruction is paired with time `r`. -/
private theorem reindexStepEmbedding_val_ne (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m t r : ℕ)
    (hused : ∀ i < t, visitCount (pathOfReindexedSuccessors π x)
      (pathOfReindexedSuccessors π x i) i < visitCount x (pathOfReindexedSuccessors π x i) m)
    (hmaps : ∀ a k, k < visitCount x a m → π a k < visitCount x a m)
    (hfixed : π (x r) (visitCount x (x r) r) = visitCount x (x r) r)
    (hbound : visitCount (pathOfReindexedSuccessors π x) (x r) t ≤ visitCount x (x r) r)
    (j : Fin t) : (reindexStepEmbedding π x m t hused hmaps j).val ≠ r := by
  intro hej
  have hsource : pathOfReindexedSuccessors π x j.val = x r := by
    rw [← reindexStepEmbedding_source π x m t hused hmaps j, hej]
  have hklt : visitCount (pathOfReindexedSuccessors π x) (x r) j.val <
      visitCount (pathOfReindexedSuccessors π x) (x r) t := by
    have hsucc : visitCount (pathOfReindexedSuccessors π x) (x r) (j.val + 1) =
        visitCount (pathOfReindexedSuccessors π x) (x r) j.val + 1 :=
      visitCount_succ_of_eq hsource
    have hj : j.val + 1 ≤ t := by
      simpa only [Nat.succ_eq_add_one] using Nat.succ_le_of_lt j.isLt
    have hmono := visitCount_monotone (pathOfReindexedSuccessors π x) (x r)
      hj
    omega
  have hp := visitCount_reindexStepIndex π x m j.val (hused j.val j.isLt) hmaps
  rw [reindexStepEmbedding_apply] at hej
  rw [hej, hsource] at hp
  have hk : visitCount (pathOfReindexedSuccessors π x) (x r) j.val = visitCount x (x r) r :=
    (π (x r)).injective (hp.symm.trans hfixed.symm)
  omega

/-- **The last-exit lemma.** Under a last-exit reindexing, every step of the reconstruction
consumes a successor entry that the original prefix consumes too: at each time `i < m` the
reconstruction has visited its current state strictly fewer times than the original prefix visits
it before `m`.

This is Lemma 1(b) of Fortini, Ladelli, Petris, and Regazzini. -/
theorem visitCount_pathOfReindexedSuccessors_lt_visitCount (π : α → Equiv.Perm ℕ) (x : ℕ → α)
    (m : ℕ) (h : LastExitAdmissible π x m) :
    ∀ i < m, visitCount (pathOfReindexedSuccessors π x) (pathOfReindexedSuccessors π x i) i <
      visitCount x (pathOfReindexedSuccessors π x i) m := by
  have hmaps : ∀ a k, k < visitCount x a m → π a k < visitCount x a m :=
    fun _ _ hk => h.maps_lt_visitCount hk
  have hlast : ∀ a, 0 < visitCount x a m →
      π a (visitCount x a m - 1) = visitCount x a m - 1 :=
    fun _ ha => h.apply_visitCount_sub_one ha
  intro i hi
  -- The proof is by strong induction on `i`. If the counts were equal, the reconstruction would
  -- end where the original prefix does. Its last deficient row then gives a fixed last exit which
  -- the reconstruction cannot have consumed, contradicting the arrival balance at the next state.
  induction i using Nat.strong_induction_on with
  | h t ih =>
    have hused : ∀ j < t, visitCount (pathOfReindexedSuccessors π x)
        (pathOfReindexedSuccessors π x j) j <
        visitCount x (pathOfReindexedSuccessors π x j) m := fun j hj => ih j hj (hj.trans hi)
    refine lt_of_le_of_ne
      (visitCount_pathOfReindexedSuccessors_le π x m t hused hmaps _) fun hcount => ?_
    -- The reconstruction has used up the row of its current state, so it ends at `x m`.
    have hend : pathOfReindexedSuccessors π x t = x m :=
      pathOfReindexedSuccessors_eq_of_visitCount_eq π x m t hused hmaps hcount
    -- Take the last index at which the original prefix is still ahead.
    obtain ⟨r, hr, hrinc, hmax⟩ := exists_maximal_visitCount_lt π x m t hused hmaps hi
    have hne : ∀ j, r < j → j < m → x j ≠ x r := by
      intro j hrj hjm hja
      have h := hmax j hrj hjm
      rw [hja] at h
      omega
    have hq := visitCount_eq_succ_of_forall_ne x hr hne
    -- Time `r` is the last visit of `x` to `x r`, so `hlast` fixes the entry it consumes.
    have hfixed : π (x r) (visitCount x (x r) r) = visitCount x (x r) r := by
      have hsub : visitCount x (x r) m - 1 = visitCount x (x r) r := by omega
      simpa only [hsub] using hlast (x r) (by omega)
    have hblt := occCount_pathOfReindexedSuccessors_lt π x m t r hr hused hmaps
      (reindexStepEmbedding_val_ne π x m t r hused hmaps hfixed (by omega))
    -- Yet the arrival counts at `x (r + 1)` have to agree, since both prefixes end at `x m`.
    have hbcount : visitCount (pathOfReindexedSuccessors π x) (x (r + 1)) t =
        visitCount x (x (r + 1)) m := by
      have hrle : r + 1 ≤ m := by
        simpa only [Nat.succ_eq_add_one] using Nat.succ_le_of_lt hr
      rcases eq_or_lt_of_le hrle with hlastIndex | hbefore
      · rw [hlastIndex, ← hend]
        exact hcount
      · exact hmax (r + 1) (by omega) hbefore
    exact absurd (occCount_pathOfReindexedSuccessors_eq_of_visitCount_eq π x m t (x (r + 1))
      hbcount hend) (Nat.ne_of_lt hblt)

/-- The pairing of times at the full horizon `m`, promoted to a permutation of `Fin m`: an
injective self-map of a finite type is a bijection. -/
private def reindexStepEquiv (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m : ℕ)
    (hmaps : ∀ a k, k < visitCount x a m → π a k < visitCount x a m)
    (hlast : ∀ a, 0 < visitCount x a m →
      π a (visitCount x a m - 1) = visitCount x a m - 1) : Fin m ≃ Fin m :=
  (reindexStepEmbedding π x m m
    (visitCount_pathOfReindexedSuccessors_lt_visitCount π x m ⟨hmaps, hlast⟩)
    hmaps).equivOfFiniteSelfEmbedding

/-- The value of `TauCeti.reindexStepEquiv`. This is the only place its body is unfolded. -/
private theorem reindexStepEquiv_apply (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m : ℕ)
    (hmaps : ∀ a k, k < visitCount x a m → π a k < visitCount x a m)
    (hlast : ∀ a, 0 < visitCount x a m →
      π a (visitCount x a m - 1) = visitCount x a m - 1) (i : Fin m) :
    reindexStepEquiv π x m hmaps hlast i =
      reindexStepEmbedding π x m m
        (visitCount_pathOfReindexedSuccessors_lt_visitCount π x m ⟨hmaps, hlast⟩) hmaps i :=
  by
    rw [reindexStepEquiv, ← Equiv.coe_toEmbedding,
      Function.Embedding.toEmbedding_equivOfFiniteSelfEmbedding]

/-- `TauCeti.reindexStepIndex_source`, read off the permutation. -/
private theorem reindexStepEquiv_source (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m : ℕ)
    (hmaps : ∀ a k, k < visitCount x a m → π a k < visitCount x a m)
    (hlast : ∀ a, 0 < visitCount x a m →
      π a (visitCount x a m - 1) = visitCount x a m - 1) (i : Fin m) :
    x (reindexStepEquiv π x m hmaps hlast i) = pathOfReindexedSuccessors π x i := by
  rw [reindexStepEquiv_apply]
  exact reindexStepEmbedding_source π x m m _ hmaps i

/-- `TauCeti.reindexStepIndex_target`, read off the permutation. -/
private theorem reindexStepEquiv_target (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m : ℕ)
    (hmaps : ∀ a k, k < visitCount x a m → π a k < visitCount x a m)
    (hlast : ∀ a, 0 < visitCount x a m →
      π a (visitCount x a m - 1) = visitCount x a m - 1) (i : Fin m) :
    x (reindexStepEquiv π x m hmaps hlast i + 1) = pathOfReindexedSuccessors π x (i + 1) := by
  rw [reindexStepEquiv_apply]
  exact reindexStepEmbedding_target π x m m _ hmaps i

/-- A last-exit reindexing uses each prescribed successor row exactly as often as the original
finite prefix. -/
theorem visitCount_pathOfReindexedSuccessors (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m : ℕ)
    (h : LastExitAdmissible π x m) (a : α) :
    visitCount (pathOfReindexedSuccessors π x) a m = visitCount x a m := by
  classical
  have hmaps : ∀ b k, k < visitCount x b m → π b k < visitCount x b m :=
    fun _ _ hk => h.maps_lt_visitCount hk
  have hlast : ∀ b, 0 < visitCount x b m →
      π b (visitCount x b m - 1) = visitCount x b m - 1 :=
    fun _ hb => h.apply_visitCount_sub_one hb
  rw [visitCount_def, visitCount_def, occCount_eq_card_filter, occCount_eq_card_filter,
    ← Fintype.card_coe, ← Fintype.card_coe]
  refine Fintype.card_congr ((reindexStepEquiv π x m hmaps hlast).subtypeEquiv fun i => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [reindexStepEquiv_source π x m hmaps hlast i]

/-- A finite path reconstructed after last-exit reindexing has the same endpoint as the original
prefix. -/
theorem pathOfReindexedSuccessors_eq (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m : ℕ)
    (h : LastExitAdmissible π x m) : pathOfReindexedSuccessors π x m = x m :=
  pathOfReindexedSuccessors_eq_of_visitCount_eq π x m m
    (visitCount_pathOfReindexedSuccessors_lt_visitCount π x m h)
    (fun _ _ hk => h.maps_lt_visitCount hk)
    (visitCount_pathOfReindexedSuccessors π x m h (pathOfReindexedSuccessors π x m))

/-- A finite path reconstructed after last-exit reindexing has the same transition counts as the
original prefix. -/
theorem transitionCount_pathOfReindexedSuccessors (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m : ℕ)
    (h : LastExitAdmissible π x m) (a b : α) :
    transitionCount (fun i : Fin (m + 1) => pathOfReindexedSuccessors π x i) a b =
      transitionCount (fun i : Fin (m + 1) => x i) a b := by
  classical
  have hmaps : ∀ c k, k < visitCount x c m → π c k < visitCount x c m :=
    fun _ _ hk => h.maps_lt_visitCount hk
  have hlast : ∀ c, 0 < visitCount x c m →
      π c (visitCount x c m - 1) = visitCount x c m - 1 :=
    fun _ hc => h.apply_visitCount_sub_one hc
  rw [transitionCount_eq_card_filter, transitionCount_eq_card_filter,
    ← Fintype.card_coe, ← Fintype.card_coe]
  refine Fintype.card_congr ((reindexStepEquiv π x m hmaps hlast).subtypeEquiv fun i => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc, Fin.val_succ]
  rw [reindexStepEquiv_source π x m hmaps hlast i, reindexStepEquiv_target π x m hmaps hlast i]

end TauCeti

end

end
