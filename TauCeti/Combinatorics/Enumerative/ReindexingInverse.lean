/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.LastExit

/-!
# Inverting last-exit successor reindexing

A last-exit-admissible family of row permutations reorders the successor entries used by a finite
path prefix.  Finite reconstruction preserves every row's visit count, so the inverse family is
admissible for the reconstructed prefix.  Reconstructing a second time with those inverse
permutations then recovers the original prefix.

This gives the invertibility needed to turn last-exit reconstruction into equivalences between
collections of finite paths.  Such equivalences transport path events while preserving the initial
state and transition counts.

## Main results

* `TauCeti.LastExitAdmissible.symm_pathOfReindexedSuccessors` proves admissibility of the inverse
  row permutations on the reconstructed prefix;
* `TauCeti.pathOfReindexedSuccessors_symm_apply` proves that inverse reconstruction recovers every
  entry through the finite horizon.

## References

* S. Fortini, L. Ladelli, G. Petris, and E. Regazzini, "On mixtures of distributions of Markov
  chains", *Stochastic Processes and their Applications* 100 (2002), 147--165, Lemma 1(b).
* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115--130.
-/

public section

noncomputable section

namespace TauCeti

variable {α : Type*}

attribute [local instance] Classical.decEq

/-- **The inverse row permutations are last-exit admissible for the reconstructed prefix.**
Last-exit reconstruction preserves each row's visit count.  On that common finite row prefix, a
permutation preserves the prefix if and only if its inverse does, and a fixed last entry is fixed
by the inverse as well. -/
theorem LastExitAdmissible.symm_pathOfReindexedSuccessors {π : α → Equiv.Perm ℕ}
    {x : ℕ → α} {m : ℕ} (h : LastExitAdmissible π x m) :
    LastExitAdmissible (fun a => (π a).symm) (pathOfReindexedSuccessors π x) m := by
  rw [lastExitAdmissible_iff]
  constructor
  · intro a k hk
    rw [visitCount_pathOfReindexedSuccessors π x m h] at hk ⊢
    let f : Fin (visitCount x a m) → Fin (visitCount x a m) :=
      fun j => ⟨π a j, h.maps_lt_visitCount j.isLt⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      exact (π a).injective (congrArg Fin.val hij)
    obtain ⟨j, hj⟩ := Finite.surjective_of_injective hf ⟨k, hk⟩
    have hjval : π a j.val = k := congrArg Fin.val hj
    rw [← hjval, (π a).symm_apply_apply]
    exact j.isLt
  · intro a ha
    rw [visitCount_pathOfReindexedSuccessors π x m h] at ha ⊢
    have hlast := h.apply_visitCount_sub_one ha
    rw [← hlast, (π a).symm_apply_apply]
    exact hlast.symm

/-- **Reindexing a finite prefix by inverse row permutations recovers the prefix.** If `π` is
last-exit admissible through time `m`, then reconstructing from the `π`-reindexed successor rows
and subsequently from the `π⁻¹`-reindexed rows returns `x i` for every `i ≤ m`.

The conclusion is deliberately restricted to the admissible finite horizon: unused successor
entries are unconstrained, so the two infinite reconstructions need not agree after `m`. -/
@[simp]
theorem pathOfReindexedSuccessors_symm_apply {π : α → Equiv.Perm ℕ} {x : ℕ → α} {m : ℕ}
    (h : LastExitAdmissible π x m) {i : ℕ} (hi : i ≤ m) :
    pathOfReindexedSuccessors (fun a => (π a).symm) (pathOfReindexedSuccessors π x) i = x i := by
  let y := pathOfReindexedSuccessors π x
  let z := pathOfReindexedSuccessors (fun a => (π a).symm) y
  have hinv : LastExitAdmissible (fun a => (π a).symm) y m :=
    h.symm_pathOfReindexedSuccessors
  -- Expose only the two local abbreviations; the reconstruction definitions themselves remain
  -- behind their public recursion equations.
  change z i = x i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    match i with
    | 0 => simp [z, y]
    | i + 1 =>
      have him : i < m := Nat.lt_of_succ_le hi
      have hiz : z i = x i := ih i (Nat.lt_succ_self i) (Nat.le_of_succ_le hi)
      have hcount : visitCount z (x i) i = visitCount x (x i) i := by
        apply visitCount_congr
        intro j hj
        exact ih j (hj.trans (Nat.lt_succ_self i))
          (hj.le.trans (Nat.le_of_succ_le hi))
      have hused := visitCount_pathOfReindexedSuccessors_lt_visitCount
        (fun a => (π a).symm) y m hinv i him
      -- Normalize the theorem through the local abbreviation `z` before rewriting its endpoint.
      change visitCount z (z i) i < visitCount y (z i) m at hused
      rw [hiz] at hused
      have hindex : (π (x i)).symm (visitCount x (x i) i) < visitCount y (x i) m := by
        exact hinv.maps_lt_visitCount (hcount ▸ hused)
      have hstep := pathOfReindexedSuccessors_succ (fun a => (π a).symm) y i
      -- State the public recursion equation using the local name `z` on both sides.
      change z (i + 1) = successorArray y (z i)
        ((π (z i)).symm (visitCount z (z i) i)) at hstep
      rw [hstep]
      rw [hiz, hcount,
        successorArray_pathOfReindexedSuccessors_of_lt_visitCount π x (x i) hindex,
        (π (x i)).apply_symm_apply, successorArray_visitCount]

end TauCeti

end

end
