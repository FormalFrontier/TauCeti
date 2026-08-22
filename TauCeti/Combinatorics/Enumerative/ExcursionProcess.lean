/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Intervals
public import TauCeti.Combinatorics.Enumerative.LoopWord
public import TauCeti.Combinatorics.Enumerative.SuccessorArray

/-!
# The excursion process of a sequence

Fix a state `a` of a sequence `x : ℕ → α`.  Its `k`-th excursion from `a` is the finite
list of values strictly between the `k`-th and `(k + 1)`-st visits to `a`.  This file defines that
list as `TauCeti.excursion x a k` and packages the first `m` excursions as
`TauCeti.excursionPrefix x a m`.

When `x` visits `a` infinitely often, the visit times are genuine and strictly increasing.  The
main reconstruction theorem then says that spelling out the first `m` excursions with
`TauCeti.loopPath` recovers exactly the segment of `x` between its zeroth and `m`-th visits:

```text
loopPath a (excursionPrefix x a m)
  = (List.Ico (visitTime x a 0) (visitTime x a m + 1)).map x.
```

In particular, if `x 0 = a`, this is the initial path segment through its `m`-th return to `a`.
This is the combinatorial bridge from the finite excursion-reordering theorem in
`TauCeti.Probability.Exchangeability.Excursion` to the exchangeability of the excursion process
of a recurrent Markov exchangeable path.

## Main definitions

* `TauCeti.excursion`: the finite word strictly between two consecutive visits to a state.
* `TauCeti.excursionPrefix`: the list of the first `m` excursions.

## Main results

* `TauCeti.not_mem_excursion`: an excursion does not visit its base state.
* `TauCeti.loopPath_excursionPrefix`: the first excursions reconstruct the corresponding segment
  of the original sequence.
* `TauCeti.loopSteps_excursionPrefix`: the number of reconstructed transitions is the difference
  of the endpoint visit times.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 8, "Markov exchangeability".

No material is adapted from `cameronfreer/exchangeability`, which treats exchangeable rather than
Markov exchangeable sequences.
-/

public section

noncomputable section

namespace TauCeti

variable {α : Type*} {x : ℕ → α} {a : α} {k m : ℕ}

/-! ## Excursions and finite prefixes -/

/-- The `k`-th excursion of `x` from `a`: the finite list of values at the times strictly between
the `k`-th and `(k + 1)`-st visits to `a`.

If either visit does not exist, `visitTime` uses its documented junk value and this interval may
be empty.  The reconstruction API below assumes that `x` visits `a` infinitely often. -/
def excursion (x : ℕ → α) (a : α) (k : ℕ) : List α :=
  (List.Ico (visitTime x a k + 1) (visitTime x a (k + 1))).map x

private theorem excursion_def_private (x : ℕ → α) (a : α) (k : ℕ) :
    excursion x a k =
      (List.Ico (visitTime x a k + 1) (visitTime x a (k + 1))).map x :=
  rfl

/-- The defining equation of an excursion. -/
theorem excursion_def (x : ℕ → α) (a : α) (k : ℕ) :
    excursion x a k =
      (List.Ico (visitTime x a k + 1) (visitTime x a (k + 1))).map x :=
  excursion_def_private x a k

/-- The list of the first `m` excursions of `x` from `a`. -/
def excursionPrefix (x : ℕ → α) (a : α) (m : ℕ) : List (List α) :=
  (List.range m).map (excursion x a)

private theorem excursionPrefix_def_private (x : ℕ → α) (a : α) (m : ℕ) :
    excursionPrefix x a m = (List.range m).map (excursion x a) :=
  rfl

/-- The defining equation of a finite excursion prefix. -/
theorem excursionPrefix_def (x : ℕ → α) (a : α) (m : ℕ) :
    excursionPrefix x a m = (List.range m).map (excursion x a) :=
  excursionPrefix_def_private x a m

@[simp]
theorem excursionPrefix_zero (x : ℕ → α) (a : α) : excursionPrefix x a 0 = [] := by
  rw [excursionPrefix_def]
  simp

@[simp]
theorem excursionPrefix_succ (x : ℕ → α) (a : α) (m : ℕ) :
    excursionPrefix x a (m + 1) = excursionPrefix x a m ++ [excursion x a m] := by
  rw [excursionPrefix_def, excursionPrefix_def, List.range_succ, List.map_append]
  rfl

@[simp]
theorem length_excursionPrefix (x : ℕ → α) (a : α) (m : ℕ) :
    (excursionPrefix x a m).length = m := by
  simp [excursionPrefix_def]

/-! ## Elementary properties -/

/-- The length of an excursion is the gap between its endpoint visit times, less one. -/
theorem length_excursion (x : ℕ → α) (a : α) (k : ℕ) :
    (excursion x a k).length = visitTime x a (k + 1) - visitTime x a k - 1 := by
  rw [excursion_def, List.length_map, List.Ico.length]
  omega

/-- An excursion never contains its base state.  This remains true in the finite-visit case,
where `visitTime` may make the interval empty. -/
theorem not_mem_excursion (x : ℕ → α) (a : α) (k : ℕ) : a ∉ excursion x a k := by
  rw [excursion_def]
  intro ha
  obtain ⟨n, hn, hxn⟩ := List.mem_map.1 ha
  have hnmem := List.Ico.mem.1 hn
  have hle' : n ≤ Nat.nth (fun i => x i = a) k :=
    Nat.le_nth_of_lt_nth_succ (by simpa only [visitTime_def] using hnmem.2) hxn
  have hle : n ≤ visitTime x a k := by simpa only [visitTime_def] using hle'
  omega

/-! ## Reconstruction -/

/-- Appending excursion lists splices their loop paths at the shared base state. -/
private theorem loopPath_append (a : α) (bs cs : List (List α)) :
    loopPath a (bs ++ cs) = (loopPath a bs).dropLast ++ loopPath a cs := by
  induction bs with
  | nil => simp
  | cons e bs ih =>
      have hne : loopPath a bs ≠ [] := by cases bs <;> simp
      have hdrop : (loopPath a (e :: bs)).dropLast =
          a :: (e ++ (loopPath a bs).dropLast) := by
        rw [loopPath_cons]
        calc
          (a :: (e ++ loopPath a bs)).dropLast = ((a :: e) ++ loopPath a bs).dropLast := by
            simp
          _ = (a :: e) ++ (loopPath a bs).dropLast :=
            List.dropLast_append_of_ne_nil hne
          _ = a :: (e ++ (loopPath a bs).dropLast) := by simp
      rw [List.cons_append, loopPath_cons, ih, hdrop]
      rw [List.cons_append, List.append_assoc]

/-- A single genuine excursion spells out exactly the segment between its two endpoint visits. -/
theorem loopPath_singleton_excursion (h : {n | x n = a}.Infinite) (k : ℕ) :
    loopPath a [excursion x a k] =
      (List.Ico (visitTime x a k) (visitTime x a (k + 1) + 1)).map x := by
  rw [loopPath_cons, loopPath_nil, excursion_def]
  have hk := visitTime_apply_of_infinite h k
  have hk1 := visitTime_apply_of_infinite h (k + 1)
  have hlt : visitTime x a k < visitTime x a (k + 1) :=
    visitTime_strictMono_of_infinite h (by omega)
  have hsucc : visitTime x a k + 1 ≤ visitTime x a (k + 1) := by omega
  have hIco :
      List.Ico (visitTime x a k) (visitTime x a (k + 1) + 1) =
        [visitTime x a k] ++
          List.Ico (visitTime x a k + 1) (visitTime x a (k + 1)) ++
            [visitTime x a (k + 1)] := by
    rw [← List.Ico.succ_singleton,
      List.Ico.append_consecutive (Nat.le_succ _) hsucc,
      ← List.Ico.succ_singleton,
      List.Ico.append_consecutive hlt.le (Nat.le_succ _)]
  rw [hIco, List.map_append, List.map_append, List.map_singleton, List.map_singleton, hk, hk1]
  rfl

/-- The loop path of the first `m` genuine excursions is the original sequence segment from the
zeroth through the `m`-th visit to the base state. -/
theorem loopPath_excursionPrefix (h : {n | x n = a}.Infinite) (m : ℕ) :
    loopPath a (excursionPrefix x a m) =
      (List.Ico (visitTime x a 0) (visitTime x a m + 1)).map x := by
  induction m with
  | zero =>
      simp only [excursionPrefix_zero, loopPath_nil]
      rw [List.Ico.succ_singleton, List.map_singleton, visitTime_apply_of_infinite h]
  | succ m ih =>
      rw [excursionPrefix_succ, loopPath_append, ih, loopPath_singleton_excursion h]
      have hmono := (visitTime_strictMono_of_infinite h).monotone (Nat.zero_le m)
      have hdrop :
          ((List.Ico (visitTime x a 0) (visitTime x a m + 1)).map x).dropLast =
            (List.Ico (visitTime x a 0) (visitTime x a m)).map x := by
        rw [List.Ico.succ_top hmono, List.map_append, List.map_singleton,
          List.dropLast_append_cons]
        simp
      rw [hdrop, ← List.map_append, List.Ico.append_consecutive hmono
        ((visitTime_strictMono_of_infinite h m.lt_succ_self).le.trans (Nat.le_succ _))]

/-- The first `m` genuine excursions contain exactly the transitions between the zeroth and
`m`-th visits to the base state. -/
theorem loopSteps_excursionPrefix (h : {n | x n = a}.Infinite) (m : ℕ) :
    loopSteps (excursionPrefix x a m) = visitTime x a m - visitTime x a 0 := by
  have hlen := congrArg List.length (loopPath_excursionPrefix h m)
  rw [length_loopPath, List.length_map, List.Ico.length] at hlen
  omega

/-- For a sequence starting at `a`, the first `m` excursions reconstruct its initial segment
through the `m`-th return. -/
theorem loopPath_excursionPrefix_of_zero (h : {n | x n = a}.Infinite) (h0 : x 0 = a) (m : ℕ) :
    loopPath a (excursionPrefix x a m) =
      (List.range (visitTime x a m + 1)).map x := by
  rw [loopPath_excursionPrefix h, visitTime_zero_of_eq h0, List.Ico.zero_bot]

/-- For a sequence starting at `a`, the first `m` excursions have total duration equal to its
`m`-th return time. -/
theorem loopSteps_excursionPrefix_of_zero (h : {n | x n = a}.Infinite) (h0 : x 0 = a) (m : ℕ) :
    loopSteps (excursionPrefix x a m) = visitTime x a m := by
  rw [loopSteps_excursionPrefix h, visitTime_zero_of_eq h0, Nat.sub_zero]

end TauCeti

end

end
