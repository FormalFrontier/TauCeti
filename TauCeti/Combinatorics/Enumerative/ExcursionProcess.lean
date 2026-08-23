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

When the `m`-th visit exists, the visit times through `m` are genuine and strictly increasing.
The main reconstruction theorem then says that spelling out the first `m` excursions with
`TauCeti.loopPath` recovers exactly the segment of `x` between its zeroth and `m`-th visits:

```text
loopPath a (excursionPrefix x a m)
  = (List.Ico (visitTime x a 0) (visitTime x a m + 1)).map x.
```

In particular this applies whenever `x` visits `a` infinitely often, and if `x 0 = a`, the result
is the initial path segment through its `m`-th return to `a`.  This is the combinatorial bridge
from the finite excursion-reordering theorem in
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
be empty. -/
def excursion (x : ℕ → α) (a : α) (k : ℕ) : List α :=
  (List.Ico (visitTime x a k + 1) (visitTime x a (k + 1))).map x

/-- The defining equation of an excursion. -/
theorem excursion_def (x : ℕ → α) (a : α) (k : ℕ) :
    excursion x a k =
      (List.Ico (visitTime x a k + 1) (visitTime x a (k + 1))).map x :=
  (rfl)

/-- The list of the first `m` excursions of `x` from `a`. -/
def excursionPrefix (x : ℕ → α) (a : α) (m : ℕ) : List (List α) :=
  (List.range m).map (excursion x a)

/-- The defining equation of a finite excursion prefix. -/
theorem excursionPrefix_def (x : ℕ → α) (a : α) (m : ℕ) :
    excursionPrefix x a m = (List.range m).map (excursion x a) :=
  (rfl)

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

/-- Membership in an excursion is membership in the corresponding open interval of times.

Deliberately not `@[simp]`: it would rewrite the left-hand side of the `@[simp]` lemma
`TauCeti.not_mem_excursion` into an existential that `simp` cannot close, so `simp` would stop
proving that an excursion avoids its base state. -/
theorem mem_excursion_iff {b : α} :
    b ∈ excursion x a k ↔
      ∃ n, visitTime x a k < n ∧ n < visitTime x a (k + 1) ∧ x n = b := by
  rw [excursion_def]
  constructor
  · intro hb
    obtain ⟨n, hn, hxn⟩ := List.mem_map.1 hb
    obtain ⟨hnk, hnk1⟩ := List.Ico.mem.1 hn
    exact ⟨n, by omega, hnk1, hxn⟩
  · rintro ⟨n, hnk, hnk1, hxn⟩
    exact List.mem_map.2 ⟨n, List.Ico.mem.2 ⟨by omega, hnk1⟩, hxn⟩

/-- The `k`-th entry of a finite excursion prefix is the `k`-th excursion. -/
@[simp]
theorem getElem_excursionPrefix (hk : k < m) :
    (excursionPrefix x a m)[k]'(by simpa using hk) = excursion x a k := by
  simp [excursionPrefix_def]

/-! ## Elementary properties -/

/-- The length of an excursion is the gap between its endpoint visit times, less one. -/
@[simp]
theorem length_excursion (x : ℕ → α) (a : α) (k : ℕ) :
    (excursion x a k).length = visitTime x a (k + 1) - visitTime x a k - 1 := by
  rw [excursion_def, List.length_map, List.Ico.length]
  omega

/-- An excursion never contains its base state.  This remains true in the finite-visit case,
where `visitTime` may make the interval empty. -/
@[simp]
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

/-- A single excursion whose next endpoint exists spells out exactly the segment between its two
endpoint visits. -/
theorem loopPath_singleton_excursion
    (h : ∃ n, x n = a ∧ visitCount x a n = k + 1) :
    loopPath a [excursion x a k] =
      (List.Ico (visitTime x a k) (visitTime x a (k + 1) + 1)).map x := by
  rw [loopPath_cons, loopPath_nil, excursion_def]
  have hk := apply_visitTime_of_le h (Nat.le_succ k)
  have hk1 := apply_visitTime_of_le h le_rfl
  have hlt : visitTime x a k < visitTime x a (k + 1) :=
    visitTime_lt_visitTime_of_le h (by omega) le_rfl
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

/-- The infinite-visit form of `loopPath_singleton_excursion`. -/
theorem loopPath_singleton_excursion_of_infinite (h : {n | x n = a}.Infinite) (k : ℕ) :
    loopPath a [excursion x a k] =
      (List.Ico (visitTime x a k) (visitTime x a (k + 1) + 1)).map x :=
  loopPath_singleton_excursion (exists_visitCount_of_infinite h (k + 1))

/-- If the `m`-th visit exists, the loop path of the first `m` excursions is the original sequence
segment from the zeroth through the `m`-th visit to the base state. -/
theorem loopPath_excursionPrefix (h : ∃ n, x n = a ∧ visitCount x a n = m) :
    loopPath a (excursionPrefix x a m) =
      (List.Ico (visitTime x a 0) (visitTime x a m + 1)).map x := by
  induction m with
  | zero =>
      simp only [excursionPrefix_zero, loopPath_nil]
      rw [List.Ico.succ_singleton, List.map_singleton, apply_visitTime_of_le h le_rfl]
  | succ m ih =>
      have hm : ∃ n, x n = a ∧ visitCount x a n = m := exists_visitCount_of_le h (Nat.le_succ m)
      rw [excursionPrefix_succ, loopPath_append, ih hm, loopPath_singleton_excursion h]
      have hstep : visitTime x a m < visitTime x a (m + 1) :=
        visitTime_lt_visitTime_of_le h (by omega) le_rfl
      have hmono : visitTime x a 0 ≤ visitTime x a m := by
        rcases Nat.eq_zero_or_pos m with rfl | hm0
        · exact le_rfl
        · exact (visitTime_lt_visitTime_of_le (j := m) h hm0 (Nat.le_succ m)).le
      have hdrop :
          ((List.Ico (visitTime x a 0) (visitTime x a m + 1)).map x).dropLast =
            (List.Ico (visitTime x a 0) (visitTime x a m)).map x := by
        rw [List.Ico.succ_top hmono, List.map_append, List.map_singleton,
          List.dropLast_append_cons]
        simp
      rw [hdrop, ← List.map_append,
        List.Ico.append_consecutive hmono (hstep.le.trans (Nat.le_succ _))]

/-- The infinite-visit form of `loopPath_excursionPrefix`. -/
theorem loopPath_excursionPrefix_of_infinite (h : {n | x n = a}.Infinite) (m : ℕ) :
    loopPath a (excursionPrefix x a m) =
      (List.Ico (visitTime x a 0) (visitTime x a m + 1)).map x :=
  loopPath_excursionPrefix (exists_visitCount_of_infinite h m)

/-- If the `m`-th visit exists, the first `m` excursions contain exactly the transitions between
the zeroth and `m`-th visits to the base state. -/
theorem loopSteps_excursionPrefix (h : ∃ n, x n = a ∧ visitCount x a n = m) :
    loopSteps (excursionPrefix x a m) = visitTime x a m - visitTime x a 0 := by
  have hlen := congrArg List.length (loopPath_excursionPrefix h)
  rw [length_loopPath, List.length_map, List.Ico.length] at hlen
  omega

/-- The infinite-visit form of `loopSteps_excursionPrefix`. -/
theorem loopSteps_excursionPrefix_of_infinite (h : {n | x n = a}.Infinite) (m : ℕ) :
    loopSteps (excursionPrefix x a m) = visitTime x a m - visitTime x a 0 :=
  loopSteps_excursionPrefix (exists_visitCount_of_infinite h m)

/-- If the `m`-th visit exists for a sequence starting at `a`, its first `m` excursions reconstruct
the initial segment through the `m`-th return. -/
theorem loopPath_excursionPrefix_of_zero
    (h : ∃ n, x n = a ∧ visitCount x a n = m) (h0 : x 0 = a) :
    loopPath a (excursionPrefix x a m) =
      (List.range (visitTime x a m + 1)).map x := by
  rw [loopPath_excursionPrefix h, visitTime_zero_of_eq h0, List.Ico.zero_bot]

/-- The infinite-visit form of `loopPath_excursionPrefix_of_zero`. -/
theorem loopPath_excursionPrefix_of_infinite_of_zero
    (h : {n | x n = a}.Infinite) (h0 : x 0 = a) (m : ℕ) :
    loopPath a (excursionPrefix x a m) =
      (List.range (visitTime x a m + 1)).map x :=
  loopPath_excursionPrefix_of_zero (exists_visitCount_of_infinite h m) h0

/-- If the `m`-th visit exists for a sequence starting at `a`, its first `m` excursions have total
duration equal to the `m`-th return time. -/
theorem loopSteps_excursionPrefix_of_zero
    (h : ∃ n, x n = a ∧ visitCount x a n = m) (h0 : x 0 = a) :
    loopSteps (excursionPrefix x a m) = visitTime x a m := by
  rw [loopSteps_excursionPrefix h, visitTime_zero_of_eq h0, Nat.sub_zero]

/-- The infinite-visit form of `loopSteps_excursionPrefix_of_zero`. -/
theorem loopSteps_excursionPrefix_of_infinite_of_zero
    (h : {n | x n = a}.Infinite) (h0 : x 0 = a) (m : ℕ) :
    loopSteps (excursionPrefix x a m) = visitTime x a m :=
  loopSteps_excursionPrefix_of_zero (exists_visitCount_of_infinite h m) h0

end TauCeti

end

end
