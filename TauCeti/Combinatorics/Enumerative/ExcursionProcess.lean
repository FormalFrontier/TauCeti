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
is the initial path segment through its `m`-th return to `a`.  Read as an equivalence
(`TauCeti.eqOn_loopPathAt_iff_excursionPrefix_eq`), this is the combinatorial bridge from the finite
excursion-reordering theorem in `TauCeti.Probability.Exchangeability.Excursion` to the
exchangeability of the excursion process of a recurrent Markov exchangeable path, which is proved
in `TauCeti.Probability.Exchangeability.Recurrence.Excursion`: a prescribed list of first
excursions is nothing but a prescribed finite path.

## Main definitions

* `TauCeti.excursion`: the finite word strictly between two consecutive visits to a state.
* `TauCeti.excursionPrefix`: the list of the first `m` excursions.
* `TauCeti.pathOfExcursions`: the sequence spelled out by a base state and an infinite sequence of
  excursions.

## Main results

* `TauCeti.not_mem_excursion`: an excursion does not visit its base state.
* `TauCeti.loopPath_excursionPrefix`: the first excursions reconstruct the corresponding segment
  of the original sequence.
* `TauCeti.loopSteps_excursionPrefix`: the number of reconstructed transitions is the difference
  of the endpoint visit times.
* `TauCeti.visitCount_loopPathAt`: a loop visits its base state once per excursion.
* `TauCeti.eqOn_loopPathAt_iff_excursionPrefix_eq`: for a path whose relevant return exists, having
  prescribed first excursions is the same as spelling out their loop word.
* `TauCeti.pathOfExcursions_excursion`: a sequence that starts at a state and returns to it
  infinitely often is rebuilt from its own excursions.
* `TauCeti.excursion_pathOfExcursions`: conversely, a sequence spelled out by excursions avoiding
  the base state has exactly those excursions.

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

/-- No excursion of a finite excursion prefix visits the base state, so such a prefix is a
legitimate argument for `TauCeti.loopPath_injOn`. -/
theorem forall_not_mem_excursionPrefix (x : ℕ → α) (a : α) (m : ℕ) :
    ∀ e ∈ excursionPrefix x a m, a ∉ e := by
  intro e he
  rw [excursionPrefix_def] at he
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 he
  exact not_mem_excursion x a k

/-- **A loop visits its base state once per excursion.** Counting the visits a loop makes to its
base letter over its whole span counts its excursions, because an excursion never returns there. -/
theorem visitCount_loopPathAt (a : α) {bs : List (List α)} (havoid : ∀ e ∈ bs, a ∉ e) :
    visitCount (loopPathAt a bs) a (loopSteps bs) = bs.length := by
  induction bs with
  | nil => simp
  | cons e bs ih =>
    -- The initial letter is the only visit inside the first excursion's span.
    have hfirst : visitCount (loopPathAt a (e :: bs)) a (e.length + 1) = 1 := by
      have h2 : visitCount (fun i => loopPathAt a (e :: bs) (1 + i)) a e.length = 0 := by
        refine visitCount_eq_zero_of_forall_ne fun i hi => ?_
        rw [Nat.add_comm 1 i, loopPathAt_cons_of_lt a e bs hi]
        exact fun hget => havoid e List.mem_cons_self (hget ▸ List.getElem_mem hi)
      rw [Nat.add_comm e.length 1, visitCount_add, h2]
      simp
    have hshift : (fun i => loopPathAt a (e :: bs) (e.length + 1 + i)) = loopPathAt a bs :=
      funext (loopPathAt_cons_add a e bs)
    rw [loopSteps_cons, visitCount_add, hfirst, hshift,
      ih fun f hf => havoid f (List.mem_cons_of_mem e hf), List.length_cons]
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

/-! ## Excursion prefixes as finite-path events -/

/-- **A returning path has prescribed first excursions exactly when it spells out their loop.**
For a sequence starting at `a` whose `bs.length`-th return to `a` exists, and a list `bs` of
excursions avoiding `a`, the following are the same condition:

* over the span `loopSteps bs` of the loop, the sequence agrees with the loop word of `bs`;
* the first `bs.length` excursions of the sequence are `bs`.

This is what turns a finite-dimensional event of the excursion process into a finite-path event of
the sequence itself, which is the form Markov exchangeability constrains. -/
theorem eqOn_loopPathAt_iff_excursionPrefix_eq {bs : List (List α)} (havoid : ∀ e ∈ bs, a ∉ e)
    (h : ∃ n, x n = a ∧ visitCount x a n = bs.length) (h0 : x 0 = a) :
    (∀ i ≤ loopSteps bs, x i = loopPathAt a bs i) ↔ excursionPrefix x a bs.length = bs := by
  have hloop := loopPath_excursionPrefix_of_zero h h0
  constructor
  · intro hx
    -- The `bs.length`-th return of `x` is the end of the loop, so the two loop words agree.
    have hvt : visitTime x a bs.length = loopSteps bs :=
      visitTime_eq_of_eqOn hx (loopPathAt_loopSteps a bs) (visitCount_loopPathAt a havoid)
    refine loopPath_injOn a (forall_not_mem_excursionPrefix x a bs.length) havoid ?_
    rw [hloop, hvt, ← map_range_loopPathAt a bs]
    exact List.map_congr_left fun i hi =>
      hx i (Nat.lt_succ_iff.1 (List.mem_range.1 hi))
  · intro hpre i hi
    have hvt : visitTime x a bs.length = loopSteps bs := by
      rw [← loopSteps_excursionPrefix_of_zero h h0, hpre]
    rw [hpre, hvt] at hloop
    have hmaps : (List.range (loopSteps bs + 1)).map (loopPathAt a bs)
        = (List.range (loopSteps bs + 1)).map x := by
      rw [map_range_loopPathAt, hloop]
    have hi' : i < ((List.range (loopSteps bs + 1)).map (loopPathAt a bs)).length := by
      simp only [List.length_map, List.length_range]
      omega
    simpa using (List.getElem_of_eq hmaps hi').symm


/-! ## The sequence spelled out by an infinite sequence of excursions -/

/-- The sequence spelled out by a base state `a` and an infinite sequence `b` of excursions:

```text
a, b 0, a, b 1, a, …
```

Index `i` is read off the loop word of the first `i + 1` excursions, which already runs for at
least `i + 1` steps, so the reading never falls off its end. -/
def pathOfExcursions (a : α) (b : ℕ → List α) (i : ℕ) : α :=
  loopPathAt a ((List.range (i + 1)).map b) i

/-- A longer list of excursions extends a shorter one. -/
private theorem exists_map_range_append (b : ℕ → List α) {m m' : ℕ} (h : m ≤ m') :
    ∃ cs, (List.range m').map b = ((List.range m).map b) ++ cs := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  refine ⟨(List.range k).map (fun i => b (m + i)), ?_⟩
  rw [List.range_add, List.map_append, List.map_map]
  rfl

/-- Below the span of a shorter list of excursions, a longer one spells out the same loop. -/
private theorem loopPathAt_map_range_eq (a : α) (b : ℕ → List α) {i m m' : ℕ} (hm : m ≤ m')
    (hi : i ≤ loopSteps ((List.range m).map b)) :
    loopPathAt a ((List.range m').map b) i = loopPathAt a ((List.range m).map b) i := by
  obtain ⟨cs, hcs⟩ := exists_map_range_append b hm
  rw [hcs, loopPathAt_append_of_le _ _ _ hi]

/-- **A sequence spelled out by excursions is read off any long enough loop word.** The definition
uses the shortest such word; this is the form the reconstruction theorems below need. -/
theorem pathOfExcursions_eq_loopPathAt (a : α) (b : ℕ → List α) {i n : ℕ}
    (hi : i ≤ loopSteps ((List.range n).map b)) :
    pathOfExcursions a b i = loopPathAt a ((List.range n).map b) i := by
  have hi1 : i ≤ loopSteps ((List.range (i + 1)).map b) := by
    have hle := length_le_loopSteps ((List.range (i + 1)).map b)
    simp only [List.length_map, List.length_range] at hle
    omega
  rw [pathOfExcursions, ← loopPathAt_map_range_eq a b (le_max_left (i + 1) n) hi1,
    loopPathAt_map_range_eq a b (le_max_right (i + 1) n) hi]

@[simp]
theorem pathOfExcursions_zero (a : α) (b : ℕ → List α) : pathOfExcursions a b 0 = a := by
  rw [pathOfExcursions, loopPathAt_zero]

/-- Appending one more excursion lengthens the loop by that excursion and the step back to the
base state. -/
theorem loopSteps_map_range_succ (b : ℕ → List α) (n : ℕ) :
    loopSteps ((List.range (n + 1)).map b) =
      loopSteps ((List.range n).map b) + ((b n).length + 1) := by
  rw [List.range_succ, List.map_append, loopSteps_append]
  simp

/-- A sequence spelled out by excursions is back at its base state at the end of every
excursion. -/
@[simp]
theorem pathOfExcursions_loopSteps (a : α) (b : ℕ → List α) (n : ℕ) :
    pathOfExcursions a b (loopSteps ((List.range n).map b)) = a := by
  rw [pathOfExcursions_eq_loopPathAt a b le_rfl, loopPathAt_loopSteps]

/-- **A sequence spelled out by excursions returns to its base state infinitely often**, whatever
the excursions are. -/
theorem infinite_setOf_pathOfExcursions_eq (a : α) (b : ℕ → List α) :
    {n | pathOfExcursions a b n = a}.Infinite := by
  have hmono : StrictMono fun n => loopSteps ((List.range n).map b) := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    rw [loopSteps_map_range_succ]
    omega
  exact Set.infinite_of_injective_forall_mem hmono.injective
    fun n => pathOfExcursions_loopSteps a b n

/-! ## The two reconstructions -/

/-- **Excursions rebuild the sequence they came from.** A sequence that starts at `a` and returns
to it infinitely often is spelled out by its own excursions. -/
theorem pathOfExcursions_excursion (h : {n | x n = a}.Infinite) (h0 : x 0 = a) :
    pathOfExcursions a (excursion x a) = x := by
  have hvisit : ∀ n : ℕ, n ≤ visitTime x a n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      exact Nat.succ_le_of_lt
        (lt_of_le_of_lt ih (visitTime_strictMono_of_infinite h (Nat.lt_succ_self n)))
  funext i
  have hpre : (List.range (i + 1)).map (excursion x a) = excursionPrefix x a (i + 1) :=
    (excursionPrefix_def x a (i + 1)).symm
  have hsteps : loopSteps (excursionPrefix x a (i + 1)) = visitTime x a (i + 1) :=
    loopSteps_excursionPrefix_of_infinite_of_zero h h0 (i + 1)
  have hi : i ≤ loopSteps ((List.range (i + 1)).map (excursion x a)) := by
    rw [hpre, hsteps]
    exact le_trans (Nat.le_succ i) (hvisit (i + 1))
  rw [pathOfExcursions_eq_loopPathAt _ _ hi, hpre]
  refine ((eqOn_loopPathAt_iff_excursionPrefix_eq
    (forall_not_mem_excursionPrefix x a (i + 1))
    (by simpa using exists_visitCount_of_infinite h (i + 1)) h0).mpr (by simp) i ?_).symm
  rw [hsteps]
  exact le_trans (Nat.le_succ i) (hvisit (i + 1))

/-- **A sequence spelled out by excursions has the prescribed excursion prefix**, provided the
excursions in that prefix avoid the base state. -/
@[simp]
theorem excursionPrefix_pathOfExcursions {b : ℕ → List α} (n : ℕ)
    (havoid : ∀ j < n, a ∉ b j) :
    excursionPrefix (pathOfExcursions a b) a n = (List.range n).map b := by
  have havoid' : ∀ e ∈ (List.range n).map b, a ∉ e := by
    intro e he
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 he
    exact havoid j (List.mem_range.1 hj)
  have hlen : ((List.range n).map b).length = n := by simp
  have heq : ∀ i ≤ loopSteps ((List.range n).map b),
      pathOfExcursions a b i = loopPathAt a ((List.range n).map b) i := fun i hi =>
    pathOfExcursions_eq_loopPathAt a b hi
  have hex : ∃ i, pathOfExcursions a b i = a ∧
      visitCount (pathOfExcursions a b) a i = ((List.range n).map b).length := by
    refine ⟨loopSteps ((List.range n).map b), pathOfExcursions_loopSteps a b n, ?_⟩
    rw [visitCount_congr fun i hi => heq i hi.le, visitCount_loopPathAt a havoid', hlen]
  have hmain := (eqOn_loopPathAt_iff_excursionPrefix_eq havoid' hex
    (pathOfExcursions_zero a b)).mp heq
  rwa [hlen] at hmain

/-- **Each excursion of a sequence spelled out by excursions is the corresponding one**, provided
that excursion and its predecessors avoid the base state. -/
@[simp]
theorem excursion_pathOfExcursions {b : ℕ → List α} (j : ℕ) (havoid : ∀ k ≤ j, a ∉ b k) :
    excursion (pathOfExcursions a b) a j = b j := by
  have hidx : j < (excursionPrefix (pathOfExcursions a b) a (j + 1)).length := by simp
  have h := List.getElem_of_eq
    (excursionPrefix_pathOfExcursions (j + 1) fun k hk => havoid k (Nat.lt_succ_iff.1 hk)) hidx
  simpa [getElem_excursionPrefix (Nat.lt_succ_self j)] using h

end TauCeti

end

end
