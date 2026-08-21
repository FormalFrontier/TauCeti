/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.TransitionCount
public import TauCeti.Data.Nat.Nth

/-!
# The successor array of a sequence

For a sequence `x : ℕ → α`, its successor array records, for each value `a`, the values that
follow successive visits to `a`. Together with `x 0`, this array determines the original sequence.
The reconstruction is total: entries after the last genuine visit use the junk value supplied by
`Nat.nth`, but the round-trip theorem never reads them.

## Main definitions

* `TauCeti.visitCount`: the number of visits to a value before a given index.
* `TauCeti.visitTime`: the index of a given visit to a value.
* `TauCeti.successorArray`: the values following successive visits to each value.
* `TauCeti.pathOfSuccessors`: reconstruction from an initial value and successor array.

## Main results

* `TauCeti.visitCount_monotone`: visit counts are monotone in the horizon.
* `TauCeti.successorArray_visitCount`: the defining step relation of the successor array.
* `TauCeti.visitTime_eq_iff`: the fibres of the visit times, including the junk-value branch.
* `TauCeti.eq_pathOfSuccessors`: the uniqueness principle for the reconstruction.
* `TauCeti.pathOfSuccessors_successorArray`: reconstruction inverts the successor decomposition.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
-/

public section

noncomputable section

namespace TauCeti

section Defs

variable {α : Type*}

/-- The number of times the sequence `x` visits `a` strictly before `n`. -/
def visitCount (x : ℕ → α) (a : α) (n : ℕ) : ℕ :=
  occCount (fun i : Fin n => x i.val) a

/-- The index of the `k`-th visit of `x` to `a`, or the junk value `0` if there is no such
visit. -/
def visitTime (x : ℕ → α) (a : α) (k : ℕ) : ℕ :=
  Nat.nth (fun i => x i = a) k

/-- The value immediately following the `k`-th visit of `x` to `a`. It is junk if that visit does
not exist. -/
def successorArray (x : ℕ → α) (a : α) (k : ℕ) : α :=
  x (visitTime x a k + 1)

/-- The finite-horizon recursion used to rebuild a sequence from an initial value and a successor
array. -/
private def pathOfSuccessorsUpTo (a₀ : α) (s : α → ℕ → α) : ℕ → ℕ → α
  | 0 => fun _ => a₀
  | n + 1 => fun i =>
    if i ≤ n then pathOfSuccessorsUpTo a₀ s n i
    else
      s (pathOfSuccessorsUpTo a₀ s n n)
        (visitCount (pathOfSuccessorsUpTo a₀ s n) (pathOfSuccessorsUpTo a₀ s n n) n)

/-- The sequence rebuilt from an initial value and a successor array. -/
def pathOfSuccessors (a₀ : α) (s : α → ℕ → α) (n : ℕ) : α :=
  pathOfSuccessorsUpTo a₀ s n n

-- These private witnesses let the exported equations keep the definition bodies unexposed.
private theorem visitCount_def_private (x : ℕ → α) (a : α) (n : ℕ) :
    visitCount x a n = occCount (fun i : Fin n => x i.val) a :=
  rfl

/-- The defining equation for visit counts. -/
theorem visitCount_def (x : ℕ → α) (a : α) (n : ℕ) :
    visitCount x a n = occCount (fun i : Fin n => x i.val) a :=
  visitCount_def_private x a n

private theorem visitTime_def_private (x : ℕ → α) (a : α) (k : ℕ) :
    visitTime x a k = Nat.nth (fun i => x i = a) k :=
  rfl

/-- The defining equation for visit times. -/
theorem visitTime_def (x : ℕ → α) (a : α) (k : ℕ) :
    visitTime x a k = Nat.nth (fun i => x i = a) k :=
  visitTime_def_private x a k

private theorem successorArray_def_private (x : ℕ → α) (a : α) (k : ℕ) :
    successorArray x a k = x (visitTime x a k + 1) :=
  rfl

/-- The defining equation for an entry of the successor array. -/
theorem successorArray_def (x : ℕ → α) (a : α) (k : ℕ) :
    successorArray x a k = x (visitTime x a k + 1) :=
  successorArray_def_private x a k

end Defs

section Counting

attribute [local instance] Classical.decEq

variable {α : Type*} {x y : ℕ → α} {a : α} {k m n : ℕ}

/-- Visit counts are `Nat.count` of the visiting predicate. -/
theorem visitCount_eq_count [DecidableEq α] (x : ℕ → α) (a : α) (n : ℕ) :
    visitCount x a n = Nat.count (fun i => x i = a) n := by
  rw [visitCount, occCount_eq_sum, Nat.count_eq_card_filter_range, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun i => if x i = a then 1 else 0) n]

@[simp, grind =]
theorem visitCount_zero (x : ℕ → α) (a : α) : visitCount x a 0 = 0 := by
  classical
  rw [visitCount_eq_count, Nat.count_zero]

/-- Visit counts are monotone in the horizon. -/
theorem visitCount_monotone (x : ℕ → α) (a : α) : Monotone (visitCount x a) := by
  classical
  intro m n hmn
  simpa only [visitCount_eq_count] using Nat.count_monotone (fun i => x i = a) hmn

/-- Visit counts before `n` depend only on sequence values before `n`. -/
theorem visitCount_congr (h : ∀ i < n, x i = y i) : visitCount x a n = visitCount y a n := by
  unfold visitCount
  apply congrArg (fun z => occCount z a)
  funext i
  exact h i.val i.isLt

/-- Splitting a visit count at the final index. -/
@[grind =]
theorem visitCount_succ [DecidableEq α] (x : ℕ → α) (a : α) (n : ℕ) :
    visitCount x a (n + 1) =
      if x n = a then visitCount x a n + 1 else visitCount x a n := by
  rw [visitCount_def, visitCount_def]
  have h := (occCount_comp_castSucc_add_last (w := fun i : Fin (n + 1) => x i.val) a).symm
  -- Normalize the finite-word endpoints while leaving `occCount` opaque.
  change occCount (fun i : Fin (n + 1) => x i.val) a =
    occCount (fun i : Fin n => x i.val) a + (if x n = a then 1 else 0) at h
  by_cases hx : x n = a
  · rw [ite_eq_left hx] at h ⊢
    exact h
  · rw [ite_eq_right hx, Nat.add_zero] at h
    rw [ite_eq_right hx]
    exact h

/-- One more visit is counted when the sequence has the specified value. -/
@[simp]
theorem visitCount_succ_of_eq (h : x n = a) : visitCount x a (n + 1) = visitCount x a n + 1 := by
  classical
  rw [visitCount_succ, ite_eq_left h]

/-- No visit is added when the sequence has a different value. -/
@[simp]
theorem visitCount_succ_of_ne (h : x n ≠ a) : visitCount x a (n + 1) = visitCount x a n := by
  classical
  rw [visitCount_succ, ite_eq_right h]

/-- A time at which `x` has value `a` is the visit indexed by the number of earlier visits. -/
@[simp]
theorem visitTime_visitCount (h : x n = a) : visitTime x a (visitCount x a n) = n := by
  classical
  rw [visitTime, visitCount_eq_count, Nat.nth_count h]

/-- The fibres of `visitTime`, including the junk-value branch. -/
theorem visitTime_eq_iff :
    visitTime x a k = m ↔
      (x m = a ∧ visitCount x a m = k) ∨ (m = 0 ∧ ∀ n, ¬(x n = a ∧ visitCount x a n = k)) := by
  classical
  simpa only [visitTime_def, visitCount_eq_count] using
    Nat.nth_eq_iff (p := fun i => x i = a) (k := k) (m := m)

end Counting

section Reconstruction

variable {α : Type*} {x y : ℕ → α} {a a₀ : α} {s : α → ℕ → α} {i n : ℕ}

/-- At a visit to `a`, the sequence moves to the corresponding entry of its successor array. -/
@[simp]
theorem successorArray_visitCount_of_eq (h : x n = a) :
    successorArray x a (visitCount x a n) = x (n + 1) := by
  rw [successorArray, visitTime_visitCount h]

/-- The step relation of the successor array. -/
theorem successorArray_visitCount (x : ℕ → α) (n : ℕ) :
    successorArray x (x n) (visitCount x (x n) n) = x (n + 1) :=
  successorArray_visitCount_of_eq rfl

@[simp]
private theorem pathOfSuccessorsUpTo_zero (a₀ : α) (s : α → ℕ → α) (i : ℕ) :
    pathOfSuccessorsUpTo a₀ s 0 i = a₀ :=
  rfl

private theorem pathOfSuccessorsUpTo_succ (a₀ : α) (s : α → ℕ → α) (n i : ℕ) :
    pathOfSuccessorsUpTo a₀ s (n + 1) i =
      if i ≤ n then pathOfSuccessorsUpTo a₀ s n i
      else
        s (pathOfSuccessorsUpTo a₀ s n n)
          (visitCount (pathOfSuccessorsUpTo a₀ s n) (pathOfSuccessorsUpTo a₀ s n n) n) :=
  rfl

/-- The rebuilt sequence starts at the given initial value. -/
@[simp]
theorem pathOfSuccessors_zero (a₀ : α) (s : α → ℕ → α) : pathOfSuccessors a₀ s 0 = a₀ := by
  simpa only [pathOfSuccessors] using pathOfSuccessorsUpTo_zero a₀ s 0

private theorem pathOfSuccessorsUpTo_of_le (a₀ : α) (s : α → ℕ → α) (h : i ≤ n) :
    pathOfSuccessorsUpTo a₀ s n i = pathOfSuccessors a₀ s i := by
  induction n generalizing i with
  | zero => rw [Nat.le_zero.1 h]; rfl
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · rfl
    · have hi : i ≤ n := Nat.lt_succ_iff.1 hlt
      rw [pathOfSuccessorsUpTo_succ, ite_eq_left hi, ih hi]

/-- The recursion equation for the rebuilt sequence. -/
@[simp]
theorem pathOfSuccessors_succ (a₀ : α) (s : α → ℕ → α) (n : ℕ) :
    pathOfSuccessors a₀ s (n + 1) =
      s (pathOfSuccessors a₀ s n)
        (visitCount (pathOfSuccessors a₀ s) (pathOfSuccessors a₀ s n) n) := by
  rw [pathOfSuccessors, pathOfSuccessorsUpTo_succ,
    ite_eq_right (Nat.not_succ_le_self n),
    pathOfSuccessorsUpTo_of_le a₀ s (le_refl n),
    visitCount_congr fun i hi => pathOfSuccessorsUpTo_of_le a₀ s hi.le]

/-- A sequence satisfying the reconstruction equations is the rebuilt sequence. -/
theorem eq_pathOfSuccessors (h₀ : y 0 = a₀)
    (hstep : ∀ n, y (n + 1) = s (y n) (visitCount y (y n) n)) :
    y = pathOfSuccessors a₀ s := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simpa using h₀
    | n + 1 =>
      have hle : ∀ i ≤ n, y i = pathOfSuccessors a₀ s i := fun i hi =>
        ih i (Nat.lt_succ_of_le hi)
      rw [hstep, pathOfSuccessors_succ, hle n (le_refl n),
        visitCount_congr fun i hi => hle i hi.le]

/-- Rebuilding from a sequence's initial value and successor array recovers the sequence. -/
@[simp]
theorem pathOfSuccessors_successorArray (x : ℕ → α) :
    pathOfSuccessors (x 0) (successorArray x) = x := by
  symm
  exact eq_pathOfSuccessors rfl fun n => (successorArray_visitCount x n).symm

end Reconstruction

end TauCeti

end

end
