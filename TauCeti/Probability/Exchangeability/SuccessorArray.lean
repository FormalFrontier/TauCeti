/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.TransitionCount
public import TauCeti.Data.Nat.Nth
public import TauCeti.MeasureTheory.MeasurableSpace.Eval
public import TauCeti.Probability.Exchangeability.Basic

/-!
# The successor array of a path

Read a sequence `x : ℕ → α` as the trajectory of a walk on the state space `α`. For each state `a`
list the times at which the walk sits at `a`, and record the state it moves to next. This is the
**successor array**

```text
successorArray x a k = x (visitTime x a k + 1),
```

the state entered just after the `k`-th visit of `x` to `a`. Together with the initial state
`x 0` it is a complete encoding: the walk is rebuilt from it by following, at each visit to a
state, that state's next unused successor. `pathOfSuccessors` performs the rebuilding and
`pathOfSuccessors_successorArray` is the round trip

```text
pathOfSuccessors (x 0) (successorArray x) = x.
```

Neither direction needs a recurrence hypothesis. The rebuilding always terminates on a value
because `Nat.nth` is total, and the round trip only ever consults entries `successorArray x a k`
for which a `k`-th visit to `a` genuinely occurred; entries beyond a state's last visit are junk
and are never read.

## Why this is the Diaconis–Freedman decomposition

Markov exchangeability (`TauCeti.Probability.MarkovExchangeable`) says that the law of a finite
path depends only on its initial state and its transition counts. The successor array is the
change of variables that makes this a statement about symmetry within rows: the transition counts
of a path are the occurrence counts of the individual successor sequences, so permuting the
entries of a row leaves the transition counts — hence the path mass — alone. The measurable
encoding proved here, `map_pathOfSuccessors_map_successorArray`, is the step that turns a
representation of the joint law of `(x 0, successorArray x)` into a representation of the law of
the path itself, which is how the Diaconis–Freedman representation theorem produces a mixture of
Markov chains from a de Finetti argument applied row by row.

## Main definitions

* `TauCeti.Probability.visitCount`: the number of visits of a sequence to a state before a time.
* `TauCeti.Probability.visitTime`: the time of the `k`-th visit of a sequence to a state.
* `TauCeti.Probability.successorArray`: the state entered just after the `k`-th visit to a state.
* `TauCeti.Probability.pathOfSuccessors`: the sequence rebuilt from an initial state and a
  successor array.

## Main results

* `TauCeti.Probability.successorArray_visitCount`: the defining step relation, that the sequence
  moves from `x n` to the successor indexed by the number of earlier visits to `x n`.
* `TauCeti.Probability.pathOfSuccessors_successorArray`: rebuilding inverts the decomposition.
* `TauCeti.Probability.transitionCount_prefixProj`: the transition counts of a prefix are the
  occurrence counts in the rows of the successor array.
* `TauCeti.Probability.visitTime_eq_iff`: the fibres of the visit times, which is what makes the
  decomposition measurable.
* `TauCeti.Probability.measurable_pathOfSuccessors` and
  `TauCeti.Probability.measurable_successorArray`: both directions are measurable.
* `TauCeti.Probability.map_pathOfSuccessors_map_successorArray`: every law on path space is the
  image of the joint law of its initial state and successor array.
* `TauCeti.Probability.pathLaw_eq_map_pathOfSuccessors`: the process-level form.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 8, "Markov exchangeability".

No material is adapted from `cameronfreer/exchangeability`, which treats exchangeable rather than
Markov exchangeable sequences.
-/

public section

noncomputable section

open MeasureTheory

open TauCeti.MeasureTheory

namespace TauCeti

namespace Probability

section Defs

variable {α : Type*}

/-- The number of times the sequence `x` visits the state `a` strictly before time `n`: the
occurrence count of `a` in the length-`n` prefix of `x`. -/
def visitCount (x : ℕ → α) (a : α) (n : ℕ) : ℕ :=
  occCount (prefixProj α n x) a

/-- The time of the `k`-th visit of the sequence `x` to the state `a`, counting from `k = 0`. It
is `0`, the junk value of `Nat.nth`, when `x` visits `a` at most `k` times. -/
def visitTime (x : ℕ → α) (a : α) (k : ℕ) : ℕ :=
  Nat.nth (fun i => x i = a) k

/-- The `(a, k)` entry of the **successor array** of the sequence `x`: the state entered just
after the `k`-th visit of `x` to `a`. It is junk when `x` visits `a` at most `k` times. -/
def successorArray (x : ℕ → α) (a : α) (k : ℕ) : α :=
  x (visitTime x a k + 1)

/-- The finite-horizon recursion rebuilding a sequence from an initial state `a₀` and a successor
array `s`: `pathOfSuccessorsUpTo a₀ s n` agrees with the rebuilt sequence at every time `i ≤ n`,
and repeats the value at time `n + 1` beyond that horizon. Each step reads the successor of the
current state indexed by the number of earlier visits to it. -/
private def pathOfSuccessorsUpTo (a₀ : α) (s : α → ℕ → α) : ℕ → ℕ → α
  | 0 => fun _ => a₀
  | n + 1 => fun i =>
    if i ≤ n then pathOfSuccessorsUpTo a₀ s n i
    else
      s (pathOfSuccessorsUpTo a₀ s n n)
        (visitCount (pathOfSuccessorsUpTo a₀ s n) (pathOfSuccessorsUpTo a₀ s n n) n)

/-- The sequence rebuilt from an initial state `a₀` and a successor array `s`: it starts at `a₀`
and, at each time, moves to the successor of the current state indexed by the number of earlier
visits to that state. -/
def pathOfSuccessors (a₀ : α) (s : α → ℕ → α) (n : ℕ) : α :=
  pathOfSuccessorsUpTo a₀ s n n

end Defs

section Counting

variable {α : Type*} {x y : ℕ → α} {a : α} {k m n : ℕ}

/-- Visit counts are `Nat.count` of the visiting predicate. -/
theorem visitCount_eq_count [DecidableEq α] (x : ℕ → α) (a : α) (n : ℕ) :
    visitCount x a n = Nat.count (fun i => x i = a) n := by
  have hpref : prefixProj α n x = fun i : Fin n => x i.val := rfl
  rw [visitCount, hpref, occCount_eq_sum, Nat.count_eq_card_filter_range, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun i => if x i = a then 1 else 0) n]

@[simp]
theorem visitCount_zero (x : ℕ → α) (a : α) : visitCount x a 0 = 0 := by
  classical
  rw [visitCount_eq_count, Nat.count_zero]

/-- Visit counts before time `n` depend only on the values of the sequence before time `n`. -/
theorem visitCount_congr (h : ∀ i < n, x i = y i) : visitCount x a n = visitCount y a n := by
  have hpref : prefixProj α n x = prefixProj α n y := funext fun i => h i.val i.isLt
  rw [visitCount, visitCount, hpref]

/-- One more visit is counted at a time when the sequence sits at the state. -/
theorem visitCount_succ_of_eq (h : x n = a) : visitCount x a (n + 1) = visitCount x a n + 1 := by
  classical
  rw [visitCount_eq_count, visitCount_eq_count, Nat.count_succ]
  simp [h]

/-- No further visit is counted at a time when the sequence sits elsewhere. -/
theorem visitCount_succ_of_ne (h : x n ≠ a) : visitCount x a (n + 1) = visitCount x a n := by
  classical
  rw [visitCount_eq_count, visitCount_eq_count, Nat.count_succ]
  simp [h]

/-- **A time at which the sequence sits at `a` is the time of a visit to `a`**, namely of the
visit indexed by the number of earlier visits. -/
theorem visitTime_visitCount (h : x n = a) : visitTime x a (visitCount x a n) = n := by
  classical
  rw [visitTime, visitCount_eq_count, Nat.nth_count h]

/-- **The fibres of `visitTime`.** The `k`-th visit of `x` to `a` happens at time `m` exactly when
`m` is a time at which `x` sits at `a` with `k` earlier visits, or else no such time exists and `m`
is the junk value `0`. -/
theorem visitTime_eq_iff :
    visitTime x a k = m ↔
      (x m = a ∧ visitCount x a m = k) ∨ (m = 0 ∧ ∀ n, ¬(x n = a ∧ visitCount x a n = k)) := by
  classical
  simpa [visitTime, visitCount_eq_count] using
    nth_eq_iff (p := fun i => x i = a) (k := k) (m := m)

end Counting

section Reconstruction

variable {α : Type*} {x : ℕ → α} {a a₀ : α} {s : α → ℕ → α} {i n : ℕ}

/-- **The step relation of the successor array**, at a time known to sit at the state `a`: the
sequence moves to the successor of `a` indexed by the number of earlier visits to `a`. -/
theorem successorArray_visitCount_of_eq (h : x n = a) :
    successorArray x a (visitCount x a n) = x (n + 1) := by
  rw [successorArray, visitTime_visitCount h]

/-- **The step relation of the successor array.** From time `n` the sequence moves to the
successor of its current state indexed by the number of earlier visits to that state. -/
theorem successorArray_visitCount (x : ℕ → α) (n : ℕ) :
    successorArray x (x n) (visitCount x (x n) n) = x (n + 1) :=
  successorArray_visitCount_of_eq rfl

/-- At horizon `0` the finite-horizon recursion is constant at the initial state. -/
@[simp]
private theorem pathOfSuccessorsUpTo_zero (a₀ : α) (s : α → ℕ → α) (i : ℕ) :
    pathOfSuccessorsUpTo a₀ s 0 i = a₀ :=
  rfl

/-- The recursion step of `pathOfSuccessorsUpTo`. -/
private theorem pathOfSuccessorsUpTo_succ (a₀ : α) (s : α → ℕ → α) (n i : ℕ) :
    pathOfSuccessorsUpTo a₀ s (n + 1) i =
      if i ≤ n then pathOfSuccessorsUpTo a₀ s n i
      else
        s (pathOfSuccessorsUpTo a₀ s n n)
          (visitCount (pathOfSuccessorsUpTo a₀ s n) (pathOfSuccessorsUpTo a₀ s n n) n) :=
  rfl

/-- The rebuilt sequence starts at the given initial state. -/
@[simp]
theorem pathOfSuccessors_zero (a₀ : α) (s : α → ℕ → α) : pathOfSuccessors a₀ s 0 = a₀ := by
  simpa only [pathOfSuccessors] using pathOfSuccessorsUpTo_zero a₀ s 0

/-- Below its horizon the finite-horizon recursion agrees with the rebuilt sequence. -/
private theorem pathOfSuccessorsUpTo_of_le (a₀ : α) (s : α → ℕ → α) (h : i ≤ n) :
    pathOfSuccessorsUpTo a₀ s n i = pathOfSuccessors a₀ s i := by
  induction n generalizing i with
  | zero => rw [Nat.le_zero.1 h]; rfl
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · rfl
    · have hi : i ≤ n := Nat.lt_succ_iff.1 hlt
      rw [pathOfSuccessorsUpTo_succ, ite_eq_left_of_eq_true _ _ (eq_true hi), ih hi]

/-- **The recursion defining the rebuilt sequence.** Each step reads the successor of the current
state indexed by the number of earlier visits to it — the step relation
`successorArray_visitCount`, transported to the rebuilt sequence. -/
theorem pathOfSuccessors_succ (a₀ : α) (s : α → ℕ → α) (n : ℕ) :
    pathOfSuccessors a₀ s (n + 1) =
      s (pathOfSuccessors a₀ s n)
        (visitCount (pathOfSuccessors a₀ s) (pathOfSuccessors a₀ s n) n) := by
  rw [pathOfSuccessors, pathOfSuccessorsUpTo_succ,
    ite_eq_right_of_eq_false _ _ (eq_false (Nat.not_succ_le_self n)),
    pathOfSuccessorsUpTo_of_le a₀ s (le_refl n),
    visitCount_congr fun i hi => pathOfSuccessorsUpTo_of_le a₀ s hi.le]

/-- **Rebuilding inverts the successor decomposition.** A sequence is recovered from its initial
state and its successor array. -/
theorem pathOfSuccessors_successorArray (x : ℕ → α) :
    pathOfSuccessors (x 0) (successorArray x) = x := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | n + 1 =>
      have hle : ∀ i ≤ n, pathOfSuccessors (x 0) (successorArray x) i = x i := fun i hi =>
        ih i (Nat.lt_succ_of_le hi)
      rw [pathOfSuccessors_succ, hle n (le_refl n),
        visitCount_congr fun i hi => hle i hi.le, successorArray_visitCount]

end Reconstruction

section TransitionCounts

variable {α : Type*} {x : ℕ → α} {a b : α} {n : ℕ}

/-- Splitting off the last transition of a prefix. -/
private theorem transitionCount_prefixProj_succ [DecidableEq α] (x : ℕ → α) (n : ℕ) (a b : α) :
    transitionCount (prefixProj α (n + 2) x) a b =
      transitionCount (prefixProj α (n + 1) x) a b +
        if x n = a ∧ x (n + 1) = b then 1 else 0 := by
  rw [transitionCount_eq_card_filter, transitionCount_eq_card_filter, Finset.card_filter,
    Finset.card_filter, Fin.sum_univ_castSucc]
  rfl

/-- **The transition counts of a path are the occurrence counts in its successor rows.** The
number of `a`-to-`b` transitions before time `n` is the number of visits to `a` before time `n`
whose successor is `b`. This is the change of variables behind the Diaconis–Freedman
representation theorem: it turns the transition-count statistic, which Markov exchangeability
holds fixed, into occurrence counts of the individual rows of the successor array, where the
symmetry becomes an ordinary exchangeability of each row. -/
theorem transitionCount_prefixProj [DecidableEq α] (x : ℕ → α) (n : ℕ) (a b : α) :
    transitionCount (prefixProj α (n + 1) x) a b =
      ((Finset.range (visitCount x a n)).filter fun k => successorArray x a k = b).card := by
  induction n with
  | zero => simp [transitionCount_eq_card_filter]
  | succ n ih =>
    rw [transitionCount_prefixProj_succ, ih]
    by_cases hx : x n = a
    · rw [visitCount_succ_of_eq hx, Finset.range_add_one, Finset.filter_insert,
        successorArray_visitCount_of_eq hx]
      by_cases hb : x (n + 1) = b
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hb), Finset.card_insert_of_notMem (by simp),
          ite_eq_left_of_eq_true _ _ (eq_true (And.intro hx hb))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hb),
          ite_eq_right_of_eq_false _ _ (eq_false fun h => hb h.2), Nat.add_zero]
    · rw [visitCount_succ_of_ne hx, ite_eq_right_of_eq_false _ _ (eq_false fun h => hx h.1),
        Nat.add_zero]

end TransitionCounts

section Measurability

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {a : α} {k n : ℕ}

/-- The event that a path sits at a given state at a given time is measurable. -/
theorem measurableSet_coord_eq (a : α) (n : ℕ) : MeasurableSet {x : ℕ → α | x n = a} := by
  have h : MeasurableSet ((fun x : ℕ → α => x n) ⁻¹' {a}) :=
    measurable_pi_apply n (measurableSet_singleton a)
  exact h

/-- Visit counts are measurable functions of the path: each is built from finitely many
coordinates. -/
theorem measurable_visitCount (a : α) (n : ℕ) :
    Measurable fun x : ℕ → α => visitCount x a n := by
  classical
  induction n with
  | zero => simp only [visitCount_zero]; exact measurable_const
  | succ n ih =>
    have hrw : (fun x : ℕ → α => visitCount x a (n + 1)) =
        fun x => if x n = a then visitCount x a n + 1 else visitCount x a n := by
      funext x
      by_cases hx : x n = a
      · simp [visitCount_succ_of_eq hx, hx]
      · simp [visitCount_succ_of_ne hx, hx]
    rw [hrw]
    exact Measurable.ite (measurableSet_coord_eq a n) (Measurable.of_discrete.comp ih) ih

/-- Visit times are measurable functions of the path. Each fibre is described by
`visitTime_eq_iff` as a countable Boolean combination of coordinate events. -/
theorem measurable_visitTime (a : α) (k : ℕ) :
    Measurable fun x : ℕ → α => visitTime x a k := by
  refine measurable_to_countable' fun m => ?_
  have hrw : (fun x : ℕ → α => visitTime x a k) ⁻¹' {m} =
      ({x : ℕ → α | x m = a} ∩ {x : ℕ → α | visitCount x a m = k}) ∪
        {x : ℕ → α | m = 0 ∧ ∀ n, ¬(x n = a ∧ visitCount x a n = k)} := by
    ext x
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using visitTime_eq_iff (x := x) (a := a)
  rw [hrw]
  refine MeasurableSet.union
    ((measurableSet_coord_eq a m).inter (measurable_visitCount a m (measurableSet_singleton k)))
    ?_
  by_cases hm : m = 0
  · have hiInter : {x : ℕ → α | m = 0 ∧ ∀ n, ¬(x n = a ∧ visitCount x a n = k)} =
        ⋂ n, ({x : ℕ → α | x n = a} ∩ {x : ℕ → α | visitCount x a n = k})ᶜ := by
      ext x
      simp [hm, Set.mem_iInter]
    rw [hiInter]
    exact MeasurableSet.iInter fun n =>
      ((measurableSet_coord_eq a n).inter
        (measurable_visitCount a n (measurableSet_singleton k))).compl
  · have hempty : {x : ℕ → α | m = 0 ∧ ∀ n, ¬(x n = a ∧ visitCount x a n = k)} = ∅ := by
      ext x
      simp [hm]
    rw [hempty]
    exact MeasurableSet.empty

/-- Each entry of the successor array is a measurable function of the path. -/
theorem measurable_successorArray_apply (a : α) (k : ℕ) :
    Measurable fun x : ℕ → α => successorArray x a k :=
  measurable_eval_index (g := fun x : ℕ → α => x) (f := fun x : ℕ → α => visitTime x a k + 1)
    measurable_id (Measurable.of_discrete.comp (measurable_visitTime a k))

/-- **The successor array of a path is a measurable function of the path.** -/
theorem measurable_successorArray :
    Measurable fun x : ℕ → α => successorArray x :=
  measurable_pi_lambda _ fun a =>
    measurable_pi_lambda _ fun k => measurable_successorArray_apply a k

/-- The measurable encoding of a path by its initial state together with its successor array. -/
theorem measurable_successorEncoding :
    Measurable fun x : ℕ → α => (x 0, successorArray x) :=
  (measurable_pi_apply 0).prodMk measurable_successorArray

variable [Countable α]

/-- The rebuilt sequence, and the visit counts of the rebuilt sequence, are jointly measurable in
the initial state and the successor array. The two statements are proved together because the
recursion for the sequence reads a visit count, and the recursion for the visit counts reads the
sequence. -/
private theorem measurable_pathOfSuccessors_and_visitCount (n : ℕ) :
    (Measurable fun q : α × (α → ℕ → α) => pathOfSuccessors q.1 q.2 n) ∧
      Measurable fun q : α × (α → ℕ → α) => fun a => visitCount (pathOfSuccessors q.1 q.2) a n := by
  classical
  induction n with
  | zero =>
    refine ⟨measurable_fst, ?_⟩
    simp only [visitCount_zero]
    exact measurable_const
  | succ n ih =>
    have hstate : Measurable fun q : α × (α → ℕ → α) => q.2 (pathOfSuccessors q.1 q.2 n) :=
      measurable_eval_index (g := fun q : α × (α → ℕ → α) => q.2)
        (f := fun q : α × (α → ℕ → α) => pathOfSuccessors q.1 q.2 n) measurable_snd ih.1
    have hcount : Measurable fun q : α × (α → ℕ → α) =>
        visitCount (pathOfSuccessors q.1 q.2) (pathOfSuccessors q.1 q.2 n) n :=
      measurable_eval_index
        (g := fun (q : α × (α → ℕ → α)) a => visitCount (pathOfSuccessors q.1 q.2) a n)
        (f := fun q : α × (α → ℕ → α) => pathOfSuccessors q.1 q.2 n) ih.2 ih.1
    refine ⟨?_, ?_⟩
    · simp only [pathOfSuccessors_succ]
      exact measurable_eval_index
        (g := fun q : α × (α → ℕ → α) => q.2 (pathOfSuccessors q.1 q.2 n))
        (f := fun q : α × (α → ℕ → α) =>
          visitCount (pathOfSuccessors q.1 q.2) (pathOfSuccessors q.1 q.2 n) n) hstate hcount
    · refine measurable_pi_lambda _ fun a => ?_
      have hrw : (fun q : α × (α → ℕ → α) => visitCount (pathOfSuccessors q.1 q.2) a (n + 1)) =
          fun q => if pathOfSuccessors q.1 q.2 n = a then
            visitCount (pathOfSuccessors q.1 q.2) a n + 1
          else visitCount (pathOfSuccessors q.1 q.2) a n := by
        funext q
        by_cases hq : pathOfSuccessors q.1 q.2 n = a
        · simp [visitCount_succ_of_eq hq, hq]
        · simp [visitCount_succ_of_ne hq, hq]
      rw [hrw]
      have hmem : MeasurableSet {q : α × (α → ℕ → α) | pathOfSuccessors q.1 q.2 n = a} := by
        have h : MeasurableSet
            ((fun q : α × (α → ℕ → α) => pathOfSuccessors q.1 q.2 n) ⁻¹' {a}) :=
          ih.1 (measurableSet_singleton a)
        exact h
      exact Measurable.ite hmem
        (Measurable.of_discrete.comp ((measurable_pi_apply a).comp ih.2))
        ((measurable_pi_apply a).comp ih.2)

/-- **Rebuilding a path from an initial state and a successor array is measurable.** -/
theorem measurable_pathOfSuccessors :
    Measurable fun q : α × (α → ℕ → α) => pathOfSuccessors q.1 q.2 :=
  measurable_pi_iff.2 fun n => (measurable_pathOfSuccessors_and_visitCount n).1

end Measurability

section Laws

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable α]

/-- **Every law on path space is the image of the joint law of the initial state and the successor
array.** This is the change of variables behind the Diaconis–Freedman representation theorem: a
description of the law of `(x 0, successorArray x)` determines the law of the path. -/
theorem map_pathOfSuccessors_map_successorArray (ρ : Measure (ℕ → α)) :
    ((ρ.map fun x => (x 0, successorArray x)).map fun q => pathOfSuccessors q.1 q.2) = ρ := by
  rw [Measure.map_map measurable_pathOfSuccessors measurable_successorEncoding]
  have hid : ((fun q : α × (α → ℕ → α) => pathOfSuccessors q.1 q.2) ∘
      fun x : ℕ → α => (x 0, successorArray x)) = id :=
    funext fun x => pathOfSuccessors_successorArray x
  rw [hid, Measure.map_id]

/-- **The path law of a process is the image of the joint law of its initial state and its
successor array.** -/
theorem pathLaw_eq_map_pathOfSuccessors {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) :
    pathLaw μ X =
      ((μ.map fun ω => (X 0 ω, successorArray fun n => X n ω)).map
        fun q => pathOfSuccessors q.1 q.2) := by
  have hY : AEMeasurable (fun ω i => X i ω) μ := aemeasurable_pi_lambda _ hX
  have hmap : (μ.map fun ω => (X 0 ω, successorArray fun n => X n ω)) =
      (pathLaw μ X).map fun x => (x 0, successorArray x) := by
    rw [pathLaw_def, AEMeasurable.map_map_of_aemeasurable
      measurable_successorEncoding.aemeasurable hY]
    rfl
  rw [hmap, map_pathOfSuccessors_map_successorArray]

end Laws

end Probability

end TauCeti

end

end
