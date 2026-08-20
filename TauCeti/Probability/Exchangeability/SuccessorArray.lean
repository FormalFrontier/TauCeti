/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.SuccessorArray
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

Neither direction needs a recurrence hypothesis. Rebuilding is total because it is defined by
finite-horizon recursion, and the round trip only ever consults entries `successorArray x a k` for
which a `k`-th visit to `a` genuinely occurred. `Nat.nth` makes the remaining entries in the
successor array junk, and they are never read.

## Why this is the Diaconis–Freedman decomposition

Markov exchangeability (`TauCeti.Probability.MarkovExchangeable`) says that the law of a finite
path depends only on its initial state and transition counts. The successor array is the change of
variables that reads those counts as occurrence counts in initial segments of its rows. Turning
this identity into within-row exchangeability requires the later endpoint and recurrence argument;
that step is not proved here. The measurable encoding proved here is what will transfer a future
representation of the joint law of `(x 0, successorArray x)` back to the law of the path.

## Main definitions

* `TauCeti.visitCount`: the number of visits of a sequence to a state before a time.
* `TauCeti.visitTime`: the time of the `k`-th visit of a sequence to a state.
* `TauCeti.successorArray`: the state entered just after the `k`-th visit to a state.
* `TauCeti.pathOfSuccessors`: the sequence rebuilt from an initial state and a
  successor array.

## Main results

* `TauCeti.successorArray_visitCount`: the defining step relation, that the sequence
  moves from `x n` to the successor indexed by the number of earlier visits to `x n`.
* `TauCeti.pathOfSuccessors_successorArray`: rebuilding inverts the decomposition.
* `TauCeti.Probability.transitionCount_prefixProj`: the transition counts of a prefix are the
  occurrence counts in the rows of the successor array.
* `TauCeti.visitTime_eq_iff`: the fibres of the visit times, which is what makes the
  decomposition measurable.
* `TauCeti.Probability.measurable_pathOfSuccessors` and
  `TauCeti.Probability.measurable_successorArray`: both directions are measurable.
* `TauCeti.Probability.map_pathOfSuccessors_map_apply_zero_prodMk_successorArray`: every law on
  path space is the image of the joint law of its initial state and successor array.
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

section TransitionCounts

attribute [local instance] Classical.decEq

variable {α : Type*} {x : ℕ → α} {a b : α} {n : ℕ}

/-- Splitting off the last transition of a prefix. -/
private theorem transitionCount_prefixProj_succ_add_ite (x : ℕ → α) (n : ℕ) (a b : α) :
    transitionCount (prefixProj α (n + 2) x) a b =
      transitionCount (prefixProj α (n + 1) x) a b +
        if x n = a ∧ x (n + 1) = b then 1 else 0 := by
  classical
  rw [transitionCount_eq_card_filter, transitionCount_eq_card_filter, Finset.card_filter,
    Finset.card_filter, Fin.sum_univ_castSucc]
  refine congrArg₂ _ (Finset.sum_congr rfl fun i _ => ?_) ?_
  · by_cases h : x i.val = a ∧ x (i.val + 1) = b <;> simp [prefixProj_apply, h]
  · by_cases h : x n = a ∧ x (n + 1) = b <;> simp [prefixProj_apply, h]

private theorem transitionCount_prefixProj_eq_card_filter
    (x : ℕ → α) (n : ℕ) (a b : α) :
    transitionCount (prefixProj α (n + 1) x) a b =
      ((Finset.range (visitCount x a n)).filter fun k => successorArray x a k = b).card := by
  classical
  induction n with
  | zero => simp [transitionCount_eq_card_filter]
  | succ n ih =>
    rw [transitionCount_prefixProj_succ_add_ite, ih]
    by_cases hx : x n = a
    · rw [visitCount_succ_of_eq hx, Finset.range_add_one, Finset.filter_insert,
        successorArray_visitCount_of_eq hx]
      by_cases hb : x (n + 1) = b
      · simp [hb, hx]
      · simp [hb, hx]
    · rw [visitCount_succ_of_ne hx]
      simp [hx]

/-- **The transition counts of a path are visit counts in its successor rows.** The number of
`a`-to-`b` transitions before time `n` is the number of occurrences of `b` among the successors of
the visits to `a` before `n`. This is the form used by the later row-exchangeability argument. -/
theorem transitionCount_prefixProj (x : ℕ → α) (n : ℕ) (a b : α) :
    transitionCount (prefixProj α (n + 1) x) a b =
      visitCount (successorArray x a) b (visitCount x a n) := by
  classical
  rw [transitionCount_prefixProj_eq_card_filter,
    visitCount_eq_count (successorArray x a) b (visitCount x a n),
    Nat.count_eq_card_filter_range]

end TransitionCounts

section Measurability

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {a : α} {k n : ℕ}

/-- The event that a path has a specified value at a specified index. -/
private theorem measurableSet_apply_eq (a : α) (n : ℕ) :
    MeasurableSet {x : ℕ → α | x n = a} := by
  -- The equality event is definitionally the preimage of the singleton.
  change MeasurableSet ((fun x : ℕ → α => x n) ⁻¹' {a})
  exact measurable_pi_apply n (measurableSet_singleton a)

/-- Visit counts of a measurably varying sequence are measurable when the relevant coordinates
are measurable. -/
theorem measurable_visitCount_comp {β : Type*} [MeasurableSpace β] {P : β → ℕ → α}
    (a : α) (n : ℕ) (hP : ∀ i < n, Measurable fun b => P b i) :
    Measurable fun b => visitCount (P b) a n := by
  classical
  induction n with
  | zero => simp only [visitCount_zero]; exact measurable_const
  | succ n ih =>
    simp only [visitCount_succ]
    exact Measurable.ite (hP n (Nat.lt_succ_self n) (measurableSet_singleton a))
      (Measurable.of_discrete.comp (ih fun i hi => hP i (hi.trans_le (Nat.le_succ n))))
      (ih fun i hi => hP i (hi.trans_le (Nat.le_succ n)))

/-- Visit counts are measurable functions of a path. -/
theorem measurable_visitCount (a : α) (n : ℕ) :
    Measurable fun x : ℕ → α => visitCount x a n :=
  measurable_visitCount_comp a n fun i _ => measurable_pi_apply i

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
    ((measurableSet_apply_eq a m).inter
      (measurable_visitCount a m (measurableSet_singleton k)))
    ?_
  by_cases hm : m = 0
  · have hiInter : {x : ℕ → α | m = 0 ∧ ∀ n, ¬(x n = a ∧ visitCount x a n = k)} =
        ⋂ n, ({x : ℕ → α | x n = a} ∩ {x : ℕ → α | visitCount x a n = k})ᶜ := by
      ext x
      simp [hm, Set.mem_iInter]
    rw [hiInter]
    exact MeasurableSet.iInter fun n =>
      ((measurableSet_apply_eq a n).inter
        (measurable_visitCount a n (measurableSet_singleton k))).compl
  · have hempty : {x : ℕ → α | m = 0 ∧ ∀ n, ¬(x n = a ∧ visitCount x a n = k)} = ∅ := by
      ext x
      simp [hm]
    rw [hempty]
    exact MeasurableSet.empty

/-- Each entry of the successor array is a measurable function of the path. -/
theorem measurable_successorArray_apply (a : α) (k : ℕ) :
    Measurable fun x : ℕ → α => successorArray x a k := by
  simp only [successorArray_def]
  exact measurable_eval_index (g := fun x : ℕ → α => x)
    (f := fun x : ℕ → α => visitTime x a k + 1)
    measurable_id (Measurable.of_discrete.comp (measurable_visitTime a k))

/-- **The successor array of a path is a measurable function of the path.** -/
theorem measurable_successorArray :
    Measurable fun x : ℕ → α => successorArray x :=
  measurable_pi_lambda _ fun a =>
    measurable_pi_lambda _ fun k => measurable_successorArray_apply a k

/-- The map pairing a path's initial state with its successor array is measurable. -/
theorem measurable_apply_zero_prodMk_successorArray :
    Measurable fun x : ℕ → α => (x 0, successorArray x) :=
  (measurable_pi_apply 0).prodMk measurable_successorArray

variable [Countable α]

/-- Each coordinate of the path rebuilt from an initial state and successor array is measurable. -/
private theorem measurable_pathOfSuccessors_apply (n : ℕ) :
    Measurable fun q : α × (α → ℕ → α) => pathOfSuccessors q.1 q.2 n := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [pathOfSuccessors_zero] using measurable_fst
    | succ n =>
      have hn : Measurable fun q : α × (α → ℕ → α) =>
          pathOfSuccessors q.1 q.2 n := ih n (Nat.lt_succ_self n)
      have hcounts : Measurable fun q : α × (α → ℕ → α) =>
          fun a => visitCount (pathOfSuccessors q.1 q.2) a n :=
        measurable_pi_lambda _ fun a => measurable_visitCount_comp a n fun i hi =>
          ih i (hi.trans (Nat.lt_succ_self n))
      have hstate : Measurable fun q : α × (α → ℕ → α) =>
          q.2 (pathOfSuccessors q.1 q.2 n) :=
        measurable_eval_index (g := fun q : α × (α → ℕ → α) => q.2)
          (f := fun q : α × (α → ℕ → α) => pathOfSuccessors q.1 q.2 n)
          measurable_snd hn
      have hcount : Measurable fun q : α × (α → ℕ → α) =>
          visitCount (pathOfSuccessors q.1 q.2) (pathOfSuccessors q.1 q.2 n) n :=
        measurable_eval_index
          (g := fun (q : α × (α → ℕ → α)) a =>
            visitCount (pathOfSuccessors q.1 q.2) a n)
          (f := fun q : α × (α → ℕ → α) => pathOfSuccessors q.1 q.2 n)
          hcounts hn
      simp only [pathOfSuccessors_succ]
      exact measurable_eval_index
        (g := fun q : α × (α → ℕ → α) => q.2 (pathOfSuccessors q.1 q.2 n))
        (f := fun q : α × (α → ℕ → α) =>
          visitCount (pathOfSuccessors q.1 q.2) (pathOfSuccessors q.1 q.2 n) n) hstate hcount

/-- **Rebuilding a path from an initial state and a successor array is measurable.** -/
theorem measurable_pathOfSuccessors :
    Measurable fun q : α × (α → ℕ → α) => pathOfSuccessors q.1 q.2 :=
  measurable_pi_iff.2 measurable_pathOfSuccessors_apply

end Measurability

section Laws

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable α]

/-- **Every law on path space is the image of the joint law of the initial state and the successor
array.** This is the change of variables behind the Diaconis–Freedman representation theorem: a
description of the law of `(x 0, successorArray x)` determines the law of the path. -/
theorem map_pathOfSuccessors_map_apply_zero_prodMk_successorArray (ρ : Measure (ℕ → α)) :
    ((ρ.map fun x => (x 0, successorArray x)).map fun q => pathOfSuccessors q.1 q.2) = ρ := by
  rw [Measure.map_map measurable_pathOfSuccessors measurable_apply_zero_prodMk_successorArray]
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
      measurable_apply_zero_prodMk_successorArray.aemeasurable hY]
    rfl
  rw [hmap, map_pathOfSuccessors_map_apply_zero_prodMk_successorArray]

end Laws

end Probability

end TauCeti

end

end
