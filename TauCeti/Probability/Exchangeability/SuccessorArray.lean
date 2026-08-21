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

The combinatorial successor-array encoding and its inverse are defined in
`TauCeti.Combinatorics.Enumerative.SuccessorArray`. This file relates that encoding to transition
counts and proves that both directions of the change of variables are measurable.

## Why this is the Diaconis–Freedman decomposition

Markov exchangeability (`TauCeti.Probability.MarkovExchangeable`) says that the law of a finite
path depends only on its initial state and transition counts. The successor array is the change of
variables that reads those counts as occurrence counts in initial segments of its rows. Turning
this identity into within-row exchangeability requires the later endpoint and recurrence argument;
that step is not proved here. The measurable encoding proved here is what will transfer a future
representation of the joint law of `(x 0, successorArray x)` back to the law of the path.

## Main results

* `TauCeti.Probability.transitionCount_prefixProj`: the transition counts of a prefix are the
  occurrence counts in the rows of the successor array.
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
  have h := (transitionCount_comp_castSucc_add_last
    (w := prefixProj α (n + 2) x) a b).symm
  have hprefix : prefixProj α (n + 2) x ∘ Fin.castSucc = prefixProj α (n + 1) x := by
    funext i
    rfl
  rw [hprefix] at h
  -- Normalize the two final indices while leaving `transitionCount` opaque.
  change transitionCount (prefixProj α (n + 2) x) a b =
    transitionCount (prefixProj α (n + 1) x) a b +
      (if x n = a ∧ x (n + 1) = b then 1 else 0) at h
  exact h

/-- A visit count is the occurrence count of the corresponding finite prefix. -/
theorem visitCount_eq_occCount_prefixProj (x : ℕ → α) (a : α) (n : ℕ) :
    visitCount x a n = occCount (prefixProj α n x) a := by
  rw [visitCount_def]
  rfl

private theorem transitionCount_prefixProj_eq_occCount
    (x : ℕ → α) (n : ℕ) (a b : α) :
    transitionCount (prefixProj α (n + 1) x) a b =
      occCount (prefixProj α (visitCount x a n) (successorArray x a)) b := by
  classical
  rw [← visitCount_eq_occCount_prefixProj (successorArray x a) b (visitCount x a n),
    visitCount_eq_count, Nat.count_eq_card_filter_range]
  induction n with
  | zero => simp [transitionCount_eq_card_filter]
  | succ n ih =>
    rw [transitionCount_prefixProj_succ_add_ite, ih]
    by_cases hx : x n = a
    · rw [visitCount_succ_of_eq hx, Finset.range_add_one, Finset.filter_insert,
        successorArray_visitCount_of_eq hx]
      by_cases hb : x (n + 1) = b
      <;> simp [hb, hx]
    · rw [visitCount_succ_of_ne hx]
      simp [hx]

/-- **The transition counts of a path are visit counts in its successor rows.** The number of
`a`-to-`b` transitions before time `n` is the number of occurrences of `b` among the successors of
the visits to `a` before `n`. This is the form used by the later row-exchangeability argument. -/
theorem transitionCount_prefixProj (x : ℕ → α) (n : ℕ) (a b : α) :
    transitionCount (prefixProj α (n + 1) x) a b =
      visitCount (successorArray x a) b (visitCount x a n) := by
  classical
  rw [transitionCount_prefixProj_eq_occCount,
    ← visitCount_eq_occCount_prefixProj (successorArray x a) b (visitCount x a n)]

end TransitionCounts

section Measurability

variable {α : Type*} [MeasurableSpace α] {a : α} {k n : ℕ}

/-- The event that a path has a specified value at a specified index. -/
private theorem measurableSet_apply_eq (a : α) (n : ℕ) (ha : MeasurableSet ({a} : Set α)) :
    MeasurableSet {x : ℕ → α | x n = a} := by
  -- Writing the set-builder as a preimage lets `measurable_pi_apply` infer its target set.
  change MeasurableSet ((fun x : ℕ → α => x n) ⁻¹' {a})
  exact measurable_pi_apply n ha

/-- Visit counts of a measurably varying sequence are measurable when the relevant coordinates
are measurable. -/
theorem measurable_visitCount_comp {β : Type*} [MeasurableSpace β] {P : β → ℕ → α}
    (a : α) (n : ℕ) (ha : MeasurableSet ({a} : Set α))
    (hP : ∀ i < n, Measurable fun b => P b i) :
    Measurable fun b => visitCount (P b) a n := by
  classical
  induction n with
  | zero => simp only [visitCount_zero]; exact measurable_const
  | succ n ih =>
    simp only [visitCount_succ]
    exact Measurable.ite (hP n (Nat.lt_succ_self n) ha)
      (Measurable.of_discrete.comp (ih fun i hi => hP i (hi.trans_le (Nat.le_succ n))))
      (ih fun i hi => hP i (hi.trans_le (Nat.le_succ n)))

/-- Visit counts are measurable functions of a path. -/
theorem measurable_visitCount (a : α) (n : ℕ) (ha : MeasurableSet ({a} : Set α)) :
    Measurable fun x : ℕ → α => visitCount x a n :=
  measurable_visitCount_comp a n ha fun i _ => measurable_pi_apply i

/-- The event witnessing that index `n` is the `k`-th visit to `a` is measurable. -/
private theorem measurableSet_isVisitWitness (a : α) (k n : ℕ)
    (ha : MeasurableSet ({a} : Set α)) :
    MeasurableSet {x : ℕ → α | x n = a ∧ visitCount x a n = k} :=
  (measurableSet_apply_eq a n ha).inter
    (measurable_visitCount a n ha (measurableSet_singleton k))

/-- Visit times are measurable functions of the path. Each fibre is described by
`visitTime_eq_iff` as a countable Boolean combination of coordinate events. -/
theorem measurable_visitTime (a : α) (k : ℕ) (ha : MeasurableSet ({a} : Set α)) :
    Measurable fun x : ℕ → α => visitTime x a k := by
  refine measurable_to_countable' fun m => ?_
  have hrw : (fun x : ℕ → α => visitTime x a k) ⁻¹' {m} =
      ({x : ℕ → α | x m = a} ∩ {x : ℕ → α | visitCount x a m = k}) ∪
        {x : ℕ → α | m = 0 ∧ ∀ n, ¬(x n = a ∧ visitCount x a n = k)} := by
    ext x
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_ofPred_eq] using visitTime_eq_iff (x := x) (a := a)
  rw [hrw]
  refine MeasurableSet.union
    (measurableSet_isVisitWitness a k m ha)
    ?_
  by_cases hm : m = 0
  · have hiInter : {x : ℕ → α | m = 0 ∧ ∀ n, ¬(x n = a ∧ visitCount x a n = k)} =
        ⋂ n, ({x : ℕ → α | x n = a} ∩ {x : ℕ → α | visitCount x a n = k})ᶜ := by
      ext x
      simp only [Set.mem_ofPred_eq, hm, true_and, Set.mem_iInter, Set.mem_compl_iff,
        Set.mem_inter_iff]
    rw [hiInter]
    exact MeasurableSet.iInter fun n => (measurableSet_isVisitWitness a k n ha).compl
  · have hempty : {x : ℕ → α | m = 0 ∧ ∀ n, ¬(x n = a ∧ visitCount x a n = k)} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, hm, false_and, Set.mem_empty_iff_false]
    rw [hempty]
    exact MeasurableSet.empty

/-- Each entry of the successor array is a measurable function of the path. -/
theorem measurable_successorArray_apply (a : α) (k : ℕ)
    (ha : MeasurableSet ({a} : Set α)) :
    Measurable fun x : ℕ → α => successorArray x a k := by
  simp only [successorArray_def]
  exact measurable_eval_index (g := fun x : ℕ → α => x)
    (f := fun x : ℕ → α => visitTime x a k + 1)
    measurable_id (Measurable.of_discrete.comp (measurable_visitTime a k ha))

variable [MeasurableSingletonClass α]

/-- **The successor array of a path is a measurable function of the path.** -/
theorem measurable_successorArray :
    Measurable fun x : ℕ → α => successorArray x :=
  measurable_pi_lambda _ fun a =>
    measurable_pi_lambda _ fun k => measurable_successorArray_apply a k (measurableSet_singleton a)

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
        measurable_pi_lambda _ fun a =>
          measurable_visitCount_comp a n (measurableSet_singleton a) fun i hi =>
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
