/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.InfinitePi
public import TauCeti.Probability.Exchangeability.ConditionallyIID.Const
public import TauCeti.Probability.Exchangeability.Recurrence.Excursion
public import TauCeti.Probability.Process.MarkovChain
-- Non-public: the reconstruction of a path from its excursions is used only inside a proof.
import TauCeti.Probability.Exchangeability.Recurrence.Reconstruction

/-!
# The excursions of a recurrent Markov chain are i.i.d.

Fix a transition kernel `κ` on a countable discrete state space and a state `a₀` that the chain
started at `a₀` returns to infinitely often almost surely. Cutting a path at its returns to `a₀`
turns it into the sequence of its excursions, and this file proves that **that sequence is
i.i.d.**: the excursions are independent, and each of them is distributed as the first one
(`TauCeti.Probability.conditionallyIIDWith_excursionProcess`). Concatenating the excursions back
therefore recovers the chain from an infinite product measure,

```text
markovChainLaw (Measure.dirac a₀) κ
  = (Measure.infinitePi fun _ : ℕ => excursionLaw κ a₀).map (pathOfExcursions a₀)
```

(`TauCeti.Probability.markovChainLaw_eq_map_pathOfExcursions`), which is the regenerative
structure of a Markov chain at a recurrent state.

## The mechanism

The mass a Markov chain gives a finite path is a product of transition weights, and the
consecutive pairs of a loop word are the consecutive pairs of its excursion loops, gathered
excursion by excursion (`TauCeti.consecutivePairs_loopPath`). So the mass of a loop factors as the
product of the masses of its individual excursion loops
(`TauCeti.Probability.markovChainLaw_apply_setOf_loopPathAt`), a product of
`TauCeti.Probability.excursionWeight`s. Once the chain has made the return closing the last of
them, prescribing the first excursions of a path is exactly prescribing the loop word it spells out
(`TauCeti.Probability.measure_setOf_excursionPrefix_eq`), so the finite-dimensional laws of the
excursion process are products and the excursions are independent with a common law.

## Where this sits in the Diaconis–Freedman theorem

`TauCeti/Probability/Exchangeability/Recurrence/Representation.lean` proves the decomposition step:
a recurrent Markov exchangeable process is a mixture of processes with i.i.d. excursions. What
remains for `TauCeti.Probability.MixedMarkovChain` is that the drawn excursion law is the excursion
law of a Markov chain. This file supplies the converse half of that identification, namely that a
Markov chain does have i.i.d. excursions and is rebuilt from them, so that a mixing law carried on
excursion laws of Markov chains yields a mixture of Markov chains.

Recurrence is a genuine hypothesis, not a technicality: the absorbed walk of
`TauCeti/Probability/Exchangeability/Recurrence/AbsorbedWalk.lean` is a Markov chain that never
returns to its initial state, and its excursion process is junk.

## Main definitions

* `TauCeti.Probability.excursionWeight`: the product of transition weights along a given finite
  word followed by a return to `a₀`; for a Markov kernel, this is the corresponding path mass.
* `TauCeti.Probability.excursionLaw`: the law of the first excursion of the chain started at `a₀`.

## Main results

* `TauCeti.Probability.markovChainLaw_apply_setOf_loopPathAt`: the mass of a loop is the
  product of the weights of its excursions.
* `TauCeti.Probability.excursionLaw_apply_singleton`: once the chain returns to the base state,
  the law of an excursion is given by the excursion weights.
* `TauCeti.Probability.prefixLaw_excursionProcess_eq_pi`: the finite-dimensional laws of the
  excursion process are products.
* `TauCeti.Probability.conditionallyIIDWith_excursionProcess`: **the excursions of a recurrent
  Markov chain are i.i.d.**, with `excursionLaw` as constant directing measure.
* `TauCeti.Probability.markovChainLaw_eq_map_pathOfExcursions`: **the chain is the concatenation of
  i.i.d. excursions.**
* `TauCeti.Probability.ae_infinite_setOf_eq_markovChainLaw_const` and
  `TauCeti.Probability.excursionLaw_const`: the returning hypothesis is satisfiable, and on the
  chain that never leaves `a₀` the excursion law is the point mass at the empty word.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 8, "Markov exchangeability".

No material is adapted from `cameronfreer/exchangeability`, which treats exchangeable rather than
Markov exchangeable sequences.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-! ## The weight of a single excursion -/

/-- The **excursion weight** of a finite word `e` at the base state `a₀`: the product of the
transition weights along the loop word `a₀, e, a₀`. For a Markov kernel, this is the probability
mass of traversing `e` from `a₀` and then returning to `a₀`. -/
def excursionWeight (κ : Kernel α α) (a₀ : α) (e : List α) : ℝ≥0∞ :=
  ((loopPath a₀ [e]).consecutivePairs.map fun q => κ q.1 {q.2}).prod

/-- The empty excursion is the single step from the base state back to itself. -/
@[simp]
theorem excursionWeight_nil (κ : Kernel α α) (a₀ : α) :
    excursionWeight κ a₀ [] = κ a₀ {a₀} := by
  rw [excursionWeight]
  simp [List.consecutivePairs]

/-! ## The mass of a loop factors over its excursions -/

section LoopMass

variable [MeasurableSingletonClass α] {κ : Kernel α α} [IsMarkovKernel κ] {a₀ : α}

/-- **The mass of a loop word factors over its excursions**, in the finite-prefix encoding. This
is the working form behind `TauCeti.Probability.markovChainLaw_apply_setOf_loopPathAt`, which is
the public loop-mass interface. -/
private theorem markovChainLaw_map_prefix_apply_singleton_loopPathAt (bs : List (List α)) :
    ((markovChainLaw (Measure.dirac a₀) κ).map
        fun x (i : Fin (loopSteps bs + 1)) => x i.1) {fun i => loopPathAt a₀ bs i.val}
      = (bs.map (excursionWeight κ a₀)).prod := by
  rw [markovChainLaw_map_prefix_apply_singleton]
  have hzero : (Measure.dirac a₀) {loopPathAt a₀ bs (0 : Fin (loopSteps bs + 1)).val} = 1 := by
    simp [loopPathAt_zero]
  rw [hzero, one_mul]
  have hstep : ∀ i : Fin (loopSteps bs),
      κ (loopPathAt a₀ bs i.castSucc.val) {loopPathAt a₀ bs i.succ.val} =
        κ ((loopPath a₀ bs).getD i.val a₀) {(loopPath a₀ bs).getD (i.val + 1) a₀} := by
    intro i
    rw [loopPathAt_def, loopPathAt_def]
    simp
  have hweight : excursionWeight κ a₀ = fun e =>
      ((loopPath a₀ [e]).consecutivePairs.map fun q => κ q.1 {q.2}).prod := by
    funext e
    rw [excursionWeight]
  rw [Finset.prod_congr rfl fun i _ => hstep i,
    prod_consecutivePairs_getD (fun a b => κ a {b}) a₀ _ (loopPath a₀ bs)
      (length_loopPath a₀ bs),
    consecutivePairs_loopPath, hweight, List.map_flatMap]
  simp only [List.flatMap, List.prod_flatten, List.map_map, Function.comp_def]

/-- **The probability that the chain traverses a prescribed loop** is the product of the excursion
weights of that loop. -/
theorem markovChainLaw_apply_setOf_loopPathAt (bs : List (List α)) :
    markovChainLaw (Measure.dirac a₀) κ {x | ∀ i ≤ loopSteps bs, x i = loopPathAt a₀ bs i}
      = (bs.map (excursionWeight κ a₀)).prod := by
  have hset : {x : ℕ → α | ∀ i ≤ loopSteps bs, x i = loopPathAt a₀ bs i}
      = (fun (x : ℕ → α) (i : Fin (loopSteps bs + 1)) => x i.1) ⁻¹'
        {fun i : Fin (loopSteps bs + 1) => loopPathAt a₀ bs i.val} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
    exact ⟨fun h i => h i.val (Nat.lt_succ_iff.1 i.2), fun h i hi => h ⟨i, Nat.lt_succ_of_le hi⟩⟩
  rw [hset, ← Measure.map_apply (by fun_prop) (measurableSet_singleton _),
    markovChainLaw_map_prefix_apply_singleton_loopPathAt]

/-- **A chain started at `a₀` starts at `a₀`.** -/
theorem markovChainLaw_dirac_ae_apply_zero (κ : Kernel α α) [IsMarkovKernel κ] (a₀ : α) :
    ∀ᵐ x ∂(markovChainLaw (Measure.dirac a₀) κ), x 0 = a₀ :=
  HasLaw.ae_eq_of_dirac
    ⟨(measurable_pi_apply 0).aemeasurable, markovChainLaw_map_eval_zero _ _⟩

end LoopMass

/-! ## The law of an excursion -/

section ExcursionLaw

variable [Countable α] [MeasurableSingletonClass α] {κ : Kernel α α} [IsMarkovKernel κ] {a₀ : α}

omit [Countable α] in
/-- **The excursions of a chain started at `a₀` have prescribed masses.** Once the chain almost
surely makes the visit closing the last prescribed excursion, prescribing the first excursions is
prescribing the loop word they spell out, whose mass factors over the excursions. -/
theorem markovChainLaw_apply_setOf_excursionPrefix_eq {bs : List (List α)}
    (hvisit : ∀ᵐ x ∂(markovChainLaw (Measure.dirac a₀) κ),
      ∃ n, x n = a₀ ∧ visitCount x a₀ n = bs.length)
    (havoid : ∀ e ∈ bs, a₀ ∉ e) :
    markovChainLaw (Measure.dirac a₀) κ {x | excursionPrefix x a₀ bs.length = bs}
      = (bs.map (excursionWeight κ a₀)).prod := by
  rw [measure_setOf_excursionPrefix_eq (X := fun n (x : ℕ → α) => x n) hvisit
      (markovChainLaw_dirac_ae_apply_zero κ a₀) havoid,
    markovChainLaw_apply_setOf_loopPathAt]

/-- The law of the first excursion of the chain started at `a₀`. Under the returning hypothesis,
this is the law of the word traversed strictly between the first two visits to `a₀`. If either
visit is absent, `visitTime` uses its junk value `0`, so the interval used by `excursion` may be
empty. -/
def excursionLaw (κ : Kernel α α) [IsMarkovKernel κ] (a₀ : α) : Measure (List α) :=
  (markovChainLaw (Measure.dirac a₀) κ).map fun x => excursion x a₀ 0

/-- The excursion law is a probability measure, being the law of a random word. -/
instance isProbabilityMeasure_excursionLaw : IsProbabilityMeasure (excursionLaw κ a₀) := by
  rw [excursionLaw]
  infer_instance

/-- The excursion law evaluated on a set of words. Every set of words is measurable, the state
space being countable and discrete. -/
theorem excursionLaw_apply (A : Set (List α)) :
    excursionLaw κ a₀ A =
      markovChainLaw (Measure.dirac a₀) κ {x | excursion x a₀ 0 ∈ A} :=
  Measure.map_apply (measurable_excursion a₀ 0) (MeasurableSet.of_discrete)

/-- **An excursion never visits its base state**, so the excursion law charges no word through
`a₀`. -/
@[simp]
theorem excursionLaw_apply_singleton_of_mem {e : List α} (he : a₀ ∈ e) :
    excursionLaw κ a₀ {e} = 0 := by
  rw [excursionLaw_apply]
  have hempty : {x : ℕ → α | excursion x a₀ 0 ∈ ({e} : Set (List α))} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    intro hx
    exact not_mem_excursion x a₀ 0 (hx ▸ he)
  rw [hempty, measure_empty]

/-- **The excursion law is given by the excursion weights.** One return to `a₀` is enough: it is
what makes the first excursion the word between the first two visits. -/
theorem excursionLaw_apply_singleton
    (hvisit : ∀ᵐ x ∂(markovChainLaw (Measure.dirac a₀) κ), ∃ n, x n = a₀ ∧ visitCount x a₀ n = 1)
    {e : List α} (he : a₀ ∉ e) :
    excursionLaw κ a₀ {e} = excursionWeight κ a₀ e := by
  have hmass := markovChainLaw_apply_setOf_excursionPrefix_eq (bs := [e]) hvisit
    (by simpa using he)
  rw [excursionLaw_apply]
  have hset : {x : ℕ → α | excursion x a₀ 0 ∈ ({e} : Set (List α))}
      = {x : ℕ → α | excursionPrefix x a₀ ([e] : List (List α)).length = [e]} := by
    ext x
    simp [excursionPrefix_def]
  rw [hset, hmass]
  simp

end ExcursionLaw

/-! ## The excursion process is i.i.d. -/

section IID

variable [Countable α] [MeasurableSingletonClass α] {κ : Kernel α α} [IsMarkovKernel κ] {a₀ : α}

omit [Countable α] [IsMarkovKernel κ] in
/-- A.e. measurability of the excursions of the coordinate process on path space. -/
private theorem aemeasurable_excursionProcess_eval (μ : Measure (ℕ → α)) (a₀ : α) (k : ℕ) :
    AEMeasurable (excursionProcess (fun n (x : ℕ → α) => x n) a₀ k) μ :=
  aemeasurable_excursionProcess (fun i => (measurable_pi_apply i).aemeasurable) a₀ k

omit [Countable α] [IsMarkovKernel κ] in
/-- A.e. measurability of the whole excursion sequence of the coordinate process. -/
private theorem aemeasurable_excursionProcess_pi (μ : Measure (ℕ → α)) (a₀ : α) :
    AEMeasurable
      (fun (x : ℕ → α) => fun k => excursionProcess (fun n (y : ℕ → α) => y n) a₀ k x) μ :=
  AEMeasurable.of_eval fun k => aemeasurable_excursionProcess_eval μ a₀ k

omit [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α] in
/-- Prescribing the first `m` excursions of a path is prescribing them coordinatewise. -/
private theorem excursionPrefix_eq_ofFn_iff (x : ℕ → α) (a₀ : α) {m : ℕ} (w : Fin m → List α) :
    excursionPrefix x a₀ m = List.ofFn w ↔ ∀ i : Fin m, excursion x a₀ i.val = w i := by
  rw [List.ext_getElem_iff]
  simp [excursionPrefix_def, Fin.forall_iff]

/-- **The finite-dimensional laws of the excursion process are products.** Once the chain almost
surely makes its `m`-th return, its first `m` excursions are independent, each with law
`TauCeti.Probability.excursionLaw`. -/
theorem prefixLaw_excursionProcess_eq_pi (m : ℕ)
    (hvisit : ∀ᵐ x ∂(markovChainLaw (Measure.dirac a₀) κ),
      ∃ n, x n = a₀ ∧ visitCount x a₀ n = m) :
    prefixLaw (markovChainLaw (Measure.dirac a₀) κ)
        (excursionProcess (fun n (x : ℕ → α) => x n) a₀) m
      = Measure.pi fun _ : Fin m => excursionLaw κ a₀ := by
  refine Measure.ext_of_singleton fun w => ?_
  rw [Measure.pi_singleton, prefixLaw_def,
    blockLaw_apply_of_measurable _ _ _
      (fun i => aemeasurable_excursionProcess_eval _ a₀ i.val) (measurableSet_singleton w)]
  have hset : (fun (x : ℕ → α) (i : Fin m) =>
      excursionProcess (fun n (y : ℕ → α) => y n) a₀ i.val x) ⁻¹' {w}
      = {x : ℕ → α | ∀ i : Fin m, excursion x a₀ i.val = w i} := by
    ext x
    simp [funext_iff]
  rw [hset]
  by_cases havoid : ∀ i : Fin m, a₀ ∉ w i
  · have hpref : {x : ℕ → α | ∀ i : Fin m, excursion x a₀ i.val = w i}
        = {x : ℕ → α | excursionPrefix x a₀ (List.ofFn w).length = List.ofFn w} := by
      ext x
      simp only [Set.mem_ofPred_eq, List.length_ofFn]
      exact (excursionPrefix_eq_ofFn_iff x a₀ w).symm
    rw [hpref, markovChainLaw_apply_setOf_excursionPrefix_eq (by simpa using hvisit)
      (by simpa using fun i => havoid i), List.map_ofFn, List.prod_ofFn]
    exact Finset.prod_congr rfl fun i _ =>
      (excursionLaw_apply_singleton
        (hvisit.mono fun x hx => exists_visitCount_of_le hx
          (Nat.succ_le_iff.2 (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)))
        (havoid i)).symm
  · obtain ⟨i₀, hi₀⟩ := not_forall.1 havoid
    have hi₀ : a₀ ∈ w i₀ := not_not.1 hi₀
    have hempty : {x : ℕ → α | ∀ i : Fin m, excursion x a₀ i.val = w i} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact not_mem_excursion x a₀ i₀.val ((hx i₀) ▸ hi₀)
    rw [hempty, measure_empty]
    exact (Finset.prod_eq_zero (Finset.mem_univ i₀)
      (excursionLaw_apply_singleton_of_mem hi₀)).symm

/-- **The excursion process gives finite boxes their product mass.** It is enough that the chain
almost surely makes all returns needed by the coordinates in the box. -/
theorem pathLaw_excursionProcess_apply_pi (s : Finset ℕ) (t : ℕ → Set (List α))
    (hvisit : ∀ᵐ x ∂(markovChainLaw (Measure.dirac a₀) κ),
      ∃ n, x n = a₀ ∧ visitCount x a₀ n = s.sup fun i => i + 1) :
    pathLaw (markovChainLaw (Measure.dirac a₀) κ)
        (excursionProcess (fun n (x : ℕ → α) => x n) a₀) (Set.pi ↑s t)
      = ∏ i ∈ s, excursionLaw κ a₀ (t i) := by
  classical
  let m := s.sup fun i => i + 1
  have hm : s ⊆ Finset.range m := fun i hi =>
    Finset.mem_range.2 ((Nat.lt_succ_self i).trans_le (Finset.le_sup hi))
  have hX := aemeasurable_excursionProcess_pi (markovChainLaw (Measure.dirac a₀) κ) a₀
  have hbox : (Set.pi ↑s t : Set (ℕ → List α))
      = prefixProj (List α) m ⁻¹'
        (Set.univ.pi fun i : Fin m => if i.val ∈ s then t i.val else Set.univ) := by
    ext y
    simp only [Set.mem_pi, Set.mem_preimage, prefixProj_apply, Finset.mem_coe]
    constructor
    · intro h i
      by_cases hi : i.val ∈ s
      · simpa [hi] using h i.val hi
      · simp [hi]
    · intro h i hi
      simpa [hi] using h ⟨i, Finset.mem_range.1 (hm hi)⟩
  rw [hbox, ← Measure.map_apply (measurable_prefixProj m)
      (MeasurableSet.univ_pi fun _ => MeasurableSet.of_discrete),
    map_prefixProj_pathLaw _ hX, prefixLaw_excursionProcess_eq_pi m (by simpa [m] using hvisit),
    Measure.pi_pi]
  rw [Fin.prod_univ_eq_prod_range
    (fun i => excursionLaw κ a₀ (if i ∈ s then t i else Set.univ)) m]
  simp only [apply_ite (excursionLaw κ a₀), measure_univ]
  rw [Finset.prod_ite_mem, Finset.inter_eq_right.2 hm]

/-- **The excursion process of the chain has the infinite product law.** -/
theorem pathLaw_excursionProcess_eq_infinitePi
    (hret : ∀ᵐ x ∂(markovChainLaw (Measure.dirac a₀) κ), {n | x n = a₀}.Infinite) :
    pathLaw (markovChainLaw (Measure.dirac a₀) κ)
        (excursionProcess (fun n (x : ℕ → α) => x n) a₀)
      = Measure.infinitePi fun _ : ℕ => excursionLaw κ a₀ :=
  Measure.eq_infinitePi _ fun s t _ =>
    pathLaw_excursionProcess_apply_pi s t
      (hret.mono fun _ hx => exists_visitCount_of_infinite hx (s.sup fun i => i + 1))

/-- **Every realized excursion of the chain has the excursion law.** For coordinate `k`, it is
enough that the chain almost surely makes its `(k + 1)`-st return. -/
theorem map_excursionProcess_eq_excursionLaw (k : ℕ)
    (hvisit : ∀ᵐ x ∂(markovChainLaw (Measure.dirac a₀) κ),
      ∃ n, x n = a₀ ∧ visitCount x a₀ n = k + 1) :
    (markovChainLaw (Measure.dirac a₀) κ).map
        (excursionProcess (fun n (x : ℕ → α) => x n) a₀ k) = excursionLaw κ a₀ := by
  let i : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  have hcoord : ((fun y : Fin (k + 1) → List α => y i) ∘
      fun (x : ℕ → α) (j : Fin (k + 1)) =>
        excursionProcess (fun n (y : ℕ → α) => y n) a₀ j.val x)
      = excursionProcess (fun n (x : ℕ → α) => x n) a₀ k := rfl
  have h := congrArg (fun ν : Measure (Fin (k + 1) → List α) => ν.map fun y => y i)
    (prefixLaw_excursionProcess_eq_pi (k + 1) hvisit)
  rw [prefixLaw_def, blockLaw_def,
    (measurable_pi_apply i).aemeasurable.map_map_of_aemeasurable
      (AEMeasurable.of_eval fun j => aemeasurable_excursionProcess_eval _ a₀ j.val),
    hcoord, Measure.pi_map_eval] at h
  simpa using h

/-- **The excursions of the chain are independent.** -/
theorem iIndepFun_excursionProcess
    (hret : ∀ᵐ x ∂(markovChainLaw (Measure.dirac a₀) κ), {n | x n = a₀}.Infinite) :
    iIndepFun (excursionProcess (fun n (x : ℕ → α) => x n) a₀)
      (markovChainLaw (Measure.dirac a₀) κ) := by
  have hX := aemeasurable_excursionProcess_pi (markovChainLaw (Measure.dirac a₀) κ) a₀
  have hlaw : (fun k => (markovChainLaw (Measure.dirac a₀) κ).map
      (excursionProcess (fun n (x : ℕ → α) => x n) a₀ k)) = fun _ : ℕ => excursionLaw κ a₀ :=
    funext fun k => map_excursionProcess_eq_excursionLaw k
      (hret.mono fun _ hx => exists_visitCount_of_infinite hx (k + 1))
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀ hX, hlaw, ← pathLaw_def]
  exact pathLaw_excursionProcess_eq_infinitePi hret

/-- **The excursions of a recurrent Markov chain are i.i.d.**: independent, and each distributed as
the first excursion. The constant directing measure is the excursion law, so this is genuine
independence and not only a mixture identity. -/
theorem conditionallyIIDWith_excursionProcess
    (hret : ∀ᵐ x ∂(markovChainLaw (Measure.dirac a₀) κ), {n | x n = a₀}.Infinite) :
    ConditionallyIIDWith (markovChainLaw (Measure.dirac a₀) κ)
      (excursionProcess (fun n (x : ℕ → α) => x n) a₀)
      (fun _ => ⟨excursionLaw κ a₀, isProbabilityMeasure_excursionLaw⟩) :=
  conditionallyIIDWith_const_iff_iIndepFun_and_map_eq.2
    ⟨aemeasurable_excursionProcess_eval _ a₀, iIndepFun_excursionProcess hret,
      fun k => map_excursionProcess_eq_excursionLaw k
        (hret.mono fun _ hx => exists_visitCount_of_infinite hx (k + 1))⟩

/-- **A recurrent Markov chain is the concatenation of i.i.d. excursions.** Drawing excursions
independently from the excursion law and concatenating them reproduces the chain: the chain is
regenerative at a recurrent state. -/
theorem markovChainLaw_eq_map_pathOfExcursions
    (hret : ∀ᵐ x ∂(markovChainLaw (Measure.dirac a₀) κ), {n | x n = a₀}.Infinite) :
    markovChainLaw (Measure.dirac a₀) κ
      = (Measure.infinitePi fun _ : ℕ => excursionLaw κ a₀).map (pathOfExcursions a₀) := by
  have hpath : pathLaw (markovChainLaw (Measure.dirac a₀) κ) (fun n (x : ℕ → α) => x n)
      = markovChainLaw (Measure.dirac a₀) κ := by
    rw [pathLaw_def]
    exact Measure.map_id
  have h := pathLaw_eq_map_pathOfExcursions (μ := markovChainLaw (Measure.dirac a₀) κ)
    (X := fun n (x : ℕ → α) => x n) (a₀ := a₀)
    (fun i => (measurable_pi_apply i).aemeasurable) hret
    (markovChainLaw_dirac_ae_apply_zero κ a₀)
  rw [hpath, pathLaw_excursionProcess_eq_infinitePi hret] at h
  exact h

end IID

/-! ## The hypothesis is satisfiable -/

section ReturningChain

variable [Countable α] [MeasurableSingletonClass α]

omit [Countable α] [MeasurableSingletonClass α] in
/-- **The chain that jumps to `a₀` from every state sits at `a₀` at every time.** -/
@[simp]
theorem markovChainLaw_const_map_eval (a₀ : α) (n : ℕ) :
    (markovChainLaw (Measure.dirac a₀) (Kernel.const α (Measure.dirac a₀))).map (fun x => x n)
      = Measure.dirac a₀ := by
  induction n with
  | zero => exact markovChainLaw_map_eval_zero _ _
  | succ n ih =>
    rw [markovChainLaw_map_eval_succ, ih]
    simp

omit [Countable α] in
/-- **A chain with a recurrent base state exists.** The chain that jumps to `a₀` from every state
returns to `a₀` at every time, so the returning hypothesis of this file is not vacuous. -/
theorem ae_infinite_setOf_eq_markovChainLaw_const (a₀ : α) :
    ∀ᵐ x ∂(markovChainLaw (Measure.dirac a₀) (Kernel.const α (Measure.dirac a₀))),
      {n | x n = a₀}.Infinite := by
  have hall : ∀ᵐ x ∂(markovChainLaw (Measure.dirac a₀) (Kernel.const α (Measure.dirac a₀))),
      ∀ n, x n = a₀ :=
    ae_all_iff.2 fun n =>
      HasLaw.ae_eq_of_dirac
        ⟨(measurable_pi_apply n).aemeasurable, markovChainLaw_const_map_eval a₀ n⟩
  filter_upwards [hall] with x hx
  rw [Set.eq_univ_of_forall hx]
  exact Set.infinite_univ

/-- **The excursions of that chain are empty.** Its excursion law is the point mass at the empty
word, which is what the representation theorem must give for a chain that never leaves `a₀`. -/
@[simp]
theorem excursionLaw_const (a₀ : α) :
    excursionLaw (Kernel.const α (Measure.dirac a₀)) a₀ = Measure.dirac ([] : List α) := by
  refine Measure.ext_of_singleton fun e => ?_
  by_cases hmem : a₀ ∈ e
  · have hne : ([] : List α) ≠ e := by
      rintro rfl
      exact List.not_mem_nil hmem
    rw [excursionLaw_apply_singleton_of_mem hmem, Measure.dirac_apply]
    simp [hne]
  · rw [excursionLaw_apply_singleton ((ae_infinite_setOf_eq_markovChainLaw_const a₀).mono
        fun x hx => exists_visitCount_of_infinite hx 1) hmem,
      Measure.dirac_apply]
    match e with
    | [] => simp
    | b :: t =>
      have hb : a₀ ≠ b := fun hb => hmem (hb ▸ List.mem_cons_self ..)
      have hzero : (Kernel.const α (Measure.dirac a₀)) a₀ {b} = 0 := by
        simp [hb]
      have hweight : excursionWeight (Kernel.const α (Measure.dirac a₀)) a₀ (b :: t) = 0 := by
        rw [excursionWeight]
        simp only [loopPath_cons, loopPath_nil, List.consecutivePairs, List.cons_append,
          List.tail_cons, List.zip_cons_cons, List.map_cons, List.prod_cons]
        rw [hzero, zero_mul]
      rw [hweight]
      simp

end ReturningChain

end Probability

end TauCeti

end

end
