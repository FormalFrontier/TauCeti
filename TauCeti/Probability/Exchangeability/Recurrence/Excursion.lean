/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.MeasurableSpace.List
public import TauCeti.Probability.Exchangeability.Excursion
import TauCeti.Probability.Exchangeability.SuccessorArray
public import TauCeti.Probability.Recurrent
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# The excursion process of a recurrent Markov exchangeable process

A recurrent process that starts at a state `a₀` returns to it infinitely often, so its path splits
into an infinite sequence of excursions away from `a₀`. This file assembles that sequence into the
**excursion process** `excursionProcess X a₀`, a process valued in the finite words `List α`, and
proves the theorem the Diaconis–Freedman representation rests on: for a **Markov exchangeable**
process the excursion process is **exchangeable**
(`TauCeti.Probability.MarkovExchangeable.exchangeable_excursionProcess`). De Finetti's theorem then
applies to it, making the excursions conditionally i.i.d. — that step is drawn in
`Recurrence.Representation`, which is where this subtree meets the representation theory, so the
excursion mechanics here stay independent of it.

## How the two symmetries meet

Markov exchangeability constrains **finite-path** events: the mass of a finite path depends only on
its initial state and its transition counts. Exchangeability of the excursion process asks instead
about events of the *excursions*. The bridge is that under recurrence these are the same events.
Prescribing the first `bs.length` excursions of a path starting at `a₀` says exactly that, over the
span `loopSteps bs` of the loop they spell out, the path is the loop word `loopPathAt a₀ bs`
(`TauCeti.eqOn_loopPathAt_iff_excursionPrefix_eq`). Reordering the excursions leaves the initial
state and the transition counts alone, so
`TauCeti.Probability.MarkovExchangeable.measure_setOf_loopPathAt_eq_of_perm` gives the two loops
equal mass, and the finite-dimensional laws of the excursion process are therefore permutation
invariant.

Recurrence is what makes the bridge two-way, and it is a genuine hypothesis: the deterministic walk
of `TauCeti/Probability/Exchangeability/Recurrence/AbsorbedWalk.lean` is Markov exchangeable and
leaves its initial state for good.

Lists carry the natural length-indexed measurable structure of
`TauCeti/MeasureTheory/MeasurableSpace/List.lean`. Over the countable discrete state space here this
structure is discrete, hence standard Borel, so de Finetti's theorem needs no hypothesis beyond the
countability Markov exchangeability already carries.

## Main definitions

* `TauCeti.Probability.excursionProcess`: the sequence of excursions of a process away from a base
  state.

## Main results

* `TauCeti.Probability.measurable_excursion`: an excursion is a measurable function of the path.
* `TauCeti.Probability.measure_setOf_excursionPrefix_eq`: for a process making the visit that
  closes the last prescribed excursion, prescribing the first excursions is a finite-path event.
* `TauCeti.Probability.MarkovExchangeable.measure_setOf_excursionPrefix_eq_of_perm`: reordering a
  list of excursions does not change the probability that it is the process's list of first
  excursions.
* `TauCeti.Probability.MarkovExchangeable.exchangeable_excursionProcess`: **the excursion process
  of a recurrent Markov exchangeable process is exchangeable**.

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

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-! ## The excursion process -/

/-- The excursion process of `X` away from `a₀`: its `k`-th value is the finite word the sample
path traverses strictly between its `k`-th and `(k + 1)`-st visits to `a₀`. -/
def excursionProcess (X : ℕ → Ω → α) (a₀ : α) : ℕ → Ω → List α :=
  fun k ω => excursion (fun n => X n ω) a₀ k

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
theorem excursionProcess_apply (X : ℕ → Ω → α) (a₀ : α) (k : ℕ) (ω : Ω) :
    excursionProcess X a₀ k ω = excursion (fun n => X n ω) a₀ k :=
  (rfl)

/-! ## Measurability -/

section Measurability

variable [MeasurableSingletonClass α]

omit [MeasurableSingletonClass α] in
/-- Reading a fixed finite list of times off a path is measurable. -/
private theorem measurable_map_of_path (l : List ℕ) :
    Measurable fun x : ℕ → α => l.map x := by
  induction l using List.ofFnRec with | _ n f
  rw [measurable_comap_iff]
  have htuple : Measurable fun x : ℕ → α => fun i : Fin n => x (f i) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply (f i)
  have hmk : Measurable fun g : Fin n → α =>
      (⟨n, g⟩ : Σ m, Fin m → α) := by
    refine Measurable.of_le_map ?_
    -- The sigma measurable space is the infimum over its fixed-length strata.
    change (⨅ m : ℕ, MeasurableSpace.map
      (@Sigma.mk ℕ (fun m => Fin m → α) m) inferInstance) ≤
        MeasurableSpace.map (@Sigma.mk ℕ (fun m => Fin m → α) n) inferInstance
    exact iInf_le _ n
  -- The list measurable structure is transported along `List.equivSigmaTuple`, so after
  -- `measurable_comap_iff` the goal is about the composite into `Σ m, Fin m → α`. That composite
  -- is not definitionally the stratum inclusion applied to the tuple of coordinates — the equiv
  -- computes the length from the list — so the two are identified by an explicit equality.
  have hcomp : (List.equivSigmaTuple ∘ fun x : ℕ → α => (List.ofFn f).map x) =
      (fun g : Fin n → α => (⟨n, g⟩ : Σ m, Fin m → α)) ∘
        (fun x => fun i : Fin n => x (f i)) := by
    funext x
    simp only [Function.comp_apply]
    rw [List.map_ofFn]
    simpa only [List.equivSigmaTuple_symm_apply, Function.comp_def] using
      List.equivSigmaTuple.apply_symm_apply (⟨n, x ∘ f⟩ : Σ m, Fin m → α)
  rw [hcomp]
  exact hmk.comp htuple

/-- **An excursion is a measurable function of the path.** The two endpoint visit times are
measurable and range over a countable set, and on each of their fibres the excursion reads a fixed
finite list of coordinates. -/
theorem measurable_excursion (a₀ : α) (k : ℕ) :
    Measurable fun x : ℕ → α => excursion x a₀ k := by
  have hidx : Measurable fun x : ℕ → α => (visitTime x a₀ k + 1, visitTime x a₀ (k + 1)) :=
    (Measurable.of_discrete.comp
        (measurable_visitTime a₀ k (measurableSet_singleton a₀))).prodMk
      (measurable_visitTime a₀ (k + 1) (measurableSet_singleton a₀))
  have hread : Measurable fun p : (ℕ → α) × ℕ × ℕ => (List.Ico p.2.1 p.2.2).map p.1 :=
    measurable_from_prod_countable_left fun q => measurable_map_of_path (List.Ico q.1 q.2)
  have hunfold : (fun x : ℕ → α => excursion x a₀ k) =
      fun x : ℕ → α => (List.Ico (visitTime x a₀ k + 1) (visitTime x a₀ (k + 1))).map x :=
    funext fun x => excursion_def x a₀ k
  rw [hunfold]
  exact hread.comp (measurable_id.prodMk hidx)

/-- Every excursion of a process with a.e. measurable coordinates is a.e. measurable. -/
theorem aemeasurable_excursionProcess {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (a₀ : α) (k : ℕ) :
    AEMeasurable (excursionProcess X a₀ k) μ :=
  (measurable_excursion a₀ k).comp_aemeasurable (aemeasurable_pi_lambda _ hX)

end Measurability

/-! ## Excursion events are finite-path events -/

variable {μ : Measure Ω} {X : ℕ → Ω → α} {a₀ : α}

omit [MeasurableSpace α] in
/-- **Prescribing the first excursions is a finite-path event.** For a process almost surely
starting at `a₀` and almost surely making a `bs.length`-th visit to `a₀`, having `bs` as its first
`bs.length` excursions is, up to a null set, spelling out the loop word of `bs`. Only the visit
closing the last prescribed excursion is used, so this asks less than returning to `a₀` infinitely
often, let alone recurrence of the whole process; `TauCeti.exists_visitCount_of_infinite` supplies
the hypothesis from infinitely many returns. -/
theorem measure_setOf_excursionPrefix_eq {bs : List (List α)}
    (hvisit : ∀ᵐ ω ∂μ, ∃ n, X n ω = a₀ ∧ visitCount (fun n => X n ω) a₀ n = bs.length)
    (h0 : ∀ᵐ ω ∂μ, X 0 ω = a₀) (havoid : ∀ e ∈ bs, a₀ ∉ e) :
    μ {ω | excursionPrefix (fun n => X n ω) a₀ bs.length = bs} =
      μ {ω | ∀ i ≤ loopSteps bs, X i ω = loopPathAt a₀ bs i} := by
  refine (measure_congr (Filter.eventuallyEqSet_iff.2 ?_)).symm
  filter_upwards [h0, hvisit] with ω hω0 hω
  exact eqOn_loopPathAt_iff_excursionPrefix_eq havoid hω hω0

/-- **Reordering a list of excursions does not change the probability that a recurrent Markov
exchangeable process traverses it.** No hypothesis on the list is needed: excursions never visit
the base state, so if some entry of `bs` does, both events are empty. -/
theorem MarkovExchangeable.measure_setOf_excursionPrefix_eq_of_perm (h : MarkovExchangeable μ X)
    (hrec : Recurrent μ X) (h0 : ∀ᵐ ω ∂μ, X 0 ω = a₀) {bs bs' : List (List α)}
    (hperm : bs.Perm bs') :
    μ {ω | excursionPrefix (fun n => X n ω) a₀ bs.length = bs} =
      μ {ω | excursionPrefix (fun n => X n ω) a₀ bs'.length = bs'} := by
  by_cases havoid : ∀ e ∈ bs, a₀ ∉ e
  · have hvisit : ∀ cs : List (List α),
        ∀ᵐ ω ∂μ, ∃ n, X n ω = a₀ ∧ visitCount (fun n => X n ω) a₀ n = cs.length := by
      intro cs
      filter_upwards [h0, hrec.ae_infinite_setOf_eq] with ω hω0 hωinf
      have hinf := hωinf 0
      rw [hω0] at hinf
      exact exists_visitCount_of_infinite hinf cs.length
    have havoid' : ∀ e ∈ bs', a₀ ∉ e := fun e he => havoid e (hperm.mem_iff.2 he)
    rw [measure_setOf_excursionPrefix_eq (hvisit bs) h0 havoid,
      measure_setOf_excursionPrefix_eq (hvisit bs') h0 havoid',
      ← loopSteps_eq_of_perm hperm]
    exact h.measure_setOf_loopPathAt_eq_of_perm a₀ hperm rfl
  · -- A list with an entry through the base state is nobody's list of excursions.
    have hempty : ∀ cs : List (List α), ¬(∀ e ∈ cs, a₀ ∉ e) →
        μ {ω | excursionPrefix (fun n => X n ω) a₀ cs.length = cs} = 0 := by
      intro cs hcs
      convert measure_empty (μ := μ)
      refine Set.eq_empty_of_forall_notMem fun ω hω => hcs ?_
      rw [← hω]
      exact forall_not_mem_excursionPrefix _ a₀ cs.length
    rw [hempty bs havoid,
      hempty bs' fun hbs' => havoid fun e he => hbs' e (hperm.mem_iff.mp he)]

/-! ## Exchangeability of the excursion process -/

section Exchangeable

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- A finite-dimensional event of the excursion process, read as an event of the excursion
prefix. -/
private theorem setOf_forall_excursion_eq {m : ℕ} (v : Fin m → List α) :
    {ω | ∀ i : Fin m, excursionProcess X a₀ i.val ω = v i} =
      {ω | excursionPrefix (fun n => X n ω) a₀ (List.ofFn v).length = List.ofFn v} := by
  ext ω
  simp only [Set.mem_ofPred_eq, excursionProcess_apply, List.length_ofFn]
  constructor
  · intro hv
    refine List.ext_getElem (by simp) fun j hj hj' => ?_
    have hjm : j < m := by simpa using hj
    rw [List.getElem_ofFn, getElem_excursionPrefix hjm]
    exact hv ⟨j, hjm⟩
  · intro hv i
    have hi : i.val < (excursionPrefix (fun n => X n ω) a₀ m).length := by simp
    simpa using List.getElem_of_eq hv hi

/-- **The excursion process of a recurrent Markov exchangeable process is exchangeable.**

This is the half of the Diaconis–Freedman representation theorem that consumes the recurrence
hypothesis. Its finite-dimensional laws are permutation invariant because each of them is the mass
of a finite path, and reordering the excursions of a path preserves both its initial state and its
transition counts — the sufficient statistic Markov exchangeability sees. -/
theorem MarkovExchangeable.exchangeable_excursionProcess (h : MarkovExchangeable μ X)
    (hrec : Recurrent μ X) (h0 : ∀ᵐ ω ∂μ, X 0 ω = a₀) :
    Exchangeable μ (excursionProcess X a₀) := by
  let _ : Countable α := h.countable
  have : MeasurableSingletonClass α := h.measurableSingletonClass
  have hmeas : ∀ k, AEMeasurable (excursionProcess X a₀ k) μ :=
    aemeasurable_excursionProcess h.aemeasurable a₀
  intro m σ
  refine Measure.ext_of_singleton fun v => ?_
  rw [prefixLaw_def,
    blockLaw_apply_of_measurable _ _ _ (fun i => hmeas _) (measurableSet_singleton v),
    blockLaw_apply_of_measurable _ _ _ (fun i => hmeas _) (measurableSet_singleton v)]
  -- Both singleton masses are excursion-prefix events, at lists differing by the permutation.
  have hleft : (fun ω i => excursionProcess X a₀ (σ i).val ω) ⁻¹' {v} =
      {ω | ∀ i : Fin m, excursionProcess X a₀ i.val ω = v (σ.symm i)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, funext_iff]
    exact ⟨fun hv i => by simpa using hv (σ.symm i), fun hv i => by simpa using hv (σ i)⟩
  have hright : (fun ω i => excursionProcess X a₀ i.val ω) ⁻¹' {v} =
      {ω | ∀ i : Fin m, excursionProcess X a₀ i.val ω = v i} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, funext_iff]
  rw [hleft, hright, setOf_forall_excursion_eq, setOf_forall_excursion_eq]
  exact h.measure_setOf_excursionPrefix_eq_of_perm hrec h0
    (Equiv.Perm.ofFn_comp_perm σ.symm v)

end Exchangeable

end Probability

end TauCeti

end

end
