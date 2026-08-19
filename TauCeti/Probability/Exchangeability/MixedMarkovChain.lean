/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.MarkovExchangeable
public import TauCeti.Probability.Exchangeability.MixedIID.Basic

/-!
# Mixtures of Markov chains

A process `X : ℕ → Ω → α` on a countable state space is a **mixture of Markov chains** when its
finite-path `μ`-masses are averages of Markov-chain path masses: there is a random
initial law `ν : Ω → ProbabilityMeasure α` and a random transition matrix
`κ : Ω → α → ProbabilityMeasure α` with

```text
prefixLaw μ X (n + 1) {w} = ∫⁻ ω, ν ω {w 0} * ∏ i, κ ω (w i.castSucc) {w i.succ} ∂μ
```

for every finite path `w`. `MixedMarkovChainWith μ X ν κ` names the pair of witnesses, and
`MixedMarkovChain μ X` is the existential wrapper. The naming and the witness/existential split
follow `MixedIIDWith` / `MixedIID`. This notion contains mixed i.i.d. processes: an i.i.d. mixture
is the mixture of Markov chains whose rows do not depend on the current state
(`MixedIIDWith.mixedMarkovChainWith`).

⚠ Like `MixedIIDWith`, this is a property of the **unconditional** finite path laws only. It says
nothing about the joint law of `(ν, κ, X)`, so it is not a conditional-independence statement, and
the witnesses are not asserted to be unique. The conditional strengthening — conditionally on
`(ν, κ)` the process is a Markov chain with that initial law and that transition matrix — is the
analogue of `ConditionallyIIDWith` and is deliberately not what is defined here.

This is the class in the conclusion of the Diaconis–Freedman representation theorem: a recurrent
Markov exchangeable process is a mixture of Markov chains. This file supplies the class together
with the **easy direction** of that theorem, `MixedMarkovChainWith.markovExchangeable`: every
mixture of Markov chains is Markov exchangeable. The mechanism is the one that makes the initial
state together with the transition counts sufficient for a Markov-chain path mass — the
transition-product factor depends on the path only through its transition counts
(`TauCeti.prod_eq_of_transitionCount_eq`) — applied inside the mixing integral, where it holds
pointwise in the mixing variable.

The class is strictly larger than the mixed i.i.d. one: the deterministic 3-cycle of
`TauCeti/Probability/Exchangeability/ThreeCycle.lean` is a Markov chain, hence a mixture of Markov
chains (`threeCycle_mixedMarkovChain`), but is not exchangeable and so not mixed i.i.d.

## Main definitions

* `TauCeti.Probability.MixedMarkovChainWith`: the mixture identity with named witnesses.
* `TauCeti.Probability.MixedMarkovChain`: its existential wrapper.

## Main results

* `TauCeti.Probability.MixedMarkovChainWith.prefixLaw_singleton_eq_lintegral_prod_pow`: the
  initial state and transition counts of a path are sufficient for its `μ`-mass.
* `TauCeti.Probability.MixedMarkovChainWith.markovExchangeable`: a mixture of Markov chains is
  Markov exchangeable — the easy direction of Diaconis–Freedman.
* `TauCeti.Probability.mixedMarkovChainWith_const_of_prefixLaw_singleton_eq`: a single Markov chain
  is the degenerate mixture.
* `TauCeti.Probability.MixedIIDWith.mixedMarkovChainWith`: a mixed i.i.d. process is a mixture of
  Markov chains with state-independent rows.

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
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **A mixture of Markov chains** with a specified random initial law `ν` and random transition
matrix `κ`: the `μ`-mass of a finite path is the `μ`-average of its Markov-chain path mass
built from `ν ω` and `κ ω`. The countability and measurable-singleton conjuncts restrict this
singleton-mass formulation to discrete state spaces, matching `MarkovExchangeable`, where it is
non-vacuous and determines the finite path laws. Bundled alongside, as in `MarkovExchangeable`, are
the regularity conjuncts the mixture identity is stated against: the process is coordinatewise a.e.
measurable, and both witnesses are measurable (`ν`, and each row `ω ↦ κ ω a`). -/
def MixedMarkovChainWith (μ : Measure Ω) (X : ℕ → Ω → α)
    (ν : Ω → ProbabilityMeasure α) (κ : Ω → α → ProbabilityMeasure α) : Prop :=
  Countable α ∧ MeasurableSingletonClass α ∧ (∀ i, AEMeasurable (X i) μ) ∧
    Measurable ν ∧ (∀ a, Measurable fun ω => κ ω a) ∧
      ∀ (n : ℕ) (w : Fin (n + 1) → α),
        prefixLaw μ X (n + 1) {w} =
          ∫⁻ ω, (ν ω : Measure α) {w 0} *
            ∏ i : Fin n, (κ ω (w i.castSucc) : Measure α) {w i.succ} ∂μ

/-- Constructor from discrete-state instances, coordinatewise a.e. measurability, measurability of
the two witnesses, and the mixture identity for finite paths. -/
theorem MixedMarkovChainWith.intro [Countable α] [MeasurableSingletonClass α]
    {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}
    {κ : Ω → α → ProbabilityMeasure α}
    (hX : ∀ i, AEMeasurable (X i) μ) (hν : Measurable ν) (hκ : ∀ a, Measurable fun ω => κ ω a)
    (h : ∀ (n : ℕ) (w : Fin (n + 1) → α),
      prefixLaw μ X (n + 1) {w} =
        ∫⁻ ω, (ν ω : Measure α) {w 0} *
          ∏ i : Fin n, (κ ω (w i.castSucc) : Measure α) {w i.succ} ∂μ) :
    MixedMarkovChainWith μ X ν κ :=
  ⟨inferInstance, inferInstance, hX, hν, hκ, h⟩

/-- The state space of a mixture of Markov chains is countable. -/
theorem MixedMarkovChainWith.countable {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} {κ : Ω → α → ProbabilityMeasure α}
    (h : MixedMarkovChainWith μ X ν κ) : Countable α :=
  h.1

/-- Singletons in the state space of a mixture of Markov chains are measurable. -/
theorem MixedMarkovChainWith.measurableSingletonClass {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} {κ : Ω → α → ProbabilityMeasure α}
    (h : MixedMarkovChainWith μ X ν κ) : MeasurableSingletonClass α :=
  h.2.1

/-- Every coordinate of a mixture of Markov chains is a.e. measurable. -/
theorem MixedMarkovChainWith.aemeasurable {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} {κ : Ω → α → ProbabilityMeasure α}
    (h : MixedMarkovChainWith μ X ν κ) (i : ℕ) : AEMeasurable (X i) μ :=
  h.2.2.1 i

/-- The random initial law of a mixture of Markov chains is measurable. -/
@[grind →]
theorem MixedMarkovChainWith.measurable_initialLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} {κ : Ω → α → ProbabilityMeasure α}
    (h : MixedMarkovChainWith μ X ν κ) : Measurable ν :=
  h.2.2.2.1

/-- Each row of the random transition matrix of a mixture of Markov chains is measurable. -/
theorem MixedMarkovChainWith.measurable_transitionMatrix {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} {κ : Ω → α → ProbabilityMeasure α}
    (h : MixedMarkovChainWith μ X ν κ) (a : α) : Measurable fun ω => κ ω a :=
  h.2.2.2.2.1 a

/-- The defining mixture identity: the `μ`-mass of a finite path is the `μ`-average of its
Markov-chain path masses. -/
@[grind =>]
theorem MixedMarkovChainWith.prefixLaw_singleton_eq_lintegral {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} {κ : Ω → α → ProbabilityMeasure α}
    (h : MixedMarkovChainWith μ X ν κ) (n : ℕ) (w : Fin (n + 1) → α) :
    prefixLaw μ X (n + 1) {w} =
      ∫⁻ ω, (ν ω : Measure α) {w 0} *
        ∏ i : Fin n, (κ ω (w i.castSucc) : Measure α) {w i.succ} ∂μ :=
  h.2.2.2.2.2 n w

/-- Simp normal form for `MixedMarkovChainWith`. -/
@[simp]
theorem mixedMarkovChainWith_iff [Countable α] [MeasurableSingletonClass α]
    {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}
    {κ : Ω → α → ProbabilityMeasure α} :
    MixedMarkovChainWith μ X ν κ ↔
      (∀ i, AEMeasurable (X i) μ) ∧ Measurable ν ∧ (∀ a, Measurable fun ω => κ ω a) ∧
        ∀ (n : ℕ) (w : Fin (n + 1) → α),
          prefixLaw μ X (n + 1) {w} =
            ∫⁻ ω, (ν ω : Measure α) {w 0} *
              ∏ i : Fin n, (κ ω (w i.castSucc) : Measure α) {w i.succ} ∂μ :=
  ⟨fun h => ⟨h.aemeasurable, h.measurable_initialLaw, h.measurable_transitionMatrix,
      h.prefixLaw_singleton_eq_lintegral⟩,
    fun h => MixedMarkovChainWith.intro h.1 h.2.1 h.2.2.1 h.2.2.2⟩

/-- **A mixture of Markov chains**: existence of a random initial law and a random transition
matrix representing the finite path laws. -/
def MixedMarkovChain (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∃ (ν : Ω → ProbabilityMeasure α) (κ : Ω → α → ProbabilityMeasure α),
    MixedMarkovChainWith μ X ν κ

/-- Constructor from a named pair of witnesses. -/
theorem MixedMarkovChain.of_witnesses {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} {κ : Ω → α → ProbabilityMeasure α}
    (h : MixedMarkovChainWith μ X ν κ) : MixedMarkovChain μ X :=
  ⟨ν, κ, h⟩

/-- A mixture of Markov chains has a random initial law and a random transition matrix. -/
theorem MixedMarkovChain.exists_witnesses {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : MixedMarkovChain μ X) :
    ∃ (ν : Ω → ProbabilityMeasure α) (κ : Ω → α → ProbabilityMeasure α),
      MixedMarkovChainWith μ X ν κ :=
  h

/-- Simp normal form for the existential wrapper `MixedMarkovChain`. -/
@[simp]
theorem mixedMarkovChain_iff {μ : Measure Ω} {X : ℕ → Ω → α} :
    MixedMarkovChain μ X ↔
      ∃ (ν : Ω → ProbabilityMeasure α) (κ : Ω → α → ProbabilityMeasure α),
        MixedMarkovChainWith μ X ν κ :=
  Iff.rfl

/-- The state space of a mixture of Markov chains is countable. -/
theorem MixedMarkovChain.countable {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : MixedMarkovChain μ X) : Countable α := by
  obtain ⟨_, _, h⟩ := h
  exact h.countable

/-- Singletons in the state space of a mixture of Markov chains are measurable. -/
theorem MixedMarkovChain.measurableSingletonClass {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : MixedMarkovChain μ X) : MeasurableSingletonClass α := by
  obtain ⟨_, _, h⟩ := h
  exact h.measurableSingletonClass

/-- Every coordinate of a mixture of Markov chains is a.e. measurable. -/
theorem MixedMarkovChain.aemeasurable {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : MixedMarkovChain μ X) (i : ℕ) : AEMeasurable (X i) μ := by
  obtain ⟨_, _, h⟩ := h
  exact h.aemeasurable i

/-- **The initial state together with the transition counts of a path is sufficient for its
`μ`-mass.** Rewriting the mixture identity through `TauCeti.prod_transitionCount` replaces the
transition-product factor by a product of powers indexed by the transition counts; the index set
`S` only has to contain the letters of the path. -/
theorem MixedMarkovChainWith.prefixLaw_singleton_eq_lintegral_prod_pow {μ : Measure Ω}
    {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α} {κ : Ω → α → ProbabilityMeasure α}
    (h : MixedMarkovChainWith μ X ν κ) {n : ℕ} (w : Fin (n + 1) → α) {S : Finset α}
    (hS : ∀ i, w i ∈ S) :
    prefixLaw μ X (n + 1) {w} =
      ∫⁻ ω, (ν ω : Measure α) {w 0} *
        ∏ ab ∈ S ×ˢ S, (κ ω ab.1 : Measure α) {ab.2} ^ transitionCount w ab.1 ab.2 ∂μ := by
  rw [h.prefixLaw_singleton_eq_lintegral n w]
  refine lintegral_congr fun ω => ?_
  rw [prod_transitionCount w (fun i : Fin n => ⟨hS i.castSucc, hS i.succ⟩)
    fun a b => (κ ω a : Measure α) {b}]

/-- **A mixture of Markov chains is Markov exchangeable.** This is the easy direction of the
Diaconis–Freedman representation theorem. Two paths with a common start and common transition
counts have equal Markov-chain probabilities for *every* value of the mixing variable, because a
product of transition weights depends on the path only through its transition counts; averaging
preserves the equality. -/
theorem MixedMarkovChainWith.markovExchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} {κ : Ω → α → ProbabilityMeasure α}
    (h : MixedMarkovChainWith μ X ν κ) : MarkovExchangeable μ X := by
  have := h.countable
  have := h.measurableSingletonClass
  refine MarkovExchangeable.intro h.aemeasurable ?_
  intro n u v h0 hcount
  rw [h.prefixLaw_singleton_eq_lintegral n u, h.prefixLaw_singleton_eq_lintegral n v]
  refine lintegral_congr fun ω => ?_
  rw [h0, prod_eq_of_transitionCount_eq hcount fun a b => (κ ω a : Measure α) {b}]

/-- **A mixture of Markov chains is Markov exchangeable**, existential form. -/
theorem MixedMarkovChain.markovExchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : MixedMarkovChain μ X) : MarkovExchangeable μ X := by
  obtain ⟨_, _, h⟩ := h
  exact h.markovExchangeable

/-- **A Markov chain is the degenerate mixture of Markov chains.** The hypothesis is the defining
product form of the finite-dimensional laws of a Markov chain with initial law `p₀` and transition
matrix `p`; the witnesses are the constant random objects. -/
theorem mixedMarkovChainWith_const_of_prefixLaw_singleton_eq
    [Countable α] [MeasurableSingletonClass α]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (p₀ : ProbabilityMeasure α) (p : α → ProbabilityMeasure α)
    (h : ∀ (n : ℕ) (w : Fin (n + 1) → α),
      prefixLaw μ X (n + 1) {w} =
        (p₀ : Measure α) {w 0} * ∏ i : Fin n, (p (w i.castSucc) : Measure α) {w i.succ}) :
    MixedMarkovChainWith μ X (fun _ => p₀) fun _ => p :=
  MixedMarkovChainWith.intro hX measurable_const (fun _ => measurable_const) fun n w => by
    rw [h n w, lintegral_const, measure_univ, mul_one]

/-- **A mixed i.i.d. process is a mixture of Markov chains** whose rows do not depend on the
current state: drawing the next coordinate from the mixing representative, whatever the present
one, reproduces the mixed i.i.d. finite-dimensional laws. Thus this places `MixedIID` below
`MixedMarkovChain` in the symmetry lattice, refining `Exchangeable.markovExchangeable` at the
level of the representations. -/
theorem MixedIIDWith.mixedMarkovChainWith [Countable α] [MeasurableSingletonClass α]
    {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}
    (h : MixedIIDWith μ X ν) : MixedMarkovChainWith μ X ν fun ω _ => ν ω := by
  -- The mixture identity already forces coordinatewise a.e. measurability, by the argument of
  -- `MixedIIDWith.aemeasurable_of_const`: a one-coordinate block law is a mixture of probability
  -- measures, hence carries the total mass of `μ`, whereas `Measure.map` along a
  -- non-a.e.-measurable function is `0`.
  have hX : ∀ i, AEMeasurable (X i) μ := by
    rcases eq_or_ne μ 0 with rfl | hμ
    · exact fun _ => aemeasurable_zero_measure
    intro i
    have hblock := h.blockLaw_eq_mixture (fun _ : Fin 1 => i) fun a b _ => Subsingleton.elim a b
    rw [blockLaw_def] at hblock
    have hmass : (μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin 1 => ν ω).toMeasure)
        Set.univ = μ Set.univ := by
      rw [Measure.bind_apply MeasurableSet.univ
        (TauCeti.MeasureTheory.aemeasurable_probabilityMeasure_pi_const_toMeasure ν
          h.measurable_mixingRepresentative.aemeasurable)]
      simp
    have hne : (μ.map fun ω (_ : Fin 1) => X i ω) ≠ 0 := by
      rw [hblock]
      intro hzero
      rw [hzero] at hmass
      exact Measure.measure_univ_ne_zero.2 hμ hmass.symm
    exact (measurable_pi_apply 0).comp_aemeasurable (AEMeasurable.of_map_ne_zero hne)
  refine MixedMarkovChainWith.intro hX h.measurable_mixingRepresentative
    (fun _ => h.measurable_mixingRepresentative) fun n w => ?_
  rw [prefixLaw_def, ← Set.univ_pi_singleton w,
    h.blockLaw_univ_pi (fun i : Fin (n + 1) => i.val) Fin.val_injective (fun i => {w i})
      fun i => measurableSet_singleton (w i)]
  exact lintegral_congr fun ω => Fin.prod_univ_succ fun i => (ν ω : Measure α) {w i}

/-- **A mixed i.i.d. process is a mixture of Markov chains**, existential form. -/
theorem MixedIID.mixedMarkovChain [Countable α] [MeasurableSingletonClass α]
    {μ : Measure Ω} {X : ℕ → Ω → α} (h : MixedIID μ X) : MixedMarkovChain μ X := by
  obtain ⟨ν, hν⟩ := h.exists_mixingRepresentative
  exact MixedMarkovChain.of_witnesses hν.mixedMarkovChainWith

end Probability

end TauCeti

end

end
