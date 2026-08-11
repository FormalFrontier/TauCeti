/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.Contractability
public import TauCeti.Probability.Exchangeability.PathSpace.Shift
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Probability.UniformOn
public import Mathlib.Data.ZMod.Basic

/-!
# A stationary process that is not exchangeable: the deterministic 3-cycle

This file discharges a worked example of the Exchangeability roadmap
(`TauCetiRoadmap/Exchangeability/README.md`, "Worked examples"):

> A stationary non-reversible finite-state Markov chain — for instance the deterministic
> 3-cycle with uniform stationary law — is shift-invariant but not exchangeable, since the law
> of `(X₀, X₁)` differs from that of `(X₁, X₀)`. This keeps stationarity, shift-invariance, and
> exchangeability distinct.

Take the base space `Ω = ZMod 3` with its uniform probability law `threeCycleMeasure =
ProbabilityTheory.uniformOn Set.univ`, and the deterministic rotation process `threeCycle n ω =
ω + n`. Starting from a uniform state and stepping by the 3-cycle, the process is stationary:
its path law is invariant under the one-sided shift
(`threeCycle_measurePreserving_shift`), because shifting the sample path of `ω` gives the sample
path of `ω + 1`, and the uniform law is translation invariant.

It is, however, neither exchangeable (`threeCycle_not_exchangeable`) nor contractable
(`threeCycle_not_contractable`): the pair `(X₀, X₁) = (ω, ω + 1)` lands in
`{(0, 1), (1, 2), (2, 0)}`, so swapping the two coordinates — or reading off the pair `(X₀, X₂)`
instead — produces a different two-dimensional law. This separates stationarity and
shift-invariance from the symmetry notions, as the roadmap example asks.

The example uses only the Layer 0 API (`Exchangeable`, `Contractable`, `pathLaw`, `blockLaw`,
`shift`) together with Mathlib's translation invariance of the counting measure on a group
(`MeasureTheory.map_add_right_eq_self`); it needs no material from
`cameronfreer/exchangeability`.
-/

public section

noncomputable section

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

/-- The deterministic 3-cycle process on `ZMod 3`: from state `ω`, the `n`-th coordinate is the
`n`-fold rotation `ω + n`. -/
abbrev threeCycle : ℕ → ZMod 3 → ZMod 3 := fun n ω => ω + (n : ZMod 3)

@[simp]
theorem threeCycle_apply (n : ℕ) (ω : ZMod 3) : threeCycle n ω = ω + (n : ZMod 3) :=
  rfl

/-- The uniform probability law on `ZMod 3`, the stationary law of the 3-cycle. This is a `def`
(not an `abbrev`) so that the `IsAddRightInvariant` instance below keys on `threeCycleMeasure`
and stays scoped to this example, rather than leaking to the general `uniformOn Set.univ`. -/
@[expose] def threeCycleMeasure : Measure (ZMod 3) := uniformOn Set.univ

/-- The stationary measure of the 3-cycle is the uniform law on `ZMod 3`. -/
@[simp]
theorem threeCycleMeasure_def : threeCycleMeasure = uniformOn Set.univ :=
  rfl

/-- The uniform law on `ZMod 3` is invariant under right addition, supplying the translation
invariance used in the shift-stationarity proof. -/
instance : threeCycleMeasure.IsAddRightInvariant := by
  have h : (uniformOn (Set.univ : Set (ZMod 3))) = (3 : ℝ≥0∞)⁻¹ • Measure.count := by
    ext s
    rw [uniformOn_univ, Measure.smul_apply, smul_eq_mul]
    rw [ENNReal.div_eq_inv_mul]
    simp [ZMod.card]
  unfold threeCycleMeasure
  rw [h]
  infer_instance

/-- The uniform law gives mass `3⁻¹` to each singleton. -/
theorem threeCycleMeasure_singleton (a : ZMod 3) : threeCycleMeasure {a} = 3⁻¹ := by
  unfold threeCycleMeasure
  rw [uniformOn_univ]
  simp [ZMod.card]

/-- **The 3-cycle is stationary.** Its path law is preserved by the one-sided shift: shifting the
sample path of `ω` yields the sample path of `ω + 1`, and the uniform law is translation
invariant. -/
theorem threeCycle_measurePreserving_shift :
    MeasurePreserving (shift (ZMod 3)) (pathLaw threeCycleMeasure threeCycle)
      (pathLaw threeCycleMeasure threeCycle) := by
  refine ⟨measurable_shift, ?_⟩
  have hP : Measurable (fun ω : ZMod 3 => fun i => threeCycle i ω) := Measurable.of_discrete
  have hT : Measurable (fun ω : ZMod 3 => ω + 1) := Measurable.of_discrete
  have hcomp : (fun ω : ZMod 3 => fun k => threeCycle (k + 1) ω)
      = (fun ω : ZMod 3 => fun i => threeCycle i ω) ∘ (fun ω : ZMod 3 => ω + 1) := by
    funext ω n
    simp only [Function.comp_apply, threeCycle_apply]
    push_cast
    ring
  -- Expose the one-step shift as the first iterate expected by `map_shift_iterate_pathLaw`.
  change (pathLaw threeCycleMeasure threeCycle).map ((shift (ZMod 3))^[1]) =
    pathLaw threeCycleMeasure threeCycle
  rw [map_shift_iterate_pathLaw threeCycleMeasure (fun _ => Measurable.of_discrete.aemeasurable) 1,
    pathLaw_def, hcomp, ← Measure.map_map hP hT,
    map_add_right_eq_self threeCycleMeasure 1, ← pathLaw_def]

/-- The straight two-coordinate event `{X₀ = 0, X₁ = 1}` is realized only from the start state
`0`. -/
private theorem threeCycle_straight_event :
    {ω : ZMod 3 | ∀ i : Fin 2, threeCycle (i.val) ω ∈ (![{0}, {1}] : Fin 2 → Set (ZMod 3)) i}
      = {0} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Set.mem_singleton_iff]
  revert ω
  decide

/-- The spread event `{X₀ = 0, X₂ = 1}` is unrealizable: it would need `ω = 0` and `ω + 2 = 1`
simultaneously. -/
private theorem threeCycle_spread_event :
    {ω : ZMod 3 | ∀ i : Fin 2,
        threeCycle ((![0, 2] : Fin 2 → ℕ) i) ω ∈
          (![{0}, {1}] : Fin 2 → Set (ZMod 3)) i} = ∅ := by
  ext ω
  simp only [Set.mem_ofPred_eq, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Set.mem_singleton_iff, Set.mem_empty_iff_false]
  revert ω
  decide

/-- **The 3-cycle is not contractable.** The pair law `(X₀, X₂)` along the strictly increasing
selection `0 < 2` differs from the prefix pair law `(X₀, X₁)`: on the rectangle `{X₀ = 0, X₁ = 1}`
the prefix law has mass `3⁻¹` while the spread law has mass `0`. -/
theorem threeCycle_not_contractable : ¬ Contractable threeCycleMeasure threeCycle := by
  intro hC
  have h := hC.map_pair (i := 0) (j := 2) (by norm_num)
  rw [prefixLaw_def] at h
  have hval := congrArg (fun m : Measure (Fin 2 → ZMod 3) => m (Set.univ.pi ![{0}, {1}])) h
  rw [blockLaw_apply_rectangle threeCycleMeasure threeCycle (![0, 2] : Fin 2 → ℕ)
        (fun _ => Measurable.of_discrete.aemeasurable) _ (fun _ => MeasurableSet.of_discrete),
      blockLaw_apply_rectangle threeCycleMeasure threeCycle (fun i : Fin 2 => (i : ℕ))
        (fun _ => Measurable.of_discrete.aemeasurable) _ (fun _ => MeasurableSet.of_discrete)]
    at hval
  rw [threeCycle_spread_event, threeCycle_straight_event, measure_empty,
    threeCycleMeasure_singleton] at hval
  exact (ENNReal.inv_ne_zero.mpr (by norm_num)) hval.symm

/-- **The 3-cycle is not exchangeable.** Its two-coordinate prefix law already fails the finite
exchangeability symmetry: the pair `(X₀, X₁) = (ω, ω + 1)` ranges over
`{(0, 1), (1, 2), (2, 0)}`, so the law of `(X₀, X₁)` differs from that of `(X₁, X₀)`. -/
theorem threeCycle_not_exchangeable : ¬ Exchangeable threeCycleMeasure threeCycle := by
  intro hE
  exact threeCycle_not_contractable (hE.contractable (fun _ => Measurable.of_discrete.aemeasurable))

end Probability

end TauCeti
