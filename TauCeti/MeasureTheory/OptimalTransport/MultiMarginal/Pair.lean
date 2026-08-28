/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Coupling
public import TauCeti.MeasureTheory.OptimalTransport.MultiMarginal.Basic

/-!
# Pair projections of multi-marginal couplings

This file connects the finite multi-marginal coupling API with the two-marginal coupling API.
A multi-marginal coupling can be projected to any ordered pair of coordinates. Conversely, a
coupling indexed by `Fin 2` is precisely a two-marginal coupling, transported along
`MeasurableEquiv.piFinTwo`.

This supplies the reduction to the two-marginal API in Layer 0, item 5 of the optimal-transport
roadmap.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

universe u v

namespace Measure.IsMultiCoupling

variable {ι : Type u} {X : ι → Type v} [∀ i, MeasurableSpace (X i)]
  {π : Measure (∀ i, X i)} {μ : ∀ i, Measure (X i)}

/-- The joint law of any two coordinates of a multi-marginal coupling is a coupling of the
corresponding two marginals. -/
theorem isCoupling_map_pair (hπ : IsMultiCoupling π μ) (i j : ι) :
    IsCoupling (π.map fun x ↦ (x i, x j)) (μ i) (μ j) :=
  ⟨hπ.fst_map_pair i j, hπ.snd_map_pair i j⟩

end Measure.IsMultiCoupling

namespace IsCoupling

variable {X : Fin 2 → Type v} [∀ i, MeasurableSpace (X i)]
  {π : Measure (X 0 × X 1)} {μ : ∀ i, Measure (X i)}

/-- A coupling of the two coordinates gives a raw `Fin 2`-indexed multi-marginal coupling after
pulling it back along the measurable equivalence between a dependent product and a pair. -/
theorem isMultiCoupling_piFinTwo (hπ : IsCoupling π (μ 0) (μ 1)) :
    Measure.IsMultiCoupling (π.map (MeasurableEquiv.piFinTwo X).symm) μ := by
  constructor
  intro i
  fin_cases i
  · calc
      (π.map (MeasurableEquiv.piFinTwo X).symm).map (Function.eval 0) =
          π.map (Function.eval 0 ∘ (MeasurableEquiv.piFinTwo X).symm) :=
        Measure.map_map (measurable_pi_apply 0) (MeasurableEquiv.piFinTwo X).symm.measurable
      _ = π.map Prod.fst := by rfl
      _ = μ 0 := hπ.fst_eq
  · calc
      (π.map (MeasurableEquiv.piFinTwo X).symm).map (Function.eval 1) =
          π.map (Function.eval 1 ∘ (MeasurableEquiv.piFinTwo X).symm) :=
        Measure.map_map (measurable_pi_apply 1) (MeasurableEquiv.piFinTwo X).symm.measurable
      _ = π.map Prod.snd := by rfl
      _ = μ 1 := hπ.snd_eq

/-- Pulling a measure back along `MeasurableEquiv.piFinTwo` is a multi-marginal coupling exactly
when the original measure is a two-marginal coupling. -/
@[simp]
theorem isMultiCoupling_piFinTwo_iff :
    Measure.IsMultiCoupling
        (π.map (fun p ↦ Fin.cons p.1 (Fin.cons p.2 finZeroElim))) μ ↔
      IsCoupling π (μ 0) (μ 1) := by
  constructor
  · intro hπ'
    have hπ'' : Measure.IsMultiCoupling (π.map (MeasurableEquiv.piFinTwo X).symm) μ := by
      simpa only [MeasurableEquiv.piFinTwo_symm_apply] using hπ'
    have hpair := hπ''.isCoupling_map_pair 0 1
    have hmap :
        (π.map (MeasurableEquiv.piFinTwo X).symm).map (fun x ↦ (x 0, x 1)) = π := by
      rw [Measure.map_map (measurable_pi_apply 0 |>.prodMk (measurable_pi_apply 1))
        (MeasurableEquiv.piFinTwo X).symm.measurable]
      have hcomp :
          (fun x : (∀ i, X i) ↦ (x 0, x 1)) ∘ (MeasurableEquiv.piFinTwo X).symm = id := by
        funext x
        exact (MeasurableEquiv.piFinTwo X).apply_symm_apply x
      rw [hcomp, Measure.map_id]
    rw [hmap] at hpair
    exact hpair
  · intro hπ
    simpa only [MeasurableEquiv.piFinTwo_symm_apply] using hπ.isMultiCoupling_piFinTwo

end IsCoupling

namespace MultiCoupling

variable {ι : Type u} {X : ι → Type v} [∀ i, MeasurableSpace (X i)]
  {μ : ∀ i, ProbabilityMeasure (X i)}

/-- The pair projection of a bundled multi-marginal coupling, regarded as a bundled coupling. -/
def projectPairCoupling (π : MultiCoupling μ) (i j : ι) : Coupling (μ i) (μ j) :=
  ⟨π.projectPair i j, by
    rw [π.coe_projectPair]
    exact π.2.isCoupling_map_pair i j⟩

/-- The probability measure underlying `projectPairCoupling` is the pair projection. -/
@[simp]
theorem coe_projectPairCoupling (π : MultiCoupling μ) (i j : ι) :
    (π.projectPairCoupling i j : ProbabilityMeasure (X i × X j)) = π.projectPair i j :=
  (rfl)

variable {X : Fin 2 → Type v} [∀ i, MeasurableSpace (X i)]
  {μ : ∀ i, ProbabilityMeasure (X i)}

/-- A multi-marginal coupling indexed by `Fin 2`, viewed as its two-coordinate coupling. -/
def toCouplingFinTwo (π : MultiCoupling μ) : Coupling (μ 0) (μ 1) :=
  π.projectPairCoupling 0 1

/-- The probability measure underlying `toCouplingFinTwo` is the pair projection. -/
@[simp]
theorem coe_toCouplingFinTwo (π : MultiCoupling μ) :
    (π.toCouplingFinTwo : ProbabilityMeasure (X 0 × X 1)) = π.projectPair 0 1 :=
  by
    exact π.coe_projectPairCoupling 0 1

end MultiCoupling

namespace Coupling

variable {X : Fin 2 → Type v} [∀ i, MeasurableSpace (X i)]
  {μ : ∀ i, ProbabilityMeasure (X i)}

/-- A two-marginal coupling, viewed as a `Fin 2`-indexed multi-marginal coupling. -/
def toMultiCouplingFinTwo (π : Coupling (μ 0) (μ 1)) : MultiCoupling μ :=
  ⟨π.1.map (MeasurableEquiv.piFinTwo X).symm.measurable.aemeasurable,
    π.2.isMultiCoupling_piFinTwo⟩

/-- The measure underlying `toMultiCouplingFinTwo` is the pushforward along the inverse of the
explicit measurable equivalence between a `Fin 2` product and an ordinary product. -/
@[simp]
theorem coe_toMultiCouplingFinTwo (π : Coupling (μ 0) (μ 1)) :
    (π.toMultiCouplingFinTwo : ProbabilityMeasure (∀ i, X i)) =
      π.1.map (MeasurableEquiv.piFinTwo X).symm.measurable.aemeasurable :=
  (rfl)

end Coupling

variable {X : Fin 2 → Type v} [∀ i, MeasurableSpace (X i)]
  {μ : ∀ i, ProbabilityMeasure (X i)}

/-- Converting a two-marginal coupling to a `Fin 2` multi-marginal coupling and back is the
identity. -/
@[simp]
theorem Coupling.toCouplingFinTwo_toMultiCouplingFinTwo (π : Coupling (μ 0) (μ 1)) :
    π.toMultiCouplingFinTwo.toCouplingFinTwo = π := by
  apply Coupling.ext
  calc
    (π.toMultiCouplingFinTwo.toCouplingFinTwo.1).toMeasure =
        (π.toMultiCouplingFinTwo.projectPair 0 1).toMeasure :=
      congrArg ProbabilityMeasure.toMeasure
        (MultiCoupling.coe_toCouplingFinTwo π.toMultiCouplingFinTwo)
    _ = π.toMultiCouplingFinTwo.1.toMeasure.map (fun x ↦ (x 0, x 1)) :=
      π.toMultiCouplingFinTwo.coe_projectPair 0 1
    _ = (π.1.toMeasure.map (MeasurableEquiv.piFinTwo X).symm).map
        (MeasurableEquiv.piFinTwo X) := by
      rw [congrArg ProbabilityMeasure.toMeasure (Coupling.coe_toMultiCouplingFinTwo π)]
      rfl
    _ = π.1.toMeasure.map ((MeasurableEquiv.piFinTwo X) ∘
        (MeasurableEquiv.piFinTwo X).symm) :=
      Measure.map_map (MeasurableEquiv.piFinTwo X).measurable
        (MeasurableEquiv.piFinTwo X).symm.measurable
    _ = π.1.toMeasure := by
      have h_comp : (MeasurableEquiv.piFinTwo X) ∘ (MeasurableEquiv.piFinTwo X).symm = id := by
        funext x
        exact (MeasurableEquiv.piFinTwo X).apply_symm_apply x
      rw [h_comp, Measure.map_id]

/-- Converting a `Fin 2` multi-marginal coupling to a two-marginal coupling and back is the
identity. -/
@[simp]
theorem MultiCoupling.toMultiCouplingFinTwo_toCouplingFinTwo (π : MultiCoupling μ) :
    π.toCouplingFinTwo.toMultiCouplingFinTwo = π := by
  apply MultiCoupling.ext
  calc
    (π.toCouplingFinTwo.toMultiCouplingFinTwo.1).toMeasure =
        π.toCouplingFinTwo.1.toMeasure.map (MeasurableEquiv.piFinTwo X).symm := by
      simpa only [ProbabilityMeasure.toMeasure_map] using
        congrArg ProbabilityMeasure.toMeasure
          (Coupling.coe_toMultiCouplingFinTwo π.toCouplingFinTwo)
    _ = (π.projectPair 0 1).toMeasure.map (MeasurableEquiv.piFinTwo X).symm := by
      rw [← congrArg ProbabilityMeasure.toMeasure (MultiCoupling.coe_toCouplingFinTwo π)]
    _ = (π.1.toMeasure.map (MeasurableEquiv.piFinTwo X)).map
        (MeasurableEquiv.piFinTwo X).symm := by
      rw [π.coe_projectPair]
      rfl
    _ = π.1.toMeasure.map ((MeasurableEquiv.piFinTwo X).symm ∘
        (MeasurableEquiv.piFinTwo X)) :=
      Measure.map_map (MeasurableEquiv.piFinTwo X).symm.measurable
        (MeasurableEquiv.piFinTwo X).measurable
    _ = π.1.toMeasure := by
      have h_comp : (MeasurableEquiv.piFinTwo X).symm ∘ MeasurableEquiv.piFinTwo X = id := by
        funext x
        exact (MeasurableEquiv.piFinTwo X).symm_apply_apply x
      rw [h_comp, Measure.map_id]

/-- The equivalence between two-marginal couplings and multi-marginal couplings indexed by
`Fin 2`. -/
def couplingEquivMultiCouplingFinTwo : Coupling (μ 0) (μ 1) ≃ MultiCoupling μ where
  toFun := Coupling.toMultiCouplingFinTwo
  invFun := MultiCoupling.toCouplingFinTwo
  left_inv := Coupling.toCouplingFinTwo_toMultiCouplingFinTwo
  right_inv := MultiCoupling.toMultiCouplingFinTwo_toCouplingFinTwo

/-- Applying the coupling equivalence to a two-marginal coupling gives its corresponding
`Fin 2`-indexed multi-marginal coupling. -/
@[simp]
theorem couplingEquivMultiCouplingFinTwo_apply (π : Coupling (μ 0) (μ 1)) :
    couplingEquivMultiCouplingFinTwo π = π.toMultiCouplingFinTwo := by
  unfold couplingEquivMultiCouplingFinTwo
  rfl

/-- Applying the inverse coupling equivalence to a `Fin 2`-indexed multi-marginal coupling gives
its corresponding two-marginal coupling. -/
@[simp]
theorem couplingEquivMultiCouplingFinTwo_symm_apply (π : MultiCoupling μ) :
    couplingEquivMultiCouplingFinTwo.symm π = π.toCouplingFinTwo := by
  unfold couplingEquivMultiCouplingFinTwo
  rfl

end TauCeti
