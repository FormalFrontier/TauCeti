/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.Contractability
public import TauCeti.Probability.Exchangeability.PathSpace.ProcessShift

/-!
# Exchangeable laws are stationary

This file records the Layer 0 stationarity bridge from the Exchangeability roadmap: a finitely
exchangeable process has a shift-invariant path law.  The existing implication
`Exchangeable.contractable` gives the exchangeability-to-contractability bridge.  The lemmas here
first expose the shift-stationarity consequences at the natural `Contractable` level, then provide
thin `Exchangeable`-named wrappers for downstream code that starts from exchangeability.

The bridge is stated for the one-sided shift and its iterates.  The final `processShift` form
packages the same invariance at the process-law level.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Every iterate of the one-sided shift preserves the path law of a contractable process. -/
theorem Contractable.measurePreserving_shift_iterate {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Contractable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (n : ℕ) :
    MeasurePreserving ((shift α)^[n]) (pathLaw μ X) (pathLaw μ X) :=
  (hX.measurePreserving_shift hX_meas).iterate n

/-- Iterating the one-sided shift leaves the path law of a contractable process unchanged. -/
theorem Contractable.map_shift_iterate_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Contractable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (n : ℕ) :
    (pathLaw μ X).map ((shift α)^[n]) = pathLaw μ X :=
  (hX.measurePreserving_shift_iterate hX_meas n).map_eq

/-- Setwise stationarity for every shift iterate of a contractable process. -/
theorem Contractable.pathLaw_preimage_shift_iterate {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Contractable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (n : ℕ) {s : Set (ℕ → α)} (hs : NullMeasurableSet s (pathLaw μ X)) :
    pathLaw μ X (((shift α)^[n]) ⁻¹' s) = pathLaw μ X s :=
  (hX.measurePreserving_shift_iterate hX_meas n).measure_preimage hs

/-- The law of the `n`-step shifted process of a contractable process is the original path law. -/
theorem Contractable.map_processShift_eq_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Contractable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (n : ℕ) :
    μ.map (processShift X n) = pathLaw μ X := by
  rw [map_processShift μ hX_meas n, hX.map_shift_iterate_pathLaw hX_meas n]

/-- Prefix laws are unchanged after shifting a contractable process by any finite amount. -/
theorem Contractable.map_prefixProj_shift_iterate_pathLaw_eq_prefixLaw {μ : Measure Ω}
    {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_meas : ∀ i, AEMeasurable (X i) μ) (n m : ℕ) :
    ((pathLaw μ X).map ((shift α)^[n])).map (prefixProj α m) = prefixLaw μ X m := by
  rw [map_prefixProj_shift_iterate_pathLaw μ hX_meas n m]
  exact hX m (fun i : Fin m => i.val + n) (fun _ _ h => Nat.add_lt_add_right h n)

/-- **An exchangeable process has a shift-invariant path law.** -/
theorem Exchangeable.measurePreserving_shift {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    MeasurePreserving (shift α) (pathLaw μ X) (pathLaw μ X) :=
  (hX.contractable hX_meas).measurePreserving_shift hX_meas

/-- Every iterate of the one-sided shift preserves the path law of an exchangeable process. -/
theorem Exchangeable.measurePreserving_shift_iterate {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (n : ℕ) :
    MeasurePreserving ((shift α)^[n]) (pathLaw μ X) (pathLaw μ X) :=
  (hX.contractable hX_meas).measurePreserving_shift_iterate hX_meas n

/-- Iterating the one-sided shift leaves the path law of an exchangeable process unchanged. -/
theorem Exchangeable.map_shift_iterate_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (n : ℕ) :
    (pathLaw μ X).map ((shift α)^[n]) = pathLaw μ X :=
  (hX.contractable hX_meas).map_shift_iterate_pathLaw hX_meas n

/-- Setwise stationarity for every shift iterate. -/
theorem Exchangeable.pathLaw_preimage_shift_iterate {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (n : ℕ) {s : Set (ℕ → α)} (hs : NullMeasurableSet s (pathLaw μ X)) :
    pathLaw μ X (((shift α)^[n]) ⁻¹' s) = pathLaw μ X s :=
  (hX.contractable hX_meas).pathLaw_preimage_shift_iterate hX_meas n hs

/-- The law of the `n`-step shifted process of an exchangeable process is the original path law. -/
theorem Exchangeable.map_processShift_eq_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (n : ℕ) :
    μ.map (processShift X n) = pathLaw μ X :=
  (hX.contractable hX_meas).map_processShift_eq_pathLaw hX_meas n

/-- Prefix laws are unchanged after shifting an exchangeable process by any finite amount. -/
theorem Exchangeable.map_prefixProj_shift_iterate_pathLaw_eq_prefixLaw {μ : Measure Ω}
    {X : ℕ → Ω → α} (hX : Exchangeable μ X)
    (hX_meas : ∀ i, AEMeasurable (X i) μ) (n m : ℕ) :
    ((pathLaw μ X).map ((shift α)^[n])).map (prefixProj α m) = prefixLaw μ X m :=
  (hX.contractable hX_meas).map_prefixProj_shift_iterate_pathLaw_eq_prefixLaw hX_meas n m

end Probability

end TauCeti
