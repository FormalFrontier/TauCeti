/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.Basic

/-!
# Path-space reindexing and iterates of the one-sided shift

This file records the elementary path-space API for iterating the one-sided shift
`TauCeti.Probability.shift`.  The Layer 2 exchangeability roadmap uses these lemmas before
building shift-invariant sigma algebras and before comparing finite-dimensional path laws after
discarding an initial block.

The shift-specialized statements reuse the general time-reindexing path-law lemmas
(`measurable_reindex`, `map_reindex_pathLaw`, `map_reindex_prefixProj_pathLaw`) from
`TauCeti.Probability.Exchangeability.Basic`. The implementation is only a Tau Ceti adapter around
the existing path-space definitions and Mathlib's generic `Measurable.iterate`; no Mathlib
infrastructure is vendored.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

omit [MeasurableSpace α] in
/-- Iterating the one-sided shift by `n` drops the first `n` coordinates. -/
@[simp]
theorem shift_iterate_apply (n k : ℕ) (x : ℕ → α) :
    (shift α)^[n] x k = x (k + n) := by
  induction n generalizing k x with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      simpa [shift_apply, Nat.add_assoc] using ih k (shift α x)

omit [MeasurableSpace α] in
/-- The `n`th shift iterate is the coordinate reindexing `k ↦ k + n`. -/
theorem shift_iterate_eq_reindex (n : ℕ) :
    (shift α)^[n] = fun x : ℕ → α => fun k => x (k + n) := by
  funext x k
  simp

/-- Every iterate of the one-sided path-space shift is measurable. -/
theorem measurable_shift_iterate (n : ℕ) : Measurable ((shift α)^[n]) :=
  measurable_shift.iterate n

/-- Every iterate of the one-sided path-space shift is a.e.-measurable with respect to any
measure on path space. -/
theorem aemeasurable_shift_iterate (n : ℕ) (μ : Measure (ℕ → α)) :
    AEMeasurable ((shift α)^[n]) μ :=
  (measurable_shift_iterate n).aemeasurable

omit [MeasurableSpace α] in
/-- A finite prefix after `n` shifts is the block of coordinates `n, …, n + m - 1`. -/
@[simp]
theorem prefixProj_shift_iterate (n m : ℕ) (x : ℕ → α) :
    prefixProj α m ((shift α)^[n] x) = fun i : Fin m => x (i.val + n) := by
  funext i
  simp [prefixProj_apply]

/-- The prefix projection after an `n`-fold shift is measurable. -/
theorem measurable_prefixProj_shift_iterate (n m : ℕ) :
    Measurable (fun x : ℕ → α => prefixProj α m ((shift α)^[n] x)) :=
  (measurable_prefixProj m).comp (measurable_shift_iterate n)

/-- Shifting the path law by `n` gives the path law of the reindexed process
`k ↦ X (k + n)`. -/
theorem map_shift_iterate_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (n : ℕ) :
    (pathLaw μ X).map ((shift α)^[n]) = pathLaw μ (fun k ω => X (k + n) ω) := by
  rw [shift_iterate_eq_reindex n]
  exact map_reindex_pathLaw μ hX (fun k => k + n)

/-- The first `m` coordinates of the path law after `n` shifts are the block law along
`i ↦ i + n`. -/
theorem map_prefixProj_shift_iterate_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (n m : ℕ) :
    ((pathLaw μ X).map ((shift α)^[n])).map (prefixProj α m) =
      blockLaw μ X (fun i : Fin m => i.val + n) := by
  rw [shift_iterate_eq_reindex n]
  exact map_reindex_prefixProj_pathLaw μ hX (fun k => k + n) m

/-- The setwise form of `map_prefixProj_shift_iterate_pathLaw`. -/
theorem map_prefixProj_shift_iterate_pathLaw_apply (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (n m : ℕ) (s : Set (Fin m → α)) :
    ((pathLaw μ X).map ((shift α)^[n])).map (prefixProj α m) s =
      blockLaw μ X (fun i : Fin m => i.val + n) s := by
  rw [map_prefixProj_shift_iterate_pathLaw μ hX n m]

end Probability

end TauCeti
