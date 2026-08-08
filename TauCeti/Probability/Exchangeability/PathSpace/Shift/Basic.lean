/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.Basic
import Mathlib.Dynamics.FixedPoints.Basic

/-!
# Path-space reindexing and iterates of the one-sided shift

This file records the elementary path-space API for iterating the one-sided shift
`TauCeti.Probability.shift`.  The Layer 2 exchangeability roadmap uses these lemmas before
building shift-invariant sigma algebras and before comparing finite-dimensional path laws after
discarding an initial block.

It also records how *shift-fixed sets* behave under time reindexing:
`preimage_reindex_eq_of_preimage_shift_eq_of_eventually_add` shows that a reindexing which is
eventually a translation `n ↦ n + C` leaves every set with `shift α ⁻¹' A = A` unchanged, because
beyond the altered prefix the reindexing agrees with a fixed shift iterate. That is a purely
set-theoretic statement — it assumes no measurability — and it is what lets a block argument move
an invariant event through a reindexing; the complementary fact, that a contractable law is
preserved by such a reindexing, needs strict monotonicity and lives with `ContractableLaw`.

The shift-specialized statements reuse the general time-reindexing path-law lemmas
(`measurable_reindex`, `map_reindex_pathLaw`, `map_reindex_prefixProj_pathLaw`) from
`TauCeti.Probability.Exchangeability.Basic`. Apart from the reindexing identity above, which is
proved from Mathlib's `Function.IsFixedPt.preimage_iterate`, the implementation is a Tau Ceti
adapter around the existing path-space definitions and Mathlib's generic `Measurable.iterate`; no
Mathlib infrastructure is vendored.
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

omit [MeasurableSpace α] in
/-- **Shift-fixed sets are fixed by an eventually-translating reindexing.** If `φ` is eventually
`n ↦ n + C`, then reindexing by `φ` leaves unchanged every set `A` exactly fixed by the shift,
`shift α ⁻¹' A = A`. No measurability is assumed — this is a set-theoretic identity, and the
`MeasurableSpace.invariants` formulation is the corollary
`preimage_reindex_eq_of_measurableSet_invariants_of_eventually_add`.

Beyond the first `m` coordinates the reindexing agrees with `(shift α)^[C]`, so the identity
`(shift α)^[m] (reindex φ x) = (shift α)^[m + C] x` holds, and exact shift invariance of `A` under
both iterates transfers membership.

Strict monotonicity of `φ` is **not** needed for this set identity; it enters separately, when
`ContractableLaw.measurePreserving_reindex` turns the reindexing into a measure-preserving map. The
two facts are the pair of inputs the Koopman block factorization needs.

The eventual-translation hypothesis is exactly the conclusion recorded by
`exists_strictMono_nat_extending_fin_eventually_add`, whose docstring describes this argument as its
intended use; this theorem is the consumer of that clause. -/
theorem preimage_reindex_eq_of_preimage_shift_eq_of_eventually_add {m C : ℕ} {φ : ℕ → ℕ}
    {A : Set (ℕ → α)} (hshift : shift α ⁻¹' A = A)
    (hφ : ∀ n, m ≤ n → φ n = n + C) :
    (fun x : ℕ → α => fun k => x (φ k)) ⁻¹' A = A := by
  have hkey : ∀ x : ℕ → α,
      (shift α)^[m] (fun k => x (φ k)) = (shift α)^[m + C] x := by
    intro x
    funext n
    rw [shift_iterate_apply, shift_iterate_apply, hφ (n + m) (Nat.le_add_left m n)]
    congr 1
    omega
  ext x
  constructor
  · intro hx
    have h1 : (shift α)^[m] (fun k => x (φ k)) ∈ A := by
      rw [← Set.mem_preimage, Function.IsFixedPt.preimage_iterate hshift m]
      exact hx
    rw [hkey x, ← Set.mem_preimage,
      Function.IsFixedPt.preimage_iterate hshift (m + C)] at h1
    exact h1
  · intro hx
    have h1 : (shift α)^[m + C] x ∈ A := by
      rw [← Set.mem_preimage, Function.IsFixedPt.preimage_iterate hshift (m + C)]
      exact hx
    rw [← hkey x, ← Set.mem_preimage,
      Function.IsFixedPt.preimage_iterate hshift m] at h1
    exact h1


end Probability

end TauCeti
