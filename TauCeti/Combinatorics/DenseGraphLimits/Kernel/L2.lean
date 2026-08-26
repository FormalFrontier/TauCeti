/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Kernel.CutNorm

/-!
# The `L²` pairing of symmetric kernels

The Frieze--Kannan weak regularity argument runs on an `L²(μ ⊗ μ)` potential, so the block-average
step graphons of a refinement chain must be compared in `L²` and not only in cut norm.  This file
supplies that pairing at the level of strict symmetric kernels: `l2inner` is the `L²(μ ⊗ μ)` inner
product `∫ K · L` and `l2sq` is the induced norm squared `∫ K²`.

**Why plain integrals and not `Lp`.**  A `SymmKernel` is a strict everywhere-defined
representative, and the whole point of that convention is that a difference `K - L` is again a
literal kernel.  Passing through `MeasureTheory.Lp` would replace each kernel by an a.e. class and
force a.e. bookkeeping into a layer that has no need of it; the a.e. view is taken once, later, on
the graphon quotient.  Kernels are bounded and the carrier is finite, so the integrals below always
converge and the expansion `l2sq_sub` needs no side conditions.

## Main definitions

* `TauCeti.DenseGraphLimits.l2inner` is the `L²(μ ⊗ μ)` inner product of two symmetric kernels;
* `TauCeti.DenseGraphLimits.l2sq` is the `L²(μ ⊗ μ)` norm squared of a symmetric kernel.

## Main results

* `TauCeti.DenseGraphLimits.SymmKernel.integrable_mul` is the integrability behind both;
* `TauCeti.DenseGraphLimits.l2sq_sub` expands the norm squared of a difference — the identity the
  Pythagoras energy increment is read off from;
* `TauCeti.DenseGraphLimits.l2sq_le_one_of_abs_le_one` bounds the norm squared of a kernel with
  values in `[-1, 1]` over a probability carrier.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §9.2.
* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 1/2 — `l2sq` and the analytic energy
  stack.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

namespace SymmKernel

/-- The pointwise product of two symmetric kernels is integrable on the product carrier: both are
bounded, and the product measure of a finite measure with itself is finite. -/
theorem integrable_mul [IsFiniteMeasure μ] (K L : SymmKernel Ω μ) :
    Integrable (fun p : Ω × Ω => K p.1 p.2 * L p.1 p.2) (μ.prod μ) := by
  obtain ⟨C, hC⟩ := K.exists_bound
  obtain ⟨D, hD⟩ := L.exists_bound
  have hmeas : Measurable fun p : Ω × Ω => K p.1 p.2 * L p.1 p.2 := K.measurable.mul L.measurable
  refine Integrable.of_bound hmeas.aestronglyMeasurable (C * D) (ae_of_all _ fun p => ?_)
  have hCp := hC p.1 p.2
  have hDp := hD p.1 p.2
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul hCp hDp (abs_nonneg _) ((abs_nonneg _).trans hCp)

/-- A symmetric kernel is square integrable on the product carrier. -/
theorem integrable_sq [IsFiniteMeasure μ] (K : SymmKernel Ω μ) :
    Integrable (fun p : Ω × Ω => K p.1 p.2 ^ 2) (μ.prod μ) := by
  simpa only [sq] using integrable_mul μ K K

end SymmKernel

/-- The `L²(μ ⊗ μ)` inner product of two symmetric kernels. -/
def l2inner (K L : SymmKernel Ω μ) : ℝ := ∫ p, K p.1 p.2 * L p.1 p.2 ∂(μ.prod μ)

/-- The defining equation of `l2inner`. The definition's body is not exposed across module
boundaries, so this is the unfolding lemma downstream modules should use. -/
theorem l2inner_def (K L : SymmKernel Ω μ) :
    l2inner μ K L = ∫ p, K p.1 p.2 * L p.1 p.2 ∂(μ.prod μ) := (rfl)

/-- The `L²(μ ⊗ μ)` norm squared of a symmetric kernel. -/
def l2sq (K : SymmKernel Ω μ) : ℝ := ∫ p, K p.1 p.2 ^ 2 ∂(μ.prod μ)

/-- The defining equation of `l2sq`. The definition's body is not exposed across module boundaries,
so this is the unfolding lemma downstream modules should use. -/
theorem l2sq_def (K : SymmKernel Ω μ) :
    l2sq μ K = ∫ p, K p.1 p.2 ^ 2 ∂(μ.prod μ) := (rfl)

/-- The `L²` norm squared is the inner product of a kernel with itself. -/
theorem l2sq_eq_l2inner_self (K : SymmKernel Ω μ) : l2sq μ K = l2inner μ K K := by
  simp only [l2sq_def, l2inner_def, sq]

/-- The `L²` norm squared is nonnegative: it is the integral of a square. -/
theorem l2sq_nonneg (K : SymmKernel Ω μ) : 0 ≤ l2sq μ K := by
  rw [l2sq_def]
  exact integral_nonneg fun _ => sq_nonneg _

/-- The `L²` inner product is symmetric. -/
theorem l2inner_comm (K L : SymmKernel Ω μ) : l2inner μ K L = l2inner μ L K := by
  simp only [l2inner_def, mul_comm]

@[simp]
theorem l2sq_zero : l2sq μ (0 : SymmKernel Ω μ) = 0 := by
  simp [l2sq_def]

variable [IsFiniteMeasure μ]

/-- The `L²` inner product is additive in its left argument. -/
theorem l2inner_add_left (K L M : SymmKernel Ω μ) :
    l2inner μ (K + L) M = l2inner μ K M + l2inner μ L M := by
  simp only [l2inner_def, SymmKernel.coe_add, Pi.add_apply, add_mul]
  exact integral_add (SymmKernel.integrable_mul μ K M) (SymmKernel.integrable_mul μ L M)

/-- The `L²` inner product subtracts in its left argument. -/
theorem l2inner_sub_left (K L M : SymmKernel Ω μ) :
    l2inner μ (K - L) M = l2inner μ K M - l2inner μ L M := by
  simp only [l2inner_def, SymmKernel.coe_sub, Pi.sub_apply, sub_mul]
  exact integral_sub (SymmKernel.integrable_mul μ K M) (SymmKernel.integrable_mul μ L M)

/-- The `L²` inner product subtracts in its right argument. -/
theorem l2inner_sub_right (K L M : SymmKernel Ω μ) :
    l2inner μ K (L - M) = l2inner μ K L - l2inner μ K M := by
  rw [l2inner_comm μ, l2inner_sub_left, l2inner_comm μ M K, l2inner_comm μ L K]

/-- The expansion of the `L²` norm squared of a difference.  Read backwards with a vanishing cross
term, this is the Pythagoras identity the energy increment uses. -/
theorem l2sq_sub (K L : SymmKernel Ω μ) :
    l2sq μ (K - L) = l2sq μ K - 2 * l2inner μ K L + l2sq μ L := by
  rw [l2sq_eq_l2inner_self, l2inner_sub_left, l2inner_sub_right, l2inner_sub_right,
    l2inner_comm μ L K, l2sq_eq_l2inner_self μ K, l2sq_eq_l2inner_self μ L]
  ring

/-- A kernel with values in `[-1, 1]` has `L²` norm squared at most `1` over a probability
carrier. -/
theorem l2sq_le_one_of_abs_le_one [IsProbabilityMeasure μ] (K : SymmKernel Ω μ)
    (h : ∀ x y, |K x y| ≤ 1) : l2sq μ K ≤ 1 := by
  rw [l2sq_def]
  calc
    (∫ p : Ω × Ω, K p.1 p.2 ^ 2 ∂(μ.prod μ)) ≤ ∫ _p : Ω × Ω, (1 : ℝ) ∂(μ.prod μ) := by
      refine integral_mono (SymmKernel.integrable_sq μ K) (integrable_const 1) fun p => ?_
      have hp := h p.1 p.2
      nlinarith [abs_nonneg (K p.1 p.2), sq_abs (K p.1 p.2)]
    _ = 1 := by simp

end DenseGraphLimits

end TauCeti
