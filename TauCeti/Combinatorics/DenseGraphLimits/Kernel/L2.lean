/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Kernel.Basic

/-!
# The `L²` pairing of symmetric kernels

The Frieze--Kannan weak regularity argument runs on an `L²(μ ⊗ μ)` potential, so the block-average
step graphons of a refinement chain must be compared in `L²` and not only in cut norm.  This file
defines the integrals `l2inner μ K L = ∫ K · L` and `l2sq μ K = ∫ K²` at the level of strict
symmetric kernels.  When `μ` is finite, bounded kernels are square-integrable, so these integrals
are the `L²(μ ⊗ μ)` integral pairing and squared seminorm on strict representatives.  They induce
the genuine inner product and norm squared after quotienting by a.e. equality.  The integrability
of a single kernel over the product carrier is already available as
`SymmKernel.integrable_uncurry` from the basic kernel layer, and everything here is built on it.

**Why plain integrals and not `Lp`.**  A `SymmKernel` is a strict everywhere-defined
representative, and the whole point of that convention is that a difference `K - L` is again a
literal kernel.  Passing through `MeasureTheory.Lp` would replace each kernel by an a.e. class and
force a.e. bookkeeping into a layer that has no need of it; the a.e. view is taken once, later, on
the graphon quotient.  Kernels are bounded, so when `μ` is finite the integrals below converge and
the expansion `l2sq_sub` needs no additional side conditions.

## Main definitions

* `TauCeti.DenseGraphLimits.l2inner` is the integral of the product of two symmetric kernels;
* `TauCeti.DenseGraphLimits.l2sq` is the integral of the square of a symmetric kernel.

## Main results

* `TauCeti.DenseGraphLimits.SymmKernel.integrable_mul` is the integrability behind both;
* `TauCeti.DenseGraphLimits.l2sq_sub` expands the squared seminorm of a difference — the identity
  the Pythagoras energy increment is read off from;
* `TauCeti.DenseGraphLimits.l2sq_le_one_of_abs_le_one` bounds the squared seminorm of a kernel
  with values in `[-1, 1]` over a probability carrier.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §9.2.
* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 1/2 — `l2sq` and the analytic energy
  stack.  The `l2sq` signature and the `l2sq_nonneg` proof are taken from
  `TauCetiRoadmap/DenseGraphLimits/Suggested.lean` (Layer 1/2); the pairing `l2inner` and its
  bilinear API are developed here.
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
  exact (L.integrable_uncurry μ).bdd_mul K.measurable.aestronglyMeasurable
    (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hC p.1 p.2)

/-- A symmetric kernel is square integrable on the product carrier. -/
theorem integrable_sq [IsFiniteMeasure μ] (K : SymmKernel Ω μ) :
    Integrable (fun p : Ω × Ω => K p.1 p.2 ^ 2) (μ.prod μ) := by
  simpa only [sq] using integrable_mul μ K K

end SymmKernel

/-- The integral of the product of two symmetric kernels.  For finite `μ`, this is their
`L²(μ ⊗ μ)` integral pairing, which becomes an inner product after quotienting by a.e. equality. -/
def l2inner (K L : SymmKernel Ω μ) : ℝ := ∫ p, K p.1 p.2 * L p.1 p.2 ∂(μ.prod μ)

/-- The defining equation of `l2inner`. The definition's body is not exposed across module
boundaries, so this is the unfolding lemma downstream modules should use. -/
theorem l2inner_def (K L : SymmKernel Ω μ) :
    l2inner μ K L = ∫ p, K p.1 p.2 * L p.1 p.2 ∂(μ.prod μ) := (rfl)

/-- The integral of the square of a symmetric kernel.  For finite `μ`, this is its squared
`L²(μ ⊗ μ)` seminorm, which becomes a squared norm after quotienting by a.e. equality. -/
def l2sq (K : SymmKernel Ω μ) : ℝ := ∫ p, K p.1 p.2 ^ 2 ∂(μ.prod μ)

/-- The defining equation of `l2sq`. The definition's body is not exposed across module boundaries,
so this is the unfolding lemma downstream modules should use. -/
theorem l2sq_def (K : SymmKernel Ω μ) :
    l2sq μ K = ∫ p, K p.1 p.2 ^ 2 ∂(μ.prod μ) := (rfl)

/-- The squared `L²` seminorm is the integral pairing of a kernel with itself. -/
theorem l2sq_eq_l2inner_self (K : SymmKernel Ω μ) : l2sq μ K = l2inner μ K K := by
  simp only [l2sq_def, l2inner_def, sq]

/-- The squared `L²` seminorm is nonnegative: it is the integral of a square. -/
theorem l2sq_nonneg (K : SymmKernel Ω μ) : 0 ≤ l2sq μ K := by
  rw [l2sq_def]
  exact integral_nonneg fun _ => sq_nonneg _

/-- The `L²` integral pairing is symmetric. -/
theorem l2inner_comm (K L : SymmKernel Ω μ) : l2inner μ K L = l2inner μ L K := by
  simp only [l2inner_def, mul_comm]

/-- Pairing the zero kernel on the left with any kernel gives zero. -/
@[simp]
theorem l2inner_zero_left (K : SymmKernel Ω μ) : l2inner μ 0 K = 0 := by
  simp [l2inner_def]

/-- Pairing any kernel with the zero kernel on the right gives zero. -/
@[simp]
theorem l2inner_zero_right (K : SymmKernel Ω μ) : l2inner μ K 0 = 0 := by
  rw [l2inner_comm, l2inner_zero_left]

/-- Negating the left argument negates the pairing. -/
@[simp]
theorem l2inner_neg_left (K L : SymmKernel Ω μ) : l2inner μ (-K) L = -l2inner μ K L := by
  simp only [l2inner_def, SymmKernel.coe_neg, Pi.neg_apply, neg_mul, integral_neg]

/-- Negating the right argument negates the pairing. -/
@[simp]
theorem l2inner_neg_right (K L : SymmKernel Ω μ) : l2inner μ K (-L) = -l2inner μ K L := by
  rw [l2inner_comm, l2inner_neg_left, l2inner_comm μ L K]

/-- Scaling the left argument scales the pairing. -/
@[simp]
theorem l2inner_smul_left (c : ℝ) (K L : SymmKernel Ω μ) :
    l2inner μ (c • K) L = c * l2inner μ K L := by
  simp only [l2inner_def, SymmKernel.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc,
    integral_const_mul]

/-- Scaling the right argument scales the pairing. -/
@[simp]
theorem l2inner_smul_right (c : ℝ) (K L : SymmKernel Ω μ) :
    l2inner μ K (c • L) = c * l2inner μ K L := by
  rw [l2inner_comm, l2inner_smul_left, l2inner_comm μ L K]

@[simp]
theorem l2sq_zero : l2sq μ (0 : SymmKernel Ω μ) = 0 := by
  simp [l2sq_def]

/-- The squared `L²` seminorm is unchanged by negation. -/
@[simp]
theorem l2sq_neg (K : SymmKernel Ω μ) : l2sq μ (-K) = l2sq μ K := by
  simp [l2sq_eq_l2inner_self]

/-- Scaling a kernel scales its squared `L²` seminorm by the square of the scalar. -/
@[simp]
theorem l2sq_smul (c : ℝ) (K : SymmKernel Ω μ) : l2sq μ (c • K) = c ^ 2 * l2sq μ K := by
  simp only [l2sq_eq_l2inner_self, l2inner_smul_left, l2inner_smul_right]
  ring

variable [IsFiniteMeasure μ]

/-- The `L²` integral pairing is additive in its left argument. -/
@[simp]
theorem l2inner_add_left (K L M : SymmKernel Ω μ) :
    l2inner μ (K + L) M = l2inner μ K M + l2inner μ L M := by
  simp only [l2inner_def, SymmKernel.coe_add, Pi.add_apply, add_mul]
  exact integral_add (SymmKernel.integrable_mul μ K M) (SymmKernel.integrable_mul μ L M)

/-- The `L²` integral pairing is additive in its right argument. -/
@[simp]
theorem l2inner_add_right (K L M : SymmKernel Ω μ) :
    l2inner μ K (L + M) = l2inner μ K L + l2inner μ K M := by
  rw [l2inner_comm, l2inner_add_left, l2inner_comm μ L K, l2inner_comm μ M K]

/-- The `L²` integral pairing subtracts in its left argument. -/
@[simp]
theorem l2inner_sub_left (K L M : SymmKernel Ω μ) :
    l2inner μ (K - L) M = l2inner μ K M - l2inner μ L M := by
  simp only [l2inner_def, SymmKernel.coe_sub, Pi.sub_apply, sub_mul]
  exact integral_sub (SymmKernel.integrable_mul μ K M) (SymmKernel.integrable_mul μ L M)

/-- The `L²` integral pairing subtracts in its right argument. -/
@[simp]
theorem l2inner_sub_right (K L M : SymmKernel Ω μ) :
    l2inner μ K (L - M) = l2inner μ K L - l2inner μ K M := by
  rw [l2inner_comm μ, l2inner_sub_left, l2inner_comm μ M K, l2inner_comm μ L K]

/-- The expansion of the squared `L²` seminorm of a difference.  Read backwards with a vanishing
cross term, this is the Pythagoras identity the energy increment uses. -/
theorem l2sq_sub (K L : SymmKernel Ω μ) :
    l2sq μ (K - L) = l2sq μ K - 2 * l2inner μ K L + l2sq μ L := by
  simp only [l2sq_eq_l2inner_self, l2inner_sub_left, l2inner_sub_right]
  rw [l2inner_comm μ L K]
  ring

omit [IsFiniteMeasure μ] in
/-- A kernel with values in `[-1, 1]` has squared `L²` seminorm at most `1` over a probability
carrier. -/
theorem l2sq_le_one_of_abs_le_one [IsProbabilityMeasure μ] (K : SymmKernel Ω μ)
    (h : ∀ x y, |K x y| ≤ 1) : l2sq μ K ≤ 1 := by
  rw [l2sq_def]
  calc
    (∫ p : Ω × Ω, K p.1 p.2 ^ 2 ∂(μ.prod μ)) ≤ ∫ _p : Ω × Ω, (1 : ℝ) ∂(μ.prod μ) := by
      refine integral_mono (SymmKernel.integrable_sq μ K) (integrable_const 1) fun p => ?_
      exact (sq_le_one_iff_abs_le_one _).2 (h p.1 p.2)
    _ = 1 := by simp

end DenseGraphLimits

end TauCeti
