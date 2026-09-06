/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Divisibility by an invertible ideal

An ideal of a domain which is invertible as a fractional ideal divides every principal ideal it
contains, the cofactor being the integral ideal representing `⟨a⟩ * I⁻¹`.

Over a Dedekind domain this is subsumed by `Ideal.dvd_iff_le` ("to contain is to divide"), which
holds for *every* nonzero ideal. The statement here assumes no Dedekind hypothesis, only that the
divisor is invertible, so it also applies to rings that are not integrally closed — coordinate
rings of possibly singular affine curves, for instance.

## Main results

* `Ideal.exists_isUnit_eq_mul_of_le`: an invertible ideal divides every invertible ideal it
  contains, over an arbitrary fraction ring.
* `Ideal.exists_isUnit_span_singleton_eq_mul`: the principal case, since a nonzero principal
  ideal is invertible.
-/

-- Design provenance (not API documentation): the argument was extracted from
-- `TauCeti/AlgebraicGeometry/EllipticCurve/Affine/Point/ToClass.lean`, itself ported from the
-- AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at the roadmap's
-- HasseWeil pin `dev/hasse-weil @ 513e83879e2f`, file `HasseWeil/Pic0/ToClassSurjective.lean`
-- (by Chris Birkbeck), where it sat inline inside the codimension-reduction step.

open scoped nonZeroDivisors

namespace Ideal

public section

variable {R : Type*} [CommRing R] {K : Type*} [CommRing K] [Algebra R K] [IsFractionRing R K]

/-- **An invertible ideal divides every invertible ideal it contains.** If `A ≤ I` are ideals
whose images in the fractional ideals are units, then `A = I * J` for an invertible `J`, namely
the integral ideal representing `A * I⁻¹`. (Such a `J` is automatically nonzero whenever the
fractional ideals are nontrivial; see `exists_isUnit_span_singleton_eq_mul`.) -/
theorem exists_isUnit_eq_mul_of_le {A I : Ideal R} (hAunit : IsUnit (A : FractionalIdeal R⁰ K))
    (hIunit : IsUnit (I : FractionalIdeal R⁰ K)) (hle : A ≤ I) :
    ∃ J : Ideal R, IsUnit (J : FractionalIdeal R⁰ K) ∧ A = I * J := by
  -- `A * I⁻¹` is contained in `1`, so it is (the image of) an integral ideal `J`.
  have hQ_le : (A : FractionalIdeal R⁰ K) * ↑hIunit.unit⁻¹ ≤ 1 := by
    calc
      (A : FractionalIdeal R⁰ K) * ↑hIunit.unit⁻¹ ≤
          (I : FractionalIdeal R⁰ K) * ↑hIunit.unit⁻¹ := by gcongr
      _ = 1 := hIunit.mul_val_inv
  obtain ⟨J, hJQ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hQ_le
  have hJ : A = I * J := by
    apply FractionalIdeal.coeIdeal_injective' (R := R) (P := K) le_rfl
    simp only [FractionalIdeal.coeIdeal_mul, hJQ]
    rw [mul_left_comm, hIunit.mul_val_inv, mul_one]
  -- `I * J` is a unit, so `J` is one too, and in particular `J ≠ ⊥`.
  have hJunit : IsUnit (J : FractionalIdeal R⁰ K) := by
    have hIJunit : IsUnit ((I : FractionalIdeal R⁰ K) * (J : FractionalIdeal R⁰ K)) := by
      rw [← FractionalIdeal.coeIdeal_mul, ← hJ]
      exact hAunit
    exact (IsUnit.mul_iff.mp hIJunit).2
  exact ⟨J, hJunit, hJ⟩

section Field

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **An invertible ideal divides every principal ideal it contains**, a nonzero principal ideal
being invertible. -/
theorem exists_isUnit_span_singleton_eq_mul (I : Ideal R)
    (hIunit : IsUnit (I : FractionalIdeal R⁰ K)) {a : R} (ha : a ≠ 0) (ha_mem : a ∈ I) :
    ∃ J : Ideal R, IsUnit (J : FractionalIdeal R⁰ K) ∧ J ≠ ⊥ ∧ Ideal.span {a} = I * J := by
  have haK : algebraMap R K a ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective R K).ne ha
  have hspanUnit : IsUnit (Ideal.span ({a} : Set R) : FractionalIdeal R⁰ K) := by
    refine ⟨toPrincipalIdeal R K (Units.mk0 (algebraMap R K a) haK), ?_⟩
    rw [coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton]
    rfl
  obtain ⟨J, hJunit, hJ⟩ := exists_isUnit_eq_mul_of_le hspanUnit hIunit
    (by rw [Ideal.span_le, Set.singleton_subset_iff]; exact ha_mem)
  exact ⟨J, hJunit, FractionalIdeal.coeIdeal_ne_zero.mp hJunit.ne_zero, hJ⟩

end Field

end

end Ideal
