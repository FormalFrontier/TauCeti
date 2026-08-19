/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace

/-!
# The trace of an endomorphism whose square is a multiple of itself

An endomorphism `f` of a finite-dimensional vector space satisfying `f * f = a • f` is a scaled
projection: when `a ≠ 0` the endomorphism `a⁻¹ • f` is idempotent with the same range as `f`, so
the trace of `f` is `a` times the dimension of that range. The degenerate case `a = 0` obeys the
same formula, because then `f` squares to zero, hence is nilpotent and traceless.

This is the standard device for pinning down the scalar in an *essential idempotence* identity
`c * c = a • c` in a finite-dimensional algebra: compute the trace of multiplication by `c` in
two ways, once from the identity and once from a basis. Mathlib has the idempotent case
(`LinearMap.IsProj.trace`, together with `IsIdempotentElem.isProj_range`); this file removes the
normalisation, which is exactly what makes the identity usable when the scalar is the unknown.

## Main statements

* `TauCeti.LinearMap.trace_eq_mul_finrank_range`: if `f * f = a • f`, then
  `trace f = a * finrank (range f)`.
-/

public section

namespace TauCeti

open Module

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- **The trace of an essentially idempotent endomorphism.** If the square of `f` is `a • f`,
then the trace of `f` is `a` times the dimension of the range of `f`.

For `a ≠ 0` this says that `a⁻¹ • f` is a projection onto `range f`; for `a = 0` both sides
vanish, because `f` then squares to zero. -/
theorem LinearMap.trace_eq_mul_finrank_range {f : M →ₗ[K] M} {a : K} (hf : f * f = a • f) :
    _root_.LinearMap.trace K M f = a * (finrank K (_root_.LinearMap.range f) : K) := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [zero_mul]
    refine IsNilpotent.eq_zero (_root_.LinearMap.isNilpotent_trace_of_isNilpotent ⟨2, ?_⟩)
    rw [pow_two, hf, zero_smul]
  · have hsq : (a⁻¹ • f) * (a⁻¹ • f) = (a⁻¹ * a⁻¹) • (f * f) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    have hnorm : (a⁻¹ • f) * (a⁻¹ • f) = a⁻¹ • f := by
      rw [hsq, hf, smul_smul, mul_assoc, inv_mul_cancel₀ ha, mul_one]
    have hidem : IsIdempotentElem (a⁻¹ • f) := hnorm
    have htrace : a⁻¹ * _root_.LinearMap.trace K M f =
        (finrank K (_root_.LinearMap.range f) : K) := by
      rw [← smul_eq_mul, ← map_smul, ← _root_.LinearMap.range_smul f a⁻¹ (inv_ne_zero ha)]
      exact (_root_.LinearMap.IsIdempotentElem.isProj_range _ hidem).trace
    rw [← htrace, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]

end TauCeti
