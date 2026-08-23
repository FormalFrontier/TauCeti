/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Trace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.RingTheory.Complex

/-!
# Trace-form diagonalisation for square-root bases

The effective discriminant bound `|d_K| ≤ |disc b|` (already in
`TauCeti/NumberTheory/EffectiveBounds/Discriminant/Basic.lean`) is only useful once one can
*evaluate* `disc b` on a concrete basis. The cheapest bases of a quadratic field are the
square-root bases `{1, x}` with `x² ∈ K`, and on those the trace form is diagonal when
`x ∉ K`: the off-diagonal entry `Tr(1 · x) = Tr x` vanishes because a non-base-field
element whose square lies in the base field has trace zero.

This file declares no new results: it records the EffectiveBounds square-root worked
examples. The discriminant example reuses `TauCeti.Algebra.discr_one_elem_eq_of_sq_algebraMap`
from `TauCeti.FieldTheory.Trace` (which in turn evaluates the off-diagonal trace via the
trace-vanishing criterion); the trace example computes `Tr_{ℂ/ℝ} I` directly via
`Algebra.trace_complex_apply`.

## Worked examples

The two `example`s below exercise that API on `ℂ / ℝ` (degree two): `Tr_{ℂ/ℝ} I = 0`
and `disc ℝ {1, I} = -4`, mirroring the roadmap's `ℚ(i)` worked example.

## Provenance

The trace-vanishing criterion migrates `trace_eq_zero_of_sq_ratCast` from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the
formalization of L. Alpöge's disproof of the uniform-constant Erdős unit-distance
conjecture, where it diagonalises the trace form on square-root bases. The reusable
criterion and discriminant formula live in `TauCeti.FieldTheory.Trace`; this file keeps
the EffectiveBounds worked examples near the roadmap target.
-/

public section

open Polynomial

namespace TauCeti

namespace Algebra

/-- `Complex.I` squares to the real number `-1`, so its trace over `ℝ` vanishes. -/
example : Algebra.trace ℝ ℂ Complex.I = 0 := by
  rw [Algebra.trace_complex_apply, Complex.I_re]
  norm_num

/-- The trace-form discriminant of the basis `{1, I}` of `ℂ` over `ℝ` is `-4`, recovering
`|disc {1, i}| = 4` of the roadmap's `ℚ(i)` worked example. -/
example : Algebra.discr ℝ ![1, Complex.I] = -4 := by
  rw [discr_one_elem_eq_of_sq_algebraMap (a := -1) Complex.finrank_real_complex]
  · norm_num
  · rw [Complex.I_sq]; simp
  · rintro ⟨r, hr⟩
    simpa [Complex.ext_iff, Complex.I_im] using congrArg Complex.im hr

end Algebra

end TauCeti
