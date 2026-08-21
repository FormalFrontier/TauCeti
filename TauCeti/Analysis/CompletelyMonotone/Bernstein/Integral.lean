/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Bernstein.Basic
public import TauCeti.Analysis.Calculus.HalfLinePrimitive

/-!
# Primitives of completely monotone functions are Bernstein functions

This file establishes one direction of the standard correspondence between completely monotone
and Bernstein functions. If `f` is completely monotone on `(0, ∞)` and continuous on `[0, ∞)`,
then

`t ↦ ∫ x in 0..t, f x` for `t ≥ 0`

is a Bernstein function. Its derivative on `(0, ∞)` is `f`, so complete monotonicity of the
derivative is inherited directly from `f`.

The primitive is packaged as `TauCeti.halfLinePrimitive` (in
`TauCeti.Analysis.Calculus.HalfLinePrimitive`), which integrates `f (max x 0)` so that the
function is defined on all of `ℝ`; on `[0, ∞)` this agrees with `∫₀ᵗ f` by
`TauCeti.halfLinePrimitive_eq_integral_of_nonneg`.

## Main declarations

* `TauCeti.IsCompletelyMonotoneOnIoi.isBernsteinFunction_halfLinePrimitive`: the primitive of a
  function that is completely monotone on `(0, ∞)` and continuous on `[0, ∞)` is Bernstein.
* `TauCeti.IsCompletelyMonotoneOnIoi.isBernsteinFunction_integral`: the same statement written
  directly in terms of `∫ x in 0..t, f x`.
* `TauCeti.IsCompletelyMonotone.isBernsteinFunction_halfLinePrimitive`,
  `TauCeti.IsCompletelyMonotone.isBernsteinFunction_integral`: the corresponding statements for
  the closed-half-line predicate `IsCompletelyMonotone`.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Chapter 3.
-/

public section

open Set intervalIntegral
open scoped ContDiff Topology

namespace TauCeti

variable {f : ℝ → ℝ} {t : ℝ}

namespace IsCompletelyMonotoneOnIoi

/-- The primitive on `[0, ∞)` of a function that is completely monotone on `(0, ∞)` and
continuous on `[0, ∞)` is a Bernstein function. -/
theorem isBernsteinFunction_halfLinePrimitive (hf : IsCompletelyMonotoneOnIoi f)
    (hcont : ContinuousOn f (Ici 0)) : IsBernsteinFunction (halfLinePrimitive f) := by
  have hcontinuous : ContinuousOn (halfLinePrimitive f) (Ici 0) :=
    (continuous_halfLinePrimitive hcont).continuousOn
  have hcontDiff : ContDiffOn ℝ ∞ (halfLinePrimitive f) (Ioi 0) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun t ht ↦
      (hasDerivAt_halfLinePrimitive hcont ht.le).differentiableAt.differentiableWithinAt, ?_⟩
    exact hf.contDiffOn.congr fun t ht ↦ deriv_halfLinePrimitive hcont ht.le
  rw [isBernsteinFunction_iff]
  refine ⟨hcontinuous, hcontDiff, fun t ht ↦ ?_, ?_⟩
  · rw [halfLinePrimitive_def]
    exact intervalIntegral.integral_nonneg ht fun x hx ↦
      hf.nonneg_of_continuousWithinAt (hcont 0 self_mem_Ici) (le_max_right x 0)
  · exact hf.congr fun t ht ↦ deriv_halfLinePrimitive hcont ht.le

/-- The primitive `t ↦ ∫₀ᵗ f` of a function that is completely monotone on `(0, ∞)` and
continuous on `[0, ∞)` is a Bernstein function. -/
theorem isBernsteinFunction_integral (hf : IsCompletelyMonotoneOnIoi f)
    (hcont : ContinuousOn f (Ici 0)) :
    IsBernsteinFunction fun t ↦ ∫ x in (0 : ℝ)..t, f x :=
  (hf.isBernsteinFunction_halfLinePrimitive hcont).congr fun _ ht ↦
    (halfLinePrimitive_eq_integral_of_nonneg ht).symm

end IsCompletelyMonotoneOnIoi

namespace IsCompletelyMonotone

/-- The primitive on `[0, ∞)` of a completely monotone function is a Bernstein function. -/
theorem isBernsteinFunction_halfLinePrimitive (hf : IsCompletelyMonotone f) :
    IsBernsteinFunction (halfLinePrimitive f) :=
  hf.isCompletelyMonotoneOnIoi.isBernsteinFunction_halfLinePrimitive hf.contDiffOn.continuousOn

/-- The primitive `t ↦ ∫₀ᵗ f` of a completely monotone function is a Bernstein function. -/
theorem isBernsteinFunction_integral (hf : IsCompletelyMonotone f) :
    IsBernsteinFunction fun t ↦ ∫ x in (0 : ℝ)..t, f x :=
  hf.isCompletelyMonotoneOnIoi.isBernsteinFunction_integral hf.contDiffOn.continuousOn

end IsCompletelyMonotone

end TauCeti

end
