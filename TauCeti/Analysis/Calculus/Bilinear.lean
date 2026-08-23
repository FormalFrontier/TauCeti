/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
# Derivatives of the diagonal of a continuous bilinear map

The quadratic map `z ↦ B z z` attached to a continuous bilinear map `B : E →L[𝕜] E →L[𝕜] F` is
smooth, with derivative at `y` the polarization `B.flip y + B y` of `B` evaluated at `y`; since
that derivative is linear in `y`, the second derivative is the constant continuous linear map
`B.flip + B`. This is the derivative computation behind the local model of a nondegenerate
critical point, but it depends on nothing beyond the bilinear chain rule
`ContinuousLinearMap.hasStrictFDerivAt_of_bilinear` and the smoothness of bounded bilinear maps.

## Main results

* `TauCeti.ContinuousLinearMap.contDiff_apply_self`: `z ↦ B z z` is `C^n` for every `n`, and its
  corollary `TauCeti.ContinuousLinearMap.differentiable_apply_self`.
* `TauCeti.ContinuousLinearMap.hasStrictFDerivAt_apply_self`: `z ↦ B z z` is strictly
  differentiable at `y`, with derivative the polarization of `B` evaluated at `y`.
* `TauCeti.ContinuousLinearMap.hasFDerivAt_apply_self`, and its `fderiv` form
  `TauCeti.ContinuousLinearMap.fderiv_apply_self`.
* `TauCeti.ContinuousLinearMap.fderiv_fderiv_apply_self`: the second derivative of `z ↦ B z z` is
  the constant `B.flip + B`.
-/

public section

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : WithTop ℕ∞}

namespace ContinuousLinearMap

/-- The map `z ↦ B z z` attached to a continuous bilinear map `B` is `C^n` for every `n`. -/
theorem contDiff_apply_self (B : E →L[𝕜] E →L[𝕜] F) : ContDiff 𝕜 n (fun z ↦ B z z) :=
  B.isBoundedBilinearMap.contDiff.comp₂ contDiff_id contDiff_id

/-- The map `z ↦ B z z` attached to a continuous bilinear map `B` is differentiable. -/
theorem differentiable_apply_self (B : E →L[𝕜] E →L[𝕜] F) : Differentiable 𝕜 (fun z ↦ B z z) :=
  (contDiff_apply_self (n := 1) B).differentiable one_ne_zero

/-- The map `z ↦ B z z` attached to a continuous bilinear map `B` is strictly differentiable at
`y`, with derivative the polarization of `B` evaluated at `y`. -/
theorem hasStrictFDerivAt_apply_self (B : E →L[𝕜] E →L[𝕜] F) (y : E) :
    HasStrictFDerivAt (fun z ↦ B z z) (B.flip y + B y) y := by
  have h : HasStrictFDerivAt (fun z ↦ B z z)
      (B.precompR E y (ContinuousLinearMap.id 𝕜 E) +
        B.precompL E (ContinuousLinearMap.id 𝕜 E) y) y :=
    B.hasStrictFDerivAt_of_bilinear (hasStrictFDerivAt_id y) (hasStrictFDerivAt_id y)
  convert h using 1
  ext v
  simp [add_comm]

/-- The map `z ↦ B z z` attached to a continuous bilinear map `B` is differentiable at `y`, with
derivative the polarization of `B` evaluated at `y`. -/
theorem hasFDerivAt_apply_self (B : E →L[𝕜] E →L[𝕜] F) (y : E) :
    HasFDerivAt (fun z ↦ B z z) (B.flip y + B y) y :=
  (hasStrictFDerivAt_apply_self B y).hasFDerivAt

/-- At `y`, the differential of `z ↦ B z z` is `B.flip y + B y`. -/
@[simp]
theorem fderiv_apply_self (B : E →L[𝕜] E →L[𝕜] F) (y : E) :
    fderiv 𝕜 (fun z ↦ B z z) y = B.flip y + B y :=
  (hasFDerivAt_apply_self B y).fderiv

/-- The second derivative of `z ↦ B z z` is the constant `B.flip + B`. -/
@[simp]
theorem fderiv_fderiv_apply_self (B : E →L[𝕜] E →L[𝕜] F) (y : E) :
    fderiv 𝕜 (fderiv 𝕜 fun z ↦ B z z) y = B.flip + B := by
  have hEq : (fderiv 𝕜 fun z ↦ B z z) = fun z ↦ (B.flip + B) z := by
    funext z
    rw [fderiv_apply_self, add_apply]
  rw [hEq]
  exact (B.flip + B).fderiv

end ContinuousLinearMap

end TauCeti

end
