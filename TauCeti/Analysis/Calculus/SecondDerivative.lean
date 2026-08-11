/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# The second derivative as a derivative

The second derivative `fderiv 𝕜 (fderiv 𝕜 g) x` of a map between normed spaces over an `RCLike`
field is, by definition, the derivative at `x` of the map `fderiv 𝕜 g`. Mathlib supplies the
differentiability of `fderiv 𝕜 g` at a twice continuously differentiable point through
`ContDiffAt.fderiv_right`, and upgrades differentiability to strict differentiability through
`ContDiffAt.hasStrictFDerivAt`; this file packages the two into the single statement that
second-order arguments use, so that the identification is made once rather than at each use.

## Main results

* `TauCeti.ContDiffAt.hasStrictFDerivAt_fderiv`: at a twice continuously differentiable point,
  `fderiv 𝕜 g` is strictly differentiable, with derivative the second derivative of `g`.
-/

public section

namespace TauCeti

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- At a twice continuously differentiable point, `fderiv 𝕜 g` is strictly differentiable, with
derivative the second derivative of `g`. -/
theorem ContDiffAt.hasStrictFDerivAt_fderiv {g : E → F} {x : E} (h : ContDiffAt 𝕜 2 g x) :
    HasStrictFDerivAt (fderiv 𝕜 g) (fderiv 𝕜 (fderiv 𝕜 g) x) x :=
  (h.fderiv_right (m := 1) (by norm_num)).hasStrictFDerivAt one_ne_zero

end TauCeti

end
