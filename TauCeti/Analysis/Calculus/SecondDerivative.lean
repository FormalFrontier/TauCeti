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

It also records the second-order chain rule at a point where the differential of the outer
function vanishes: there the first-order term drops out, so the second derivative of a composition
is the second derivative of the outer function evaluated on the images of the differential of the
inner one, i.e. the second derivative transforms as a bilinear form. Neither statement mentions
critical points as such, so both belong here rather than with the Morse theory that uses them.

## Main results

* `TauCeti.ContDiffAt.hasStrictFDerivAt_fderiv`: at a twice continuously differentiable point,
  `fderiv 𝕜 g` is strictly differentiable, with derivative the second derivative of `g`.
* `TauCeti.fderiv_fderiv_comp_apply_of_fderiv_eq_zero`: where the differential of the outer
  function vanishes, the second derivative of a composition is the pullback of the second
  derivative along the differential of the inner function.
-/

public section

open Filter Topology

namespace TauCeti

variable {𝕜 E F G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- At a twice continuously differentiable point, `fderiv 𝕜 g` is strictly differentiable, with
derivative the second derivative of `g`. -/
theorem ContDiffAt.hasStrictFDerivAt_fderiv {n : WithTop ℕ∞} {g : E → F} {x : E}
    (h : ContDiffAt 𝕜 n g x) (hn : 2 ≤ n) :
    HasStrictFDerivAt (fderiv 𝕜 g) (fderiv 𝕜 (fderiv 𝕜 g) x) x :=
  (h.fderiv_right (m := 1) (by exact_mod_cast hn)).hasStrictFDerivAt one_ne_zero

/-- **The second derivative at a critical value is a bilinear form pullback.** If the differential
of `f` vanishes at `φ b`, then the second derivative of `f ∘ φ` at `b` is the second derivative of
`f` at `φ b` evaluated on the images of the differential of `φ`. -/
theorem fderiv_fderiv_comp_apply_of_fderiv_eq_zero {f : E → G} {φ : F → E} {b : F}
    (hf : ContDiffAt 𝕜 2 f (φ b)) (hφ : ContDiffAt 𝕜 2 φ b) (hc : fderiv 𝕜 f (φ b) = 0) (v w : F) :
    fderiv 𝕜 (fderiv 𝕜 (f ∘ φ)) b v w =
      fderiv 𝕜 (fderiv 𝕜 f) (φ b) (fderiv 𝕜 φ b v) (fderiv 𝕜 φ b w) := by
  have hf1 : HasFDerivAt (fderiv 𝕜 f) (fderiv 𝕜 (fderiv 𝕜 f) (φ b)) (φ b) :=
    (ContDiffAt.hasStrictFDerivAt_fderiv hf le_rfl).hasFDerivAt
  have hφ1 : HasFDerivAt (fderiv 𝕜 φ) (fderiv 𝕜 (fderiv 𝕜 φ) b) b :=
    (ContDiffAt.hasStrictFDerivAt_fderiv hφ le_rfl).hasFDerivAt
  have hφ0 : HasFDerivAt φ (fderiv 𝕜 φ b) b := (hφ.differentiableAt (by norm_num)).hasFDerivAt
  have hA : HasFDerivAt (fun y ↦ fderiv 𝕜 f (φ y))
      ((fderiv 𝕜 (fderiv 𝕜 f) (φ b)).comp (fderiv 𝕜 φ b)) b := hf1.comp b hφ0
  have hev : ∀ᶠ y in 𝓝 b, fderiv 𝕜 (f ∘ φ) y = (fderiv 𝕜 f (φ y)).comp (fderiv 𝕜 φ y) := by
    have h1 : ∀ᶠ y in 𝓝 b, DifferentiableAt 𝕜 φ y := by
      filter_upwards [hφ.eventually (by norm_num)] with y hy
        using hy.differentiableAt (by norm_num)
    have h2 : ∀ᶠ y in 𝓝 b, DifferentiableAt 𝕜 f (φ y) := by
      filter_upwards [hφ.continuousAt.eventually (hf.eventually (by norm_num))] with y hy
        using hy.differentiableAt (by norm_num)
    filter_upwards [h1, h2] with y hy1 hy2 using fderiv_comp (x := y) hy2 hy1
  rw [((hA.clm_comp hφ1).congr_of_eventuallyEq hev).fderiv]
  simp [hc]

end TauCeti

end
