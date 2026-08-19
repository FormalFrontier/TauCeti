/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
-- Private: the derivative sum and scalar rules are used only inside the proofs below.
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# The gradient is an isometric linear image of the Fréchet derivative

Mathlib defines `gradient f x`, written `∇ f x`, as the Riesz representative
`(InnerProductSpace.toDual 𝕜 F).symm (fderiv 𝕜 f x)` of the Fréchet derivative of a scalar
function on an inner product space, and develops its differential calculus. This file records the
three consequences of the defining formula that come from `toDual` being a *conjugate-linear
isometric equivalence*: the gradient has the same norm as the derivative, it is additive, and it
is conjugate-homogeneous.

These are exactly what is needed to see a family of gradients as a linear, norm-preserving image
of the corresponding family of derivatives — for instance to know that `φ ↦ ∇ φ` is linear on
test functions and that `‖∇ φ‖` may be estimated by any theorem about `‖Dφ‖`.

## Main declarations

* `TauCeti.norm_gradient`: `‖∇ f x‖ = ‖fderiv 𝕜 f x‖`.
* `TauCeti.gradient_add`: additivity of the gradient at a point of differentiability.
* `TauCeti.gradient_const_smul`: `∇ (c • f) x = conj c • ∇ f x`.
-/

public section

namespace TauCeti

open InnerProductSpace

open scoped ComplexConjugate Gradient

variable {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F] {f g : F → 𝕜} {x : F}

/-- The gradient has the same norm as the Fréchet derivative it represents: `toDual` is an
isometry. -/
theorem norm_gradient (f : F → 𝕜) (x : F) : ‖∇ f x‖ = ‖fderiv 𝕜 f x‖ :=
  (toDual 𝕜 F).symm.norm_map _

/-- The gradient is additive wherever both summands are differentiable. -/
theorem gradient_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    ∇ (f + g) x = ∇ f x + ∇ g x := by
  refine ext_inner_right 𝕜 fun y => ?_
  rw [inner_add_left, inner_gradient_left, inner_gradient_left, inner_gradient_left,
    fderiv_add hf hg]
  rfl

/-- The gradient is conjugate-homogeneous: `toDual` is conjugate-linear, so scaling the function
by `c` scales the gradient by `conj c`. Over `ℝ` the conjugation is the identity. -/
theorem gradient_const_smul (hf : DifferentiableAt 𝕜 f x) (c : 𝕜) :
    ∇ (c • f) x = conj c • ∇ f x := by
  refine ext_inner_right 𝕜 fun y => ?_
  rw [inner_smul_left, inner_gradient_left, inner_gradient_left, RingHomCompTriple.comp_apply,
    RingHom.id_apply, fderiv_const_smul hf c]
  simp

end TauCeti
