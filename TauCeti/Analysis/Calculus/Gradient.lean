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
# The gradient is an isometric conjugate-linear image of the Fréchet derivative

Mathlib defines `gradient f x`, written `∇ f x`, as the Riesz representative
`(InnerProductSpace.toDual 𝕜 F).symm (fderiv 𝕜 f x)` of the Fréchet derivative of a scalar
function on an inner product space, and develops its differential calculus. This file records the
three consequences of the defining formula that come from `toDual` being a *conjugate-linear
isometric equivalence*: the gradient has the same norm as the derivative, it is additive, and it
is conjugate-homogeneous.

These are exactly what is needed to see a family of gradients as a conjugate-linear,
norm-preserving image of the corresponding family of derivatives. Over `ℝ` it is linear; for
instance, `φ ↦ ∇ φ` is linear on real-valued test functions, and `‖∇ φ‖` may be estimated by any
theorem about `‖Dφ‖`.

## Main declarations

* `TauCeti.norm_gradient_eq_norm_fderiv`: `‖∇ f x‖ = ‖fderiv 𝕜 f x‖`.
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
theorem norm_gradient_eq_norm_fderiv (f : F → 𝕜) (x : F) : ‖∇ f x‖ = ‖fderiv 𝕜 f x‖ :=
  (toDual 𝕜 F).symm.norm_map _

/-- The gradient is additive wherever both summands are differentiable. -/
theorem gradient_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    ∇ (f + g) x = ∇ f x + ∇ g x := by
  apply (toDual 𝕜 F).injective
  simp only [toDual_gradient, map_add, fderiv_add hf hg]

/-- The gradient is conjugate-homogeneous: `toDual` is conjugate-linear, so scaling the function
by `c` scales the gradient by `conj c`. Over `ℝ` the conjugation is the identity. -/
theorem gradient_const_smul (c : 𝕜) :
    ∇ (c • f) x = conj c • ∇ f x := by
  apply (toDual 𝕜 F).injective
  simp only [toDual_gradient, map_smulₛₗ, RingHomCompTriple.comp_apply, RingHom.id_apply,
    fderiv_const_smul_field, Pi.smul_apply]

end TauCeti
