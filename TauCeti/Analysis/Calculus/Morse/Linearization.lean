/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Calculus.Morse.Index

/-!
# Linearization of the negative-gradient field at a Morse critical point

The stable-manifold theorem starts with the derivative of the vector field at an equilibrium. For
a gradient field on a real Hilbert space, the second derivative of the function naturally takes
values in the continuous dual. The Riesz equivalence turns it into an endomorphism of the original
space: `TauCeti.hessianOperator`.

At a twice continuously differentiable point this operator is self-adjoint, by symmetry of the
second derivative. At a nondegenerate critical point it is invertible, and the negative-gradient
field has derivative `-hessianOperator f x`. Consequently the field is its invertible linear part
up to a remainder of order `o(‖y - x‖)`. The characterization
`TauCeti.isNondegenerateCriticalPoint_iff_neg_gradient_linearization` packages exactly the
equilibrium and invertible-linearization hypotheses needed for the stable-manifold theorem in the
gradient setting.

The definition uses Mathlib's totalized Fréchet derivative, just as
`TauCeti.IsNondegenerateCriticalPoint` and `TauCeti.hessianQuadraticForm` do. Regularity enters the
results that identify the operator as the derivative of the gradient and prove self-adjointness.

## Main declarations

* `TauCeti.hessianOperator`: the Riesz-represented Hessian as an endomorphism of the Hilbert space.
* `TauCeti.ContDiffAt.isSelfAdjoint_hessianOperator`: symmetry of the second derivative becomes
  self-adjointness of the Hessian operator.
* `TauCeti.ContDiffAt.hasFDerivAt_neg_gradient`: the derivative of `-∇ f` is the negative Hessian
  operator.
* `TauCeti.IsNondegenerateCriticalPoint.neg_gradient_sub_linearization_isLittleO`: the nonlinear
  remainder after subtracting the linearization is little-o of the displacement.
* `TauCeti.isNondegenerateCriticalPoint_iff_neg_gradient_linearization`: nondegenerate critical
  points are exactly the equilibria with invertible negative-gradient linearization, under `C²`
  regularity.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
* [Heegaard Floer homology roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HeegaardFloer/README.md),
  Lane M, "Morse homology".
-/

public section

open InnerProductSpace
open scoped Gradient

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {x : E}

/-- The Hessian of `f` at `x`, represented as an endomorphism of the Hilbert space using the Riesz
equivalence. Its inner product with `w` is the second derivative of `f` evaluated on `v, w`.

The definition is meaningful without regularity because Mathlib's Fréchet derivative is
totalized by zero. Twice continuous differentiability is assumed when this operator is used as
the derivative of the gradient. -/
noncomputable def hessianOperator (f : E → ℝ) (x : E) : E →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    fderiv ℝ (fderiv ℝ f) x

/-- Applying the Riesz map to the Hessian operator recovers the dual-valued second derivative. -/
@[simp]
theorem toDual_hessianOperator (f : E → ℝ) (x : E) :
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap ∘L
      hessianOperator f x = fderiv ℝ (fderiv ℝ f) x := by
  ext v
  simp [hessianOperator]

/-- The inner-product characterization of the Hessian operator. -/
@[simp]
theorem inner_hessianOperator_left (f : E → ℝ) (x v w : E) :
    ⟪hessianOperator f x v, w⟫_ℝ = fderiv ℝ (fderiv ℝ f) x v w := by
  rw [← InnerProductSpace.toDual_apply_apply]
  change ((InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    hessianOperator f x) v w = _
  rw [toDual_hessianOperator]

/-- Twice continuous differentiability makes the Hessian operator self-adjoint. This is the
operator form of symmetry of the second Fréchet derivative. -/
theorem ContDiffAt.isSelfAdjoint_hessianOperator (hf : ContDiffAt ℝ 2 f x) :
    IsSelfAdjoint (hessianOperator f x) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro v w
  calc
    ⟪(hessianOperator f x : E → E) v, w⟫_ℝ =
        fderiv ℝ (fderiv ℝ f) x v w := inner_hessianOperator_left f x v w
    _ = fderiv ℝ (fderiv ℝ f) x w v := hf.isSymmSndFDerivAt (by norm_num) v w
    _ = ⟪(hessianOperator f x : E → E) w, v⟫_ℝ :=
      (inner_hessianOperator_left f x w v).symm
    _ = ⟪v, (hessianOperator f x : E → E) w⟫_ℝ := real_inner_comm _ _

/-- The Hessian operator is invertible exactly when the dual-valued second derivative is. Thus
the Hilbert-space operator formulation is equivalent to the Banach-space formulation used in
`TauCeti.IsNondegenerateCriticalPoint`. -/
theorem isInvertible_hessianOperator_iff :
    (hessianOperator f x).IsInvertible ↔ (fderiv ℝ (fderiv ℝ f) x).IsInvertible := by
  rw [← ContinuousLinearMap.isInvertible_equiv_comp
    (e := (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv)]
  rw [toDual_hessianOperator]

/-- The Hessian operator at a nondegenerate critical point is invertible. -/
theorem IsNondegenerateCriticalPoint.isInvertible_hessianOperator
    (h : IsNondegenerateCriticalPoint f x) : (hessianOperator f x).IsInvertible :=
  isInvertible_hessianOperator_iff.2 h.isInvertible

/-- The gradient is differentiable at a twice continuously differentiable point, with derivative
the Hessian operator. -/
theorem ContDiffAt.hasFDerivAt_gradient (hf : ContDiffAt ℝ 2 f x) :
    HasFDerivAt (∇ f) (hessianOperator f x) x := by
  have hfd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero |>.hasFDerivAt
  have h := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.hasFDerivAt.comp x hfd
  convert h using 1
  · ext y
    rfl
  · rfl

/-- The negative-gradient vector field is differentiable at a twice continuously differentiable
point, with derivative minus the Hessian operator. -/
theorem ContDiffAt.hasFDerivAt_neg_gradient (hf : ContDiffAt ℝ 2 f x) :
    HasFDerivAt (-∇ f) (-hessianOperator f x) x :=
  (ContDiffAt.hasFDerivAt_gradient hf).neg

/-- The gradient vanishes at a nondegenerate critical point. This translates the dual-valued
criticality condition in `TauCeti.IsNondegenerateCriticalPoint` through the Riesz equivalence. -/
theorem IsNondegenerateCriticalPoint.gradient_eq_zero
    (h : IsNondegenerateCriticalPoint f x) : ∇ f x = 0 := by
  apply (InnerProductSpace.toDual ℝ E).injective
  simp [h.fderiv_eq_zero]

/-- Negating a Hessian operator preserves and reflects invertibility. -/
theorem isInvertible_neg_hessianOperator_iff :
    (-hessianOperator f x).IsInvertible ↔ (hessianOperator f x).IsInvertible := by
  have hneg : -hessianOperator f x =
      (ContinuousLinearEquiv.neg ℝ : E ≃L[ℝ] E) ∘L hessianOperator f x := by
    ext v
    simp
  rw [hneg, ContinuousLinearMap.isInvertible_equiv_comp]

/-- The derivative of the negative-gradient field at a nondegenerate critical point is
invertible. -/
theorem IsNondegenerateCriticalPoint.isInvertible_neg_hessianOperator
    (h : IsNondegenerateCriticalPoint f x) : (-hessianOperator f x).IsInvertible :=
  isInvertible_neg_hessianOperator_iff.2 h.isInvertible_hessianOperator

/-- At a nondegenerate critical point, the negative-gradient field differs from its linearization
by a term of order `o(‖y - x‖)`. This is the nonlinear remainder controlled in the local
stable-manifold argument. -/
theorem IsNondegenerateCriticalPoint.neg_gradient_sub_linearization_isLittleO
    (h : IsNondegenerateCriticalPoint f x) :
    (fun y ↦ (-∇ f) y + hessianOperator f x (y - x)) =o[nhds x]
      (fun y ↦ y - x) := by
  have hrem := (ContDiffAt.hasFDerivAt_neg_gradient h.contDiffAt).isLittleO
  simpa only [Pi.neg_apply, h.gradient_eq_zero, neg_zero, sub_zero, neg_apply,
    sub_neg_eq_add] using hrem

/-- On a real Hilbert space, nondegeneracy can be read entirely from the gradient and its Hessian
operator. -/
theorem isNondegenerateCriticalPoint_iff_gradient :
    IsNondegenerateCriticalPoint f x ↔
      ContDiffAt ℝ 2 f x ∧ ∇ f x = 0 ∧ (hessianOperator f x).IsInvertible := by
  constructor
  · intro h
    exact ⟨h.contDiffAt, h.gradient_eq_zero, h.isInvertible_hessianOperator⟩
  · rintro ⟨hf, hgrad, hinv⟩
    refine ⟨hf, ?_, isInvertible_hessianOperator_iff.1 hinv⟩
    rw [← toDual_gradient]
    simp [hgrad]

/-- A nondegenerate critical point is precisely an equilibrium of the negative-gradient field
whose derivative is invertible, under the stated `C²` regularity. This is the hyperbolicity input
to the stable-manifold theorem in the self-adjoint gradient setting. -/
theorem isNondegenerateCriticalPoint_iff_neg_gradient_linearization :
    IsNondegenerateCriticalPoint f x ↔
      ContDiffAt ℝ 2 f x ∧ (-∇ f) x = 0 ∧
        (fderiv ℝ (-∇ f) x).IsInvertible := by
  constructor
  · intro h
    refine ⟨h.contDiffAt, by simp [h.gradient_eq_zero], ?_⟩
    rw [(ContDiffAt.hasFDerivAt_neg_gradient h.contDiffAt).fderiv]
    exact h.isInvertible_neg_hessianOperator
  · rintro ⟨hf, hzero, hinv⟩
    rw [(ContDiffAt.hasFDerivAt_neg_gradient hf).fderiv,
      isInvertible_neg_hessianOperator_iff] at hinv
    rw [isNondegenerateCriticalPoint_iff_gradient]
    refine ⟨hf, ?_, hinv⟩
    simpa only [Pi.neg_apply, neg_eq_zero] using hzero

end TauCeti
