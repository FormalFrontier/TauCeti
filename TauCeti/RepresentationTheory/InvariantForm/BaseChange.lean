/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.InvariantForm

/-!
# Base change of an invariant bilinear form

Extending the scalars of a representation along an algebra `R → A` extends the scalars of its
invariant forms: the base change `LinearMap.BilinForm.baseChange` of an invariant form is invariant
for the base-changed representation `Representation.baseChange`.  Both sides are determined by
their values on pure tensors, where they are the original form and the original action, so the
statement reduces to invariance over `R`.

## Main results

* `TauCeti.Representation.IsInvariantForm.baseChange`: the base change of an invariant form is
  invariant.
-/

public section

open LinearMap (BilinForm)

open scoped TensorProduct

namespace TauCeti

namespace Representation

variable {R A G W : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [Monoid G]
  [AddCommMonoid W] [Module R W]

/-- **The base change of an invariant form is invariant** for the base-changed representation.  The
two base changes are matched on pure tensors, where both are the original form and the original
action, and extended by bilinearity. -/
theorem IsInvariantForm.baseChange {σ : Representation R G W} {B : BilinForm R W}
    (hB : IsInvariantForm σ B) :
    IsInvariantForm (Representation.baseChange A σ) (B.baseChange A) := by
  rw [isInvariantForm_iff]
  intro g u v
  simp only [Representation.baseChange_apply]
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u₁ u₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul a w =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v₁ v₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul a' w' =>
      simp only [LinearMap.baseChange_tmul, BilinForm.baseChange_tmul, hB.apply g w w']

end Representation

end TauCeti
