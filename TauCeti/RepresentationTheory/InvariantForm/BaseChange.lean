/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.InvariantForm

/-!
# Base change of an invariant bilinear form

Extending the scalars of a representation along an algebra `R → A` extends the scalars of its
invariant forms: the base change `LinearMap.BilinForm.baseChange` of an invariant form is invariant
for the base-changed representation `Representation.baseChange`.  Invariance is elementwise the
statement that each `ρ g` is an isometry of the form, so this is
`TauCeti.BilinForm.IsIsometry.baseChange` applied one group element at a time.

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

/-- **The base change of an invariant form is invariant** for the base-changed representation:
each base-changed action `(σ g).baseChange A` is an isometry of the base-changed form, by
`TauCeti.BilinForm.IsIsometry.baseChange`. -/
theorem IsInvariantForm.baseChange {σ : Representation R G W} {B : BilinForm R W}
    (hB : IsInvariantForm σ B) :
    IsInvariantForm (Representation.baseChange A σ) (B.baseChange A) := by
  rw [isInvariantForm_iff_isIsometry]
  intro g
  simpa only [Representation.baseChange_apply] using (hB.isIsometry g).baseChange A

end Representation

end TauCeti
