/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Evaluating the first isomorphism theorem on a class

Mathlib packages the first isomorphism theorem for a surjective homomorphism `φ : G →* M` as
`QuotientGroup.quotientKerEquivOfSurjective φ hφ : G ⧸ φ.ker ≃* M`. It is defined through
`QuotientGroup.quotientKerEquivOfRightInverse` applied to a right inverse extracted from `hφ`
by choice, so evaluating it on a class otherwise means unfolding that noncomputable
implementation.

This file records the computation rule on classes, so that users never have to. It is the
group-theoretic counterpart of Mathlib's `RingHom.quotientKerEquivOfSurjective_apply_mk`, and
belongs beside `QuotientGroup.quotientKerEquivOfSurjective` in Mathlib.

## Main statements

* `TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk`: the isomorphism
  `G ⧸ φ.ker ≃* M` sends the class of `g` to `φ g`.
-/

public section

namespace TauCeti

namespace QuotientGroup

variable {G M : Type*} [Group G] [Group M] (φ : G →* M) (hφ : Function.Surjective φ)

/-- The first isomorphism theorem for a surjective homomorphism sends the class of `g` to
`φ g`. -/
@[simp]
theorem quotientKerEquivOfSurjective_apply_mk (g : G) :
    _root_.QuotientGroup.quotientKerEquivOfSurjective φ hφ (_root_.QuotientGroup.mk g) = φ g :=
  rfl

end QuotientGroup

end TauCeti
