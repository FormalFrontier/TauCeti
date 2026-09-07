/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction

/-!
# The contraction equivalence is the contraction map

For a finite projective module `M`, Mathlib's contraction equivalence
`dualTensorHomEquiv R M N : Module.Dual R M ⊗[R] N ≃ₗ[R] M →ₗ[R] N` is built as
`LinearEquiv.ofBijective` of the contraction `dualTensorHom R M N`, so the two agree on the nose.
Mathlib records this identification for the basis-dependent companion
`dualTensorHomEquivOfBasis` (`dualTensorHomEquivOfBasis_apply`,
`coe_dualTensorHomEquivOfBasis`) but states no such lemma for `dualTensorHomEquiv` itself. This
file supplies it, so that proofs can pass between the equivalence and the contraction — for
instance to combine `LinearEquiv.apply_symm_apply` with the `dualTensorHom_apply` computation on
pure tensors — without unfolding the implementation of the equivalence.

## Main results

* `TauCeti.dualTensorHomEquiv_apply`: the forward map of the contraction equivalence is the
  contraction `dualTensorHom`.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N] [Module.Finite R M] [Module.Projective R M]

/-- The forward map of the contraction equivalence `M^* ⊗ N ≃ₗ[R] (M →ₗ[R] N)` is the contraction
`dualTensorHom` itself. -/
theorem dualTensorHomEquiv_apply (z : Module.Dual R M ⊗[R] N) :
    dualTensorHomEquiv R M N z = dualTensorHom R M N z :=
  (rfl)

end TauCeti
