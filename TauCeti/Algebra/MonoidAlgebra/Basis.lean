/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# The coordinates of the standard basis of a monoid algebra

Mathlib defines the standard basis `MonoidAlgebra.basis X k` of `k[X]` by
`repr := MonoidAlgebra.coeffLinearEquiv _` but records no lemma for the resulting `repr`. This
file is that missing bridge: the coordinates in the standard basis are the coefficients.

It is all that is needed for the generic basis API -- `Module.Basis.coe_sumCoords`,
`Module.Basis.sumCoords_self_apply`, `LinearMap.toMatrix_apply` -- to compute in terms of
`MonoidAlgebra.coeff`.

## Main statements

* `TauCeti.MonoidAlgebra.basis_repr`: the coordinates of `k[X]` in the standard basis are the
  coefficients.
-/

public section

namespace TauCeti

/-- The coordinates of `k[X]` in the standard basis are the coefficients. -/
@[simp]
theorem MonoidAlgebra.basis_repr {k : Type*} [Semiring k] {X : Type*} (v : MonoidAlgebra k X) :
    (MonoidAlgebra.basis X k).repr v = v.coeff :=
  rfl

end TauCeti
