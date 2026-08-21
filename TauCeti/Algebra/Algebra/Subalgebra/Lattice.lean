/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# What `Algebra.botEquivOfInjective` does to an element

For an injective `algebraMap R A`, `Algebra.botEquivOfInjective` identifies the bottom subalgebra
`⊥` of `A` with `R`. Mathlib states it without `@[simps]` — unlike `Algebra.botEquiv`, which
carries `@[simps! symm_apply]` — so nothing names its value on an element. This file supplies the
equation in the direction a caller needs: applying `algebraMap R A` to the result returns the
element itself.

## Main results

* `Algebra.algebraMap_botEquivOfInjective`: `algebraMap R A (botEquivOfInjective h x) = x` for
  `x : (⊥ : Subalgebra R A)`.
-/

public section

namespace Algebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- **`algebraMap R A` undoes `botEquivOfInjective`.** The equiv sends an element of `⊥` to the
scalar it comes from, so mapping that scalar back into `A` returns the element.

The proof is the inverse equiv's `AlgEquiv.commutes`, read through `Subalgebra.coe_algebraMap`. -/
@[simp]
theorem algebraMap_botEquivOfInjective (h : Function.Injective (algebraMap R A))
    (x : (⊥ : Subalgebra R A)) : algebraMap R A (botEquivOfInjective h x) = (x : A) := by
  have hx := (botEquivOfInjective h).symm.commutes (botEquivOfInjective h x)
  simp only [algebraMap_self_apply, AlgEquiv.symm_apply_apply] at hx
  conv_rhs => rw [hx]
  exact (Subalgebra.coe_algebraMap _ _).symm

end Algebra

end
