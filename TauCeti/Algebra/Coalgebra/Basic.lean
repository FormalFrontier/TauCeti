/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Elements whose comultiplication is a single tensor

If the comultiplication of an element `a` of a coalgebra is the pure tensor `a ⊗ c`, then the
counit law `(ε ⊗ id) ∘ Δ = id` collapses the coalgebra structure at `a`: applying it to
`Δ a = a ⊗ c` gives `a = ε(a) • c`. In particular an element fixed by the regular coaction,
`Δ a = a ⊗ 1`, is the scalar multiple `ε(a) • 1` of the identity.

## Main declarations

* `TauCeti.Coalgebra.eq_counit_smul_of_comul_eq_tmul`: `Δ a = a ⊗ c` implies `a = ε(a) • c`.

## References

* M. E. Sweedler, *Hopf Algebras*, Chapter 1.
-/

public section

open scoped TensorProduct

namespace TauCeti.Coalgebra

universe u v

variable {R : Type u} {A : Type v}
variable [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]

/-- An element whose comultiplication is the pure tensor `a ⊗ c` is the scalar multiple of `c` by
its counit. -/
theorem eq_counit_smul_of_comul_eq_tmul {a c : A}
    (h : Coalgebra.comul (R := R) a = a ⊗ₜ[R] c) :
    a = Coalgebra.counit (R := R) a • c := by
  have hc := congrArg ((Coalgebra.counit (R := R) (A := A)).rTensor A) h
  rw [Coalgebra.rTensor_counit_comul, LinearMap.rTensor_tmul] at hc
  simpa using congrArg (TensorProduct.lid R A) hc

end TauCeti.Coalgebra
