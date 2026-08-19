/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Products of submodules

A product submodule `p.prod q : Submodule R (M × N)` is, as a module, the product `p × q`.

## Main declaration

* `Submodule.prodEquiv`: `↥(p.prod q) ≃ₗ p × q`.
-/

public section

namespace Submodule

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N]

/-- A product submodule, as a module, is the product of the two submodules.

This is the linear refinement of `AddSubmonoid.prodEquiv`. -/
def prodEquiv (p : Submodule R M) (q : Submodule R N) : ↥(p.prod q) ≃ₗ[R] p × q :=
  { Equiv.Set.prod (p : Set M) (q : Set N) with
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

@[simp]
theorem prodEquiv_apply (p : Submodule R M) (q : Submodule R N) (x : ↥(p.prod q)) :
    prodEquiv p q x = (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩) :=
  (rfl)

@[simp]
theorem prodEquiv_symm_apply (p : Submodule R M) (q : Submodule R N) (x : p × q) :
    (prodEquiv p q).symm x = ⟨(x.1.1, x.2.1), x.1.2, x.2.2⟩ :=
  (rfl)

end Submodule
