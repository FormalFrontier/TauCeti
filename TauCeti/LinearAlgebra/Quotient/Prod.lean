/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Products of submodules and their quotients

A product submodule `p.prod q ≤ M × N` is, as a module, the product `p × q`, and the quotient by
it is the product of the two quotients:

`(M × N) ⧸ p.prod q ≃ₗ (M ⧸ p) × (N ⧸ q)`.

Mathlib has the additive-group form of the second statement,
`QuotientAddGroup.prodAddEquiv`; `quotientProdEquiv` below refines it with the scalar action,
which is the form module-theoretic consumers need. There is no submodule form upstream.

## Main declarations

* `Submodule.prodEquiv`: `↥(p.prod q) ≃ₗ p × q`.
* `Submodule.quotientProdEquiv`: `(M × N) ⧸ p.prod q ≃ₗ (M ⧸ p) × (N ⧸ q)`.
* `Submodule.finrank_quotient_prod`: the ranks of the quotients add.
-/

public section

namespace Submodule

section Subtype

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N]

/-- A product submodule, as a module, is the product of the two submodules.

This is the module refinement of `AddSubgroup.prodEquiv`, and is stated here over an arbitrary
semiring and additive commutative monoids, where that additive-group statement does not apply. -/
def prodEquiv (p : Submodule R M) (q : Submodule R N) : ↥(p.prod q) ≃ₗ[R] p × q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun x := ⟨(x.1.1, x.2.1), x.1.2, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem prodEquiv_apply (p : Submodule R M) (q : Submodule R N) (x : ↥(p.prod q)) :
    prodEquiv p q x = (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩) :=
  (rfl)

@[simp]
theorem prodEquiv_symm_apply (p : Submodule R M) (q : Submodule R N) (x : p × q) :
    (prodEquiv p q).symm x = ⟨(x.1.1, x.2.1), x.1.2, x.2.2⟩ :=
  (rfl)

end Subtype

section Quotient

variable {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]

/-- The quotient by a product of submodules is the product of the quotients.

This refines `QuotientAddGroup.prodAddEquiv` with the scalar action; the underlying additive
equivalence, and hence the whole construction, is Mathlib's. -/
def quotientProdEquiv (p : Submodule R M) (q : Submodule R N) :
    ((M × N) ⧸ p.prod q) ≃ₗ[R] (M ⧸ p) × (N ⧸ q) :=
  AddEquiv.toLinearEquiv
    (QuotientAddGroup.prodAddEquiv p.toAddSubgroup q.toAddSubgroup)
    (by rintro r ⟨x⟩; rfl)

@[simp]
theorem quotientProdEquiv_mk (p : Submodule R M) (q : Submodule R N) (x : M × N) :
    quotientProdEquiv p q (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x.1, Submodule.Quotient.mk x.2) :=
  by
    convert QuotientAddGroup.prodAddEquiv_apply p.toAddSubgroup q.toAddSubgroup
      (Quotient.mk'' x) using 1 <;> rfl

@[simp]
theorem quotientProdEquiv_symm_mk (p : Submodule R M) (q : Submodule R N) (x : M) (y : N) :
    (quotientProdEquiv p q).symm (Submodule.Quotient.mk x, Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x, y) :=
  by
    convert QuotientAddGroup.prodAddEquiv_symm_apply p.toAddSubgroup q.toAddSubgroup
      (Quotient.mk'' x, Quotient.mk'' y) using 1 <;> rfl

/-- The quotient by a product of submodules has rank the sum of the two quotients' ranks. -/
theorem finrank_quotient_prod {R M N : Type*} [DivisionRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (p : Submodule R M) (q : Submodule R N)
    [FiniteDimensional R (M ⧸ p)] [FiniteDimensional R (N ⧸ q)] :
    Module.finrank R ((M × N) ⧸ p.prod q)
      = Module.finrank R (M ⧸ p) + Module.finrank R (N ⧸ q) := by
  rw [(quotientProdEquiv p q).finrank_eq, Module.finrank_prod]

end Quotient

end Submodule
