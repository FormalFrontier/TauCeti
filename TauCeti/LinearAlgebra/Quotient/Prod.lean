/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Quotients by products of submodules

The quotient by a product submodule is the product of the two quotients:

`(M × N) ⧸ p.prod q ≃ₗ (M ⧸ p) × (N ⧸ q)`.

Mathlib has the additive-group form of the second statement,
`QuotientAddGroup.prodAddEquiv`; `quotientProdEquiv` below refines it with the scalar action,
which is the form module-theoretic consumers need. There is no submodule form upstream.

## Main declarations

* `Submodule.quotientProdEquiv`: `(M × N) ⧸ p.prod q ≃ₗ (M ⧸ p) × (N ⧸ q)`.
* `Submodule.finrank_quotient_prod`: the ranks of the quotients add.
-/

public section

namespace Submodule

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

/- `Submodule.Quotient` is definitionally the corresponding additive quotient, but their inferred
additive structures are not interchangeable at rewrite transparency. Mathlib therefore has no
typed equality that directly transports the two `prodAddEquiv` computation lemmas to submodule
quotients. Isolate that unavoidable definitional conversion here, once for both directions; the
public lemmas below depend only on this named bridge. -/
private theorem quotientProdEquiv_mk_bridge (p : Submodule R M) (q : Submodule R N) :
    (∀ x : M × N,
      quotientProdEquiv p q (Submodule.Quotient.mk x) =
        (Submodule.Quotient.mk x.1, Submodule.Quotient.mk x.2)) ∧
    (∀ (x : M) (y : N),
      (quotientProdEquiv p q).symm (Submodule.Quotient.mk x, Submodule.Quotient.mk y) =
        Submodule.Quotient.mk (x, y)) := by
  constructor
  · intro x
    convert QuotientAddGroup.prodAddEquiv_apply p.toAddSubgroup q.toAddSubgroup
      (Quotient.mk'' x) using 1 <;> rfl
  · intro x y
    convert QuotientAddGroup.prodAddEquiv_symm_apply p.toAddSubgroup q.toAddSubgroup
      (Quotient.mk'' x, Quotient.mk'' y) using 1 <;> rfl

@[simp]
theorem quotientProdEquiv_apply_mk (p : Submodule R M) (q : Submodule R N) (x : M × N) :
    quotientProdEquiv p q (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x.1, Submodule.Quotient.mk x.2) :=
  (quotientProdEquiv_mk_bridge p q).1 x

@[simp]
theorem quotientProdEquiv_symm_apply_mk
    (p : Submodule R M) (q : Submodule R N) (x : M) (y : N) :
    (quotientProdEquiv p q).symm (Submodule.Quotient.mk x, Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x, y) :=
  (quotientProdEquiv_mk_bridge p q).2 x y

/-- The quotient by a product of submodules has rank the sum of the two quotients' ranks. -/
@[simp]
theorem finrank_quotient_prod {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [StrongRankCondition R]
    (p : Submodule R M) (q : Submodule R N)
    [Module.Free R (M ⧸ p)] [Module.Free R (N ⧸ q)]
    [Module.Finite R (M ⧸ p)] [Module.Finite R (N ⧸ q)] :
    Module.finrank R ((M × N) ⧸ p.prod q)
      = Module.finrank R (M ⧸ p) + Module.finrank R (N ⧸ q) := by
  rw [(quotientProdEquiv p q).finrank_eq, Module.finrank_prod]

end Quotient

end Submodule
