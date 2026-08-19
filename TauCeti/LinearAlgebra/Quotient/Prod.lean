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

Mathlib has the additive-group form of this statement,
`QuotientAddGroup.prodAddEquiv`; `quotientProdEquiv` below records the analogous scalar-compatible
equivalence, which is the form module-theoretic consumers need. There is no submodule form upstream.

The additive equivalence cannot simply be transported. It is stated for
`p.toAddSubgroup.prod q.toAddSubgroup`, whose quotient carries `QuotientAddGroup.Quotient.addGroup`,
whereas `(M × N) ⧸ p.prod q` carries `Submodule.Quotient.addCommMonoid`. Feeding it to
`AddEquiv.toLinearEquiv` elaborates, but the resulting term is not type-correct at instance
transparency: neither `AddEquiv.coe_toLinearEquiv` nor `QuotientAddGroup.prodAddEquiv_apply`
rewrites in the characteristic lemmas, which are then provable only by bare `rfl` through the
wrappers. `quotientProdEquiv` is therefore assembled from `Submodule.liftQ` and `LinearMap.coprod`,
which keeps its computation rules inside the `Submodule` API.

## Main declarations

* `Submodule.quotientProdEquiv`: `(M × N) ⧸ p.prod q ≃ₗ (M ⧸ p) × (N ⧸ q)`.
* `Submodule.finrank_quotient_prod`: the ranks of the quotients add.
-/

public section

namespace Submodule

section Quotient

variable {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]

private theorem ker_prodMap_mkQ (p : Submodule R M) (q : Submodule R N) :
    LinearMap.ker (p.mkQ.prodMap q.mkQ) = p.prod q := by
  simp

private def quotientProdMap (p : Submodule R M) (q : Submodule R N) :
    ((M × N) ⧸ p.prod q) →ₗ[R] (M ⧸ p) × (N ⧸ q) :=
  (p.prod q).liftQ (p.mkQ.prodMap q.mkQ) (ker_prodMap_mkQ p q).ge

@[simp]
private theorem quotientProdMap_apply_mk
    (p : Submodule R M) (q : Submodule R N) (x : M × N) :
    quotientProdMap p q (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x.1, Submodule.Quotient.mk x.2) := by
  simp [quotientProdMap]

private def quotientProdInvMap (p : Submodule R M) (q : Submodule R N) :
    (M ⧸ p) × (N ⧸ q) →ₗ[R] ((M × N) ⧸ p.prod q) :=
  LinearMap.coprod
    (p.liftQ ((p.prod q).mkQ.comp (LinearMap.inl R M N)) (by
      intro x hx
      simp [LinearMap.mem_ker, hx]))
    (q.liftQ ((p.prod q).mkQ.comp (LinearMap.inr R M N)) (by
      intro y hy
      simp [LinearMap.mem_ker, hy]))

private theorem quotientProdInvMap_apply_mk
    (p : Submodule R M) (q : Submodule R N) (x : M) (y : N) :
    quotientProdInvMap p q (Submodule.Quotient.mk x, Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x, y) := by
  simp only [quotientProdInvMap, LinearMap.coprod_apply, liftQ_apply, LinearMap.coe_comp,
    LinearMap.coe_inl, Function.comp_apply, mkQ_apply, LinearMap.coe_inr]
  rw [← Submodule.Quotient.mk_add]
  simp

private theorem quotientProdInvMap_comp_quotientProdMap
    (p : Submodule R M) (q : Submodule R N) :
    (quotientProdInvMap p q).comp (quotientProdMap p q) = LinearMap.id := by
  ext x <;> simp [LinearMap.comp_apply, quotientProdInvMap]

private theorem quotientProdMap_comp_quotientProdInvMap
    (p : Submodule R M) (q : Submodule R N) :
    (quotientProdMap p q).comp (quotientProdInvMap p q) = LinearMap.id := by
  ext x <;> simp [LinearMap.comp_apply, quotientProdInvMap]

/-- The quotient by a product of submodules is the product of the quotients.

This is the module analogue of `QuotientAddGroup.prodAddEquiv`. Its action and inverse action on
quotient representatives are recorded by `quotientProdEquiv_apply_mk` and
`quotientProdEquiv_symm_apply_mk`. -/
def quotientProdEquiv (p : Submodule R M) (q : Submodule R N) :
    ((M × N) ⧸ p.prod q) ≃ₗ[R] (M ⧸ p) × (N ⧸ q) :=
  LinearEquiv.ofLinearMap
    (quotientProdMap p q)
    (quotientProdInvMap p q)
    (quotientProdMap_comp_quotientProdInvMap p q)
    (quotientProdInvMap_comp_quotientProdMap p q)

@[simp]
theorem quotientProdEquiv_apply_mk (p : Submodule R M) (q : Submodule R N) (x : M × N) :
    quotientProdEquiv p q (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x.1, Submodule.Quotient.mk x.2) := by
  rw [quotientProdEquiv, LinearEquiv.coe_ofLinearMap, quotientProdMap_apply_mk]

@[simp]
theorem quotientProdEquiv_symm_apply_mk
    (p : Submodule R M) (q : Submodule R N) (x : M) (y : N) :
    (quotientProdEquiv p q).symm (Submodule.Quotient.mk x, Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x, y) := by
  rw [quotientProdEquiv, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap,
    quotientProdInvMap_apply_mk]

/-- The quotient by a product of submodules has rank the sum of the two quotients' ranks. -/
@[simp]
theorem finrank_quotient_prod [StrongRankCondition R] (p : Submodule R M) (q : Submodule R N)
    [Module.Free R (M ⧸ p)] [Module.Free R (N ⧸ q)]
    [Module.Finite R (M ⧸ p)] [Module.Finite R (N ⧸ q)] :
    Module.finrank R ((M × N) ⧸ p.prod q)
      = Module.finrank R (M ⧸ p) + Module.finrank R (N ⧸ q) := by
  rw [(quotientProdEquiv p q).finrank_eq, Module.finrank_prod]

end Quotient

end Submodule
