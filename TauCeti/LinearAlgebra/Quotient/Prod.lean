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

## Main declarations

* `Submodule.quotientProdEquiv`: `(M × N) ⧸ p.prod q ≃ₗ (M ⧸ p) × (N ⧸ q)`.
* `Submodule.finrank_quotient_prod`: the ranks of the quotients add.
-/

public section

namespace Submodule

section Quotient

variable {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]

private theorem ker_prod_mkQ (p : Submodule R M) (q : Submodule R N) :
    LinearMap.ker (p.mkQ.prodMap q.mkQ) = p.prod q := by
  simp

private noncomputable def quotientProdMap (p : Submodule R M) (q : Submodule R N) :
    ((M × N) ⧸ p.prod q) →ₗ[R] (M ⧸ p) × (N ⧸ q) :=
  (p.prod q).liftQ (p.mkQ.prodMap q.mkQ) (ker_prod_mkQ p q).ge

@[simp]
private theorem quotientProdMap_apply_mk
    (p : Submodule R M) (q : Submodule R N) (x : M × N) :
    quotientProdMap p q (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x.1, Submodule.Quotient.mk x.2) := by
  simp [quotientProdMap]

private theorem quotientProdMap_bijective (p : Submodule R M) (q : Submodule R N) :
    Function.Bijective (quotientProdMap p q) := by
  constructor
  · exact LinearMap.ker_eq_bot.mp
      (Submodule.ker_liftQ_eq_bot (p.prod q) (p.mkQ.prodMap q.mkQ)
        (ker_prod_mkQ p q).ge (ker_prod_mkQ p q).le)
  · rintro ⟨⟨x⟩, ⟨y⟩⟩
    refine ⟨(p.prod q).mkQ (x, y), ?_⟩
    exact quotientProdMap_apply_mk p q (x, y)

/-- The quotient by a product of submodules is the product of the quotients.

This is the module analogue of `QuotientAddGroup.prodAddEquiv`. It is built directly from
`Submodule.mkQ` and `Submodule.liftQ`, so its computation rules remain in the submodule quotient
API. -/
noncomputable def quotientProdEquiv (p : Submodule R M) (q : Submodule R N) :
    ((M × N) ⧸ p.prod q) ≃ₗ[R] (M ⧸ p) × (N ⧸ q) :=
  LinearEquiv.ofBijective (quotientProdMap p q) (quotientProdMap_bijective p q)

@[simp]
theorem quotientProdEquiv_apply_mk (p : Submodule R M) (q : Submodule R N) (x : M × N) :
    quotientProdEquiv p q (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x.1, Submodule.Quotient.mk x.2) := by
  rw [quotientProdEquiv, LinearEquiv.ofBijective_apply, quotientProdMap_apply_mk]

@[simp]
theorem quotientProdEquiv_symm_apply_mk
    (p : Submodule R M) (q : Submodule R N) (x : M) (y : N) :
    (quotientProdEquiv p q).symm (Submodule.Quotient.mk x, Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x, y) := by
  rw [LinearEquiv.symm_apply_eq]
  exact (quotientProdEquiv_apply_mk p q (x, y)).symm

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
