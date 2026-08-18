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

/-- The quotient by a product of submodules is the product of the quotients.

This is the module analogue of `QuotientAddGroup.prodAddEquiv`. It is built directly from
`Submodule.mkQ` and `Submodule.liftQ`, so its computation rules remain in the submodule quotient
API. -/
noncomputable def quotientProdEquiv (p : Submodule R M) (q : Submodule R N) :
    ((M × N) ⧸ p.prod q) ≃ₗ[R] (M ⧸ p) × (N ⧸ q) := by
  let f : M × N →ₗ[R] (M ⧸ p) × (N ⧸ q) := p.mkQ.prodMap q.mkQ
  have hker : LinearMap.ker f = p.prod q := by
    simp [f]
  let g : ((M × N) ⧸ p.prod q) →ₗ[R] (M ⧸ p) × (N ⧸ q) :=
    (p.prod q).liftQ f hker.ge
  refine LinearEquiv.ofBijective g ⟨?_, ?_⟩
  · exact LinearMap.ker_eq_bot.mp
      (Submodule.ker_liftQ_eq_bot (p.prod q) f hker.ge hker.le)
  · rintro ⟨⟨x⟩, ⟨y⟩⟩
    refine ⟨(p.prod q).mkQ (x, y), ?_⟩
    simp only [g, Submodule.mkQ_apply, Submodule.liftQ_apply, f, LinearMap.prodMap_apply,
      Submodule.Quotient.quot_mk_eq_mk]

@[simp]
theorem quotientProdEquiv_apply_mk (p : Submodule R M) (q : Submodule R N) (x : M × N) :
    quotientProdEquiv p q (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x.1, Submodule.Quotient.mk x.2) := by
  have hker : LinearMap.ker (p.mkQ.prodMap q.mkQ) = p.prod q := by
    simp
  change (p.prod q).liftQ (p.mkQ.prodMap q.mkQ) hker.ge (Submodule.Quotient.mk x) = _
  simp

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
