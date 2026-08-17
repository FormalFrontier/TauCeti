/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# Comodules with a group-like basis

A basis `b` of a module `M` together with a family `c` of group-like elements of a coalgebra `C`
determines a right `C`-comodule structure on `M`, namely the linear extension of

```text
b x ↦ b x ⊗ c x.
```

The comodule axioms hold entry by entry: coassociativity is `Δ(c x) = c x ⊗ c x` and the counit
law is `ε(c x) = 1`, which is exactly what group-likeness says. Its coefficient matrix in the
basis `b` is the diagonal matrix of the `c x`.

When `C = R[G]` is the coordinate Hopf algebra of a diagonalizable group `D(G)` and
`c x = single (wt x) 1` for a weight function `wt`, this is the representation of `D(G)` acting on
the `x`-th basis vector through the character `wt x`; the basis vectors then lie in the weight
submodules of `TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic`. Every comodule over a
group algebra is of this form, so this is the converse of the weight decomposition proved there:
that file splits a comodule into weight spaces, and this one builds a comodule out of a
prescribed weight function on a basis.

## Main declarations

* `TauCeti.Comodule.ofGroupLike`: the comodule structure with prescribed group-like eigenvalues
  on a basis.
* `TauCeti.Comodule.ofWeights`: its specialization to a group algebra, given by a weight function.

## Main results

* `TauCeti.Comodule.coefficientMatrix_ofGroupLike`: the coefficient matrix of a group-like basis
  is diagonal.
* `TauCeti.Comodule.basis_mem_weightSpace_ofWeights`: the `x`-th basis vector has weight `wt x`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
* J. S. Milne, *Algebraic Groups* (2017), §12.c.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace Comodule

variable {R : Type u} {C : Type v} {M : Type w} {η : Type x}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M]

/-! ## The comodule attached to a group-like basis -/

/-- The right `C`-comodule structure on a free module which sends each basis vector `b x` to
`b x ⊗ c x`, for a prescribed family `c` of group-like elements of `C`.

Group-likeness of `c x` is exactly the pair of comodule axioms evaluated at `b x`. -/
@[instance_reducible] noncomputable def ofGroupLike (b : Module.Basis η R M) (c : η → C)
    (hc : ∀ x, IsGroupLikeElem R (c x)) : Comodule R C M where
  coact := b.constr R fun x => b x ⊗ₜ[R] c x
  coassoc := by
    refine b.ext fun x => ?_
    simp [Module.Basis.constr_basis, (hc x).comul_eq_tmul_self]
  lTensor_counit_comp_coact := by
    refine b.ext fun x => ?_
    simp [Module.Basis.constr_basis, (hc x).counit_eq_one]

/-- The coaction of `ofGroupLike` on a basis vector. -/
@[simp]
theorem ofGroupLike_coact_basis (b : Module.Basis η R M) (c : η → C)
    (hc : ∀ x, IsGroupLikeElem R (c x)) (x : η) :
    (ofGroupLike b c hc).coact (b x) = b x ⊗ₜ[R] c x :=
  b.constr_basis R _ x

/-- The coaction of `ofGroupLike` on an arbitrary vector expands its coordinates. -/
theorem ofGroupLike_coact (b : Module.Basis η R M) (c : η → C)
    (hc : ∀ x, IsGroupLikeElem R (c x)) (m : M) :
    (ofGroupLike b c hc).coact m = (b.repr m).sum fun x r => r • (b x ⊗ₜ[R] c x) := by
  conv_lhs => rw [← b.linearCombination_repr m]
  rw [Finsupp.linearCombination_apply, map_finsuppSum]
  exact Finsupp.sum_congr fun x _ => by
    rw [map_smul, ofGroupLike_coact_basis]

/-- **The coefficient matrix of a group-like basis is diagonal**, with the prescribed group-like
elements down the diagonal. -/
theorem coefficientMatrix_ofGroupLike [DecidableEq η] (b : Module.Basis η R M) (c : η → C)
    (hc : ∀ x, IsGroupLikeElem R (c x)) :
    letI : Comodule R C M := ofGroupLike b c hc
    coefficientMatrix (C := C) b = Matrix.diagonal c := by
  let : Comodule R C M := ofGroupLike b c hc
  ext i j
  rw [coefficientMatrix_apply, matrixCoefficient_def, ofGroupLike_coact_basis,
    TensorProduct.map_tmul]
  simp only [LinearMap.id_coe, id_eq, TensorProduct.lid_tmul, Module.Basis.coord_apply,
    Module.Basis.repr_self_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [Ne.symm hij, Matrix.diagonal_apply_ne _ hij]

/-! ## Weights over a group algebra -/

section MonoidAlgebra

variable {G : Type*}

/-- The right `R[G]`-comodule structure on a free module determined by a weight function on a
basis: the basis vector `b x` is acted on through the character `wt x`.

This is the representation of the diagonalizable group `D(G)` which is diagonal in the basis `b`
with the prescribed weights. -/
@[instance_reducible] noncomputable def ofWeights (b : Module.Basis η R M) (wt : η → G) :
    Comodule R (MonoidAlgebra R G) M :=
  ofGroupLike b (fun x => MonoidAlgebra.single (wt x) 1) fun _ =>
    MonoidAlgebra.isGroupLikeElem_single_one _

/-- The coaction of `ofWeights` on a basis vector.

This is not a `simp` lemma: `ofWeights` unfolds to `ofGroupLike`, whose corresponding lemma is
the simp normal form. -/
theorem ofWeights_coact_basis (b : Module.Basis η R M) (wt : η → G) (x : η) :
    (ofWeights b wt).coact (b x) = b x ⊗ₜ[R] MonoidAlgebra.single (wt x) (1 : R) :=
  ofGroupLike_coact_basis b _ _ x

/-- **The `x`-th basis vector of `ofWeights` has weight `wt x`.** -/
theorem basis_mem_weightSpace_ofWeights (b : Module.Basis η R M) (wt : η → G) (x : η) :
    letI : Comodule R (MonoidAlgebra R G) M := ofWeights b wt
    b x ∈ weightSpace R G M (wt x) := by
  let : Comodule R (MonoidAlgebra R G) M := ofWeights b wt
  rw [mem_weightSpace]
  exact ofWeights_coact_basis b wt x

/-- The coefficient matrix of `ofWeights` is the diagonal matrix of the characters. -/
theorem coefficientMatrix_ofWeights [DecidableEq η] (b : Module.Basis η R M) (wt : η → G) :
    letI : Comodule R (MonoidAlgebra R G) M := ofWeights b wt
    coefficientMatrix (C := MonoidAlgebra R G) b =
      Matrix.diagonal fun x => MonoidAlgebra.single (wt x) (1 : R) :=
  coefficientMatrix_ofGroupLike b _ _

end MonoidAlgebra

end Comodule

end TauCeti
