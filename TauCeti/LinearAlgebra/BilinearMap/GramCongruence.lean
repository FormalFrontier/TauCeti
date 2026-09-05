/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Determinant

/-!
# Change of basis for the matrix of a bilinear map with values outside the scalars

Mathlib's `LinearMap.toMatrix₂_mul_basis_toMatrix` records how the matrix of a bilinear map
responds to a change of basis, but it is stated for `B : M₁ →ₗ[R] M₂ →ₗ[R] R`, whose values are
the scalars themselves. A bilinear map valued in an `R`-algebra `S` has no such lemma, because its
matrix has entries in `S` while a change-of-basis matrix has entries in `R`; the two are related
only after pushing the latter along `algebraMap R S`. That is what this file supplies, for
`LinearMap.toMatrix₂Aux`, the combinator whose target is the map's own codomain.

## Main results

* `LinearMap.toMatrix₂Aux_comp_index`: precomposing the index families takes a submatrix, of
  which reindexing a basis is the special case. Stated at the full sesquilinear generality
  `LinearMap.toMatrix₂Aux` accepts, since the equality is definitional.
* `LinearMap.toMatrix₂Aux_mul_map_basis_toMatrix`: the change-of-basis law, oriented as Mathlib's
  is, with the change-of-basis matrices pushed into the codomain. The codomain need only be a
  possibly noncommutative semiring.
* `LinearMap.det_toMatrix₂Aux_eq_det_toMatrix₂Aux`: for a map on a single `ℤ`-module, the signed
  determinant of the matrix is independent of the basis, and of its index type. An integral
  change-of-basis matrix has determinant `±1`, so the congruence above multiplies the determinant
  by its square, namely `1`. This needs `CommRing S` and **no order**; the absolute-value
  statement is `congrArg abs` away and is left to the caller.

The scalar ring `R` is a commutative semiring throughout; the three statements differ in what
they ask of the codomain. `toMatrix₂Aux_comp_index` needs only an additive commutative monoid
carrying an `R`-action, and accepts sesquilinear maps. The change-of-basis law needs an
`R`-algebra, which may be a **noncommutative** semiring: the proof uses only that the images of
`algebraMap` are central. The determinant result needs a commutative ring, and `ℤ` as the
scalars.

## Implementation notes

`TauCeti/LinearAlgebra/IntegralLattice/Gram.lean` carries the same mathematics for an *integral*
form — `gramMatrix`, `gramMatrix_reindex`, `gramDet_eq_gramDet`, `determinant`, `discriminant` —
with the same argument about integral change-of-basis matrices having determinant `±1`. That
development is `ℤ`-valued: its Gram matrix has entries in the scalars, so it cannot serve a map
valued in a larger codomain, which is the gap filled here.
-/

public section

open Matrix

namespace LinearMap

section CompIndex

variable {R R₁ S₁ R₂ S₂ M₁ M₂ N₂ n m n' m' : Type*} [CommSemiring R] [Semiring R₁] [Semiring S₁]
  [Semiring R₂] [Semiring S₂] [AddCommMonoid M₁] [Module R₁ M₁] [AddCommMonoid M₂] [Module R₂ M₂]
  [AddCommMonoid N₂] [Module R N₂] [Module S₁ N₂] [Module S₂ N₂] [SMulCommClass S₁ R N₂]
  [SMulCommClass S₂ R N₂] [SMulCommClass S₂ S₁ N₂] {σ₁ : R₁ →+* S₁} {σ₂ : R₂ →+* S₂}

/-- **Precomposing the index families with any maps takes a submatrix.** Reindexing a basis is
the special case where the maps are the inverses of equivalences, since `Module.Basis.coe_reindex`
puts `b.reindex σ` into the form `b ∘ σ.symm`. Stated for the sesquilinear maps
`LinearMap.toMatrix₂Aux` accepts, the equality being definitional. -/
@[simp]
theorem toMatrix₂Aux_comp_index (B : M₁ →ₛₗ[σ₁] M₂ →ₛₗ[σ₂] N₂) (v₁ : n → M₁) (v₂ : m → M₂)
    (e₁ : n' → n) (e₂ : m' → m) :
    toMatrix₂Aux R (v₁ ∘ e₁) (v₂ ∘ e₂) B = (toMatrix₂Aux R v₁ v₂ B).submatrix e₁ e₂ :=
  rfl

end CompIndex

section BasisChange

variable {R S M₁ M₂ ι₁ ι₂ ι₁' ι₂' : Type*} [CommSemiring R] [AddCommMonoid M₁] [Module R M₁]
  [AddCommMonoid M₂] [Module R M₂] [Semiring S] [Algebra R S]

/-- **The change-of-basis law for the matrix of a bilinear map valued outside the scalars.** The
change-of-basis matrices enter through `algebraMap R S`, since the matrix of `B` has entries in
`S`. Compare `LinearMap.toMatrix₂_mul_basis_toMatrix`, which is the case `S = R`. The codomain
need not be commutative: the images of `algebraMap` are central, which is all the proof uses. -/
@[simp]
theorem toMatrix₂Aux_mul_map_basis_toMatrix [Fintype ι₁] [Fintype ι₂] (B : M₁ →ₗ[R] M₂ →ₗ[R] S)
    (b₁ : Module.Basis ι₁ R M₁) (b₂ : Module.Basis ι₂ R M₂) (c₁ : Module.Basis ι₁' R M₁)
    (c₂ : Module.Basis ι₂' R M₂) :
    ((b₁.toMatrix c₁).map (algebraMap R S))ᵀ * toMatrix₂Aux R (b₁ : ι₁ → M₁) (b₂ : ι₂ → M₂) B *
        ((b₂.toMatrix c₂).map (algebraMap R S)) =
      toMatrix₂Aux R (c₁ : ι₁' → M₁) (c₂ : ι₂' → M₂) B := by
  ext i j
  simp only [toMatrix₂Aux_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Module.Basis.toMatrix_apply, Finset.sum_mul]
  -- Expand `B` over `b₁` and `b₂` with Mathlib's basis expansion, then align the two double
  -- sums: the matrix side sums over the second index outermost, the expansion over the first.
  rw [← LinearMap.sum_repr_mul_repr_mul b₁ b₂ (c₁ i) (c₂ j),
    Finsupp.sum_fintype _ _ fun _ ↦ by simp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finsupp.sum_fintype _ _ fun _ ↦ by simp]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  -- The second coordinate's scalar has to cross `B (b₁ k) (b₂ l)`, which `Algebra.commutes` does.
  simp only [Algebra.smul_def]
  rw [mul_assoc, ← Algebra.commutes]

end BasisChange

section Determinant

variable {S M ι ι' : Type*} [CommRing S] [AddCommGroup M] [Module ℤ M]

/-- **Over `ℤ`, the determinant of the matrix is basis-independent**, and independent of the index
type too. An integral change-of-basis matrix has determinant `±1`, so the congruence of
`toMatrix₂Aux_mul_map_basis_toMatrix` multiplies the determinant by its square, namely `1`. -/
theorem det_toMatrix₂Aux_eq_det_toMatrix₂Aux [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (B : M →ₗ[ℤ] M →ₗ[ℤ] S) (b : Module.Basis ι ℤ M)
    (b' : Module.Basis ι' ℤ M) :
    (toMatrix₂Aux ℤ (b' : ι' → M) (b' : ι' → M) B).det =
      (toMatrix₂Aux ℤ (b : ι → M) (b : ι → M) B).det := by
  -- Transport `b` along `b.indexEquiv b'` so both bases share one index type; reindexing only
  -- permutes the matrix, which leaves its determinant alone.
  set c := b.reindex (b.indexEquiv b') with hc
  have hcb : (toMatrix₂Aux ℤ (c : ι' → M) (c : ι' → M) B).det =
      (toMatrix₂Aux ℤ (b : ι → M) (b : ι → M) B).det := by
    rw [hc]
    simp [Module.Basis.coe_reindex, Matrix.det_submatrix_equiv_self]
  have hcast : ((c.toMatrix b').map (algebraMap ℤ S)).det = ((c.toMatrix b').det : S) := by
    simp [algebraMap_int_eq, ← Int.cast_det]
  have hu : IsUnit ((c.toMatrix b').det) := by
    simpa [Module.Basis.det_apply] using c.isUnit_det b'
  rw [← hcb, ← toMatrix₂Aux_mul_map_basis_toMatrix B c c b' b', Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, hcast]
  rcases Int.isUnit_eq_one_or hu with h | h <;> rw [h] <;> simp [mul_comm]

end Determinant

end LinearMap
