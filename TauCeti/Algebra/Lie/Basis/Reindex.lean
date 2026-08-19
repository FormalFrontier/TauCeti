/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basis.Basic

/-!
# Renumbering the nodes of a Lie algebra basis

A `LieAlgebra.Basis ι H` is a Chevalley-style presentation of a Lie algebra: a Cartan matrix
indexed by `ι`, three families `h`, `e`, `f` of elements indexed by `ι`, and the relations between
them. Nothing in the structure depends on which index type is used, so a bijection `ι' ≃ ι`
transports the whole package.

This is what lets a construction whose index set arises from the construction itself — Geck's, for
instance, whose nodes are the support of a base, a subtype of the root index type — be read against
an index type fixed in advance, such as `Fin n` in a pinned Bourbaki numbering. The Cartan matrix
is renumbered by `Matrix.submatrix`, so the entry at renumbered nodes is by definition the entry at
the corresponding original nodes and no reindexed copy of the matrix has to be compared with the
original one.

## Main definitions

* `LieAlgebra.Basis.reindex`: the basis obtained by renumbering the nodes along a bijection.
-/

public section

open Function Set

namespace LieAlgebra.Basis

variable {ι ι' R L : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [CommRing R] [LieRing L] [LieAlgebra R L] {H : LieSubalgebra R L}

/-- **Renumber the nodes of a Lie algebra basis along a bijection.** The Cartan matrix is
renumbered by `Matrix.submatrix`, and each of the three families of elements is precomposed with
the bijection. -/
def reindex (b : Basis ι H) (σ : ι' ≃ ι) : Basis ι' H where
  A := b.A.submatrix σ σ
  h := b.h ∘ σ
  e := b.e ∘ σ
  f := b.f ∘ σ
  cartan_eq_lieSpan := by
    rw [σ.surjective.range_comp]
    exact b.cartan_eq_lieSpan
  span_ef := by rw [σ.surjective.range_comp, σ.surjective.range_comp]; exact b.span_ef
  linInd := b.linInd.comp σ σ.injective
  nondegen := by
    rw [Matrix.nondegenerate_iff_det_ne_zero, Matrix.det_submatrix_equiv_self,
      ← Matrix.nondegenerate_iff_det_ne_zero]
    exact b.nondegen
  sl2 i := b.sl2 (σ i)
  lie_h_h i j := b.lie_h_h (σ i) (σ j)
  lie_h_e i j := b.lie_h_e (σ i) (σ j)
  lie_h_f i j := b.lie_h_f (σ i) (σ j)
  lie_e_f_ne i j hij := b.lie_e_f_ne (σ i) (σ j) fun h => hij (σ.injective h)

/-- Reindexing transports the Cartan matrix along the given equivalence. -/
@[simp] theorem reindex_A (b : Basis ι H) (σ : ι' ≃ ι) :
    (b.reindex σ).A = b.A.submatrix σ σ := by
  ext i j
  change b.A (σ i) (σ j) = _
  rw [Matrix.submatrix_apply]

/-- Reindexing precomposes the Cartan generators with the given equivalence. -/
@[simp] theorem reindex_h (b : Basis ι H) (σ : ι' ≃ ι) :
    (b.reindex σ).h = b.h ∘ σ := by
  funext i
  change b.h (σ i) = (b.h ∘ σ) i
  rw [Function.comp_apply]

/-- Reindexing precomposes the raising generators with the given equivalence. -/
@[simp] theorem reindex_e (b : Basis ι H) (σ : ι' ≃ ι) :
    (b.reindex σ).e = b.e ∘ σ := by
  funext i
  change b.e (σ i) = (b.e ∘ σ) i
  rw [Function.comp_apply]

/-- Reindexing precomposes the lowering generators with the given equivalence. -/
@[simp] theorem reindex_f (b : Basis ι H) (σ : ι' ≃ ι) :
    (b.reindex σ).f = b.f ∘ σ := by
  funext i
  change b.f (σ i) = (b.f ∘ σ) i
  rw [Function.comp_apply]

end LieAlgebra.Basis
