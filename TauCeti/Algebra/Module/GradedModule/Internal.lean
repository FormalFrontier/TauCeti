/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Internally graded modules

This file packages a `ℤ`-graded module as a total module together with an internal direct-sum
decomposition.  The total-module presentation is convenient for DG and `A∞` operations, while
`DirectSum.IsInternal` ensures that every element is a finite, uniquely determined sum of
homogeneous elements.

Mathlib already provides the direct-sum equivalence and its induction principle through
`DirectSum.Decomposition`.  An `InternalGrading` retains the family of homogeneous submodules and
the proof that it is internal; the API below installs and reuses Mathlib's decomposition rather
than duplicating it.

## Main definitions

* `InternalGrading`: an internal `ℤ`-grading of a module.
* `InternalGrading.IsHomogeneous`: membership in a specified homogeneous piece.
* `InternalGrading.component`: the linear projection onto a homogeneous piece.
* `InternalGrading.support`: the finite set of degrees at which an element’s homogeneous component
  is nonzero.

## Main results

* `InternalGrading.sum_support_component`: every element is the finite sum of its homogeneous
  components.
* `InternalGrading.linearMap_ext_homogeneous`: linear maps agree when they agree on all homogeneous
  elements.

This is the first graded-module target in Layer 0 of the `DGAInfinity` roadmap.  Later files use
these projections to define maps of nonzero degree, shifts, tensor-product gradings, and signed
multilinear operations.
-/

public section

open scoped DirectSum

namespace TauCeti

universe u v

variable (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]

/-- An internal integer grading of an `R`-module `M`.

The `isInternal` field says that the canonical map from the external direct sum of the `piece p`
to `M` is bijective.  Thus elements of `M` have unique finite homogeneous decompositions. -/
structure InternalGrading where
  /-- The submodule of elements of degree `p`. -/
  piece : ℤ → Submodule R M
  /-- The homogeneous pieces form an internal direct sum. -/
  isInternal : DirectSum.IsInternal piece

namespace InternalGrading

variable {R M}

/-- An element is homogeneous of degree `p` when it belongs to the `p`-th graded piece. -/
def IsHomogeneous (G : InternalGrading R M) (p : ℤ) (x : M) : Prop :=
  x ∈ G.piece p

@[simp]
theorem isHomogeneous_iff_mem (G : InternalGrading R M) (p : ℤ) (x : M) :
    G.IsHomogeneous p x ↔ x ∈ G.piece p :=
  Iff.rfl

/-- The decomposition attached to an internal grading. -/
noncomputable instance (G : InternalGrading R M) : DirectSum.Decomposition G.piece :=
  G.isInternal.chooseDecomposition

/-- Projection onto the homogeneous piece of degree `p`. -/
noncomputable def component (G : InternalGrading R M) (p : ℤ) : M →ₗ[R] G.piece p :=
  DirectSum.component R ℤ (fun q ↦ G.piece q) p ∘ₗ
    (DirectSum.decomposeLinearEquiv G.piece).toLinearMap

@[simp]
theorem component_apply (G : InternalGrading R M) (p : ℤ) (x : M) :
    G.component p x = DirectSum.decompose G.piece x p := by
  simp only [component, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, DirectSum.decomposeLinearEquiv_apply]
  exact (DirectSum.apply_eq_component (R := R) (DirectSum.decompose G.piece x) p).symm

theorem isHomogeneous_component (G : InternalGrading R M) (p : ℤ) (x : M) :
    G.IsHomogeneous p (G.component p x : M) :=
  (G.component p x).property

theorem isHomogeneous_zero (G : InternalGrading R M) (p : ℤ) :
    G.IsHomogeneous p (0 : M) :=
  (G.piece p).zero_mem

theorem IsHomogeneous.add {G : InternalGrading R M} {p : ℤ} {x y : M}
    (hx : G.IsHomogeneous p x) (hy : G.IsHomogeneous p y) : G.IsHomogeneous p (x + y) :=
  (G.piece p).add_mem hx hy

theorem IsHomogeneous.smul {G : InternalGrading R M} {p : ℤ} {x : M}
    (hx : G.IsHomogeneous p x) (r : R) : G.IsHomogeneous p (r • x) :=
  (G.piece p).smul_mem r hx

section Ring

variable {S : Type u} {N : Type v} [Ring S] [AddCommGroup N] [Module S N]

theorem IsHomogeneous.neg {G : InternalGrading S N} {p : ℤ} {x : N}
    (hx : G.IsHomogeneous p x) : G.IsHomogeneous p (-x) :=
  (G.piece p).neg_mem hx

theorem IsHomogeneous.sub {G : InternalGrading S N} {p : ℤ} {x y : N}
    (hx : G.IsHomogeneous p x) (hy : G.IsHomogeneous p y) : G.IsHomogeneous p (x - y) :=
  (G.piece p).sub_mem hx hy

end Ring

theorem component_same (G : InternalGrading R M) (p : ℤ) (x : G.piece p) :
    G.component p (x : M) = x := by
  ext
  simp only [component_apply]
  exact DirectSum.decompose_of_mem_same G.piece x.property

theorem component_ne (G : InternalGrading R M) {p q : ℤ} (hpq : p ≠ q) (x : G.piece p) :
    G.component q (x : M) = 0 := by
  ext
  simp only [component_apply, Submodule.coe_zero]
  exact DirectSum.decompose_of_mem_ne G.piece x.property hpq

theorem component_of_isHomogeneous_same (G : InternalGrading R M) {p : ℤ} {x : M}
    (hx : G.IsHomogeneous p x) : (G.component p x : M) = x := by
  simp only [component_apply]
  exact DirectSum.decompose_of_mem_same G.piece hx

theorem component_of_isHomogeneous_ne (G : InternalGrading R M) {p q : ℤ}
    (hpq : p ≠ q) {x : M} (hx : G.IsHomogeneous p x) : G.component q x = 0 := by
  ext
  simp only [component_apply, Submodule.coe_zero]
  exact DirectSum.decompose_of_mem_ne G.piece hx hpq

/-- The finite set of degrees at which an element’s homogeneous component is nonzero. -/
noncomputable def support (G : InternalGrading R M) (x : M) : Finset ℤ := by
  classical
  exact (DirectSum.decompose G.piece x).support

theorem mem_support_iff (G : InternalGrading R M) (x : M) (p : ℤ) :
    p ∈ G.support x ↔ G.component p x ≠ 0 := by
  classical
  simp [support, component_apply]

/-- Every element is the finite sum of its homogeneous components. -/
theorem sum_support_component (G : InternalGrading R M) (x : M) :
    (∑ p ∈ G.support x, (G.component p x : M)) = x := by
  classical
  simp only [support]
  simpa only [component_apply] using
    DirectSum.sum_support_decompose G.piece x

/-- Linear maps agree when they agree on all homogeneous elements. -/
theorem linearMap_ext_homogeneous {N : Type*} [AddCommMonoid N] [Module R N]
    (G : InternalGrading R M) ⦃f g : M →ₗ[R] N⦄
    (h : ∀ p (x : G.piece p), f (x : M) = g (x : M)) : f = g := by
  apply DirectSum.decompose_lhom_ext G.piece
  intro p
  ext x
  exact h p x

end InternalGrading

end TauCeti
