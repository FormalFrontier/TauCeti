/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.Module.GradedModule.Internal
public import TauCeti.LinearAlgebra.Graded.LinearMap

/-!
# Opposites of internally graded modules

This file transports an internal grading across a linear equivalence and applies that construction
to the multiplicative opposite. The degree of an element is unchanged by `MulOpposite.op`, and an
internal graded algebra therefore induces an internal graded algebra on its opposite. The order of
homogeneous factors reverses, but their total degree is unchanged because the grading group is
`ℤ`.

The Koszul twist commutes with passage to the opposite. This is the compatibility needed to form
opposite DG and `A∞` objects without changing their sign convention.

## Main definitions

* `InternalGrading.map`: transport an internal grading across a linear equivalence.
* `InternalGrading.opposite`: the induced grading on the multiplicative opposite.

## Main results

* `InternalGrading.op_mem_opposite_piece_iff`: `op` preserves each degree.
* `InternalGrading.oppositeGradedAlgebra`: a graded algebra induces one on its opposite.
* `InternalGrading.op_koszulTwist`: the Koszul twist commutes with `op`.

This supplies the opposite compatibility in Layer 0 of the `DGAInfinity` roadmap. The conventions
follow B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3 and 7.
-/

public section

open MulOpposite
open scoped DirectSum

namespace TauCeti

universe u v w

namespace InternalGrading

section Map

variable {R : Type u} {M : Type v} {N : Type w}
  [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

private noncomputable def mapPiecesEquiv (G : InternalGrading R M) (e : M ≃ₗ[R] N) :
    (⨁ p : ℤ, G.piece p) ≃ₗ[R] (⨁ p : ℤ, (G.piece p).map e.toLinearMap) :=
  DirectSum.congrLinearEquiv fun p ↦
    Submodule.equivMapOfInjective e.toLinearMap e.injective (G.piece p)

private theorem mapPiecesEquiv_lof (G : InternalGrading R M) (e : M ≃ₗ[R] N)
    (p : ℤ) (x : G.piece p) :
    mapPiecesEquiv G e (DirectSum.lof R ℤ (fun i ↦ G.piece i) p x) =
      DirectSum.lof R ℤ (fun i ↦ (G.piece i).map e.toLinearMap) p
        ((Submodule.equivMapOfInjective e.toLinearMap e.injective (G.piece p)).toLinearMap x) := by
  -- Expose the bundled linear map so the direct-sum application lemma can rewrite it.
  change (mapPiecesEquiv G e).toLinearMap
    (DirectSum.lof R ℤ (fun i ↦ G.piece i) p x) = _
  rw [mapPiecesEquiv, DirectSum.congrLinearEquiv_toLinearMap, DirectSum.lmap_lof]

private theorem coeLinearMap_comp_mapPiecesEquiv (G : InternalGrading R M)
    (e : M ≃ₗ[R] N) :
    (DirectSum.coeLinearMap fun p : ℤ ↦ (G.piece p).map e.toLinearMap) ∘ₗ
        (mapPiecesEquiv G e).toLinearMap =
      e.toLinearMap ∘ₗ DirectSum.coeLinearMap G.piece := by
  apply DirectSum.linearMap_ext R
  intro p
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  calc
    (DirectSum.coeLinearMap fun p : ℤ ↦ (G.piece p).map e.toLinearMap)
        ((mapPiecesEquiv G e).toLinearMap
          (DirectSum.lof R ℤ (fun i ↦ G.piece i) p x)) =
        (DirectSum.coeLinearMap fun p : ℤ ↦ (G.piece p).map e.toLinearMap)
          (DirectSum.lof R ℤ (fun i ↦ (G.piece i).map e.toLinearMap) p
            ((Submodule.equivMapOfInjective e.toLinearMap e.injective
              (G.piece p)).toLinearMap x)) :=
      congrArg _ (mapPiecesEquiv_lof G e p x)
    _ = e x := by
      rw [DirectSum.coeLinearMap_lof]
      exact Submodule.coe_equivMapOfInjective_apply e.toLinearMap e.injective (G.piece p) x
    _ = e.toLinearMap (DirectSum.coeLinearMap G.piece
        (DirectSum.lof R ℤ (fun i ↦ G.piece i) p x)) := by
      rw [DirectSum.coeLinearMap_lof]
      rfl

/-- Transport an internal grading across a linear equivalence. The degree-`p` piece of the target
is the image of the degree-`p` piece of the source. -/
noncomputable def map (G : InternalGrading R M) (e : M ≃ₗ[R] N) : InternalGrading R N where
  piece p := (G.piece p).map e.toLinearMap
  isInternal := by
    -- Expose `coeLinearMap` rather than its definitionally equal additive coercion so it can be
    -- composed with `mapPiecesEquiv` below.
    change Function.Bijective
      (DirectSum.coeLinearMap fun p : ℤ ↦ (G.piece p).map e.toLinearMap)
    let E := mapPiecesEquiv G e
    have hcomp : Function.Bijective
        ((DirectSum.coeLinearMap fun p : ℤ ↦ (G.piece p).map e.toLinearMap) ∘ₗ E.toLinearMap) := by
      rw [coeLinearMap_comp_mapPiecesEquiv]
      exact e.bijective.comp G.isInternal
    constructor
    · intro x y hxy
      obtain ⟨x', rfl⟩ := E.surjective x
      obtain ⟨y', rfl⟩ := E.surjective y
      exact congrArg E (hcomp.injective (by
        simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using hxy))
    · intro y
      obtain ⟨x, hx⟩ := hcomp.surjective y
      exact ⟨E x, by
        simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using hx⟩

/-- The degree-`p` piece of a transported grading is the image of the original piece. -/
@[simp]
theorem map_piece (G : InternalGrading R M) (e : M ≃ₗ[R] N) (p : ℤ) :
    (G.map e).piece p = (G.piece p).map e.toLinearMap :=
  (rfl)

/-- Membership in a transported piece can be checked after applying the inverse equivalence.

This is not a `simp` lemma: `map_piece` already rewrites the left-hand side to a `Submodule.map`,
on which the `simp` set fires `Submodule.mem_map_equiv` to reach the same right-hand side. -/
theorem mem_map_piece_iff (G : InternalGrading R M) (e : M ≃ₗ[R] N) (p : ℤ) (y : N) :
    y ∈ (G.map e).piece p ↔ e.symm y ∈ G.piece p := by
  exact Submodule.mem_map_equiv (p := G.piece p) (e := e)

/-- A linear equivalence maps a homogeneous element into the transported piece of the same
degree. This is the special case of `mem_map_piece_iff` that `simp` already reaches. -/
theorem apply_mem_map_piece_iff (G : InternalGrading R M) (e : M ≃ₗ[R] N) (p : ℤ) (x : M) :
    e x ∈ (G.map e).piece p ↔ x ∈ G.piece p := by
  simp

/-- The equivalence used to transport a grading is homogeneous of degree zero. -/
theorem isHomogeneous_map (G : InternalGrading R M) (e : M ≃ₗ[R] N) :
    TauCeti.LinearMap.IsHomogeneous e.toLinearMap G.piece (G.map e).piece 0 := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p x hx
  simpa using hx

/-- The inverse of an equivalence used to transport a grading is homogeneous of degree zero. -/
theorem isHomogeneous_map_symm (G : InternalGrading R M) (e : M ≃ₗ[R] N) :
    TauCeti.LinearMap.IsHomogeneous e.symm.toLinearMap (G.map e).piece G.piece 0 := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p y hy
  simpa using hy

/-- Transport along the identity equivalence leaves an internal grading unchanged. -/
@[simp]
theorem map_refl (G : InternalGrading R M) : G.map (LinearEquiv.refl R M) = G := by
  apply InternalGrading.ext
  intro p
  apply Submodule.ext
  intro x
  simp

/-- Successive transport agrees with transport along the composite equivalence. -/
@[simp]
theorem map_trans {P : Type*} [AddCommMonoid P] [Module R P]
    (G : InternalGrading R M) (e : M ≃ₗ[R] N) (f : N ≃ₗ[R] P) :
    (G.map e).map f = G.map (e.trans f) := by
  apply InternalGrading.ext
  intro p
  apply Submodule.ext
  intro x
  simp

end Map

section Opposite

variable {R : Type u} {M : Type v}
  [Semiring R] [AddCommMonoid M] [Module R M]

/-- The internal grading on the multiplicative opposite, with `op x` in the same degree as `x`. -/
noncomputable def opposite (G : InternalGrading R M) : InternalGrading R Mᵐᵒᵖ :=
  G.map (opLinearEquiv R)

/-- The degree-`p` opposite piece is the image of the original piece under `op`. -/
@[simp]
theorem opposite_piece (G : InternalGrading R M) (p : ℤ) :
    G.opposite.piece p = (G.piece p).map (opLinearEquiv R).toLinearMap :=
  (rfl)

/-- An opposite element belongs to degree `p` exactly when the original element does. This is the
special case of `mem_opposite_piece_iff` that `simp` already reaches. -/
theorem op_mem_opposite_piece_iff (G : InternalGrading R M) (p : ℤ) (x : M) :
    op x ∈ G.opposite.piece p ↔ x ∈ G.piece p := by
  simp [opposite]

/-- Membership in an opposite piece is membership of the underlying element in the original piece.

This is not a `simp` lemma: `opposite_piece` already rewrites the left-hand side to a
`Submodule.map`, from which the `simp` set reaches the same right-hand side. -/
theorem mem_opposite_piece_iff (G : InternalGrading R M) (p : ℤ) (x : Mᵐᵒᵖ) :
    x ∈ G.opposite.piece p ↔ x.unop ∈ G.piece p := by
  simp [opposite]

/-- Passage to the multiplicative opposite is homogeneous of degree zero. -/
theorem isHomogeneous_op (G : InternalGrading R M) :
    TauCeti.LinearMap.IsHomogeneous
      (opLinearEquiv R).toLinearMap G.piece G.opposite.piece 0 :=
  G.isHomogeneous_map (opLinearEquiv R)

/-- Returning from the multiplicative opposite is homogeneous of degree zero. -/
theorem isHomogeneous_unop (G : InternalGrading R M) :
    TauCeti.LinearMap.IsHomogeneous
      (opLinearEquiv R).symm.toLinearMap G.opposite.piece G.piece 0 :=
  G.isHomogeneous_map_symm (opLinearEquiv R)

end Opposite

section KoszulTwist

variable {R : Type u} {M : Type v}
  [CommRing R] [AddCommMonoid M] [Module R M]

/-- The Koszul twist commutes with the linear equivalence to the multiplicative opposite. -/
theorem opLinearEquiv_comp_koszulTwist (G : InternalGrading R M) (q : ℤ) :
    (opLinearEquiv R).toLinearMap ∘ₗ G.koszulTwist q =
      G.opposite.koszulTwist q ∘ₗ (opLinearEquiv R).toLinearMap := by
  refine DirectSum.decompose_lhom_ext (ℳ := G.piece) fun p => ?_
  ext x
  have hx : (x : M) ∈ G.piece p := Submodule.coe_mem x
  have hop : op (x : M) ∈ G.opposite.piece p :=
    (G.op_mem_opposite_piece_iff p x).2 hx
  have htwist := G.koszulTwist_apply_of_mem hx q
  have htwistOp := G.opposite.koszulTwist_apply_of_mem hop q
  calc
    ((opLinearEquiv R).toLinearMap ∘ₗ G.koszulTwist q) (x : M) =
        op (G.koszulTwist q (x : M)) := rfl
    _ = op (((((q * p).negOnePow : ℤ) : R)) • (x : M)) := congrArg op htwist
    _ = (((q * p).negOnePow : ℤ) : R) • op (x : M) := by simp
    _ = G.opposite.koszulTwist q (op (x : M)) := htwistOp.symm
    _ = (G.opposite.koszulTwist q ∘ₗ (opLinearEquiv R).toLinearMap) (x : M) := rfl

/-- Applying the Koszul twist and then `op` agrees with twisting the opposite element. -/
@[simp]
theorem op_koszulTwist (G : InternalGrading R M) (q : ℤ) (x : M) :
    op (G.koszulTwist q x) = G.opposite.koszulTwist q (op x) := by
  exact LinearMap.congr_fun (G.opLinearEquiv_comp_koszulTwist q) x

/-- Applying the Koszul twist to an opposite element and then `unop` agrees with twisting its
underlying element. -/
@[simp]
theorem unop_koszulTwist (G : InternalGrading R M) (q : ℤ) (x : Mᵐᵒᵖ) :
    unop (G.opposite.koszulTwist q x) = G.koszulTwist q x.unop := by
  have h := congrArg unop (G.op_koszulTwist q x.unop)
  simpa only [op_unop, unop_op] using h.symm

end KoszulTwist

section GradedAlgebra

variable {R : Type u} {A : Type v}
  [CommSemiring R] [Semiring A] [Algebra R A]

variable (G : InternalGrading R A) [SetLike.GradedMonoid G.piece]

/-- The opposite pieces are multiplicative: reversing the factors reverses their degrees, which
does not change their sum in the integer grading. -/
noncomputable instance oppositeGradedMonoid : SetLike.GradedMonoid G.opposite.piece where
  one_mem := by
    rw [G.mem_opposite_piece_iff]
    exact SetLike.one_mem_graded G.piece
  mul_mem := by
    intro p q x y hx hy
    rw [G.mem_opposite_piece_iff] at hx hy ⊢
    rw [unop_mul, add_comm]
    exact SetLike.mul_mem_graded hy hx

/-- An internally graded algebra induces the internal graded algebra on its multiplicative
opposite. -/
noncomputable instance oppositeGradedAlgebra : GradedAlgebra G.opposite.piece :=
  G.opposite.isInternal.gradedAlgebra

end GradedAlgebra

end InternalGrading

end TauCeti
