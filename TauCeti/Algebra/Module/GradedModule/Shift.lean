/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Internal
public import TauCeti.LinearAlgebra.Graded.Shift

/-!
# Shifting an internal grading

An internal grading may be regraded by a fixed shift `c`, so that the degree-`p` piece of the
shifted grading is the degree-`(p + c)` piece of the original one. The underlying module is
unchanged, and the shifted family is again an internal direct sum: reindexing the homogeneous
pieces along an equivalence of degrees only permutes the summands of `⨁ p, G.piece p`.

This is the suspension `sA` of the `A∞` conventions of the `DGAInfinity` roadmap, seen on the
internal presentation of a graded module. The suspension map `s : A ⟶ sA` is the identity of the
underlying module; its content is the degree `-c` recorded below, which
`TauCeti.MultilinearMap.isHomogeneous_suspension_iff` turns into the degree `2 - n` of the
unsuspended operations `mₙ`.

## Main definitions

* `TauCeti.InternalGrading.shift`: the shift of an internal grading.

## Main results

* `TauCeti.isInternal_comp_symm`: an internal decomposition stays internal after reindexing the
  degrees along an equivalence.
* `TauCeti.InternalGrading.isHomogeneous_id_shift`: the suspension map has degree `-c`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
-/

public section

namespace TauCeti

universe u v

/-- Reindexing an internal direct-sum decomposition along an equivalence of index types again
gives an internal decomposition: the reindexing only permutes the summands. -/
theorem isInternal_comp_symm {ι : Type*} {κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {M : Type*} {σ : Type*} [AddCommMonoid M] [SetLike σ M] [AddSubmonoidClass σ M]
    {A : ι → σ} (h : DirectSum.IsInternal A) (e : ι ≃ κ) :
    DirectSum.IsInternal fun k ↦ A (e.symm k) := by
  have hcomp : (DirectSum.coeAddMonoidHom A).comp
      (DirectSum.equivCongrLeft (β := fun i ↦ (A i : Type _)) e).symm.toAddMonoidHom =
      DirectSum.coeAddMonoidHom fun k ↦ A (e.symm k) := by
    refine DirectSum.addHom_ext' fun k ↦ AddMonoidHom.ext fun y ↦ ?_
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      DirectSum.coeAddMonoidHom_of]
    rw [← DirectSum.equivCongrLeft_of (β := fun i ↦ (A i : Type _)) e k y,
      AddEquiv.symm_apply_apply, DirectSum.coeAddMonoidHom_of]
  have hbij : Function.Bijective (DirectSum.coeAddMonoidHom fun k ↦ A (e.symm k)) := by
    rw [← hcomp]
    simpa only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom] using
      h.comp (AddEquiv.bijective _)
  exact hbij

namespace InternalGrading

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Two internal gradings of the same module are equal as soon as their homogeneous pieces
agree. -/
@[ext]
theorem ext : ∀ {G H : InternalGrading R M}, (∀ p, G.piece p = H.piece p) → G = H
  | ⟨_, _⟩, ⟨_, _⟩, h => by
    obtain rfl := funext h
    rfl

/-- The shift of an internal grading by `c`: its degree-`p` piece is the degree-`(p + c)` piece of
the original grading. The underlying module is unchanged. -/
@[expose]
def shift (G : InternalGrading R M) (c : ℤ) : InternalGrading R M where
  piece := Graded.shift G.piece c
  isInternal :=
    isInternal_comp_symm G.isInternal
      ⟨fun p ↦ p - c, fun p ↦ p + c, fun p ↦ by ring, fun p ↦ by ring⟩

@[simp]
theorem shift_piece (G : InternalGrading R M) (c p : ℤ) :
    (G.shift c).piece p = G.piece (p + c) :=
  rfl

/-- The pieces of a shifted internal grading are the shifted family of pieces. -/
theorem shift_piece_eq (G : InternalGrading R M) (c : ℤ) :
    (G.shift c).piece = Graded.shift G.piece c :=
  rfl

@[simp]
theorem shift_zero (G : InternalGrading R M) : G.shift 0 = G := by
  ext p
  simp

/-- Shifting twice shifts by the sum of the two amounts. -/
theorem shift_shift (G : InternalGrading R M) (c d : ℤ) :
    (G.shift c).shift d = G.shift (d + c) := by
  ext p
  simp [add_assoc]

/-- The suspension map `s : A ⟶ sA` is the identity of the underlying module and has degree `-c`
from an internal grading to its shift by `c`. -/
theorem isHomogeneous_id_shift (G : InternalGrading R M) (c : ℤ) :
    LinearMap.IsHomogeneous (LinearMap.id : M →ₗ[R] M) G.piece (G.shift c).piece (-c) :=
  LinearMap.isHomogeneous_id_shift G.piece c

/-- The unsuspension map `s⁻¹ : sA ⟶ A` is the identity of the underlying module and has
degree `c` from the shift by `c` back to the original internal grading. -/
theorem isHomogeneous_id_unshift (G : InternalGrading R M) (c : ℤ) :
    LinearMap.IsHomogeneous (LinearMap.id : M →ₗ[R] M) (G.shift c).piece G.piece c :=
  LinearMap.isHomogeneous_id_unshift G.piece c

end InternalGrading

end TauCeti
