/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# Shifting an internal grading

An internal grading may be regraded by a fixed shift `c`, so that the degree-`p` piece of the
shifted grading is the degree-`(p + c)` piece of the original one. The underlying module is
unchanged, and the shifted family is again an internal direct sum: reindexing the homogeneous
pieces along an equivalence of degrees only permutes the summands of `⨁ p, G.piece p`.

This is the suspension `sA` of the `A∞` conventions of the `DGAInfinity` roadmap, seen on the
internal presentation of a graded module. The suspension leaves the underlying module unchanged
and reindexes its homogeneous pieces.

## Main definitions

* `TauCeti.InternalGrading.shift`: the shift of an internal grading.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
-/

public section

namespace TauCeti

universe u v

private theorem isInternal_comp_symm {ι : Type*} {κ : Type*} [DecidableEq ι] [DecidableEq κ]
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

/-- The shift of an internal grading by `c`: its degree-`p` piece is the degree-`(p + c)` piece of
the original grading. The underlying module is unchanged. -/
def shift (G : InternalGrading R M) (c : ℤ) : InternalGrading R M where
  piece := fun p ↦ G.piece (p + c)
  isInternal :=
    isInternal_comp_symm G.isInternal
      ⟨fun p ↦ p - c, fun p ↦ p + c, fun p ↦ by ring, fun p ↦ by ring⟩

@[simp]
theorem shift_piece (G : InternalGrading R M) (c p : ℤ) :
    (G.shift c).piece p = G.piece (p + c) :=
  (rfl)

@[simp]
theorem shift_zero (G : InternalGrading R M) : G.shift 0 = G := by
  ext p
  simp

/-- Shifting twice shifts by the sum of the two amounts. -/
@[simp]
theorem shift_shift (G : InternalGrading R M) (c d : ℤ) :
    (G.shift c).shift d = G.shift (d + c) := by
  ext p
  simp [add_assoc]

end InternalGrading

end TauCeti
