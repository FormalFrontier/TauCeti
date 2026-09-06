/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Basic
public import TauCeti.Algebra.Module.GradedModule.Opposite

/-!
# Opposites of differential graded algebras

The ordinary multiplication on `Aᵐᵒᵖ` reverses products without a Koszul sign.  In this file its
differential is defined to be

`dᵒᵖ (op a) = (-1) ^ |a| • op (d a)`

on homogeneous elements.  Equivalently, before applying `d`, one applies the Koszul twist which
multiplies degree `p` by `(-1) ^ p`.  Using the general opposite differential from
`TauCeti.Algebra.Module.GradedModule.Opposite`, this file proves its square and Leibniz laws and
makes passage to opposites functorial on DG algebra morphisms.

This convention is equivalent to the other common presentation, which keeps the differential
unchanged and uses the signed product `op a ⋅ op b = (-1) ^ (|a| |b|) op (b a)`.  The convention
here retains Mathlib's existing ring and algebra structures on `Aᵐᵒᵖ`.

## Main definitions

* `IsDGAlgebra.opposite`: the differential graded algebra structure on the opposite.
* `DGAlgHom.op`: the morphism between opposites induced by a DG algebra morphism.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

open MulOpposite

namespace TauCeti

universe uR uA uB

namespace IsDGAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {G : InternalGrading R A} [GradedAlgebra G.piece] {d : A →ₗ[R] A}

private theorem oppositeDifferential_sq_zero (h : IsDGAlgebra G.piece d) (a : A) :
    G.oppositeDifferential d (G.oppositeDifferential d (op a)) = 0 := by
  induction a using DirectSum.Decomposition.inductionOn G.piece with
  | zero => simp
  | @homogeneous p a =>
      rw [G.oppositeDifferential_op_of_mem d a.2, map_smul,
        G.oppositeDifferential_op_of_mem d (h.map_mem a.2), h.sq_zero, op_zero, smul_zero,
        smul_zero]
  | add a b ha hb => rw [op_add, map_add, map_add, ha, hb, add_zero]

private theorem oppositeDifferential_leibniz (h : IsDGAlgebra G.piece d) {p : ℤ} {a : A}
    (ha : a ∈ G.piece p) (b : A) :
    G.oppositeDifferential d (op a * op b) =
      G.oppositeDifferential d (op a) * op b +
        p.negOnePow • (op a * G.oppositeDifferential d (op b)) := by
  induction b using DirectSum.Decomposition.inductionOn G.piece with
  | zero => simp
  | @homogeneous q b =>
      rw [← op_mul, G.oppositeDifferential_op_of_mem d (SetLike.mul_mem_graded b.2 ha),
        h.leibniz b.2 a, G.oppositeDifferential_op_of_mem d ha,
        G.oppositeDifferential_op_of_mem d b.2]
      apply unop_injective
      simp only [unop_smul, unop_op, unop_add, unop_mul, Units.smul_def,
        ← Int.cast_smul_eq_zsmul R, smul_add, smul_smul, Int.negOnePow_add,
        add_comm q p]
      simp only [mul_smul_comm, smul_mul_assoc, smul_smul, ← Int.cast_mul,
        ← Units.val_mul, mul_assoc, Int.units_mul_self, mul_one]
      rw [add_comm]
  | add b c hb hc =>
      simp only [op_add, mul_add, map_add, hb, hc, smul_add]
      abel

/-- The ordinary opposite algebra of a differential graded algebra is differential graded when its
differential is twisted by `(-1) ^ p` in degree `p`. -/
theorem opposite (h : IsDGAlgebra G.piece d) :
    IsDGAlgebra G.opposite.piece (G.oppositeDifferential d) where
  map_mem := by
    intro p x hx
    rw [G.mem_opposite_piece_iff] at hx ⊢
    rw [G.unop_oppositeDifferential]
    exact h.map_mem (G.koszulTwist_mem_piece hx 1)
  sq_zero := MulOpposite.rec' (h.oppositeDifferential_sq_zero)
  leibniz := by
    intro p x hx y
    rw [← op_unop x, ← op_unop y]
    exact h.oppositeDifferential_leibniz ((G.mem_opposite_piece_iff p x).mp hx) y.unop

end IsDGAlgebra

namespace DGAlgHom

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {G : InternalGrading R A} {H : InternalGrading R B}
  [GradedAlgebra G.piece] [GradedAlgebra H.piece]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra G.piece dA} {hB : IsDGAlgebra H.piece dB}

private noncomputable def gradedOp (f : DGAlgHom hA hB) :
    G.opposite.piece →ₐᵍ[R] H.opposite.piece :=
  { f.toGradedAlgHom.toAlgHom.op with
    map_mem := by
      intro p x hx
      rw [G.mem_opposite_piece_iff] at hx
      rw [H.mem_opposite_piece_iff]
      exact f.map_mem hx }

private theorem gradedOp_op (f : DGAlgHom hA hB) (a : A) :
    gradedOp f (MulOpposite.op a) = MulOpposite.op (f a) :=
  (rfl)

private theorem gradedOp_map_oppositeDifferential (f : DGAlgHom hA hB) (a : A) :
    H.oppositeDifferential dB (gradedOp f (MulOpposite.op a)) =
      gradedOp f (G.oppositeDifferential dA (MulOpposite.op a)) := by
  induction a using DirectSum.Decomposition.inductionOn G.piece with
  | zero => simp only [op_zero, map_zero]
  | @homogeneous p a =>
      calc
        H.oppositeDifferential dB (gradedOp f (MulOpposite.op (a : A))) =
            H.oppositeDifferential dB (MulOpposite.op (f (a : A))) := by
          rw [gradedOp_op]
        _ = (((p.negOnePow : ℤ) : R) • MulOpposite.op (dB (f (a : A)))) :=
          H.oppositeDifferential_op_of_mem dB (f.map_mem a.2)
        _ = (((p.negOnePow : ℤ) : R) • MulOpposite.op (f (dA (a : A)))) := by
          rw [f.map_d]
        _ = gradedOp f ((((p.negOnePow : ℤ) : R) • MulOpposite.op (dA (a : A)))) := by
          rw [map_smul, gradedOp_op]
        _ = gradedOp f (G.oppositeDifferential dA (MulOpposite.op (a : A))) :=
          congrArg (gradedOp f) (G.oppositeDifferential_op_of_mem dA a.2).symm
  | add a b ha hb => simpa only [op_add, map_add] using congrArg₂ (fun x y ↦ x + y) ha hb

/-- Passage to the ordinary opposite sends a morphism of differential graded algebras to a
morphism between their twisted-differential opposites. -/
noncomputable def op (f : DGAlgHom hA hB) : DGAlgHom hA.opposite hB.opposite where
  toGradedAlgHom := gradedOp f
  map_d' := MulOpposite.rec' f.gradedOp_map_oppositeDifferential

/-- The opposite morphism acts by applying the original morphism under `op`. -/
@[simp]
theorem op_apply (f : DGAlgHom hA hB) (x : Aᵐᵒᵖ) : f.op x = MulOpposite.op (f x.unop) :=
  MulOpposite.rec' f.gradedOp_op x

/-- Passage to opposites preserves identity morphisms. -/
@[simp]
theorem op_id (hA : IsDGAlgebra G.piece dA) :
    (DGAlgHom.id hA).op = DGAlgHom.id hA.opposite := by
  ext x
  simp

/-- Passage to opposites preserves composition of DG algebra morphisms. -/
@[simp]
theorem op_comp {C : Type*} [Ring C] [Algebra R C] {K : InternalGrading R C}
    [GradedAlgebra K.piece] {dC : C →ₗ[R] C} {hC : IsDGAlgebra K.piece dC}
    (g : DGAlgHom hB hC) (f : DGAlgHom hA hB) :
    (g.comp f).op = g.op.comp f.op := by
  ext x
  simp

end DGAlgHom

end TauCeti
