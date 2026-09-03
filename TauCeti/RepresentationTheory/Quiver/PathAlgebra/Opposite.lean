/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.Quiver.Symmetric
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic

/-!
# Opposites of path algebras

Reversing every path in a quiver with involutive arrow reversal identifies its path algebra with
its opposite algebra. This file constructs that identification directly on the path basis and
records its action on paths, vertices, and arrows.

## Main definitions

* `TauCeti.Quiver.TotalPath.reverse`: reversal of an indexed path, including its endpoints.
* `TauCeti.PathAlgebra.reverseOpAlgEquiv`: the algebra isomorphism from a path algebra to its
  opposite induced by path reversal.

## References

This is the path-algebra prerequisite for the opposite-algebra comparison in Layer 4 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`.
-/

public section

namespace TauCeti

open _root_.Quiver MulOpposite

universe u v w

namespace Quiver.TotalPath

variable {Q : Type u} [Quiver.{v} Q]

/-- Reverse an indexed path and exchange its source and target. -/
def reverse [HasReverse Q] (x : TotalPath Q) : TotalPath Q :=
  ⟨x.2.1, x.1, x.2.2.reverse⟩

/-- Reversal of an explicitly indexed path reverses its underlying path. -/
@[simp]
theorem reverse_mk [HasReverse Q] {a b : Q} (p : Path a b) :
    reverse (⟨a, b, p⟩ : TotalPath Q) = ⟨b, a, p.reverse⟩ :=
  (rfl)

/-- Reversing an indexed path twice returns the original path. -/
@[simp]
theorem reverse_reverse [HasInvolutiveReverse Q] (x : TotalPath Q) :
    x.reverse.reverse = x := by
  obtain ⟨a, b, p⟩ := x
  simp

end Quiver.TotalPath

namespace PathAlgebra

section Reverse

variable (k : Type w) (Q : Type u) [CommSemiring k] [Quiver.{v} Q]
  [HasInvolutiveReverse Q] [Finite Q]

omit [Finite Q] in
private theorem reverseOp_hcomp {a b c : Q} (p : Path a b) (q : Path c a) :
    op (ofPath (Quiver.TotalPath.reverse ⟨a, b, p⟩) : pathAlgebra k Q) *
        op (ofPath (Quiver.TotalPath.reverse ⟨c, a, q⟩) : pathAlgebra k Q) =
      op (ofPath (Quiver.TotalPath.reverse ⟨c, b, q.comp p⟩) : pathAlgebra k Q) := by
  rw [← op_mul, Quiver.TotalPath.reverse_mk, Quiver.TotalPath.reverse_mk,
    ofPath_mul_ofPath_of_comp, Quiver.TotalPath.reverse_mk, Path.reverse_comp]

private theorem reverseOp_hzero {x y : Quiver.TotalPath Q} (h : y.2.1 ≠ x.1) :
    op (ofPath x.reverse : pathAlgebra k Q) * op (ofPath y.reverse : pathAlgebra k Q) = 0 := by
  rw [← op_mul, ofPath_mul_ofPath_of_not_composable]
  · exact op_zero
  · exact fun hxy ↦ h hxy.symm

private theorem reverseOp_hone :
    letI := Fintype.ofFinite Q
    ∑ a : Q, op (ofPath (Quiver.TotalPath.reverse ⟨a, a, Path.nil⟩) : pathAlgebra k Q) = 1 := by
  let _ := Fintype.ofFinite Q
  simp only [Quiver.TotalPath.reverse_mk, Path.reverse, ofPath_eq_single,
    ← vertexIdempotent_eq_single]
  rw [← Finset.op_sum Finset.univ]
  exact (congrArg op (one_def (k := k) (Q := Q))).symm

private noncomputable def reverseOpAlgHom :
    pathAlgebra k Q →ₐ[k] (pathAlgebra k Q)ᵐᵒᵖ :=
  liftAlgHom k (fun x ↦ op (ofPath x.reverse)) (reverseOp_hcomp k Q)
    (reverseOp_hzero k Q) (reverseOp_hone k Q)

@[simp]
private theorem reverseOpAlgHom_ofPath (x : Quiver.TotalPath Q) :
    reverseOpAlgHom k Q (ofPath x) = op (ofPath x.reverse) := by
  rw [reverseOpAlgHom, liftAlgHom_ofPath]

/-- Reversing paths identifies the path algebra of a quiver with involutive arrow reversal with
its opposite algebra. -/
noncomputable def reverseOpAlgEquiv : pathAlgebra k Q ≃ₐ[k] (pathAlgebra k Q)ᵐᵒᵖ :=
  AlgEquiv.ofAlgHom (reverseOpAlgHom k Q) (AlgHom.opComm (reverseOpAlgHom k Q))
    (by
      apply AlgHom.ext
      intro z
      obtain ⟨y, rfl⟩ := MulOpposite.op_surjective z
      rw [AlgHom.comp_apply, AlgHom.id_apply]
      induction y using induction_linear with
      | zero => simp
      | add y₁ y₂ h₁ h₂ => rw [op_add, map_add, map_add, h₁, h₂]
      | single x c =>
          rw [single_eq_smul_ofPath, op_smul, map_smul, map_smul,
            AlgHom.opComm_apply_apply, unop_op, reverseOpAlgHom_ofPath,
            unop_op, reverseOpAlgHom_ofPath, Quiver.TotalPath.reverse_reverse])
    (algHom_ext k fun x ↦ by
      rw [AlgHom.comp_apply, reverseOpAlgHom_ofPath, AlgHom.opComm_apply_apply, unop_op,
        reverseOpAlgHom_ofPath, Quiver.TotalPath.reverse_reverse, AlgHom.id_apply, unop_op])

/-- The path-reversal isomorphism sends a basis path to the opposite of its reverse. -/
@[simp]
theorem reverseOpAlgEquiv_ofPath (x : Quiver.TotalPath Q) :
    reverseOpAlgEquiv k Q (ofPath x) = op (ofPath x.reverse) := by
  rw [reverseOpAlgEquiv, AlgEquiv.ofAlgHom_apply, reverseOpAlgHom_ofPath]

/-- The inverse path-reversal isomorphism sends the opposite of a basis path to its reverse. -/
@[simp]
theorem reverseOpAlgEquiv_symm_op_ofPath (x : Quiver.TotalPath Q) :
    (reverseOpAlgEquiv k Q).symm (op (ofPath x)) = ofPath x.reverse := by
  rw [reverseOpAlgEquiv, AlgEquiv.ofAlgHom_symm, AlgEquiv.ofAlgHom_apply,
    AlgHom.opComm_apply_apply, unop_op, reverseOpAlgHom_ofPath, unop_op]

/-- Path reversal fixes vertex idempotents, up to passage to the opposite algebra. -/
@[simp]
theorem reverseOpAlgEquiv_vertexIdempotent (a : Q) :
    reverseOpAlgEquiv k Q (vertexIdempotent k a) = op (vertexIdempotent k a) := by
  rw [vertexIdempotent_eq_single, ← ofPath_eq_single, reverseOpAlgEquiv_ofPath,
    Quiver.TotalPath.reverse_mk, Path.reverse, ofPath_eq_single, ← vertexIdempotent_eq_single]

/-- Path reversal sends an arrow to the opposite of its reversed arrow. -/
theorem reverseOpAlgEquiv_ofArrow {a b : Q} (e : a ⟶ b) :
    reverseOpAlgEquiv k Q (ofArrow e) = op (ofArrow (Quiver.reverse e)) := by
  rw [ofArrow_eq_ofPath, reverseOpAlgEquiv_ofPath, Quiver.TotalPath.reverse_mk,
    Path.reverse_toPath, ofArrow_eq_ofPath]

end Reverse

end PathAlgebra

end TauCeti
