/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Opposite
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Basic

/-!
# The opposite of a preprojective algebra

Reversing every path of the doubled quiver preserves each of the two backtracks attached to an
original arrow. It therefore preserves the signed preprojective relator and descends to an
isomorphism from the additive preprojective algebra to its opposite. On a path class this
isomorphism takes the class of the path to the opposite of the class of its reverse.

## Main results

* `TauCeti.reverseOpAlgEquiv_preprojectiveRelator`: path reversal preserves the preprojective
  relator, up to passage to the opposite algebra.
* `TauCeti.reverseOpAlgEquiv_localPreprojectiveRelator`: the same statement for each local
  relator.
* `TauCeti.preprojectiveOpAlgEquiv`: the preprojective algebra is isomorphic to its opposite.

## References

This proves the opposite-algebra comparison in the first bullet of Layer 4 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`. The preprojective presentation and its signs
follow Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
problem*, Section 1.
-/

public section

namespace TauCeti

open _root_.Quiver MulOpposite PathAlgebra

universe u v w

section Backtrack

variable (k : Type w) {Q : Type u} [CommSemiring k] [Quiver.{v + 1} Q] [Finite Q]

/-- Reversal fixes the head backtrack of an original arrow, up to passage to the opposite path
algebra. -/
@[simp]
theorem reverseOpAlgEquiv_headBacktrackElem {i j : Q} (a : i ⟶ j) :
    reverseOpAlgEquiv k (Symmetrify Q) (headBacktrackElem k a) =
      op (headBacktrackElem k a) := by
  rw [← ofArrow_mul_ofArrow_reverse_eq_headBacktrackElem]
  rw [map_mul, reverseOpAlgEquiv_ofArrow, reverseOpAlgEquiv_ofArrow,
    Quiver.reverse_reverse, ← op_mul]

/-- Reversal fixes the tail backtrack of an original arrow, up to passage to the opposite path
algebra. -/
@[simp]
theorem reverseOpAlgEquiv_tailBacktrackElem {i j : Q} (a : i ⟶ j) :
    reverseOpAlgEquiv k (Symmetrify Q) (tailBacktrackElem k a) =
      op (tailBacktrackElem k a) := by
  rw [← ofArrow_reverse_mul_ofArrow_eq_tailBacktrackElem]
  rw [map_mul, reverseOpAlgEquiv_ofArrow, reverseOpAlgEquiv_ofArrow,
    Quiver.reverse_reverse, ← op_mul]

/-- Reversal fixes the vertex idempotent of the doubled quiver, up to passage to the opposite
path algebra. -/
@[simp]
theorem reverseOpAlgEquiv_doubledVertexIdempotent (i : Q) :
    reverseOpAlgEquiv k (Symmetrify Q) (doubledVertexIdempotent k i) =
      op (doubledVertexIdempotent k i) := by
  rw [doubledVertexIdempotent_def, reverseOpAlgEquiv_vertexIdempotent]

end Backtrack

section Relator

variable (k : Type w) (Q : Type u) [CommRing k] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- **Path reversal preserves the preprojective relator**, up to passage to the opposite path
algebra. Both backtracks of every arrow are palindromic, so their signed difference is fixed. -/
@[simp]
theorem reverseOpAlgEquiv_preprojectiveRelator :
    reverseOpAlgEquiv k (Symmetrify Q) (preprojectiveRelator k Q) =
      op (preprojectiveRelator k Q) := by
  rw [preprojectiveRelator_def]
  simp only [map_sum, map_sub, reverseOpAlgEquiv_headBacktrackElem,
    reverseOpAlgEquiv_tailBacktrackElem, Finset.op_sum, op_sub]

/-- Path reversal preserves each local preprojective relator, up to passage to the opposite path
algebra. -/
@[simp]
theorem reverseOpAlgEquiv_localPreprojectiveRelator (v : Q) :
    reverseOpAlgEquiv k (Symmetrify Q) (localPreprojectiveRelator k v) =
      op (localPreprojectiveRelator k v) := by
  rw [← preprojectiveRelator_vertexCorner_eq_localPreprojectiveRelator,
    doubledVertexIdempotent_def, map_mul, map_mul, reverseOpAlgEquiv_vertexIdempotent,
    reverseOpAlgEquiv_preprojectiveRelator, ← op_mul, ← op_mul, mul_assoc]

end Relator

section Quotient

variable (k : Type w) (Q : Type u) [CommRing k] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- Reversal followed by the opposite of the preprojective quotient map. -/
private noncomputable def preprojectiveReversePathAlgHom :
    pathAlgebra k (Symmetrify Q) →ₐ[k] (preprojectiveAlgebra k Q)ᵐᵒᵖ :=
  (AlgHom.op (preprojectiveMk k Q)).comp
    (reverseOpAlgEquiv k (Symmetrify Q)).toAlgHom

private theorem preprojectiveReversePathAlgHom_relator :
    preprojectiveReversePathAlgHom k Q (preprojectiveRelator k Q) = 0 := by
  rw [preprojectiveReversePathAlgHom, AlgHom.comp_apply]
  -- Expose the coerced `AlgEquiv` application so its characteristic lemma can rewrite it.
  change (AlgHom.op (preprojectiveMk k Q))
    (reverseOpAlgEquiv k (Symmetrify Q) (preprojectiveRelator k Q)) = 0
  rw [reverseOpAlgEquiv_preprojectiveRelator]
  simp

/-- The path-reversal homomorphism from a preprojective algebra to its opposite, obtained by
descending reversal of the doubled path algebra through the preprojective relation. -/
private noncomputable def preprojectiveReverseOpAlgHom :
    preprojectiveAlgebra k Q →ₐ[k] (preprojectiveAlgebra k Q)ᵐᵒᵖ :=
  preprojectiveLift (preprojectiveReversePathAlgHom k Q)
    (preprojectiveReversePathAlgHom_relator k Q)

private theorem preprojectiveReverseOpAlgHom_preprojectiveMk (x) :
    preprojectiveReverseOpAlgHom k Q (preprojectiveMk k Q x) =
      preprojectiveReversePathAlgHom k Q x := by
  rw [preprojectiveReverseOpAlgHom, preprojectiveLift_preprojectiveMk]

private theorem preprojectiveReverseOpAlgHom_preprojectiveMk_ofPath
    (x : Quiver.TotalPath (Symmetrify Q)) :
    preprojectiveReverseOpAlgHom k Q (preprojectiveMk k Q (ofPath x)) =
      op (preprojectiveMk k Q (ofPath x.reverse)) := by
  rw [preprojectiveReverseOpAlgHom_preprojectiveMk, preprojectiveReversePathAlgHom,
    AlgHom.comp_apply]
  -- Expose the coerced `AlgEquiv` application so its path formula can rewrite it.
  change (AlgHom.op (preprojectiveMk k Q))
    (reverseOpAlgEquiv k (Symmetrify Q) (ofPath x)) = _
  rw [reverseOpAlgEquiv_ofPath]
  rfl

private theorem preprojectiveReverseOpAlgHom_opComm_op_preprojectiveMk_ofPath
    (x : Quiver.TotalPath (Symmetrify Q)) :
    AlgHom.opComm (preprojectiveReverseOpAlgHom k Q)
        (op (preprojectiveMk k Q (ofPath x))) =
      preprojectiveMk k Q (ofPath x.reverse) := by
  rw [AlgHom.opComm_apply_apply, unop_op,
    preprojectiveReverseOpAlgHom_preprojectiveMk_ofPath, unop_op]

private theorem preprojectiveReverseOpAlgHom_involutive_preprojectiveMk
    (x : pathAlgebra k (Symmetrify Q)) :
    (preprojectiveReverseOpAlgHom k Q
          (AlgHom.opComm (preprojectiveReverseOpAlgHom k Q)
            (op (preprojectiveMk k Q x))) = op (preprojectiveMk k Q x)) ∧
      (AlgHom.opComm (preprojectiveReverseOpAlgHom k Q)
          (preprojectiveReverseOpAlgHom k Q (preprojectiveMk k Q x)) =
        preprojectiveMk k Q x) := by
  induction x using PathAlgebra.induction_linear with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
      obtain ⟨h₁₁, h₁₂⟩ := h₁
      obtain ⟨h₂₁, h₂₂⟩ := h₂
      constructor
      · rw [map_add, op_add, map_add, map_add, h₁₁, h₂₁]
      · rw [map_add, map_add, map_add, h₁₂, h₂₂]
  | single x c =>
      constructor
      · rw [single_eq_smul_ofPath, map_smul, op_smul, map_smul, map_smul,
          preprojectiveReverseOpAlgHom_opComm_op_preprojectiveMk_ofPath,
          preprojectiveReverseOpAlgHom_preprojectiveMk_ofPath,
          Quiver.TotalPath.reverse_reverse]
      · rw [single_eq_smul_ofPath, map_smul, map_smul, map_smul,
          preprojectiveReverseOpAlgHom_preprojectiveMk_ofPath,
          preprojectiveReverseOpAlgHom_opComm_op_preprojectiveMk_ofPath,
          Quiver.TotalPath.reverse_reverse]

/-- **The additive preprojective algebra is isomorphic to its opposite algebra.** The isomorphism
is induced by reversing every path of the doubled quiver. -/
noncomputable def preprojectiveOpAlgEquiv :
    preprojectiveAlgebra k Q ≃ₐ[k] (preprojectiveAlgebra k Q)ᵐᵒᵖ :=
  AlgEquiv.ofAlgHom (preprojectiveReverseOpAlgHom k Q)
    (AlgHom.opComm (preprojectiveReverseOpAlgHom k Q))
    (by
      apply AlgHom.ext
      intro z
      obtain ⟨y, rfl⟩ := MulOpposite.op_surjective z
      obtain ⟨x, rfl⟩ := preprojectiveMk_surjective k Q y
      simp only [AlgHom.comp_apply, AlgHom.id_apply]
      exact (preprojectiveReverseOpAlgHom_involutive_preprojectiveMk k Q x).1)
    (by
      apply AlgHom.ext
      intro y
      obtain ⟨x, rfl⟩ := preprojectiveMk_surjective k Q y
      simp only [AlgHom.comp_apply, AlgHom.id_apply]
      exact (preprojectiveReverseOpAlgHom_involutive_preprojectiveMk k Q x).2)

/-- On an arbitrary path-algebra representative, the opposite-algebra isomorphism reverses the
representative before applying the opposite of the quotient map. -/
@[simp]
theorem preprojectiveOpAlgEquiv_preprojectiveMk (x : pathAlgebra k (Symmetrify Q)) :
    preprojectiveOpAlgEquiv k Q (preprojectiveMk k Q x) =
      (AlgHom.op (preprojectiveMk k Q)) (reverseOpAlgEquiv k (Symmetrify Q) x) := by
  rw [preprojectiveOpAlgEquiv, AlgEquiv.ofAlgHom_apply,
    preprojectiveReverseOpAlgHom_preprojectiveMk, preprojectiveReversePathAlgHom,
    AlgHom.comp_apply]
  rfl

/-- On the opposite of an arbitrary path-algebra representative, the inverse opposite-algebra
isomorphism reverses the representative before applying the quotient map. -/
@[simp]
theorem preprojectiveOpAlgEquiv_symm_op_preprojectiveMk (x : pathAlgebra k (Symmetrify Q)) :
    (preprojectiveOpAlgEquiv k Q).symm (op (preprojectiveMk k Q x)) =
      preprojectiveMk k Q (unop (reverseOpAlgEquiv k (Symmetrify Q) x)) := by
  rw [preprojectiveOpAlgEquiv, AlgEquiv.ofAlgHom_symm, AlgEquiv.ofAlgHom_apply,
    AlgHom.opComm_apply_apply, unop_op, preprojectiveReverseOpAlgHom_preprojectiveMk,
    preprojectiveReversePathAlgHom, AlgHom.comp_apply]
  -- Expose the coerced `AlgEquiv` application so `AlgHom.op` can compute on it.
  change unop ((AlgHom.op (preprojectiveMk k Q)) (reverseOpAlgEquiv k (Symmetrify Q) x)) = _
  rw [AlgHom.op_apply_apply, unop_op]

/- The generator formulas below specialize the two representative rules above, which are the simp
normal forms: `simp` derives each of them from those rules, so they carry no `@[simp]` attribute
of their own. -/

/-- On a path class, the opposite-algebra isomorphism takes the opposite of the class of the
reversed path. -/
theorem preprojectiveOpAlgEquiv_preprojectiveMk_ofPath
    (x : Quiver.TotalPath (Symmetrify Q)) :
    preprojectiveOpAlgEquiv k Q (preprojectiveMk k Q (ofPath x)) =
      op (preprojectiveMk k Q (ofPath x.reverse)) := by
  rw [preprojectiveOpAlgEquiv_preprojectiveMk, reverseOpAlgEquiv_ofPath]
  rfl

/-- The inverse opposite-algebra isomorphism reverses a path representative as well. -/
theorem preprojectiveOpAlgEquiv_symm_op_preprojectiveMk_ofPath
    (x : Quiver.TotalPath (Symmetrify Q)) :
    (preprojectiveOpAlgEquiv k Q).symm (op (preprojectiveMk k Q (ofPath x))) =
      preprojectiveMk k Q (ofPath x.reverse) := by
  rw [preprojectiveOpAlgEquiv, AlgEquiv.ofAlgHom_symm, AlgEquiv.ofAlgHom_apply,
    preprojectiveReverseOpAlgHom_opComm_op_preprojectiveMk_ofPath]

/-- The opposite-algebra isomorphism fixes every vertex idempotent class, up to passage to the
opposite algebra. -/
theorem preprojectiveOpAlgEquiv_preprojectiveMk_doubledVertexIdempotent (i : Q) :
    preprojectiveOpAlgEquiv k Q (preprojectiveMk k Q (doubledVertexIdempotent k i)) =
      op (preprojectiveMk k Q (doubledVertexIdempotent k i)) := by
  rw [preprojectiveOpAlgEquiv_preprojectiveMk, reverseOpAlgEquiv_doubledVertexIdempotent,
    AlgHom.op_apply_apply, unop_op]

/-- The opposite-algebra isomorphism sends a doubled arrow class to the opposite of the class of
its formal reverse. -/
theorem preprojectiveOpAlgEquiv_preprojectiveMk_ofArrow {i j : Symmetrify Q} (a : i ⟶ j) :
    preprojectiveOpAlgEquiv k Q (preprojectiveMk k Q (ofArrow a)) =
      op (preprojectiveMk k Q (ofArrow (Quiver.reverse a))) := by
  rw [ofArrow_eq_ofPath, preprojectiveOpAlgEquiv_preprojectiveMk_ofPath,
    Quiver.TotalPath.reverse_mk, Path.reverse_toPath, ofArrow_eq_ofPath]

end Quotient

end TauCeti
