/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Opposite
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Gauge

/-!
# The opposite of a preprojective algebra

Reversing every path of the doubled quiver preserves each of the two backtracks attached to an
original arrow. It therefore preserves every gauged preprojective relator `ρ_ε`, whatever the
labelling `ε`, and descends to an isomorphism from the gauged preprojective algebra to its
opposite. Specializing to the constant labelling `1` gives the same isomorphism for the additive
preprojective algebra. On a path class the isomorphism takes the class of the path to the opposite
of the class of its reverse.

## Main results

* `TauCeti.reverseOpAlgEquiv_gaugedPreprojectiveRelator`: path reversal preserves every gauged
  preprojective relator, up to passage to the opposite algebra.
* `TauCeti.reverseOpAlgEquiv_preprojectiveRelator` and
  `TauCeti.reverseOpAlgEquiv_localPreprojectiveRelator`: the same statement for the preprojective
  relator and for each local relator.
* `TauCeti.gaugedPreprojectiveOpAlgEquiv`: every gauged preprojective algebra is isomorphic to its
  opposite.
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

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- **Path reversal preserves every gauged preprojective relator**, up to passage to the opposite
path algebra. Both backtracks of every arrow are palindromic, so each signed difference is fixed
however its coefficient is chosen. -/
@[simp]
theorem reverseOpAlgEquiv_gaugedPreprojectiveRelator (ε : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) :
    reverseOpAlgEquiv k (Symmetrify Q) (gaugedPreprojectiveRelator k ε) =
      op (gaugedPreprojectiveRelator k ε) := by
  rw [gaugedPreprojectiveRelator_def]
  simp only [map_sum, map_smul, map_sub, reverseOpAlgEquiv_headBacktrackElem,
    reverseOpAlgEquiv_tailBacktrackElem, Finset.op_sum, op_smul, op_sub]

variable (Q)

/-- **Path reversal preserves the preprojective relator**, up to passage to the opposite path
algebra. This is the constant labelling `1` of the gauged statement. -/
@[simp]
theorem reverseOpAlgEquiv_preprojectiveRelator :
    reverseOpAlgEquiv k (Symmetrify Q) (preprojectiveRelator k Q) =
      op (preprojectiveRelator k Q) := by
  rw [← gaugedPreprojectiveRelator_one, reverseOpAlgEquiv_gaugedPreprojectiveRelator]

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

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)] (ε : ∀ ⦃i j : Q⦄, (i ⟶ j) → k)

/-- Reversal followed by the opposite of the gauged preprojective quotient map. -/
private noncomputable def gaugedPreprojectiveReversePathAlgHom :
    pathAlgebra k (Symmetrify Q) →ₐ[k] (gaugedPreprojectiveAlgebra k ε)ᵐᵒᵖ :=
  (AlgHom.op (gaugedPreprojectiveMk k ε)).comp
    (reverseOpAlgEquiv k (Symmetrify Q)).toAlgHom

private theorem gaugedPreprojectiveReversePathAlgHom_relator :
    gaugedPreprojectiveReversePathAlgHom k ε (gaugedPreprojectiveRelator k ε) = 0 := by
  rw [gaugedPreprojectiveReversePathAlgHom, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    reverseOpAlgEquiv_gaugedPreprojectiveRelator]
  simp

/-- The path-reversal homomorphism from a gauged preprojective algebra to its opposite, obtained
by descending reversal of the doubled path algebra through the gauged relation. -/
private noncomputable def gaugedPreprojectiveReverseOpAlgHom :
    gaugedPreprojectiveAlgebra k ε →ₐ[k] (gaugedPreprojectiveAlgebra k ε)ᵐᵒᵖ :=
  gaugedPreprojectiveLift k ε (gaugedPreprojectiveReversePathAlgHom k ε)
    (gaugedPreprojectiveReversePathAlgHom_relator k ε)

private theorem gaugedPreprojectiveReverseOpAlgHom_gaugedPreprojectiveMk (x) :
    gaugedPreprojectiveReverseOpAlgHom k ε (gaugedPreprojectiveMk k ε x) =
      gaugedPreprojectiveReversePathAlgHom k ε x := by
  rw [gaugedPreprojectiveReverseOpAlgHom, gaugedPreprojectiveLift_gaugedPreprojectiveMk]

private theorem gaugedPreprojectiveReverseOpAlgHom_gaugedPreprojectiveMk_ofPath
    (x : Quiver.TotalPath (Symmetrify Q)) :
    gaugedPreprojectiveReverseOpAlgHom k ε (gaugedPreprojectiveMk k ε (ofPath x)) =
      op (gaugedPreprojectiveMk k ε (ofPath x.reverse)) := by
  rw [gaugedPreprojectiveReverseOpAlgHom_gaugedPreprojectiveMk,
    gaugedPreprojectiveReversePathAlgHom, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    reverseOpAlgEquiv_ofPath, AlgHom.op_apply_apply, unop_op]

private theorem gaugedPreprojectiveReverseOpAlgHom_opComm_op_gaugedPreprojectiveMk_ofPath
    (x : Quiver.TotalPath (Symmetrify Q)) :
    AlgHom.opComm (gaugedPreprojectiveReverseOpAlgHom k ε)
        (op (gaugedPreprojectiveMk k ε (ofPath x))) =
      gaugedPreprojectiveMk k ε (ofPath x.reverse) := by
  rw [AlgHom.opComm_apply_apply, unop_op,
    gaugedPreprojectiveReverseOpAlgHom_gaugedPreprojectiveMk_ofPath, unop_op]

private theorem gaugedPreprojectiveReverseOpAlgHom_involutive_gaugedPreprojectiveMk
    (x : pathAlgebra k (Symmetrify Q)) :
    (gaugedPreprojectiveReverseOpAlgHom k ε
          (AlgHom.opComm (gaugedPreprojectiveReverseOpAlgHom k ε)
            (op (gaugedPreprojectiveMk k ε x))) = op (gaugedPreprojectiveMk k ε x)) ∧
      (AlgHom.opComm (gaugedPreprojectiveReverseOpAlgHom k ε)
          (gaugedPreprojectiveReverseOpAlgHom k ε (gaugedPreprojectiveMk k ε x)) =
        gaugedPreprojectiveMk k ε x) := by
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
          gaugedPreprojectiveReverseOpAlgHom_opComm_op_gaugedPreprojectiveMk_ofPath,
          gaugedPreprojectiveReverseOpAlgHom_gaugedPreprojectiveMk_ofPath,
          Quiver.TotalPath.reverse_reverse]
      · rw [single_eq_smul_ofPath, map_smul, map_smul, map_smul,
          gaugedPreprojectiveReverseOpAlgHom_gaugedPreprojectiveMk_ofPath,
          gaugedPreprojectiveReverseOpAlgHom_opComm_op_gaugedPreprojectiveMk_ofPath,
          Quiver.TotalPath.reverse_reverse]

/-- **A gauged preprojective algebra is isomorphic to its opposite algebra.** The isomorphism is
induced by reversing every path of the doubled quiver, which fixes both backtracks of every arrow
and hence the gauged relator, whatever the labelling. -/
noncomputable def gaugedPreprojectiveOpAlgEquiv :
    gaugedPreprojectiveAlgebra k ε ≃ₐ[k] (gaugedPreprojectiveAlgebra k ε)ᵐᵒᵖ :=
  AlgEquiv.ofAlgHom (gaugedPreprojectiveReverseOpAlgHom k ε)
    (AlgHom.opComm (gaugedPreprojectiveReverseOpAlgHom k ε))
    (by
      apply AlgHom.ext
      intro z
      obtain ⟨y, rfl⟩ := MulOpposite.op_surjective z
      obtain ⟨x, rfl⟩ := gaugedPreprojectiveMk_surjective k ε y
      simp only [AlgHom.comp_apply, AlgHom.id_apply]
      exact (gaugedPreprojectiveReverseOpAlgHom_involutive_gaugedPreprojectiveMk k ε x).1)
    (by
      apply AlgHom.ext
      intro y
      obtain ⟨x, rfl⟩ := gaugedPreprojectiveMk_surjective k ε y
      simp only [AlgHom.comp_apply, AlgHom.id_apply]
      exact (gaugedPreprojectiveReverseOpAlgHom_involutive_gaugedPreprojectiveMk k ε x).2)

/-- On an arbitrary path-algebra representative, the gauged opposite-algebra isomorphism reverses
the representative before applying the opposite of the quotient map. -/
@[simp]
theorem gaugedPreprojectiveOpAlgEquiv_gaugedPreprojectiveMk (x : pathAlgebra k (Symmetrify Q)) :
    gaugedPreprojectiveOpAlgEquiv k ε (gaugedPreprojectiveMk k ε x) =
      (AlgHom.op (gaugedPreprojectiveMk k ε)) (reverseOpAlgEquiv k (Symmetrify Q) x) := by
  rw [gaugedPreprojectiveOpAlgEquiv, AlgEquiv.ofAlgHom_apply,
    gaugedPreprojectiveReverseOpAlgHom_gaugedPreprojectiveMk,
    gaugedPreprojectiveReversePathAlgHom, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply]

/-- On the opposite of an arbitrary path-algebra representative, the inverse gauged
opposite-algebra isomorphism reverses the representative before applying the quotient map. -/
@[simp]
theorem gaugedPreprojectiveOpAlgEquiv_symm_op_gaugedPreprojectiveMk
    (x : pathAlgebra k (Symmetrify Q)) :
    (gaugedPreprojectiveOpAlgEquiv k ε).symm (op (gaugedPreprojectiveMk k ε x)) =
      gaugedPreprojectiveMk k ε (unop (reverseOpAlgEquiv k (Symmetrify Q) x)) := by
  rw [gaugedPreprojectiveOpAlgEquiv, AlgEquiv.ofAlgHom_symm, AlgEquiv.ofAlgHom_apply,
    AlgHom.opComm_apply_apply, unop_op, gaugedPreprojectiveReverseOpAlgHom_gaugedPreprojectiveMk,
    gaugedPreprojectiveReversePathAlgHom, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    AlgHom.op_apply_apply, unop_op]

variable (Q)

private theorem preprojectiveAlgebraEquivGaugedOne_op_symm_op
    (y : (pathAlgebra k (Symmetrify Q))ᵐᵒᵖ) :
    (AlgEquiv.op (preprojectiveAlgebraEquivGaugedOne (Q := Q) k)).symm
        ((AlgHom.op (gaugedPreprojectiveMk k fun _ _ _ => 1)) y) =
      (AlgHom.op (preprojectiveMk k Q)) y := by
  rw [AlgEquiv.symm_apply_eq, AlgHom.op_apply_apply, AlgEquiv.op_apply_apply,
    AlgHom.op_apply_apply, unop_op, preprojectiveAlgebraEquivGaugedOne_preprojectiveMk]

/-- **The additive preprojective algebra is isomorphic to its opposite algebra.** The isomorphism
is induced by reversing every path of the doubled quiver; it is the constant labelling `1` of
`TauCeti.gaugedPreprojectiveOpAlgEquiv`, transported along the identification of the two
presentations. -/
noncomputable def preprojectiveOpAlgEquiv :
    preprojectiveAlgebra k Q ≃ₐ[k] (preprojectiveAlgebra k Q)ᵐᵒᵖ :=
  (preprojectiveAlgebraEquivGaugedOne (Q := Q) k).trans <|
    (gaugedPreprojectiveOpAlgEquiv k fun _ _ _ => 1).trans <|
      (AlgEquiv.op (preprojectiveAlgebraEquivGaugedOne (Q := Q) k)).symm

/-- On an arbitrary path-algebra representative, the opposite-algebra isomorphism reverses the
representative before applying the opposite of the quotient map. -/
@[simp]
theorem preprojectiveOpAlgEquiv_preprojectiveMk (x : pathAlgebra k (Symmetrify Q)) :
    preprojectiveOpAlgEquiv k Q (preprojectiveMk k Q x) =
      (AlgHom.op (preprojectiveMk k Q)) (reverseOpAlgEquiv k (Symmetrify Q) x) := by
  rw [preprojectiveOpAlgEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    preprojectiveAlgebraEquivGaugedOne_preprojectiveMk,
    gaugedPreprojectiveOpAlgEquiv_gaugedPreprojectiveMk,
    preprojectiveAlgebraEquivGaugedOne_op_symm_op]

/-- On the opposite of an arbitrary path-algebra representative, the inverse opposite-algebra
isomorphism reverses the representative before applying the quotient map. -/
@[simp]
theorem preprojectiveOpAlgEquiv_symm_op_preprojectiveMk (x : pathAlgebra k (Symmetrify Q)) :
    (preprojectiveOpAlgEquiv k Q).symm (op (preprojectiveMk k Q x)) =
      preprojectiveMk k Q (unop (reverseOpAlgEquiv k (Symmetrify Q) x)) := by
  rw [preprojectiveOpAlgEquiv, AlgEquiv.symm_trans_apply, AlgEquiv.symm_trans_apply,
    AlgEquiv.symm_symm, AlgEquiv.op_apply_apply, unop_op,
    preprojectiveAlgebraEquivGaugedOne_preprojectiveMk,
    gaugedPreprojectiveOpAlgEquiv_symm_op_gaugedPreprojectiveMk,
    preprojectiveAlgebraEquivGaugedOne_symm_gaugedPreprojectiveMk]

/- The generator formulas below specialize the two representative rules above, which are the simp
normal forms: `simp` derives each of them from those rules, so they carry no `@[simp]` attribute
of their own. -/

/-- On a path class, the opposite-algebra isomorphism takes the opposite of the class of the
reversed path. -/
theorem preprojectiveOpAlgEquiv_preprojectiveMk_ofPath
    (x : Quiver.TotalPath (Symmetrify Q)) :
    preprojectiveOpAlgEquiv k Q (preprojectiveMk k Q (ofPath x)) =
      op (preprojectiveMk k Q (ofPath x.reverse)) := by
  rw [preprojectiveOpAlgEquiv_preprojectiveMk, reverseOpAlgEquiv_ofPath,
    AlgHom.op_apply_apply, unop_op]

/-- The inverse opposite-algebra isomorphism reverses a path representative as well. -/
theorem preprojectiveOpAlgEquiv_symm_op_preprojectiveMk_ofPath
    (x : Quiver.TotalPath (Symmetrify Q)) :
    (preprojectiveOpAlgEquiv k Q).symm (op (preprojectiveMk k Q (ofPath x))) =
      preprojectiveMk k Q (ofPath x.reverse) := by
  rw [preprojectiveOpAlgEquiv_symm_op_preprojectiveMk, reverseOpAlgEquiv_ofPath, unop_op]

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
