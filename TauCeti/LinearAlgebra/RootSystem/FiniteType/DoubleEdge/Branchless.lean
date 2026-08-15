/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.DoubleEdge.Basic
import TauCeti.LinearAlgebra.RootSystem.FiniteType.DoubleEdge.Reindex
import TauCeti.LinearAlgebra.RootSystem.FiniteType.TwoDoubleEdges

public section

/-!
# The branchless double-edge case of the finite-type classification

A connected finite-type Cartan diagram of maximum degree two is a path. If one edge of that path is
double, `TauCeti.IsFiniteType.exists_equiv_forall_eq_doubleEdgeCartanMatrix` reindexes the diagram
onto `TauCeti.doubleEdgeCartanMatrix p q`, and the double-edge bound
`TauCeti.eq_one_or_eq_one_or_eq_two_two_of_isFiniteType_doubleEdge` leaves precisely the families
`B_n`, `C_n`, and the exceptional type `F_4`.

The double edge is taken here in the orientation-free form `A u v * A v u = 2`, which is what the
sign conditions of a finite-type matrix produce at a multiple edge. Its two orientations reindex to
the two transposed models, and the alternatives below are stated so as to cover both.

Excluding a branch vertex from a connected finite-type diagram containing a double edge remains the
final extraction step before this result applies to the unrestricted double-edge branch.

## Main results

* `IsFiniteType.exists_equiv_forall_eq_doubleEdgeCartanMatrix_eq_one_or_eq_one_or_eq_two_two`
  (in the `TauCeti` namespace, the full name being too long for one line): a preconnected
  finite-type diagram of maximum degree two containing a double edge is a double-edge model whose
  two nonempty arms have one of the `B`, `C`, and `F_4` shapes.

## References

This is the branchless double-edge case of the "classification of finite-type Cartan matrices" in
Layer 5 of `TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. The exclusion of two
multiple edges is the affine-diagram argument in N. Bourbaki, *Lie Groups and Lie Algebras,
Chapters 4--6*, Chapter VI, section 4, and J. E. Humphreys, *Introduction to Lie Algebras and
Representation Theory*, section 11.4.
-/

namespace TauCeti

open SimpleGraph

variable {B : Type*} [Fintype B] {A : Matrix B B ℤ}

/-- **The branchless double-edge case is a double-edge model of one of the admissible shapes.** A
preconnected finite-type diagram of maximum degree two in which the edge `u -- v` is double
reindexes to two nonempty chains joined by that edge, and those chains have one of the three shapes
in the Cartan--Killing list: the second is a singleton (type `C`), the first is a singleton (type
`B`), or both have two vertices (type `F_4`).

The double edge is given by the orientation-free hypothesis `A u v * A v u = 2`; the two
orientations of the edge give the two transposed models, both of which the disjunction covers. -/
-- `degree` needs finite neighbour sets while the theorem type is elaborated, so this decidability
-- instance cannot be confined to the proof.
theorem IsFiniteType.exists_equiv_forall_eq_doubleEdgeCartanMatrix_eq_one_or_eq_one_or_eq_two_two
    [DecidableEq B] (h : IsFiniteType A) (hconn : (diagramGraph A).Preconnected)
    (hdeg : ∀ i, (diagramGraph A).degree i ≤ 2)
    {u v : B} (huv : A u v * A v u = 2) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (q = 1 ∨ p = 1 ∨ (p = 2 ∧ q = 2)) ∧
      ∃ e : B ≃ Fin p ⊕ Fin q,
        ∀ i j, A i j = doubleEdgeCartanMatrix p q (e i) (e j) := by
  -- Either orientation of the double edge reindexes; the model classification then applies to the
  -- resulting model, which finite type inherits as a principal submatrix.
  have key : ∀ {x y : B}, A y x = -2 →
      ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (q = 1 ∨ p = 1 ∨ (p = 2 ∧ q = 2)) ∧
        ∃ e : B ≃ Fin p ⊕ Fin q,
          ∀ i j, A i j = doubleEdgeCartanMatrix p q (e i) (e j) := by
    intro x y hyx
    obtain ⟨p, q, hp, hq, e, he⟩ := h.exists_equiv_forall_eq_doubleEdgeCartanMatrix hconn hdeg hyx
    have hmatrix : doubleEdgeCartanMatrix p q = A.submatrix e.symm e.symm := by
      ext i j
      simpa only [Matrix.submatrix_apply, e.apply_symm_apply] using (he (e.symm i) (e.symm j)).symm
    have hmodel : IsFiniteType (doubleEdgeCartanMatrix p q) := by
      rw [hmatrix]
      exact h.submatrix e.symm.injective
    exact ⟨p, q, hp, hq, eq_one_or_eq_one_or_eq_two_two_of_isFiniteType_doubleEdge hp hq hmodel,
      e, he⟩
  -- A double edge has entries `-1` and `-2`, in one order or the other.
  have hne : u ≠ v := by
    rintro rfl
    rw [h.apply_self] at huv
    norm_num at huv
  rcases eq_neg_one_and_eq_neg_two_or_of_mul_eq_two (h.apply_le_zero_of_ne hne) huv with
    ⟨-, hvu⟩ | ⟨huv', -⟩
  · exact key hvu
  · exact key huv'

end TauCeti
