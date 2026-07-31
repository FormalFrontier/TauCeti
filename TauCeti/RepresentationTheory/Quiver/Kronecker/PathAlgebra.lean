/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Kronecker.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra

/-!
# The path algebra of the generalized Kronecker quiver

The generalized Kronecker quiver on `n` arrows has `n + 2` paths: the two trivial paths and the
arrows themselves. So its path algebra has dimension `n + 2`; for the Kronecker quiver `• ⇉ •`
itself this is `4`. Finite-dimensionality needs nothing specific to this quiver: it is acyclic, so
`TauCeti.finiteDimensional_pathAlgebra_of_isAcyclic` applies to it as it stands, via
`TauCeti.Quiver.Kronecker.isAcyclic`.

## Main results

* `TauCeti.Quiver.Kronecker.card_totalPath` and
  `TauCeti.Quiver.Kronecker.finrank_pathAlgebra`: there are `n + 2` paths, so the path algebra has
  dimension `n + 2`.
* `TauCeti.Quiver.Kronecker.totalPath_eq_or`: for a single arrow the three paths are named
  individually.
* `TauCeti.Quiver.Kronecker.finrank_pathAlgebra_eq_four` and
  `TauCeti.Quiver.Kronecker.finrank_pathAlgebra_eq_three`: for the Kronecker quiver `• ⇉ •` the
  path algebra is four-dimensional, and for the `A₂` quiver `• → •` three-dimensional.

## References

This file supplies the four-dimensional path algebra asked for by the “Kronecker quiver” worked
example of `TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`. See
Derksen--Weyman, *An Introduction to Quiver Representations*, and Assem--Simson--Skowroński,
*Elements of the Representation Theory of Associative Algebras I*, Ch. II.
-/

public section

namespace TauCeti

open _root_.Quiver

universe v w

namespace Quiver.Kronecker

variable {A : Type v}

/-- The generalized Kronecker quiver on `n` arrows has `n + 2` paths: the two trivial paths and the
arrows themselves. -/
theorem card_totalPath [Fintype A] :
    Fintype.card (Quiver.TotalPath (Kronecker A)) = Fintype.card A + 2 := by
  have h : Fintype.card (Quiver.TotalPath (Kronecker A))
      = ∑ a : Kronecker A, ∑ b : Kronecker A, Fintype.card (Path a b) := by
    rw [Fintype.card_sigma]
    exact Finset.sum_congr rfl fun _ _ => Fintype.card_sigma
  rw [h]
  simp only [sum_univ, card_path_src_tgt, Fintype.card_unique, Fintype.card_eq_zero]
  omega

/-- The `A₂` quiver has exactly three paths: the trivial path at each vertex, and its arrow. -/
theorem totalPath_eq_or [Unique A] (x : Quiver.TotalPath (Kronecker A)) :
    x = ⟨tgt, tgt, Path.nil⟩ ∨ x = ⟨src, tgt, arrowPath default⟩ ∨
      x = ⟨src, src, Path.nil⟩ := by
  obtain ⟨a, b, p⟩ := x
  cases a <;> cases b
  · exact Or.inr (Or.inr (by rw [path_src_src_eq_nil p]))
  · refine Or.inr (Or.inl ?_)
    have h := arrowPath_pathEquivArrow p
    rw [Unique.eq_default (pathEquivArrow p)] at h
    rw [h]
  · exact isEmptyElim p
  · exact Or.inl (by rw [path_tgt_tgt_eq_nil p])

/-- The path algebra of the generalized Kronecker quiver on `n` arrows has dimension `n + 2`. For
the Kronecker quiver `• ⇉ •` itself this is `4`. -/
theorem finrank_pathAlgebra (k : Type w) [DivisionRing k] [Fintype A] :
    Module.finrank k (pathAlgebra k (Kronecker A)) = Fintype.card A + 2 := by
  rw [TauCeti.finrank_pathAlgebra k (Kronecker A), card_totalPath]

/-- The path algebra of the Kronecker quiver is four-dimensional: two trivial paths and two
arrows. -/
theorem finrank_pathAlgebra_eq_four [Fintype A] (h : Fintype.card A = 2) (k : Type w)
    [DivisionRing k] : Module.finrank k (pathAlgebra k (Kronecker A)) = 4 := by
  rw [finrank_pathAlgebra k, h]

/-- The path algebra of the `A₂` quiver is three-dimensional: the two trivial paths and the
arrow. -/
theorem finrank_pathAlgebra_eq_three [Unique A] (k : Type w) [DivisionRing k] :
    Module.finrank k (pathAlgebra k (Kronecker A)) = 3 := by
  letI : Fintype A := Fintype.ofFinite A
  rw [finrank_pathAlgebra k, Fintype.card_unique]

end Quiver.Kronecker

end TauCeti
