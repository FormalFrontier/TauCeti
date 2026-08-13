/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Combinatorics.SimpleGraph.BranchComponents
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.UniqueBranch

public section

/-!
# The three arms of a simply-laced finite-type diagram

A connected simply-laced finite-type diagram with a branch vertex becomes three paths when that
vertex is deleted.  The finite-type degree bound supplies degree at most three, while the affine
`D` obstruction in `TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.UniqueBranch` says that the
chosen branch vertex is the only vertex of degree three.  The general tree decomposition from
`TauCeti.Combinatorics.SimpleGraph.BranchComponents` then applies.

This is the extraction step connecting arbitrary simply-laced finite-type diagrams to the model
stars classified in `TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.Classification`.  The next
step attaches each path to the deleted vertex, reindexes the matrix onto `starCartanMatrix`, and
applies `TauCeti.IsFiniteType.existsUnique_dynkinType_of_star`.

## Main result

* `TauCeti.IsFiniteType.exists_three_path_components_of_isSimplyLaced`: deleting a branch vertex
  from a connected simply-laced finite-type diagram leaves three path components.

## References

This is the simply-laced extraction step in Layer 5 of the root-systems roadmap.  See J. E.
Humphreys, *Introduction to Lie Algebras and Representation Theory*, Section 11.4, and Bourbaki,
*Lie Groups and Lie Algebras, Chapters 4--6*, Chapter VI, Section 4.
-/

namespace TauCeti

open SimpleGraph

namespace IsFiniteType

variable {B : Type*} [Fintype B] [DecidableEq B] {A : Matrix B B Int}

/-- **Deleting a branch vertex from a connected simply-laced finite-type diagram leaves three
paths.**

The equivalence indexes the components by `Fin 3`; the component at `i` is a path graph on its own
number of vertices.  These cardinalities are the three arm lengths in the subsequent reindexing
onto `TauCeti.starCartanMatrix`. -/
theorem exists_three_path_components_of_isSimplyLaced (h : IsFiniteType A)
    (hconn : (diagramGraph A).Connected) (hsl : A.IsSimplyLaced) {c : B}
    (hc : (diagramGraph A).degree c = 3) :
    ∃ e : Fin 3 ≃ ((diagramGraph A).induce ({c}ᶜ : Set B)).ConnectedComponent,
      ∀ i, Nonempty ((e i).toSimpleGraph ≃g pathGraph (Nat.card (e i))) := by
  have htree : (diagramGraph A).IsTree := h.isTree_diagramGraph hconn
  refine TauCeti.IsTree.exists_equiv_pathGraph_components htree c hc fun v => ?_
  -- Deleting a vertex only removes edges, so it is enough to bound the degree in the diagram.
  have hle : ((diagramGraph A).induce ({c}ᶜ : Set B)).degree v ≤ (diagramGraph A).degree (v : B) :=
    (SimpleGraph.Copy.induce (diagramGraph A) ({c}ᶜ : Set B)).degree_le v
  refine le_trans hle ?_
  have hvc : (v : B) ≠ c := Set.mem_compl_singleton_iff.mp v.property
  have hv3 := h.degree_le_three (v : B)
  by_contra hv2
  have hv : (diagramGraph A).degree (v : B) = 3 := by omega
  exact hvc (h.eq_of_degree_eq_three hsl hconn hv hc)

end IsFiniteType

end TauCeti
