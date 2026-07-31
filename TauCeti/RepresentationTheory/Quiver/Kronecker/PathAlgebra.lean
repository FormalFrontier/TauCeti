/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Kronecker.Basic
public import TauCeti.RepresentationTheory.Quiver.Acyclic.PathAlgebra

/-!
# The path algebra of the generalized Kronecker quiver

The generalized Kronecker quiver on `n` arrows has `n + 2` paths: the two trivial paths and the
arrows themselves. It is acyclic, so its path algebra is finite-dimensional, of dimension `n + 2`;
for the Kronecker quiver `• ⇉ •` itself this is `4`.

## Main results

* `TauCeti.Quiver.Kronecker.card_totalPath` and
  `TauCeti.Quiver.Kronecker.finrank_pathAlgebra`: there are `n + 2` paths, so the path algebra has
  dimension `n + 2`.
* `TauCeti.Quiver.Kronecker.finrank_pathAlgebra_eq_four`: for the Kronecker quiver `• ⇉ •` the path
  algebra is four-dimensional.

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

/-- The path algebra of the generalized Kronecker quiver on `n` arrows has dimension `n + 2`. For
the Kronecker quiver `• ⇉ •` itself this is `4`. -/
theorem finrank_pathAlgebra (k : Type w) [DivisionRing k] [Fintype A] :
    Module.finrank k (pathAlgebra k (Kronecker A)) = Fintype.card A + 2 := by
  rw [TauCeti.finrank_pathAlgebra k (Kronecker A), card_totalPath]

/-- The path algebra of the generalized Kronecker quiver is finite-dimensional: unlike the one-loop
quiver, it is acyclic, so it has only finitely many paths. -/
theorem finiteDimensional_pathAlgebra (k : Type w) [DivisionRing k] [Finite A] :
    FiniteDimensional k (pathAlgebra k (Kronecker A)) :=
  finiteDimensional_pathAlgebra_of_isAcyclic k (Kronecker A) isAcyclic

/-- The path algebra of the Kronecker quiver is four-dimensional: two trivial paths and two
arrows. -/
theorem finrank_pathAlgebra_eq_four [Fintype A] (h : Fintype.card A = 2) (k : Type w)
    [DivisionRing k] : Module.finrank k (pathAlgebra k (Kronecker A)) = 4 := by
  rw [finrank_pathAlgebra k, h]

end Quiver.Kronecker

end TauCeti
