/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import TauCeti.AlgebraicTopology.SimplicialComplex.Dimension
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization

/-!
# Contractible two-dimensional simplicial complexes

This file supplies the predicate used in the statement of Zeeman's collapsibility conjecture.
An abstract simplicial complex is a **contractible 2-complex** when it has finitely many faces,
dimension at most two, and contractible geometric realization.  The finiteness condition records
the finite complexes considered by simplicial collapse, while the dimension bound is expressed
using the intrinsic dimension from `Dimension` rather than a bound on the ambient vertex type.

The standard one-simplex is provided as a nontrivial witness.  Its realization is contractible by
the homeomorphism with Mathlib's convex standard simplex, so the predicate is exercised without
assuming the desired Zeeman conclusion.

## Main definitions

* `AbstractSimplicialComplex.Contractible2Complex`: finite, at-most-two-dimensional complexes
  with contractible realization.

## Main results

* `AbstractSimplicialComplex.contractible2Complex_iff`: the defining characterization.
* `AbstractSimplicialComplex.contractible2Complex_standardOneSimplex`: the standard one-simplex
  is a non-void contractible 2-complex (the dimension bound is at most two).
* `AbstractSimplicialComplex.contractible2Complex_standardOneSimplex_faces_finite`: its
  finiteness component, useful when passing to the collapse API.

No claim that a product with an interval is collapsible is made here.
-/

public section

noncomputable section

open Set

namespace AbstractSimplicialComplex

variable {ι : Type*}

/-- A finite abstract simplicial complex of dimension at most two whose realization is
contractible.  This is the class of complexes occurring in Zeeman's conjecture. -/
def Contractible2Complex (K : AbstractSimplicialComplex ι) : Prop :=
  K.faces.Finite ∧ dimension K ≤ (2 : WithBot ℕ∞) ∧ ContractibleSpace (Realization K)

/-- The defining finiteness, dimension, and contractibility conditions for a contractible
2-complex. -/
theorem contractible2Complex_iff {K : AbstractSimplicialComplex ι} :
    Contractible2Complex K ↔
      K.faces.Finite ∧ dimension K ≤ (2 : WithBot ℕ∞) ∧ ContractibleSpace (Realization K) :=
  Iff.rfl

namespace Contractible2Complex

variable {K : AbstractSimplicialComplex ι}

/-- A contractible 2-complex has finitely many faces. -/
theorem finite_faces (hK : Contractible2Complex K) : K.faces.Finite :=
  hK.1

/-- A contractible 2-complex has dimension at most two. -/
theorem dimension_le_two (hK : Contractible2Complex K) : dimension K ≤ (2 : WithBot ℕ∞) :=
  hK.2.1

/-- The realization of a contractible 2-complex is contractible. -/
theorem contractibleSpace (hK : Contractible2Complex K) : ContractibleSpace (Realization K) :=
  hK.2.2

end Contractible2Complex

/-- The standard one-simplex gives a concrete non-void witness for the `≤ 2` dimension bound. -/
theorem contractible2Complex_standardOneSimplex :
    Contractible2Complex (⊤ : AbstractSimplicialComplex (Fin 2)) := by
  let e := realizationOneSimplexHomeomorphUnitInterval
  let hunit : ContractibleSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  have hreal : ContractibleSpace (Realization (⊤ : AbstractSimplicialComplex (Fin 2))) :=
    @Homeomorph.contractibleSpace _ _ _ _ hunit e
  refine ⟨?_, ?_, hreal⟩
  · change ((⊤ : PreAbstractSimplicialComplex (Fin 2)).faces).Finite
    simpa only [PreAbstractSimplicialComplex.simplex_univ] using
      (PreAbstractSimplicialComplex.finite_faces_simplex (Finset.univ : Finset (Fin 2)))
  · calc
      dimension (⊤ : AbstractSimplicialComplex (Fin 2)) ≤
          ((Finset.univ.card - 1 : ℕ) : WithBot ℕ∞) :=
        dimension_le_card_sub_one (V := Finset.univ) (fun _ _ => Finset.subset_univ _)
      _ = (1 : WithBot ℕ∞) := by norm_num
      _ ≤ 2 := by norm_num

/-- The standard one-simplex has finite face set, the finiteness component of the predicate. -/
theorem contractible2Complex_standardOneSimplex_faces_finite :
    ((⊤ : AbstractSimplicialComplex (Fin 2)).faces).Finite :=
  (contractible2Complex_standardOneSimplex).finite_faces

end AbstractSimplicialComplex
