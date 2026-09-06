/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RepresentationTheory.Spin.OddStructure
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Three

/-!
# The chosen even Clifford matrix model in dimension three

This file chooses the two-by-two matrix model of a nondegenerate three-dimensional quadratic
space. Generic reversal results live in `LinearAlgebra/CliffordAlgebra/Reversal/Three.lean`.

## References

This is the matrix-model step of Layer 6 in the
[SpinRepresentations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md).
See Fulton and Harris, *Representation Theory: A First Course*, Lecture 20.
-/

public section

universe u v

namespace CliffordAlgebra

variable {K : Type u} [Field K] [NeZero (2 : K)] [IsSepClosed K]
  {V : Type v} [AddCommGroup V] [Module K V]
  (Q : QuadraticForm K V)

/-- A chosen matrix model of the even Clifford algebra of a nondegenerate three-dimensional
quadratic space over a separably closed field of characteristic not two. -/
noncomputable def evenEquivMatrixFinTwoOfFinrankEqThree
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) :
    ↥(even Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K :=
  let _ : FiniteDimensional K V := .of_finrank_eq_succ (by omega)
  (nonempty_algEquiv_even_matrix_of_finrank_eq_two_mul_add_one hQ (l := 1) (by omega)).some

/-- In the chosen two-by-two matrix model, Clifford reversal is matrix adjugation. -/
@[simp]
theorem evenEquivMatrixFinTwoOfFinrankEqThree_reverse
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) (x : ↥(even Q)) :
    evenEquivMatrixFinTwoOfFinrankEqThree Q hQ hV (reverseEven Q x) =
      Matrix.adjugate (evenEquivMatrixFinTwoOfFinrankEqThree Q hQ hV x) :=
  map_reverseEven_eq_adjugate_of_finrank_eq_three Q hV
    (evenEquivMatrixFinTwoOfFinrankEqThree Q hQ hV) x

end CliffordAlgebra
