/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Adjoin

/-!
# Finite matrix-coefficient submodules

This file proves that the matrix-coefficient submodule of a finite projective right comodule
over a commutative semiring is finite.

This is the first finite-dimensionality step toward the fundamental theorem of comodules in
the reductive-groups roadmap. The next substantive step is to show that this finite submodule
is closed under comultiplication, making it a coefficient subcoalgebra.

## Main results

* `TauCeti.Comodule.matrixCoefficientSubmodule_finite`: a finite projective comodule has a
  finite matrix-coefficient submodule.

## References

The coefficient-space construction is standard; see Sweedler, *Hopf Algebras*, Chapter 2.
It advances `ReductiveGroups/README.md` in TauCetiRoadmap, Layer 1,
"Finite-dimensional subcoalgebras (the fundamental theorem of comodules)".
-/

public section

namespace TauCeti

namespace Comodule

universe u v w

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- The matrix-coefficient submodule of a finite projective comodule is finite. -/
theorem matrixCoefficientSubmodule_finite
    [Module.Finite R M] [Module.Projective R M] :
    Module.Finite R
      (matrixCoefficientSubmodule (R := R) (C := C) (M := M)) := by
  rw [← range_matrixCoefficientTensor]
  infer_instance

end Comodule

end TauCeti
