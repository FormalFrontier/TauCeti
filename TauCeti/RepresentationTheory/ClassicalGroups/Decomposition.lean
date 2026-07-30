/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Tensor.Square
public import TauCeti.RepresentationTheory.ClassicalGroups.ExteriorPower
public import TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower
public import TauCeti.RepresentationTheory.ClassicalGroups.TensorPower

/-!
# The first decomposition of the standard representation

When `2` is invertible, the tensor square of a representation splits into its symmetric and
exterior squares. This file establishes the representation equivalence and specializes it to the
standard representation of the general linear group. Over a field, it also records the resulting
character identity.

## Main definitions

* `TauCeti.tensorSquareRepEquiv` specializes it to the standard representation of `GL n k`.
* `TauCeti.char_tensorSquare_stdRep` is the associated character identity.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 1, “The first decomposition”.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 6.
-/

public section

open CategoryTheory
open Matrix
open scoped TensorProduct

namespace TauCeti

variable (k : Type) (n : ℕ)

section Field

variable [Field k] [NeZero (2 : k)]

/-- The tensor square of the standard representation is equivalent to the product of its
symmetric and exterior squares. -/
noncomputable abbrev tensorSquareRepEquiv :
    (tensorPowerRep k n 2).Equiv
      ((symPowerRep k n 2).prod (extPowerRep k n 2)) :=
  letI : Invertible (2 : k) := invertibleOfNonzero (NeZero.ne _)
  (stdRep k n).tensorSquareEquivSymmetricExterior

/-- The tensor-square decomposition bundled as an isomorphism in `FDRep`. The product
representation is the direct sum of the symmetric and exterior squares. -/
noncomputable def tensorSquareFDRepIso :
    tensorPowerFDRep k n 2 ≅
      FDRep.of ((symPowerRep k n 2).prod (extPowerRep k n 2)) :=
  Action.mkIso
    (tensorSquareRepEquiv k n).toLinearEquiv.toFGModuleCatIso
    fun g ↦ by
      apply FGModuleCat.hom_ext
      exact (tensorSquareRepEquiv k n).isIntertwining' g

/-- The square of the standard character is the sum of the symmetric-square and
exterior-square characters. -/
theorem char_tensorSquare_stdRep (g : GL (Fin n) k) :
    Matrix.trace (g : Matrix (Fin n) (Fin n) k) ^ 2 =
      (symPowerRep k n 2).character g + (extPowerRep k n 2).character g := by
  rw [← char_stdRep]
  exact Representation.char_tensorSquare (stdRep k n) g

end Field

end TauCeti
