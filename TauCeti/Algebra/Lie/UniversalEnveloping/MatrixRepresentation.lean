/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.Algebra.Lie.UniversalEnveloping

/-!
# The defining representation of a matrix Lie subalgebra

A Lie subalgebra of square matrices acts faithfully on coordinate vectors. This file extends that
action to the universal enveloping algebra and records its values on Lie generators. It also
transports nilpotency of an underlying matrix to nilpotency of the resulting endomorphism.

## Main definitions and results

* `LieSubalgebra.matrixRepresentation`: the defining representation extended to the
  universal enveloping algebra.
* `LieSubalgebra.matrixRepresentation_ι_injective`: faithfulness on the Lie algebra.
* `LieSubalgebra.isNilpotent_matrixRepresentation_ι`: nilpotency transport.
-/

public section

namespace LieSubalgebra

open scoped _root_.Matrix

noncomputable section

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The defining action of a matrix Lie subalgebra, extended to its universal enveloping algebra. -/
def matrixRepresentation (K : _root_.LieSubalgebra R (Matrix n n R)) :
    _root_.UniversalEnvelopingAlgebra R K →ₐ[R] Module.End R (n → R) :=
  _root_.UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R K (n → R))

/-- The defining representation is the universal-enveloping extension of the matrix Lie-module
action. -/
theorem matrixRepresentation_def (K : _root_.LieSubalgebra R (Matrix n n R)) :
    matrixRepresentation K =
      _root_.UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R K (n → R)) := (rfl)

/-- A Lie generator acts through its underlying matrix. -/
theorem matrixRepresentation_ι (K : _root_.LieSubalgebra R (Matrix n n R)) (x : K) :
    matrixRepresentation K (_root_.UniversalEnvelopingAlgebra.ι R x) =
      Matrix.toLinAlgEquiv' (x : Matrix n n R) := by
  rw [matrixRepresentation, _root_.UniversalEnvelopingAlgebra.lift_ι_apply]
  apply LinearMap.ext
  intro v
  rw [LieModule.toEnd_apply_apply, LieSubalgebra.coe_bracket_of_module, Matrix.lie_apply,
    Matrix.toLinAlgEquiv'_apply]

/-- Pointwise, a Lie generator acts by matrix-vector multiplication. -/
theorem matrixRepresentation_ι_apply (K : _root_.LieSubalgebra R (Matrix n n R))
    (x : K) (v : n → R) :
    matrixRepresentation K (_root_.UniversalEnvelopingAlgebra.ι R x) v =
      (x : Matrix n n R) *ᵥ v := by
  rw [matrixRepresentation_ι, Matrix.toLinAlgEquiv'_apply]

/-- The defining representation of a matrix Lie subalgebra is faithful on the Lie algebra. -/
theorem matrixRepresentation_ι_injective (K : _root_.LieSubalgebra R (Matrix n n R)) :
    Function.Injective fun x : K =>
      matrixRepresentation K (_root_.UniversalEnvelopingAlgebra.ι R x) := by
  intro x y hxy
  apply LieModule.IsFaithful.injective_toEnd (R := R) (L := K) (M := n → R)
  simpa only [matrixRepresentation, _root_.UniversalEnvelopingAlgebra.lift_ι_apply] using hxy

/-- A nilpotent matrix acts nilpotently in the defining representation. -/
theorem isNilpotent_matrixRepresentation_ι (K : _root_.LieSubalgebra R (Matrix n n R))
    (x : K) (hx : IsNilpotent (x : Matrix n n R)) :
    IsNilpotent (matrixRepresentation K (_root_.UniversalEnvelopingAlgebra.ι R x)) := by
  rw [matrixRepresentation_ι]
  exact IsNilpotent.map hx (Matrix.toLinAlgEquiv' (n := n) (R := R))

end


end LieSubalgebra
