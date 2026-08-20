/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The defining representation of a matrix Lie subalgebra

A Lie subalgebra of square matrices acts faithfully on coordinate vectors. This file extends that
action to the universal enveloping algebra and records its values on Lie generators. It also
transports nilpotency of an underlying matrix to nilpotency of the resulting endomorphism.

## Main definitions and results

* `TauCeti.MatrixLieSubalgebra.matrixRepresentation`: the defining representation extended to the
  universal enveloping algebra.
* `TauCeti.MatrixLieSubalgebra.matrixRepresentation_ι_injective`: faithfulness on the Lie algebra.
* `TauCeti.MatrixLieSubalgebra.isNilpotent_matrixRepresentation_ι`: nilpotency transport.
-/

public section

namespace TauCeti.MatrixLieSubalgebra

open scoped _root_.Matrix

noncomputable section

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The defining action of a matrix Lie subalgebra, extended to its universal enveloping algebra. -/
def matrixRepresentation (K : _root_.LieSubalgebra R (Matrix n n R)) :
    _root_.UniversalEnvelopingAlgebra R K →ₐ[R] Module.End R (n → R) :=
  _root_.UniversalEnvelopingAlgebra.lift R
    (_root_.LieHom.comp
      (_root_.AlgHom.toLieHom (Matrix.toLinAlgEquiv' (n := n) (R := R)).toAlgHom)
      K.incl)

/-- A Lie generator acts through its underlying matrix. -/
theorem matrixRepresentation_ι (K : _root_.LieSubalgebra R (Matrix n n R)) (x : K) :
    matrixRepresentation K (_root_.UniversalEnvelopingAlgebra.ι R x) =
      Matrix.toLinAlgEquiv' (x : Matrix n n R) :=
  _root_.UniversalEnvelopingAlgebra.lift_ι_apply R _ x

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
  simp only [matrixRepresentation_ι] at hxy
  exact Subtype.ext (Matrix.toLinAlgEquiv'.injective hxy)

/-- A nilpotent matrix acts nilpotently in the defining representation. -/
theorem isNilpotent_matrixRepresentation_ι (K : _root_.LieSubalgebra R (Matrix n n R))
    (x : K) (hx : IsNilpotent (x : Matrix n n R)) :
    IsNilpotent (matrixRepresentation K (_root_.UniversalEnvelopingAlgebra.ι R x)) := by
  rw [matrixRepresentation_ι]
  exact IsNilpotent.map hx (Matrix.toLinAlgEquiv' (n := n) (R := R)).toRingHom

end


end TauCeti.MatrixLieSubalgebra
