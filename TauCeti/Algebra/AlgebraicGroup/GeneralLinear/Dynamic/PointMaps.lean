/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Parabolic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints

/-!
# Polynomial point maps for the general linear group

This file compares the generic polynomial point maps used in the dynamic-subgroup construction
with the matrix description of general-linear points. Inclusion into Laurent polynomials and
evaluation at zero both act entrywise on the corresponding invertible matrix.
-/

public section

open WithConv

namespace TauCeti.GeneralLinear.Dynamic

universe u v

variable {R : Type u} [CommRing R] {N : ℕ}
variable {A : Type v} [CommRing A] [Algebra R A]

/-- Applying the inclusion `A[X] → A[T;T⁻¹]` to a general-linear point applies that
inclusion entrywise to its matrix. -/
theorem pointsMulEquiv_ofPolyPoint
    (F : WithConv (coordinateHopfAlgebra R N →ₐ[R] Polynomial A)) :
    pointsMulEquiv N (Cocharacter.ofPolyPoint A F) =
      Matrix.GeneralLinearGroup.map
        (Polynomial.toLaurentAlg.restrictScalars R).toRingHom (pointsMulEquiv N F) := by
  rw [Cocharacter.ofPolyPoint_apply, ← AlgHom.mapValue_apply, pointsMulEquiv_mapValue]

/-- Evaluating a polynomial-valued general-linear point at zero evaluates every matrix entry
at zero. -/
theorem pointsMulEquiv_evalZeroPoint
    (F : WithConv (coordinateHopfAlgebra R N →ₐ[R] Polynomial A)) :
    pointsMulEquiv N (Cocharacter.evalZeroPoint A F) =
      Matrix.GeneralLinearGroup.map
        ((Polynomial.aeval (0 : A)).restrictScalars R).toRingHom (pointsMulEquiv N F) := by
  rw [Cocharacter.evalZeroPoint_apply, ← AlgHom.mapValue_apply, pointsMulEquiv_mapValue]

end TauCeti.GeneralLinear.Dynamic
