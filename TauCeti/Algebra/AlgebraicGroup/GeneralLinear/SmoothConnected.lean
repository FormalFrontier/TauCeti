/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced

/-!
# Smoothness and connectedness of the general linear group

The determinant localization defining the coordinate Hopf algebra of `GL_n` is smooth. It is
also an integral domain whenever the base ring is an integral domain. After base change to any
field it therefore has connected prime spectrum, proving geometric connectedness over a field.

## Main declarations

* `TauCeti.GeneralLinear.instSmoothCoordinateHopfAlgebra`: `O(GL_n)` is smooth.
* `TauCeti.GeneralLinear.instIsDomainCoordinateHopfAlgebra`: `O(GL_n)` is an integral domain
  over an integral domain.
* `TauCeti.GeneralLinear.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra`:
  `GL_n` is geometrically connected.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.GeneralLinear

universe u

noncomputable section

/-- The coordinate Hopf algebra of `GL_n` is smooth over its base ring. -/
instance instSmoothCoordinateHopfAlgebra (R : Type u) [CommRing R] (n : Nat) :
    Algebra.Smooth R (coordinateHopfAlgebra R n) := by
  let _ : Algebra.Smooth R (MatrixMonoid.CoordinateRing R n) :=
    ⟨inferInstance, inferInstance⟩
  let _ : Algebra.Smooth (MatrixMonoid.CoordinateRing R n) (CoordinateRing R n) :=
    Algebra.Smooth.of_isLocalization_Away
      (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R))
  let _ : Algebra.Smooth R (CoordinateRing R n) :=
    Algebra.Smooth.comp R (MatrixMonoid.CoordinateRing R n) (CoordinateRing R n)
  exact Algebra.Smooth.of_equiv (coordinateHopfAlgebraAlgEquiv R n)

/-- Over an integral domain, the coordinate Hopf algebra of `GL_n` is an integral domain. -/
instance instIsDomainCoordinateHopfAlgebra
    (R : Type u) [CommRing R] [IsDomain R] (n : Nat) :
    IsDomain (coordinateHopfAlgebra R n) := by
  let _ : IsDomain (CoordinateRing R n) :=
    Localization.Away.isDomain (Matrix.det_mvPolynomialX_ne_zero (Fin n) R)
  exact (coordinateHopfAlgebraAlgEquiv R n).toRingEquiv.isDomain_iff.mp inferInstance

/-- The coordinate Hopf algebra of `GL_n` is geometrically connected over every field. -/
theorem geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] (n : Nat) :
    geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra k n) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  intro K _ _
  let e : coordinateHopfAlgebra k n ⊗[k] K ≃+* coordinateHopfAlgebra K n :=
    (Algebra.TensorProduct.comm k (coordinateHopfAlgebra k n) K).toRingEquiv.trans
      (coordinateHopfAlgebraBaseChangeBialgEquiv k K n).toAlgEquiv.toRingEquiv
  exact (PrimeSpectrum.homeomorphOfRingEquiv e).connectedSpace_iff.mpr inferInstance

end

end TauCeti.GeneralLinear
