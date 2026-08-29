/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.Product
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Levi.DiagonalTorus
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Levi.SemidirectProduct
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Unipotent.Geometry
public import TauCeti.Algebra.AlgebraicGroup.Smooth.Product
public import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected

/-!
# Geometry of injective-weight parabolics

An injective weight has diagonal split torus as its Levi factor. Combining this identification
with the represented weight-parabolic Levi decomposition

```text
U(w) ⋊ L(w) ≅ P(w)
```

shows that its weight parabolic is smooth and geometrically connected over every field.

## Main declarations

* `TauCeti.GeneralLinear.smooth_weightParabolicCoordinateHopfAlgebra`: smoothness of an
  injective-weight parabolic.
* `TauCeti.GeneralLinear.geometricallyConnected_weightParabolicCoordinateHopfAlgebra`:
  geometric connectedness of an injective-weight parabolic.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 12--13 and 17.
* T. A. Springer, *Linear Algebraic Groups*, Sections 6.2--6.3.

This advances the dynamic approach to parabolics and Levi decomposition in Layer 7,
"Structure theory", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable {N : ℕ}

private theorem smooth_weightLeviCoordinateHopfAlgebra
    (k : Type u) [Field k] (w : Fin N → ℤ) (hw : Function.Injective w) :
    smoothCommHopfAlgProperty k (weightLeviCoordinateHopfAlgebra k w) := by
  apply (smoothCommHopfAlgProperty k).prop_of_iso
    (weightLeviDiagonalCoordinateIso k w hw).symm
  let H := DiagonalizableGroup.coordinateRing k
    (SplitTorus.characterGroup (ULift.{u} (Fin N)))
  exact torusCommHopfAlgProperty.smooth k H
    ((SplitTorus.splitTorus_coordinateRing k (ULift.{u} (Fin N))).torus)

private theorem geometricallyConnected_weightLeviCoordinateHopfAlgebra
    (k : Type u) [Field k] (w : Fin N → ℤ) (hw : Function.Injective w) :
    geometricallyConnectedCommHopfAlgProperty k (weightLeviCoordinateHopfAlgebra k w) := by
  apply (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
    (weightLeviDiagonalCoordinateIso k w hw).symm
  let H := DiagonalizableGroup.coordinateRing k
    (SplitTorus.characterGroup (ULift.{u} (Fin N)))
  exact torusCommHopfAlgProperty.geometricallyConnected k H
    ((SplitTorus.splitTorus_coordinateRing k (ULift.{u} (Fin N))).torus)

/-- The coordinate Hopf algebra of an injective-weight parabolic is smooth over every field. -/
theorem smooth_weightParabolicCoordinateHopfAlgebra
    (k : Type u) [Field k] (w : Fin N → ℤ) (hw : Function.Injective w) :
    smoothCommHopfAlgProperty k (weightParabolicCoordinateHopfAlgebra k w) := by
  let A := CommHopfAlgCat.quotientNormalConjugation
    (weightParabolicCoordinateHopfAlgebra k w)
    (Dynamic.weightUnipotentInParabolicHopfIdeal k w)
    (Dynamic.weightLeviInParabolicHopfIdeal k w)
    (Dynamic.isNormal_weightUnipotentInParabolicHopfIdeal k w)
  apply (smoothCommHopfAlgProperty k).prop_of_iso
    (Dynamic.weightParabolicSemidirectProductCoordinateIso k w).symm
  unfold Dynamic.weightParabolicSemidirectProductCoordinateHopfAlgebra
  apply smoothCommHopfAlgProperty.semidirectProduct _ _ A
  · apply (smoothCommHopfAlgProperty k).prop_of_iso
      (Dynamic.weightUnipotentInParabolicCoordinateIso k w)
    rw [smoothCommHopfAlgProperty_iff]
    infer_instance
  · apply (smoothCommHopfAlgProperty k).prop_of_iso
      (Dynamic.weightLeviInParabolicCoordinateIso k w)
    exact smooth_weightLeviCoordinateHopfAlgebra k w hw

/-- The coordinate Hopf algebra of an injective-weight parabolic is geometrically connected
over every field. -/
theorem geometricallyConnected_weightParabolicCoordinateHopfAlgebra
    (k : Type u) [Field k] (w : Fin N → ℤ) (hw : Function.Injective w) :
    geometricallyConnectedCommHopfAlgProperty k
      (weightParabolicCoordinateHopfAlgebra k w) := by
  let A := CommHopfAlgCat.quotientNormalConjugation
    (weightParabolicCoordinateHopfAlgebra k w)
    (Dynamic.weightUnipotentInParabolicHopfIdeal k w)
    (Dynamic.weightLeviInParabolicHopfIdeal k w)
    (Dynamic.isNormal_weightUnipotentInParabolicHopfIdeal k w)
  apply (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
    (Dynamic.weightParabolicSemidirectProductCoordinateIso k w).symm
  unfold Dynamic.weightParabolicSemidirectProductCoordinateHopfAlgebra
  apply geometricallyConnectedCommHopfAlgProperty.semidirectProduct _ _ A
  · apply (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
      (Dynamic.weightUnipotentInParabolicCoordinateIso k w)
    exact geometricallyConnectedCommHopfAlgProperty_weightUnipotentCoordinateHopfAlgebra k w
  · apply (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
      (Dynamic.weightLeviInParabolicCoordinateIso k w)
    exact geometricallyConnected_weightLeviCoordinateHopfAlgebra k w hw

end

end TauCeti.GeneralLinear
