/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.UpperUnitriangular.Scheme
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Connected
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# The upper-unitriangular group is geometrically connected

The coordinate ring of the upper-unitriangular group `U_m` is the polynomial algebra on the
strictly upper-triangular matrix entries. After every field extension it remains a polynomial
algebra over a field, hence a domain. Its prime spectrum is therefore connected.

This file records geometric connectedness in both synchronized models used by the reductive-groups
roadmap: as an object property of the coordinate Hopf algebra and as geometric connectedness of the
structural morphism of the affine group scheme.

## Main declarations

* `TauCeti.UpperUnitriangular.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra`:
  the coordinate Hopf algebra of `U_m` is geometrically connected.
* `TauCeti.UpperUnitriangular.geometricallyConnected_groupScheme`: the structural morphism of
  the upper-unitriangular group scheme is geometrically connected.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.

This supplies the connectedness of the standard ambient group in Layer 5, "Unipotent groups", of
the ReductiveGroups roadmap. Together with its existing smoothness and unipotence, it completes
the model required by the characterization of smooth connected unipotent groups as closed
subgroups of some `U_n`.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.UpperUnitriangular

open AlgebraicGeometry

universe u

/-- Scalar extension identifies the upper-unitriangular coordinate ring with a polynomial
algebra over the extension field. -/
private noncomputable def coordinateRingBaseChangeEquiv
    (k : Type u) [Field k] (m : Type) [Fintype m] [LinearOrder m]
    (K : Type u) [Field K] [Algebra k K] :
    coordinateHopfAlgebra k m ⊗[k] K ≃+* MvPolynomial (Index m) K :=
  (Algebra.TensorProduct.comm k _ K).toRingEquiv.trans
    ((Algebra.TensorProduct.congr
      (AlgEquiv.refl : K ≃ₐ[k] K) (coordinateHopfAlgebraAlgEquiv k m).symm).trans
      ((MvPolynomial.scalarRTensorAlgEquiv
        (R := k) (N := K) (σ := Index m)).restrictScalars k)).toRingEquiv

/-- **The upper-unitriangular coordinate Hopf algebra is geometrically connected.** After every
field extension its coordinate ring is a polynomial algebra over a field, hence a domain with
connected prime spectrum. -/
theorem geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] (m : Type) [Fintype m] [LinearOrder m] :
    geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra k m) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  intro K _ _
  exact (PrimeSpectrum.homeomorphOfRingEquiv
    (coordinateRingBaseChangeEquiv k m K)).connectedSpace_iff.mpr inferInstance

/-- **The upper-unitriangular group scheme is geometrically connected over a field.** This is the
scheme-side form of geometric connectedness of its coordinate Hopf algebra. -/
theorem geometricallyConnected_groupScheme
    (k : Type u) [Field k] (m : Type) [Fintype m] [LinearOrder m] :
    GeometricallyConnected (groupScheme k m).X.hom := by
  rw [groupScheme_def]
  exact (geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec
    k (coordinateHopfAlgebra k m)).mp
      (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k m)

end TauCeti.UpperUnitriangular
