/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.CommHopfAlgCat
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.BaseChange

/-!
# Geometric connectedness and reducedness of diagonalizable groups

The coordinate ring of a diagonalizable group is a group algebra. When its character group has
the unique-product property, this group algebra is a domain over every field, so it is reduced and
has connected prime spectrum. In particular, this applies to the finite-rank free character group
of every split torus.

## Main declarations

* `TauCeti.DiagonalizableGroup.geometricallyConnected_coordinateRing`: the coordinate ring of a
  unique-product diagonalizable group is geometrically connected.
* `TauCeti.DiagonalizableGroup.geometricallyReduced_coordinateRing`: the coordinate ring of a
  unique-product diagonalizable group is geometrically reduced.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.

This establishes the geometric connectedness and reducedness of the split-torus case in Layer 4,
"Tori: split and non-split", of the ReductiveGroups roadmap.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u

namespace DiagonalizableGroup

/-- Scalar extension identifies a diagonalizable-group coordinate ring with the corresponding
group algebra over the extension field. -/
private noncomputable def coordinateRingBaseChangeEquiv
    (k : Type u) [Field k] (G : FGCommGrpCat.{u})
    (K : Type u) [Field K] [Algebra k K] :
    MonoidAlgebra k G ⊗[k] K ≃+* MonoidAlgebra K G :=
  (Algebra.TensorProduct.comm k _ K).toRingEquiv.trans
    (_root_.CommHopfAlgCat.ofIso
      ((finiteTypeCommHopfAlgProperty K).ι.mapIso
        (baseChangeCoordinateRingIso k K G))).toAlgEquiv.toRingEquiv

/-- **The coordinate Hopf algebra of a unique-product diagonalizable group is geometrically
connected.** -/
theorem geometricallyConnected_coordinateRing
    (k : Type u) [Field k] (G : FGCommGrpCat.{u}) [UniqueProds G] :
    geometricallyConnectedCommHopfAlgProperty k
      (DiagonalizableGroup.coordinateRing k G).obj := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  intro K _ _
  exact (PrimeSpectrum.homeomorphOfRingEquiv
    (coordinateRingBaseChangeEquiv k G K)).connectedSpace_iff.mpr inferInstance

/-- **The coordinate Hopf algebra of a unique-product diagonalizable group is geometrically
reduced.** -/
theorem geometricallyReduced_coordinateRing
    (k : Type u) [Field k] (G : FGCommGrpCat.{u}) [UniqueProds G] :
    geometricallyReducedCommHopfAlgProperty k
      (DiagonalizableGroup.coordinateRing k G).obj := by
  rw [geometricallyReducedCommHopfAlgProperty_iff]
  intro K _ _
  let φ := coordinateRingBaseChangeEquiv k G K
  exact isReduced_of_injective φ.toRingHom φ.injective

end DiagonalizableGroup

end TauCeti
