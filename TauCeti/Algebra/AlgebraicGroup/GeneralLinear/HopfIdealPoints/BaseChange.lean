/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Functor

/-!
# Base change of the matrix points cut out by a Hopf ideal

A closed subgroup scheme of `GLₙ/A` is often built over an extension `A` of `k` by a Hopf ideal
`J` of `O(GLₙ/A)` together with an isomorphism identifying the quotient it cuts out with the
scalar extension of the quotient by a Hopf ideal `I` of `O(GLₙ/k)`. The points of such a presented
quotient are already the points of the quotient over `k` on the value algebra with its scalars
restricted to `k`, by `CommHopfAlgCat.baseChangeIsoPointsMulEquiv`. This file records that this
identification preserves the ambient invertible matrix.

The only input is the commuting square relating the two quotient maps through the general-linear
coordinate base-change isomorphism. Nothing here chooses either ideal, so any carrier presented
this way — in particular an explicit pinned Chevalley carrier and its scalar extension — can
instantiate the result below.

## Main declarations

* `TauCeti.GeneralLinear.pointsMulEquiv_quotientPointsHom_baseChangeIsoPointsMulEquiv`: the
  presented base-change point equivalence preserves the ambient invertible matrix.

## Roadmap

This advances the carrier-independent half of the base-change and points targets in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`, whose consumer is milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md`. It identifies no particular carrier with the pinned
simply connected group.
-/

public section

open CategoryTheory TensorProduct

namespace TauCeti.GeneralLinear

universe u v w

noncomputable section

variable {k : Type u} [CommRing k] {A : Type max u v} [CommRing A] [Algebra k A]
variable (n : ℕ)
variable (I : HopfIdeal k (coordinateHopfAlgebra k n))
variable (J : HopfIdeal A (coordinateHopfAlgebra A n))
variable (e : CommHopfAlgCat.quotient (coordinateHopfAlgebra A n) J ≅
  CommHopfAlgCat.baseChange (K := A) (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I))
variable (he : CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra A n) J ≫ e.hom =
  (coordinateHopfAlgebraBaseChangeIso k A n).inv ≫
    CommHopfAlgCat.baseChangeMap (CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra k n) I))

include he in
/-- The inverse presenting isomorphism sends an extended generic-matrix coordinate of the quotient
over `k` to the corresponding coordinate of the quotient formed directly over `A`.

This is stated in terms of `CommHopfAlgCat.mkQuotient`, which `simp` unfolds to
`Ideal.Quotient.mk`, so it is a `rw` lemma rather than a `simp` one. -/
private theorem iso_inv_one_tmul_mkQuotient_X (i j : Fin n) :
    e.inv
        (1 ⊗ₜ[k] (CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra k n) I).hom
          (coordinateHopfAlgebraAlgEquiv k n
            (coordinateRingMap k n (MvPolynomial.X (i, j))))) =
      (CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra A n) J).hom
        (coordinateHopfAlgebraAlgEquiv A n
          (coordinateRingMap A n (MvPolynomial.X (i, j)))) := by
  symm
  have h := coordinateHopfAlgebraBaseChangeMap_X k A n
    (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I)
    (CommHopfAlgCat.quotient (coordinateHopfAlgebra A n) J)
    (CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra k n) I) e.symm i j
  rw [← Category.assoc, ← he] at h
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using h

include he in
/-- **The presented base-change point equivalence preserves the ambient invertible matrix.** Both
sides read the same matrix over the value algebra, one through the quotient over `k` and one
through the quotient over `A`. -/
theorem pointsMulEquiv_quotientPointsHom_baseChangeIsoPointsMulEquiv (B : CommAlgCat.{w} A)
    (q : HopfAlgebra.points (R := A)
      (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra A n) J) B) :
    pointsMulEquiv n
        (CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra k n) I
          (TauCeti.CommAlgCat.restrictScalarsObj (algebraMap k A) B)
          (CommHopfAlgCat.baseChangeIsoPointsMulEquiv e B q)) =
      pointsMulEquiv n
        (CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra A n) J B q) := by
  refine Matrix.GeneralLinearGroup.ext fun i j ↦ ?_
  simp only [pointsMulEquiv_apply, pointToGeneralLinear_apply]
  rw [CommHopfAlgCat.quotientPointsHom_apply_apply,
    CommHopfAlgCat.quotientPointsHom_apply_apply, ← CommHopfAlgCat.mkQuotient_apply,
    ← CommHopfAlgCat.mkQuotient_apply, CommHopfAlgCat.baseChangeIsoPointsMulEquiv_apply_apply]
  exact congrArg q.ofConv (iso_inv_one_tmul_mkQuotient_X n I J e he i j)

end

end TauCeti.GeneralLinear
