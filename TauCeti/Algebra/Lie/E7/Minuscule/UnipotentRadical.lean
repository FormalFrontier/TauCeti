/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction
import TauCeti.Algebra.AlgebraicGroup.Reductive.LinearlyReductive
import TauCeti.Algebra.AlgebraicGroup.Representation.ClosedSubgroup
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Embedding
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# The unipotent radical obstruction for the type-E7 minuscule carrier

Let `H` be the coordinate Hopf algebra of the specialized full-weight type-`E₇` minuscule
carrier. Over an algebraically closed field, if `H` is reduced, then every normal smooth
unipotent closed subgroup of the carrier is trivial. Consequently its unipotent radical is
trivial.

The mathematical input is the carrier's standard 56-dimensional comodule. It is simple, hence
completely reducible, and faithful. Normality makes the fixed vectors of a smooth unipotent
closed subgroup into an ambient subcomodule. Kolchin's fixed-vector theorem then forces the
subgroup to act trivially, and faithfulness identifies its defining ideal with the augmentation
ideal.

Reducedness is stated explicitly. No smoothness or connectedness of the carrier is asserted here,
so the result is the normal-unipotent obstruction needed for reductivity rather than a proof that
the carrier is reductive.

## Main declarations

* `TauCeti.E7Minuscule.eq_augmentation_of_isNormal_of_smoothUnipotent`: every normal smooth
  unipotent closed subgroup of a reduced specialized carrier is trivial.
* `TauCeti.E7Minuscule.unipotentRadicalDefiningIdeal_eq_augmentation`: the unipotent radical of
  a reduced specialized carrier is trivial.

## References

* The proof of the normal-unipotent obstruction is adapted from
  `TauCeti/Algebra/AlgebraicGroup/SpecialLinear/Reductive.lean`.
* J. E. Humphreys, *Linear Algebraic Groups*, §§19 and 26.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.
-/

public section

open CategoryTheory

namespace TauCeti.E7Minuscule

universe u

noncomputable section

open HopfIdeal

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- The specialized type-`E₇` minuscule carrier as a finite-type commutative Hopf algebra. -/
public noncomputable abbrev finiteTypeCoordinateHopfAlgebra :
    FiniteTypeCommHopfAlgCat.{u, u} k :=
  FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra k)

attribute [local instance] standardComodule

/-- **Every normal smooth unipotent closed subgroup of a reduced specialized type-`E₇`
minuscule carrier is trivial.**

The conclusion is stated contravariantly: the subgroup's defining Hopf ideal is the augmentation
ideal of the carrier's coordinate algebra. -/
theorem eq_augmentation_of_isNormal_of_smoothUnipotent
    [IsReduced (coordinateHopfAlgebra k)]
    (I : HopfIdeal k (coordinateHopfAlgebra k)) (hI : I.IsNormal)
    (hU : smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra k) I)) :
    I = HopfIdeal.augmentation k (coordinateHopfAlgebra k) := by
  have hU' := (smoothUnipotentCommHopfAlgProperty_iff k
    (FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra k) I)).mp hU
  let _ : Algebra.Smooth k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k) I) := hU'.1
  let _ : IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k) I) :=
    isReduced_of_smooth_of_field k _
  have hu : ∀ g : WithConv
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k) I →ₐ[k] k),
      HopfAlgebra.IsUnipotentPoint g :=
    geometricallyUnipotentPointsCommHopfAlgProperty.forall_isUnipotentPoint
      ((geometricallyUnipotentPointsCommHopfAlgProperty_iff k _).mpr hU'.2)
  have htrivial :=
    mkQuotient_coact_eq_tmul_one_of_isNormal_of_forall_isUnipotentPoint_of_isCompletelyReducible
      (M := Fin 56 → k) hI hu Comodule.isCompletelyReducible_of_isSimpleOrder
  exact Comodule.eq_augmentation_of_isFaithful_of_quotient_coact_eq_tmul_one I
    (isFaithful_standardComodule k) htrivial

/-- **The unipotent radical of a reduced specialized type-`E₇` minuscule carrier over an
algebraically closed field is trivial.** -/
theorem unipotentRadicalDefiningIdeal_eq_augmentation
    [IsReduced (coordinateHopfAlgebra k)] :
    FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
        (finiteTypeCoordinateHopfAlgebra k) =
      HopfIdeal.augmentation k (coordinateHopfAlgebra k) := by
  rw [FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_augmentation_iff]
  intro I hI
  exact eq_augmentation_of_isNormal_of_smoothUnipotent k I hI.isNormal hI.smoothUnipotent

end

end TauCeti.E7Minuscule
