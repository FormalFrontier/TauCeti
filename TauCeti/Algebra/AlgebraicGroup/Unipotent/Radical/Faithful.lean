/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ClosedSubgroup
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive
import TauCeti.Algebra.AlgebraicGroup.Reductive.LinearlyReductive
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Embedding
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Normal unipotent subgroups seen through a faithful representation

Let `H` be a reduced finite-type commutative Hopf algebra over an algebraically closed field `k`
and let `M` be a finite-dimensional `H`-comodule which is completely reducible and faithful. Then
every normal Hopf ideal of `H` whose quotient is smooth unipotent is the augmentation ideal:
contravariantly, every normal smooth unipotent closed subgroup of the represented affine group is
trivial. Consequently the unipotent radical of `H` is trivial.

Smoothness of the quotient makes the subgroup coordinate ring reduced, and geometric unipotence
says that all of its points act unipotently. Normality makes the fixed vectors of the subgroup an
ambient subcomodule, so the normal-invariants theorem together with Kolchin's fixed-vector theorem
forces the subgroup to act trivially on `M`, and faithfulness then identifies its defining ideal
with the augmentation ideal.

Only the existence of one faithful completely reducible finite-dimensional representation is used,
so the same statement serves `GLₙ`, `SLₙ` and the explicit Chevalley carriers. Neither smoothness
nor connectedness of `H` itself is needed; reducedness of `H` is.

## Main results

* `TauCeti.HopfIdeal.eq_augmentation_of_isNormal_of_forall_isUnipotentPoint_of_isFaithful`:
  a normal subgroup with reduced quotient and only unipotent points is trivial.
* `TauCeti.HopfIdeal.eq_augmentation_of_isNormal_of_smoothUnipotent_of_isFaithful`: a normal
  smooth unipotent closed subgroup of such an `H` is trivial.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_augmentation_of_isFaithful`:
  the unipotent radical of such an `H` is trivial.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§4.a, 5 and 19.b.
* J. E. Humphreys, *Linear Algebraic Groups*, §§19 and 26.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.
* The argument is the one already formalized for `SLₙ` in
  `TauCeti/Algebra/AlgebraicGroup/SpecialLinear/Reductive.lean`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

variable (k : Type u) [Field k] [IsAlgClosed k]
variable (H : FiniteTypeCommHopfAlgCat.{u, u} k) [IsReduced H]
variable (M : Type u) [AddCommGroup M] [Module k M] [Comodule k H M] [FiniteDimensional k M]

namespace HopfIdeal

/-- **A normal closed subgroup is trivial when its quotient is reduced, all of its points are
unipotent, and the ambient affine group has a faithful completely reducible representation.**

The conclusion is stated contravariantly: the subgroup's defining Hopf ideal is the augmentation
ideal. -/
theorem eq_augmentation_of_isNormal_of_forall_isUnipotentPoint_of_isFaithful
    (hcr : Comodule.IsCompletelyReducible k H M)
    (hM : Comodule.IsFaithful (k := k) (H := H) (V := M))
    (I : HopfIdeal k H) (hI : I.IsNormal)
    [IsReduced (CommHopfAlgCat.quotient H.obj I)]
    (hu : ∀ g : WithConv (CommHopfAlgCat.quotient H.obj I →ₐ[k] k),
      HopfAlgebra.IsUnipotentPoint g) :
    I = HopfIdeal.augmentation k H := by
  have htrivial :=
    mkQuotient_coact_eq_tmul_one_of_isNormal_of_forall_isUnipotentPoint_of_isCompletelyReducible
      (M := M) hI hu hcr
  exact Comodule.eq_augmentation_of_isFaithful_of_quotient_coact_eq_tmul_one I hM htrivial

/-- **A normal smooth unipotent closed subgroup is trivial as soon as the ambient reduced
finite-type affine group has a faithful completely reducible finite-dimensional
representation.**

The conclusion is stated contravariantly: the subgroup's defining Hopf ideal is the augmentation
ideal. Neither smoothness nor connectedness of the ambient group is needed. -/
theorem eq_augmentation_of_isNormal_of_smoothUnipotent_of_isFaithful
    (hcr : Comodule.IsCompletelyReducible k H M)
    (hM : Comodule.IsFaithful (k := k) (H := H) (V := M))
    (I : HopfIdeal k H) (hI : I.IsNormal)
    (hU : smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I)) :
    I = HopfIdeal.augmentation k H := by
  have hU' := (smoothUnipotentCommHopfAlgProperty_iff k
    (FiniteTypeCommHopfAlgCat.quotient H I)).mp hU
  have hgeom : geometricallyUnipotentPointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient H.obj I) :=
    (geometricallyUnipotentPointsCommHopfAlgProperty_iff k _).mpr hU'.2
  let _ : Algebra.Smooth k (CommHopfAlgCat.quotient H.obj I) :=
    (smoothCommHopfAlgProperty_iff _).mp <|
      (smoothCommHopfAlgProperty_iff _).mpr hU'.1
  let _ : IsReduced (CommHopfAlgCat.quotient H.obj I) := isReduced_of_smooth_of_field k _
  have hu : ∀ g : WithConv (CommHopfAlgCat.quotient H.obj I →ₐ[k] k),
      HopfAlgebra.IsUnipotentPoint g :=
    geometricallyUnipotentPointsCommHopfAlgProperty.forall_isUnipotentPoint hgeom
  exact eq_augmentation_of_isNormal_of_forall_isUnipotentPoint_of_isFaithful
    k H M hcr hM I hI hu

end HopfIdeal

namespace FiniteTypeCommHopfAlgCat

/-- **The unipotent radical is trivial as soon as the reduced finite-type affine group has a
faithful completely reducible finite-dimensional representation.** -/
theorem unipotentRadicalDefiningIdeal_eq_augmentation_of_isFaithful
    (hcr : Comodule.IsCompletelyReducible k H M)
    (hM : Comodule.IsFaithful (k := k) (H := H) (V := M)) :
    unipotentRadicalDefiningIdeal H = HopfIdeal.augmentation k H := by
  rw [unipotentRadicalDefiningIdeal_eq_augmentation_iff]
  intro I hI
  exact HopfIdeal.eq_augmentation_of_isNormal_of_smoothUnipotent_of_isFaithful k H M hcr hM I
    hI.isNormal hI.smoothUnipotent

end FiniteTypeCommHopfAlgCat

end

end TauCeti
