/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.GroupLike

import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation

/-!
# Finite generation of group-like elements

If a finite-type Hopf algebra over a nontrivial commutative ring is spanned by linearly independent
group-like elements, then its group of group-like elements is finitely generated. Indeed,
evaluation identifies the group algebra on the group-like elements with the original Hopf algebra.
Finite type transports across this equivalence, and a group algebra over a nontrivial commutative
ring is of finite type exactly when its indexing group is finitely generated.

The result does not require the Hopf algebra to be commutative. Over a domain, linear independence
is automatic when the carrier is torsion-free.

## Main declarations

* `TauCeti.GroupLike.fg_of_finiteType_of_linearIndependent_of_groupLikeSetSpan_eq_top`: finite
  generation when the group-like elements are linearly independent and span.
* `TauCeti.GroupLike.fg_of_finiteType_of_groupLikeSetSpan_eq_top`: the domain specialization for
  a torsion-free carrier.

## References

See Milne, *Algebraic Groups*, Proposition 4.23 and Theorems 12.8--12.9.
-/

public section

namespace TauCeti

universe u v

namespace GroupLike

/-- The linearly independent group-like elements spanning a finite-type Hopf algebra over a
nontrivial commutative ring form a finitely generated group.

The spanning hypothesis is expressed intrinsically through the subcoalgebra spanned by all
group-like elements. -/
theorem fg_of_finiteType_of_linearIndependent_of_groupLikeSetSpan_eq_top
    (R : Type u) (H : Type v) [CommRing R] [Nontrivial R] [Ring H] [HopfAlgebra R H]
    (hfinite : Algebra.FiniteType R H)
    (hlinear : LinearIndependent R (_root_.GroupLike.val (R := R) (A := H)))
    (hspan : Subcoalgebra.groupLikeSetSpan (R := R) (C := H) Set.univ = ⊤) :
    Group.FG (_root_.GroupLike R H) := by
  have hlinearSpan :
      Submodule.span R
          (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤ :=
    (evaluationBialgHom_surjective_iff_span_eq_top R H).1
      ((evaluationBialgHom_surjective_iff_groupLikeSetSpan_eq_top R H).2 hspan)
  apply (MonoidAlgebra.finiteType_iff_group_fg
    (R := R) (G := _root_.GroupLike R H)).1
  exact Algebra.FiniteType.equiv hfinite
    (evaluationBialgEquivOfLinearIndependentOfSpanEqTop R H
      hlinear hlinearSpan).toAlgEquiv.symm

/-- The group-like elements spanning a finite-type Hopf algebra over a domain form a finitely
generated group, provided the carrier is torsion-free over the base. -/
theorem fg_of_finiteType_of_groupLikeSetSpan_eq_top
    (R : Type u) (H : Type v) [CommRing R] [IsDomain R] [Ring H] [HopfAlgebra R H]
    [Module.IsTorsionFree R H] (hfinite : Algebra.FiniteType R H)
    (hspan : Subcoalgebra.groupLikeSetSpan (R := R) (C := H) Set.univ = ⊤) :
    Group.FG (_root_.GroupLike R H) :=
  fg_of_finiteType_of_linearIndependent_of_groupLikeSetSpan_eq_top R H hfinite
    (linearIndep_groupLikeVal (R := R) (A := H)) hspan

end GroupLike

end TauCeti
