/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation

/-!
# Finite generation of group-like elements

If a finite-type Hopf algebra over a domain is spanned by its group-like elements, then its
group of group-like elements is finitely generated. Indeed, evaluation identifies the group
algebra on the group-like elements with the original Hopf algebra. Finite type transports across
this equivalence, and a group algebra over a nontrivial commutative ring is of finite type exactly
when its indexing group is finitely generated.

The general result does not require the Hopf algebra to be commutative. A specialization to
commutative Hopf algebras over a field supplies the form used in the diagonalizable-group
correspondence.

## Main declarations

* `TauCeti.GroupLike.fg_of_finiteType_of_groupLikeSetSpan_eq_top`: finite generation over a
  domain when the carrier is torsion-free.
* `TauCeti.GroupLike.fg_of_finiteType_of_groupLikeSetSpan_eq_top_of_field`: the commutative
  Hopf-algebra specialization over a field.

## References

See Milne, *Algebraic Groups*, Proposition 4.23 and Theorems 12.8--12.9.
-/

public section

namespace TauCeti

universe u v

namespace GroupLike

/-- The group-like elements spanning a finite-type Hopf algebra over a domain form a finitely
generated group, provided the carrier is torsion-free over the base.

The spanning hypothesis is expressed intrinsically through the subcoalgebra spanned by all
group-like elements. -/
theorem fg_of_finiteType_of_groupLikeSetSpan_eq_top
    (R : Type u) (H : Type v) [CommRing R] [IsDomain R] [Ring H] [HopfAlgebra R H]
    [Module.IsTorsionFree R H] (hfinite : Algebra.FiniteType R H)
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
    (evaluationBialgEquiv R H hlinearSpan).toAlgEquiv.symm

/-- If a finite-type commutative Hopf algebra over a field is spanned by its group-like elements,
then its group of group-like elements is finitely generated. The group-like elements carry their
canonical commutative-group structure. -/
theorem fg_of_finiteType_of_groupLikeSetSpan_eq_top_of_field
    (k : Type u) (H : Type v) [Field k] [CommRing H] [HopfAlgebra k H]
    (hfinite : Algebra.FiniteType k H)
    (hspan : Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ = ⊤) :
    Group.FG (_root_.GroupLike k H) :=
  fg_of_finiteType_of_groupLikeSetSpan_eq_top k H hfinite hspan

end GroupLike

end TauCeti
