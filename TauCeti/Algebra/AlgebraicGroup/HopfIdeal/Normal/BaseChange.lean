/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic

/-!
# Normal closed subgroups under base change

Let `J` be the Hopf ideal cutting out a normal closed subgroup of the affine group represented
by a commutative Hopf algebra `H`. This file proves that the extended Hopf ideal in
`K ⊗[k] H` again cuts out a normal subgroup after an arbitrary extension of commutative base
rings. It also compares extension of the normal core of an ideal with the normal core after
extension.

The proof uses the pointwise characterization of normal Hopf ideals. A point of the base-changed
group over a commutative `K`-algebra is the same point of the original group after restriction of
scalars, and membership in the base-changed closed subgroup is detected by that equivalence.
Conjugation therefore carries subgroup points to subgroup points after base change.

## Main declarations

* `TauCeti.CommHopfAlgCat.isNormal_baseChangeHopfIdeal`: extension of scalars preserves normal
  Hopf ideals.
* `TauCeti.CommHopfAlgCat.baseChangeHopfIdeal_normalCore_le`: extending the normal core of a Hopf
  ideal is contained in the normal core of its extension.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§2.a and 10.20.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §16.

This is base-change infrastructure for Layer 5, "The unipotent radical", of the ReductiveGroups
roadmap. Compatibility of the radical with scalar extension first requires its defining normal
closed subgroup to remain normal after extension of the ground field.
-/

public section

open WithConv

namespace TauCeti.CommHopfAlgCat

universe u v w

variable {k : Type u} {K : Type w} [CommRing k] [CommRing K] [Algebra k K]
variable {H : _root_.CommHopfAlgCat.{v} k}

/-- **Base change preserves normal Hopf ideals.** Equivalently, the base change of a normal
closed subgroup of an affine group scheme is again normal. -/
theorem isNormal_baseChangeHopfIdeal {J : HopfIdeal k H} (hJ : J.IsNormal) :
    (baseChangeHopfIdeal (K := K) J).IsNormal := by
  rw [isNormal_iff_quotientPointsSubgroup_normal]
  intro A
  let e := baseChangePointsMulEquiv (K := K) A H
  have hsubgroup :
      quotientPointsSubgroup (baseChange (K := K) H) (baseChangeHopfIdeal (K := K) J) A =
        (quotientPointsSubgroup H J
          (_root_.TauCeti.CommAlgCat.restrictScalarsObj (algebraMap k K) A)).comap
            e.toMonoidHom := by
    ext g
    exact mem_quotientPointsSubgroup_baseChangeHopfIdeal_iff A J g
  rw [hsubgroup]
  exact (quotientPointsSubgroup_normal H J hJ
    (_root_.TauCeti.CommAlgCat.restrictScalarsObj (algebraMap k K) A)).comap e.toMonoidHom

/-- Extension of the normal core of a Hopf ideal is contained in the normal core after
extension. Contravariantly, the base change of the normal closure contains the normal closure of
the base-changed closed subgroup. -/
theorem baseChangeHopfIdeal_normalCore_le (J : HopfIdeal k H) :
    baseChangeHopfIdeal (K := K) J.normalCore ≤
      (baseChangeHopfIdeal (K := K) J).normalCore := by
  apply (HopfIdeal.le_normalCore_iff_of_isNormal _ _
    (isNormal_baseChangeHopfIdeal (HopfIdeal.isNormal_normalCore J))).mpr
  exact baseChangeHopfIdeal_mono J.normalCore_le

end TauCeti.CommHopfAlgCat
