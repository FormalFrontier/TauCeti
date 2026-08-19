/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Central

/-!
# The center is commutative

The center of an affine group scheme is a commutative group scheme. On coordinate Hopf algebras,
this says that the quotient by `centerDefiningIdeal` is cocommutative. The result follows from the
more general fact that the coordinate Hopf algebra of every central closed subgroup is
cocommutative.

The cocommutativity result supplies the commutative-group-object structure on the Hopf spectrum,
which is bundled here as `centerCommGroupScheme`. Its underlying group scheme is canonically
identified with the previously constructed `centerGroupScheme`.

## Main declarations

* `TauCeti.CommHopfAlgCat.isCocomm_quotient_centerDefiningIdeal`: the coordinate Hopf algebra of
  the center is cocommutative.
* `TauCeti.CommHopfAlgCat.isMulCommutative_centerPointsSubgroup`: the points of the center form a
  commutative group.
* `TauCeti.CommHopfAlgCat.centerCommGroupScheme`: the center bundled as a commutative group
  scheme.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 1.k and 2.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.

This supplies a structural property of the center required in Layer 6, "Reductive and semisimple
groups", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} [Field k]

/-- The coordinate Hopf algebra of the center is cocommutative. -/
noncomputable instance isCocomm_quotient_centerDefiningIdeal
    (H : _root_.CommHopfAlgCat.{v} k) :
    _root_.Coalgebra.IsCocomm k (quotient H (centerDefiningIdeal H)) :=
  (isCentral_centerDefiningIdeal H).isCocomm_quotient

/-- The algebra-valued points of the center form a commutative group. -/
noncomputable instance isMulCommutative_centerPointsSubgroup
    (H : _root_.CommHopfAlgCat.{v} k) (A : CommAlgCat.{v} k) :
    IsMulCommutative (centerPointsSubgroup H A) :=
  (isCentral_centerDefiningIdeal H).isMulCommutative_quotientPointsSubgroup A

section Scheme

open AlgebraicGeometry

/-- The center of an affine group scheme, bundled as a commutative group scheme. -/
noncomputable def centerCommGroupScheme (H : _root_.CommHopfAlgCat.{u} k) :
    CommGrp (Over (Spec (CommRingCat.of k))) :=
  centralSubgroupCommGroupScheme H (centerDefiningIdeal H) (isCentral_centerDefiningIdeal H)

/-- Forgetting commutativity from the bundled center recovers the center group scheme. -/
@[simp]
theorem centerCommGroupScheme_toGrp (H : _root_.CommHopfAlgCat.{u} k) :
    (centerCommGroupScheme H).toGrp = centerGroupScheme H :=
  centralSubgroupCommGroupScheme_toGrp H (centerDefiningIdeal H)
    (isCentral_centerDefiningIdeal H)

end Scheme

end TauCeti.CommHopfAlgCat
