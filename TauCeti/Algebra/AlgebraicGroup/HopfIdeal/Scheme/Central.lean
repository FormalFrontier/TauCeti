/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Central
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic
import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec

/-!
# Central closed subgroup schemes are commutative

A central Hopf ideal cuts out a commutative closed subgroup scheme. The coordinate quotient is
cocommutative by `HopfIdeal.IsCentral.isCocomm_quotient`, so its Hopf spectrum carries a
commutative group-object structure. This file bundles that structure and identifies its underlying
group scheme with the ordinary Hopf-ideal quotient spectrum.

## Main declarations

* `TauCeti.CommHopfAlgCat.centralSubgroupCommGroupScheme`: a central closed subgroup bundled as a
  commutative group scheme.
* `TauCeti.CommHopfAlgCat.centralSubgroupCommGroupScheme_toGrp`: forgetting commutativity recovers
  the quotient group scheme.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 1.k and 2.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.

This supplies a structural property of central closed subgroups used by the center in Layer 6,
"Reductive and semisimple groups", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

open AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R]

/-- A central closed subgroup of an affine group scheme, bundled as a commutative group scheme. -/
noncomputable def centralSubgroupCommGroupScheme (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) (hI : I.IsCentral) : CommGrp (Over (Spec (CommRingCat.of R))) := by
  let _ : _root_.Coalgebra.IsCocomm R (quotient H I) := hI.isCocomm_quotient
  exact CommGrp.mk ((Spec (CommRingCat.of (quotient H I))).asOver (Spec (CommRingCat.of R)))

/-- Forgetting commutativity from a central closed subgroup recovers its quotient group scheme. -/
@[simp]
theorem centralSubgroupCommGroupScheme_toGrp (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) (hI : I.IsCentral) :
    (centralSubgroupCommGroupScheme H I hI).toGrp = quotientSpec H I :=
  (TauCeti.hopfSpec_obj_eq_asOver R (quotient H I)).symm

end TauCeti.CommHopfAlgCat
