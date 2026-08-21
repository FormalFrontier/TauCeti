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
commutative group-object structure on the canonical Hopf-ideal quotient spectrum.

## Main declarations

* `TauCeti.HopfIdeal.IsCentral.isCommMonObj_quotientSpec`: the canonical quotient group scheme of
  a central Hopf ideal is a commutative group object.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 1.k and 2.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.

This supplies a structural property of central closed subgroups used by the center in Layer 6,
"Reductive and semisimple groups", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory

namespace TauCeti.HopfIdeal

open AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R]

/-- The canonical quotient group scheme of a central Hopf ideal is a commutative group object. -/
theorem IsCentral.isCommMonObj_quotientSpec {H : _root_.CommHopfAlgCat.{u} R}
    {I : HopfIdeal R H} (hI : I.IsCentral) :
    IsCommMonObj (CommHopfAlgCat.quotientSpec H I).X := by
  let _ := hI.isCocomm_quotient
  infer_instance

end TauCeti.HopfIdeal
