/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product.Basic
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Basic
import TauCeti.Algebra.AlgebraicGroup.Connected.Product
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product.Properties
import TauCeti.Algebra.AlgebraicGroup.Smooth.Product
import TauCeti.Algebra.AlgebraicGroup.Solvable.NormalProduct

/-!
# Products of solvable-radical candidates

Let `I` and `J` cut out connected normal smooth solvable closed subgroups of a finite-type
affine group. Since `I` is normal, multiplication on the two subgroups is a homomorphism after
their product is equipped with the conjugation semidirect-product law. Its scheme-theoretic image
is the closed subgroup represented by `CommHopfAlgCat.productOfNormal`.

The semidirect-product source is geometrically connected, smooth, and solvable. These properties
descend to its scheme-theoretic image; for solvability, the source's smoothness lets the
derived-word identity descend along the injective image coordinate map. Together with normality
of the product, this proves that solvable-radical candidates are closed under binary products.

## Main declarations

The declarations are in `TauCeti.HopfIdeal.IsSolvableRadicalCandidate`.

* `geometricallyConnected_productOfNormal`: the multiplication image of two candidates is
  geometrically connected.
* `smooth_productOfNormal`: the multiplication image of two candidates is smooth.
* `geometricallySolvable_productOfNormal`: the multiplication image of two candidates has
  solvable geometric points.
* `productOfNormal`: solvable-radical candidates are closed under scheme-theoretic
  multiplication images.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and Sections 5.a, 6.a.
* A. Borel, *Linear Algebraic Groups*, §11.21.

This advances Layer 6, "Reductive and semisimple groups", of the ReductiveGroups roadmap by
proving binary-product closure for connected normal smooth solvable closed subgroups. This is
the closure input that makes a maximal-dimensional candidate the solvable radical.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal.IsSolvableRadicalCandidate

variable {k : Type u} [Field k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I J : HopfIdeal k H}

/-- The scheme-theoretic multiplication image of two solvable-radical candidates is
geometrically connected. -/
theorem geometricallyConnected_productOfNormal
    (hI : IsSolvableRadicalCandidate H I)
    (hJ : IsSolvableRadicalCandidate H J) :
    geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.productOfNormal H.obj I J hI.isNormal) :=
  geometricallyConnectedCommHopfAlgProperty.productOfNormal H.obj I J hI.isNormal
    hI.geometricallyConnected hJ.geometricallyConnected

/-- The scheme-theoretic multiplication image of two solvable-radical candidates is smooth. -/
theorem smooth_productOfNormal
    (hI : IsSolvableRadicalCandidate H I)
    (hJ : IsSolvableRadicalCandidate H J) :
    smoothCommHopfAlgProperty k
      (CommHopfAlgCat.productOfNormal H.obj I J hI.isNormal) := by
  exact smoothCommHopfAlgProperty.productOfNormal H.obj I J hI.isNormal
    ((smoothCommHopfAlgProperty_iff _).mpr hI.smooth)
    ((smoothCommHopfAlgProperty_iff _).mpr hJ.smooth)

/-- The scheme-theoretic multiplication image of two solvable-radical candidates has a solvable
group of geometric points. -/
theorem geometricallySolvable_productOfNormal
    (hI : IsSolvableRadicalCandidate H I)
    (hJ : IsSolvableRadicalCandidate H J) :
    geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.productOfNormal H.obj I J hI.isNormal) := by
  exact geometricallySolvablePointsCommHopfAlgProperty.productOfNormal H.obj I J hI.isNormal
    ((smoothCommHopfAlgProperty_iff _).mpr hI.smooth)
    ((smoothCommHopfAlgProperty_iff _).mpr hJ.smooth)
    hI.geometricallySolvable hJ.geometricallySolvable

/-- The scheme-theoretic multiplication image of two solvable-radical candidates is again a
solvable-radical candidate.

Its defining Hopf ideal is the kernel of the multiplication map from the conjugation semidirect
product. It is normal because both factors are normal, and its quotient is geometrically
connected, smooth, and geometrically solvable. -/
theorem productOfNormal
    (hI : IsSolvableRadicalCandidate H I)
    (hJ : IsSolvableRadicalCandidate H J) :
    IsSolvableRadicalCandidate H
      (HopfIdeal.ker
        (CommHopfAlgCat.productMapOfNormal H.obj I J hI.isNormal).hom) := by
  refine .mk
    (CommHopfAlgCat.isNormal_ker_productMapOfNormal H.obj I J hI.isNormal hJ.isNormal)
    (hI.geometricallyConnected_productOfNormal hJ)
    ((smoothCommHopfAlgProperty_iff _).mp (hI.smooth_productOfNormal hJ)) ?_
  exact hI.geometricallySolvable_productOfNormal hJ

end HopfIdeal.IsSolvableRadicalCandidate

end

end TauCeti
