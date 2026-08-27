/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Basic
import TauCeti.Algebra.AlgebraicGroup.Connected.Product
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product.Properties
import TauCeti.Algebra.AlgebraicGroup.Smooth.Product
import TauCeti.Algebra.AlgebraicGroup.Unipotent.NormalProduct

/-!
# Geometric properties of products of unipotent-radical candidates

Let `I` and `J` cut out connected normal smooth unipotent closed subgroups of a finite-type
affine group. Since `I` is normal, multiplication on the two subgroups is a homomorphism after
their product is equipped with the conjugation semidirect-product law. Its scheme-theoretic image
is the closed subgroup represented by `CommHopfAlgCat.productOfNormal`.

The semidirect-product source is geometrically connected, because its underlying scheme is the
direct product of the two connected factors, and it is smooth. Geometric connectedness and
smoothness then descend to the scheme-theoretic image. Its geometric points are unipotent because
the source is reduced and the image coordinate algebra embeds into the source. Together with the
normal-product coordinate calculation, these facts show that the multiplication image is again a
unipotent-radical candidate.

## Main declarations

* `TauCeti.HopfIdeal.IsUnipotentRadicalCandidate.geometricallyConnected_productOfNormal`:
  the multiplication image of two candidates is geometrically connected.
* `TauCeti.HopfIdeal.IsUnipotentRadicalCandidate.smooth_productOfNormal`: the multiplication
  image of two candidates is smooth.
* `TauCeti.HopfIdeal.IsUnipotentRadicalCandidate.productOfNormal`: unipotent-radical candidates
  are closed under scheme-theoretic multiplication images.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and Sections 5.a, 6.a.
* A. Borel, *Linear Algebraic Groups*, Proposition 14.4 and Section 11.21.

This advances Layer 5, "The unipotent radical", of the ReductiveGroups roadmap by proving
binary-product closure for connected normal smooth unipotent closed subgroups. This is the
closure input in the maximal-dimension construction of the unipotent radical.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal.IsUnipotentRadicalCandidate

variable {k : Type u} [Field k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I J : HopfIdeal k H}

/-- The scheme-theoretic multiplication image of two unipotent-radical candidates is
geometrically connected.

The conjugation semidirect product has the tensor-product scheme underlying it, so it is
geometrically connected when both quotient subgroups are. Geometric connectedness then descends
to its scheme-theoretic image in the ambient group. -/
theorem geometricallyConnected_productOfNormal
    (hI : IsUnipotentRadicalCandidate H I)
    (hJ : IsUnipotentRadicalCandidate H J) :
    geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.productOfNormal H.obj I J hI.isNormal) := by
  exact geometricallyConnectedCommHopfAlgProperty.productOfNormal H.obj I J hI.isNormal
    hI.geometricallyConnected hJ.geometricallyConnected

/-- The scheme-theoretic multiplication image of two unipotent-radical candidates is smooth.

The conjugation semidirect product is smooth because both factors are. Its smoothness
descends to the scheme-theoretic image inside the finite-type ambient group. This result does not
assert unipotence of the image. -/
theorem smooth_productOfNormal
    (hI : IsUnipotentRadicalCandidate H I)
    (hJ : IsUnipotentRadicalCandidate H J) :
    smoothCommHopfAlgProperty k
      (CommHopfAlgCat.productOfNormal H.obj I J hI.isNormal) := by
  have hIs : smoothCommHopfAlgProperty k (CommHopfAlgCat.quotient H.obj I) :=
    (smoothCommHopfAlgProperty_iff (CommHopfAlgCat.quotient H.obj I)).mpr
      ((smoothUnipotentCommHopfAlgProperty_iff k
        (FiniteTypeCommHopfAlgCat.quotient H I)).mp hI.smoothUnipotent |>.1)
  have hJs : smoothCommHopfAlgProperty k (CommHopfAlgCat.quotient H.obj J) :=
    (smoothCommHopfAlgProperty_iff (CommHopfAlgCat.quotient H.obj J)).mpr
      ((smoothUnipotentCommHopfAlgProperty_iff k
        (FiniteTypeCommHopfAlgCat.quotient H J)).mp hJ.smoothUnipotent |>.1)
  exact smoothCommHopfAlgProperty.productOfNormal H.obj I J hI.isNormal hIs hJs

/-- The scheme-theoretic multiplication image of two unipotent-radical candidates is again a
unipotent-radical candidate.

Its defining Hopf ideal is the kernel of the multiplication map from the conjugation semidirect
product. It is normal because both factors are normal. The quotient is geometrically connected,
smooth, and geometrically unipotent, so it represents a connected normal smooth unipotent closed
subgroup containing both factors. -/
theorem productOfNormal
    (hI : IsUnipotentRadicalCandidate H I)
    (hJ : IsUnipotentRadicalCandidate H J) :
    IsUnipotentRadicalCandidate H
      (HopfIdeal.ker
        (CommHopfAlgCat.productMapOfNormal H.obj I J hI.isNormal).hom) := by
  refine .mk
    (CommHopfAlgCat.isNormal_ker_productMapOfNormal H.obj I J hI.isNormal hJ.isNormal)
    (hI.geometricallyConnected_productOfNormal hJ) ?_
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  refine ⟨(smoothCommHopfAlgProperty_iff _).mp (hI.smooth_productOfNormal hJ), ?_⟩
  exact (geometricallyUnipotentPointsCommHopfAlgProperty_iff k _).mp <|
    geometricallyUnipotentPointsCommHopfAlgProperty.productOfNormal H I J hI.isNormal
      hI.smoothUnipotent hJ.smoothUnipotent

end HopfIdeal.IsUnipotentRadicalCandidate

end

end TauCeti
