/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Unipotent
import TauCeti.Algebra.AlgebraicGroup.Unipotent.SemidirectProduct
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Unipotence of normal products

Let `I` and `J` cut out smooth unipotent closed subgroups of a finite-type affine group, with
`I` normal. Multiplication is a homomorphism from their conjugation semidirect product into the
ambient group, and `CommHopfAlgCat.productOfNormal` is its scheme-theoretic image.

The semidirect-product source is again smooth unipotent. In particular, its coordinate algebra
is reduced. The coordinate algebra of the multiplication image embeds in that reduced algebra,
so every geometric point of the image is unipotent. This avoids any appeal to faithful flatness
of the source-to-image morphism.

Together with connectedness and smoothness of the multiplication image, this is the remaining
geometric input for binary-product closure of unipotent-radical candidates. Containment and
normality of the image are supplied by the normal-product API.

## Main declarations

* `TauCeti.smoothUnipotentCommHopfAlgProperty.normalSemidirectProduct`: the named normal
  semidirect product of two smooth unipotent groups is smooth unipotent.
* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.productOfNormal`: the multiplication
  image of two smooth unipotent subgroups has geometrically unipotent points.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and Sections 5.a, 6.a.
* A. Borel, *Linear Algebraic Groups*, Proposition 14.4 and Section 11.21.

This advances Layer 5, "The unipotent radical", of the ReductiveGroups roadmap by supplying the
geometric-unipotence part of binary-product closure for connected normal smooth unipotent closed
subgroups.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

namespace smoothUnipotentCommHopfAlgProperty

variable {k : Type u} [Field k]

/-- The named normal semidirect product of two smooth unipotent closed subgroups is smooth
unipotent. -/
theorem normalSemidirectProduct (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (I J : HopfIdeal k H) (hI : I.IsNormal)
    (hIu : smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I))
    (hJu : smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H J)) :
    smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.of k
        (CommHopfAlgCat.normalSemidirectProduct H.obj I J hI)) := by
  let _ : Algebra.FiniteType k (CommHopfAlgCat.quotient H.obj I) :=
    (FiniteTypeCommHopfAlgCat.quotient H I).property
  let _ : Algebra.FiniteType k (CommHopfAlgCat.quotient H.obj J) :=
    (FiniteTypeCommHopfAlgCat.quotient H J).property
  let A := CommHopfAlgCat.quotientNormalConjugation H.obj I J hI
  let _ : Algebra.FiniteType k A.coordinateHopfAlgebra :=
    GrpObj.Action.coordinateHopfAlgebra_finiteType A
  have hsource : smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.of k A.coordinateHopfAlgebra) :=
    smoothUnipotentCommHopfAlgProperty.semidirectProduct k
      (FiniteTypeCommHopfAlgCat.quotient H I)
      (FiniteTypeCommHopfAlgCat.quotient H J) A hIu hJu
  let e : FiniteTypeCommHopfAlgCat.of k
      (CommHopfAlgCat.normalSemidirectProduct H.obj I J hI) ≅
      FiniteTypeCommHopfAlgCat.of k A.coordinateHopfAlgebra :=
    ObjectProperty.isoMk _ (CommHopfAlgCat.normalSemidirectProductIso H.obj I J hI)
  exact (smoothUnipotentCommHopfAlgProperty k).prop_of_iso e.symm hsource

end smoothUnipotentCommHopfAlgProperty

namespace geometricallyUnipotentPointsCommHopfAlgProperty

variable {k : Type u} [Field k]

/-- The scheme-theoretic multiplication image of two smooth unipotent closed subgroups has
geometrically unipotent points when the first subgroup is normal.

The semidirect-product source is smooth unipotent, hence reduced. Unipotence then descends to its
scheme-theoretic image through the canonical embedding of coordinate algebras. -/
theorem productOfNormal (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (I J : HopfIdeal k H) (hI : I.IsNormal)
    (hIu : smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I))
    (hJu : smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H J)) :
    geometricallyUnipotentPointsCommHopfAlgProperty k
      (CommHopfAlgCat.productOfNormal H.obj I J hI) := by
  have hsource := smoothUnipotentCommHopfAlgProperty.normalSemidirectProduct
    H I J hI hIu hJu
  have hsource' :=
    (smoothUnipotentCommHopfAlgProperty_iff k
      (FiniteTypeCommHopfAlgCat.of k
        (CommHopfAlgCat.normalSemidirectProduct H.obj I J hI))).mp hsource
  let _ : Algebra.Smooth k (CommHopfAlgCat.normalSemidirectProduct H.obj I J hI) := hsource'.1
  let _ : IsReduced (CommHopfAlgCat.normalSemidirectProduct H.obj I J hI) :=
    isReduced_of_smooth_of_field k _
  apply image_of_reduced (CommHopfAlgCat.productMapOfNormal H.obj I J hI)
  rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff]
  exact hsource'.2

end geometricallyUnipotentPointsCommHopfAlgProperty

end

end TauCeti
