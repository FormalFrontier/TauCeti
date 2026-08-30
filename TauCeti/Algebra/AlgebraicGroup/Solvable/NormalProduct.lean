/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product.Basic
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
import TauCeti.Algebra.AlgebraicGroup.Solvable.Reduced
import TauCeti.Algebra.AlgebraicGroup.Solvable.SemidirectProduct
import TauCeti.Algebra.AlgebraicGroup.Smooth.Product

/-!
# Solvability of normal products

Let `I` and `J` cut out smooth solvable closed subgroups of an affine group, with
`I` normal. Multiplication is a homomorphism from their conjugation semidirect product into the
ambient group, and `CommHopfAlgCat.productOfNormal` is its scheme-theoretic image.

The semidirect-product source is smooth and has solvable geometric points. Its coordinate map
from the multiplication image is injective, so solvability descends by the derived-word identity
criterion for schematically dense morphisms. No faithful-flatness hypothesis on the
source-to-image morphism is needed.

## Main declaration

* `TauCeti.geometricallySolvablePointsCommHopfAlgProperty.productOfNormal`: the multiplication
  image of two smooth solvable subgroups has solvable geometric points.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and Sections 5.a, 6.a.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.

This supplies the geometric-solvability part of binary-product closure for connected normal
smooth solvable closed subgroups in Layer 6, "Reductive and semisimple groups", of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

namespace geometricallySolvablePointsCommHopfAlgProperty

variable {k : Type u} [Field k]

/-- The scheme-theoretic multiplication image of two smooth solvable closed subgroups has
solvable geometric points when the first subgroup is normal.

The conjugation semidirect-product source is smooth and solvable. The canonical coordinate map
from the image into that source is injective, so the derived-word identity for solvability
descends to the image. -/
theorem productOfNormal (H : CommHopfAlgCat.{u} k)
    (I J : HopfIdeal k H) (hI : I.IsNormal)
    (hIs : smoothCommHopfAlgProperty k (CommHopfAlgCat.quotient H I))
    (hJs : smoothCommHopfAlgProperty k (CommHopfAlgCat.quotient H J))
    (hIsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient H I))
    (hJsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient H J)) :
    geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.productOfNormal H I J hI) := by
  let f := CommHopfAlgCat.productMapOfNormal H I J hI
  apply of_injective_of_smooth (CommHopfAlgCat.imageι f)
    (CommHopfAlgCat.imageι_injective f)
  · exact (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty.normalSemidirectProduct H I J hI hIs hJs)
  · exact normalSemidirectProduct k H I J hI hIsolv hJsolv

end geometricallySolvablePointsCommHopfAlgProperty

end

end TauCeti
