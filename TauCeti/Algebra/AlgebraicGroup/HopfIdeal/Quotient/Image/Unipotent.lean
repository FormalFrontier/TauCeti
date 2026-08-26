/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.FaithfullyFlat
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Reduced

/-!
# Unipotence of affine group images

For a morphism `f : H ⟶ K` of commutative Hopf algebras, its scheme-theoretic image has coordinate
algebra
`CommHopfAlgCat.image f = H / ker f`; finite type of `K` makes the canonical inclusion
`CommHopfAlgCat.image f ⟶ K` finite type. If this inclusion is faithfully flat, every
algebraically closed point of the image lifts to a point of `Spec K`.

There are two ways to descend unipotence from `Spec K` to the image. A faithfully flat inclusion
lifts every geometric point of the image to the source. More directly, when `K` is reduced and
finite type, injectivity of the canonical inclusion lets the general reduced descent theorem
apply to every scheme-theoretic image of a smooth unipotent affine group.

## Main declaration

* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.image_of_reduced`: the image of a
  reduced finite-type geometrically unipotent affine group is geometrically unipotent.
* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.image_of_faithfullyFlat`: a
  faithfully flat finite-type affine group image has only unipotent geometric points when its
  source does.

## References

* A. Borel, *Linear Algebraic Groups*, Proposition 14.4, for the unipotent-radical application.

This is the image-unipotence step for Layer 5, "The unipotent radical", of the ReductiveGroups
roadmap. In particular, it supplies the remaining geometric-unipotence input in the binary-product
closure of connected normal smooth unipotent subgroup schemes.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v

namespace geometricallyUnipotentPointsCommHopfAlgProperty

variable {k : Type u} [Field k]
variable {H K : _root_.CommHopfAlgCat.{v} k}

/-- The scheme-theoretic image of a reduced finite-type geometrically unipotent affine group is
geometrically unipotent. -/
theorem image_of_reduced (f : H ⟶ K) [Algebra.FiniteType k K] [IsReduced K]
    (hK : geometricallyUnipotentPointsCommHopfAlgProperty k K) :
    geometricallyUnipotentPointsCommHopfAlgProperty k (CommHopfAlgCat.image f) :=
  of_injective_of_reduced (CommHopfAlgCat.imageι f)
    (CommHopfAlgCat.imageι_injective f) hK

/-- The scheme-theoretic image of a finite-type geometrically unipotent affine group is
geometrically unipotent when the source-to-image morphism is faithfully flat.

The finite-type hypothesis on `K` makes the canonical inclusion of the image coordinate algebra
into `K` a finite-type algebra map. Faithful flatness then lifts every algebraic-closure-valued
point of the image to a point of `K`, whose unipotence descends by precomposition. -/
theorem image_of_faithfullyFlat (f : H ⟶ K) [Algebra.FiniteType k K]
    (hK : geometricallyUnipotentPointsCommHopfAlgProperty k K)
    (hflat : (CommHopfAlgCat.imageι f).hom.toAlgHom.toRingHom.FaithfullyFlat) :
    geometricallyUnipotentPointsCommHopfAlgProperty k (CommHopfAlgCat.image f) := by
  have hfinite : (CommHopfAlgCat.imageι f).hom.toAlgHom.FiniteType := by
    apply AlgHom.FiniteType.of_comp_finiteType
      (f := Algebra.ofId k (CommHopfAlgCat.image f))
    rw [Algebra.comp_ofId]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  exact of_faithfullyFlat (CommHopfAlgCat.imageι f) hfinite hflat hK

end geometricallyUnipotentPointsCommHopfAlgProperty

end TauCeti
