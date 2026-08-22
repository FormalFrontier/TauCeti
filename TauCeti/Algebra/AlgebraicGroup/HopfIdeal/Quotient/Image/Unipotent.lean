/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.FaithfullyFlatPoints
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Basic

/-!
# Unipotence of faithfully flat affine group images

Let `f : H ⟶ K` be a finite-type faithfully flat morphism of commutative Hopf algebras over a
field. Contravariantly, every algebraically closed point of `Spec H` lifts to a point of
`Spec K`, so geometric unipotence descends from `K` to `H`. In particular, for an arbitrary
morphism, its scheme-theoretic image has coordinate algebra
`CommHopfAlgCat.image f = H / ker f`; finite type of `K` makes the canonical inclusion
`CommHopfAlgCat.image f ⟶ K` finite type, giving the image result.

Unipotence is preserved when a point is precomposed with a Hopf-algebra morphism. It therefore
descends from `Spec K` to the scheme-theoretic image. This supplies the geometric-point step in
forming the product of two normal smooth unipotent closed subgroup schemes: after multiplication
is realized as a faithfully flat morphism onto its image, the image is again geometrically
unipotent.

## Main declaration

* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.of_faithfullyFlat`: geometric
  unipotence descends along a finite-type faithfully flat coordinate morphism.
* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.image_of_faithfullyFlat`: a
  faithfully flat finite-type affine group image has only unipotent geometric points when its
  source does.

## References

* The Stacks Project, Tags 00HQ and 00FV, for algebraically closed points of faithfully flat
  finite-type algebras.
* A. Borel, *Linear Algebraic Groups*, Proposition 14.4, for the unipotent-radical application.

This is the algebraically-closed-point bridge for Layer 5, "The unipotent radical", of the
ReductiveGroups roadmap. It combines point lifting along a faithfully flat finite-type algebra
map with functoriality of unipotent points. The separate theorem that a homomorphism of affine
groups is faithfully flat onto its scheme-theoretic image remains the input that discharges the
hypothesis below.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u v

namespace geometricallyUnipotentPointsCommHopfAlgProperty

variable {k : Type u} [Field k]
variable {H K : _root_.CommHopfAlgCat.{v} k}

/-- Geometric unipotence descends along a finite-type faithfully flat coordinate morphism. -/
theorem of_faithfullyFlat (f : H ⟶ K) (hfinite : f.hom.toAlgHom.FiniteType)
    (hflat : f.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (hK : geometricallyUnipotentPointsCommHopfAlgProperty k K) :
    geometricallyUnipotentPointsCommHopfAlgProperty k H := by
  rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff] at hK ⊢
  intro g
  obtain ⟨(q : WithConv (K →ₐ[k] AlgebraicClosure k)), hq⟩ :=
    CommHopfAlgCat.mapPointsFunctor_app_surjective_of_faithfullyFlat
      (AlgebraicClosure k) f hfinite hflat g
  have hqunipotent := (hK q).mapDomain f.hom
  have hmap : AlgHom.mapDomain f.hom q = g := by
    rw [AlgHom.mapDomain_apply]
    rw [CommHopfAlgCat.mapPointsFunctor_app_apply] at hq
    exact hq
  rw [hmap] at hqunipotent
  exact hqunipotent

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
