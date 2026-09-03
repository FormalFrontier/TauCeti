/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Basic
public import TauCeti.RingTheory.FiniteType.FaithfullyFlatPoints

/-!
# Points of faithfully flat affine group morphisms

Let `f : H ⟶ K` be a morphism of commutative Hopf algebras over a commutative ring `R`.
Contravariantly, it represents an affine group morphism from `Spec K` to `Spec H`. If the
underlying algebra map is faithfully flat and of finite type, this morphism is surjective on
points valued in every algebraically closed field over `R`.

The algebraic point-lifting theorem is
`AlgHom.surjective_comp_right_of_faithfullyFlat`. The result here records it in the group-valued
functor-of-points API, where precomposition is the component of
`CommHopfAlgCat.mapPointsFunctor f`.

## Main declaration

* `TauCeti.CommHopfAlgCat.mapPointsFunctor_app_surjective_of_faithfullyFlat`: a faithfully flat
  finite-type coordinate morphism induces a surjection on algebraically closed points.

## References

* The Stacks Project, Tag 00HQ, Lemma 10.39.16.
* The Stacks Project, Tag 00FV, *Hilbert Nullstellensatz*.

This is the group-valued point-lifting interface used in Layer 5, "The unipotent radical", of the
ReductiveGroups roadmap. Applied to the faithfully flat morphism from an affine group onto its
scheme-theoretic image, it lets properties of source points descend to all image points.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.CommHopfAlgCat

universe u v w

variable {R : Type u} [CommRing R]
variable {H K : _root_.CommHopfAlgCat.{v} R}
variable (L : Type w) [Field L] [Algebra R L] [IsAlgClosed L]

/-- A faithfully flat finite-type morphism of commutative Hopf algebras is surjective on points
valued in an algebraically closed field.

The conclusion is stated for the component of the group-valued points functor, rather than for
bare algebra maps, so it can be used directly with group-theoretic point properties. -/
theorem mapPointsFunctor_app_surjective_of_faithfullyFlat (f : H ⟶ K)
    (hfinite : f.hom.toAlgHom.FiniteType)
    (hflat : f.hom.toAlgHom.toRingHom.FaithfullyFlat) :
    Function.Surjective ((mapPointsFunctor f).app (CommAlgCat.of R L)) := by
  intro p
  obtain ⟨q, hq⟩ := AlgHom.surjective_comp_right_of_faithfullyFlat
    f.hom.toAlgHom hfinite hflat p.ofConv
  refine ⟨WithConv.toConv q, ?_⟩
  apply WithConv.ofConv_injective
  rw [mapPointsFunctor_app_apply]
  simpa only [WithConv.ofConv_toConv] using hq

end TauCeti.CommHopfAlgCat
