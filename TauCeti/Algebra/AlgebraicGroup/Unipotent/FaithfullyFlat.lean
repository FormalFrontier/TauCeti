/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.FaithfullyFlatPoints
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Basic

/-!
# Unipotence under faithfully flat morphisms

Let `f : H ⟶ K` be a finite-type faithfully flat morphism of commutative Hopf algebras over a
field. Contravariantly, every algebraically closed point of `Spec H` lifts to a point of
`Spec K`, so geometric unipotence descends from `K` to `H`.

Unipotence is preserved when a point is precomposed with a Hopf-algebra morphism. Point lifting
along `f` therefore transfers geometric unipotence from its source affine group to its target.

## Main declaration

* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.of_faithfullyFlat`: geometric
  unipotence descends along a finite-type faithfully flat coordinate morphism.

## References

* The Stacks Project, Tags 00HQ and 00FV, for algebraically closed points of faithfully flat
  finite-type algebras.

This is an algebraically-closed-point bridge for Layer 5, "The unipotent radical", of the
ReductiveGroups roadmap.
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

end geometricallyUnipotentPointsCommHopfAlgProperty

end TauCeti
