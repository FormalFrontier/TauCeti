/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic

/-!
# Borel subgroups in Hopf coordinates

A closed subgroup of a finite-type affine group over a field is encoded contravariantly by a
Hopf ideal in its coordinate algebra. This file defines a Borel subgroup to be a smooth,
geometrically connected, geometrically solvable closed subgroup which is maximal among closed
subgroups with those properties.

Smoothness remains explicit: the ambient affine group need not be smooth, and geometric
connectedness and solvability alone do not exclude nonreduced subgroup schemes. Because Hopf
ideals reverse subgroup inclusion, maximality of the represented subgroup is minimality of its
defining ideal among ideals satisfying the three geometric properties.

## Main declarations

* `TauCeti.HopfIdeal.IsBorel`: the Borel-subgroup predicate in Hopf coordinates.
* `TauCeti.HopfIdeal.IsBorel.comapOfIso`: Borel subgroups transport across isomorphisms of the
  ambient coordinate Hopf algebra.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 17.a.
* T. A. Springer, *Linear Algebraic Groups*, Sections 6.2--6.3.

This supplies the Borel-subgroup predicate required by Layer 7, "Borel subgroups, maximal tori,
and their conjugacy", of the ReductiveGroups roadmap. Existence and conjugacy for general
reductive groups remain downstream.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace HopfIdeal

/-- A Hopf ideal defines a Borel subgroup when its quotient coordinate algebra is smooth,
geometrically connected, and geometrically solvable, and no strictly larger closed subgroup has
all three properties.

The order is contravariant: `J ≤ I` says that the subgroup cut out by `I` is contained in the
subgroup cut out by `J`. -/
def IsBorel (k : Type u) [Field k] (H : _root_.CommHopfAlgCat.{u} k)
    [Algebra.FiniteType k H] (I : HopfIdeal k H) : Prop :=
  Minimal (fun J : HopfIdeal k H ↦
    smoothCommHopfAlgProperty k
        (FiniteTypeCommHopfAlgCat.quotient
          ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ J).obj ∧
      geometricallyConnectedCommHopfAlgProperty k
        (FiniteTypeCommHopfAlgCat.quotient
          ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ J).obj ∧
      geometricallySolvablePointsCommHopfAlgProperty k
        (FiniteTypeCommHopfAlgCat.quotient
          ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ J).obj) I

/-- The Hopf-ideal criterion for a Borel subgroup: its quotient is smooth, geometrically
connected, and geometrically solvable, and it is maximal among such closed subgroups. -/
@[simp]
theorem isBorel_iff (k : Type u) [Field k] (H : _root_.CommHopfAlgCat.{u} k)
    [Algebra.FiniteType k H] (I : HopfIdeal k H) :
    IsBorel k H I ↔
      smoothCommHopfAlgProperty k
          (FiniteTypeCommHopfAlgCat.quotient
            ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ I).obj ∧
        geometricallyConnectedCommHopfAlgProperty k
          (FiniteTypeCommHopfAlgCat.quotient
            ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ I).obj ∧
        geometricallySolvablePointsCommHopfAlgProperty k
          (FiniteTypeCommHopfAlgCat.quotient
            ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ I).obj ∧
        ∀ J : HopfIdeal k H,
          smoothCommHopfAlgProperty k
              (FiniteTypeCommHopfAlgCat.quotient
                ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ J).obj →
            geometricallyConnectedCommHopfAlgProperty k
              (FiniteTypeCommHopfAlgCat.quotient
                ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ J).obj →
            geometricallySolvablePointsCommHopfAlgProperty k
              (FiniteTypeCommHopfAlgCat.quotient
                ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ J).obj →
            J ≤ I → I ≤ J := by
  constructor
  · rintro ⟨⟨hsmooth, hconnected, hsolvable⟩, hmax⟩
    exact ⟨hsmooth, hconnected, hsolvable,
      fun J hJsmooth hJconnected hJsolvable hJI ↦
        hmax ⟨hJsmooth, hJconnected, hJsolvable⟩ hJI⟩
  · rintro ⟨hsmooth, hconnected, hsolvable, hmax⟩
    exact ⟨⟨hsmooth, hconnected, hsolvable⟩,
      fun J hJ hJI ↦ hmax J hJ.1 hJ.2.1 hJ.2.2 hJI⟩

namespace IsBorel

variable {k : Type u} [Field k]
variable {H K : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k K.obj}

/-- Pulling a Borel subgroup back across an ambient Hopf-algebra isomorphism gives a Borel
subgroup in the source. -/
theorem comapOfIso (hI : IsBorel k K.obj I) (e : H ≅ K) :
    IsBorel k H.obj
      (I.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
        (ConcreteCategory.bijective_of_isIso e.hom).2) := by
  let f := FiniteTypeCommHopfAlgCat.toBialgHom e.hom
  let hf := (ConcreteCategory.bijective_of_isIso e.hom).2
  let g := FiniteTypeCommHopfAlgCat.toBialgHom e.inv
  let hg := (ConcreteCategory.bijective_of_isIso e.inv).2
  let forget : FiniteTypeCommHopfAlgCat.{u, u} k ⥤ _root_.CommHopfAlgCat.{u} k :=
    forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k) (_root_.CommHopfAlgCat.{u} k)
  rw [isBorel_iff] at hI ⊢
  refine ⟨(smoothCommHopfAlgProperty k).prop_of_iso
      (forget.mapIso (FiniteTypeCommHopfAlgCat.quotientIsoOfIso e I)).symm hI.1,
    (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
      (forget.mapIso (FiniteTypeCommHopfAlgCat.quotientIsoOfIso e I)).symm hI.2.1,
    (geometricallySolvablePointsCommHopfAlgProperty k).prop_of_iso
      (forget.mapIso (FiniteTypeCommHopfAlgCat.quotientIsoOfIso e I)).symm hI.2.2.1, ?_⟩
  intro J hJsmooth hJconnected hJsolvable hJpulled
  let J' := J.comapOfSurjective g hg
  have hJ'smooth : smoothCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient K J').obj :=
    (smoothCommHopfAlgProperty k).prop_of_iso
      (forget.mapIso (FiniteTypeCommHopfAlgCat.quotientIsoOfIso e.symm J)).symm hJsmooth
  have hJ'connected : geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient K J').obj :=
    (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
      (forget.mapIso (FiniteTypeCommHopfAlgCat.quotientIsoOfIso e.symm J)).symm hJconnected
  have hJ'solvable : geometricallySolvablePointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient K J').obj :=
    (geometricallySolvablePointsCommHopfAlgProperty k).prop_of_iso
      (forget.mapIso (FiniteTypeCommHopfAlgCat.quotientIsoOfIso e.symm J)).symm hJsolvable
  have hJ'comap : J'.comapOfSurjective f hf = J :=
    HopfIdeal.comapOfSurjective_bialgEquiv_symm_apply J
      (_root_.CommHopfAlgCat.ofIso <| (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
        (_root_.CommHopfAlgCat.{u} k)).mapIso e)
  have hJ'I : J' ≤ I := by
    rw [← HopfIdeal.comapOfSurjective_le_comapOfSurjective_iff f hf, hJ'comap]
    exact hJpulled
  have hIJ' : I ≤ J' := hI.2.2.2 J' hJ'smooth hJ'connected hJ'solvable hJ'I
  calc
    I.comapOfSurjective f hf ≤ J'.comapOfSurjective f hf :=
      HopfIdeal.comapOfSurjective_mono f hf hIJ'
    _ = J := hJ'comap

end IsBorel

end HopfIdeal

end TauCeti
