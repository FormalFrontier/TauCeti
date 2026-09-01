/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic

/-!
# Maximal tori in Hopf coordinates

A closed subgroup of an affine group is encoded contravariantly by a Hopf ideal in its
coordinate algebra. This file defines a maximal torus to be a torus closed subgroup which is
not properly contained in another torus. Thus, if `I` is maximal and `J ≤ I` defines a torus,
then `I = J`.

## Main declarations

* `TauCeti.HopfIdeal.IsMaximalTorus`: maximality among torus Hopf ideals.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§12 and 17.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §8.

This supplies the Hopf-coordinate maximal-torus predicate required by Layer 7, "Borel subgroups,
maximal tori, and their conjugacy", of the ReductiveGroups roadmap. Existence and conjugacy of
maximal tori remain to be proved.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace HopfIdeal

/-- A Hopf ideal defines a maximal torus when its quotient coordinate Hopf algebra is a torus
and every torus closed subgroup containing it is equal to it.

Because coordinate rings reverse arrows, `J ≤ I` says that the subgroup cut out by `I` is
contained in the subgroup cut out by `J`. -/
def IsMaximalTorus (k : Type u) [Field k] (H : _root_.CommHopfAlgCat.{u} k)
    [Algebra.FiniteType k H] (I : HopfIdeal k H) : Prop :=
  Minimal (fun J : HopfIdeal k H ↦
    torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ J)) I

/-- The Hopf-ideal criterion for a maximal torus: the quotient is a torus and no strictly larger
torus closed subgroup contains it. -/
@[simp]
theorem isMaximalTorus_iff (k : Type u) [Field k] (H : _root_.CommHopfAlgCat.{u} k)
    [Algebra.FiniteType k H] (I : HopfIdeal k H) :
    IsMaximalTorus k H I ↔
      torusCommHopfAlgProperty k
          (FiniteTypeCommHopfAlgCat.quotient
            ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ I) ∧
        ∀ J : HopfIdeal k H,
          torusCommHopfAlgProperty k
              (FiniteTypeCommHopfAlgCat.quotient
                ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ J) →
            J ≤ I → I ≤ J :=
  Iff.rfl

namespace IsMaximalTorus

variable {k : Type u} [Field k]
variable {H K : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k K.obj}

/-- Pulling a maximal torus back across an ambient Hopf-algebra isomorphism gives a maximal
torus in the source. -/
theorem comapOfIso (hI : IsMaximalTorus k K.obj I) (e : H ≅ K) :
    IsMaximalTorus k H.obj
      (I.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
        (ConcreteCategory.bijective_of_isIso e.hom).2) := by
  let f := FiniteTypeCommHopfAlgCat.toBialgHom e.hom
  let hf := (ConcreteCategory.bijective_of_isIso e.hom).2
  let g := FiniteTypeCommHopfAlgCat.toBialgHom e.inv
  let hg := (ConcreteCategory.bijective_of_isIso e.inv).2
  refine ⟨(torusCommHopfAlgProperty k).prop_of_iso
    (FiniteTypeCommHopfAlgCat.quotientIsoOfIso e I).symm hI.prop, ?_⟩
  intro J hJ hJpulled
  let J' := J.comapOfSurjective g hg
  have hJ' : torusCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient K J') :=
    (torusCommHopfAlgProperty k).prop_of_iso
      (FiniteTypeCommHopfAlgCat.quotientIsoOfIso e.symm J).symm hJ
  have hJ'I : J' ≤ I := by
    intro x hx
    have hx' := HopfIdeal.mem_comapOfSurjective.mp hx
    have hx'' := HopfIdeal.mem_comapOfSurjective.mp (hJpulled hx')
    have hcancel : f (g x) = x := by
      have h := congrArg (fun q : K ⟶ K ↦ FiniteTypeCommHopfAlgCat.toBialgHom q x)
        e.inv_hom_id
      simpa only [FiniteTypeCommHopfAlgCat.toBialgHom_comp, BialgHom.comp_apply,
        FiniteTypeCommHopfAlgCat.toBialgHom_id, BialgHom.coe_id, id_eq] using h
    rwa [hcancel] at hx''
  have hIJ' : I ≤ J' := hI.le_of_le hJ' hJ'I
  intro x hx
  have hx' := hIJ' (HopfIdeal.mem_comapOfSurjective.mp hx)
  have hx'' := HopfIdeal.mem_comapOfSurjective.mp hx'
  have hcancel : g (f x) = x := by
    have h := congrArg (fun q : H ⟶ H ↦ FiniteTypeCommHopfAlgCat.toBialgHom q x)
      e.hom_inv_id
    simpa only [FiniteTypeCommHopfAlgCat.toBialgHom_comp, BialgHom.comp_apply,
      FiniteTypeCommHopfAlgCat.toBialgHom_id, BialgHom.coe_id, id_eq] using h
  rwa [hcancel] at hx''

/-- Maximal-torus status is invariant under pulling the defining ideal back across an ambient
Hopf-algebra isomorphism. -/
theorem comapOfIso_iff (e : H ≅ K) (I : HopfIdeal k K.obj) :
    IsMaximalTorus k H.obj
        (I.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
          (ConcreteCategory.bijective_of_isIso e.hom).2) ↔
      IsMaximalTorus k K.obj I := by
  constructor
  · intro hI
    have hback := hI.comapOfIso e.symm
    have hcancel :
        (I.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
            (ConcreteCategory.bijective_of_isIso e.hom).2).comapOfSurjective
          (FiniteTypeCommHopfAlgCat.toBialgHom e.symm.hom)
            (ConcreteCategory.bijective_of_isIso e.symm.hom).2 = I := by
      ext x
      simp only [HopfIdeal.mem_comapOfSurjective]
      have h := congrArg (fun q : K ⟶ K ↦ FiniteTypeCommHopfAlgCat.toBialgHom q x)
        e.symm.hom_inv_id
      have h' : (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
          ((FiniteTypeCommHopfAlgCat.toBialgHom e.symm.hom) x) = x := by
        simpa only [Iso.symm_inv, FiniteTypeCommHopfAlgCat.toBialgHom_comp,
          BialgHom.comp_apply, FiniteTypeCommHopfAlgCat.toBialgHom_id, BialgHom.coe_id,
          id_eq] using h
      rw [h']
    rwa [hcancel] at hback
  · exact fun hI ↦ hI.comapOfIso e

end IsMaximalTorus

end HopfIdeal

end TauCeti
