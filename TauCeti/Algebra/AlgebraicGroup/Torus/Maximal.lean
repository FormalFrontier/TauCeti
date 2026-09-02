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

The isomorphism-invariance API follows the formal organization of
`TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Isomorphism` and
`TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Isomorphism`.

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
  have hJ'comap : J'.comapOfSurjective f hf = J := by
    exact HopfIdeal.comapOfSurjective_bialgEquiv_symm_apply J
      (_root_.CommHopfAlgCat.ofIso <| (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
        (_root_.CommHopfAlgCat.{u} k)).mapIso e)
  have hJ'I : J' ≤ I := by
    rw [← HopfIdeal.comapOfSurjective_le_comapOfSurjective_iff f hf]
    rw [hJ'comap]
    exact hJpulled
  have hIJ' : I ≤ J' := hI.le_of_le hJ' hJ'I
  calc
    I.comapOfSurjective f hf ≤ J'.comapOfSurjective f hf :=
      HopfIdeal.comapOfSurjective_mono f hf hIJ'
    _ = J := hJ'comap

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
    let e' := (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
      (_root_.CommHopfAlgCat.{u} k)).mapIso e
    let e'' := _root_.CommHopfAlgCat.ofIso e'
    -- `toBialgHom` for a finite-type morphism is definitionally the bialgebra morphism of
    -- its image under this forgetful functor. No propositional compatibility lemma exists
    -- for this reducible full-subcategory wrapper.
    change IsMaximalTorus k K.obj
      (HopfIdeal.comapOfSurjective
        (I.comapOfSurjective e''.toBialgHom
          (by simpa only [BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_toBialgHom] using
            EquivLike.surjective e''))
        e''.symm.toBialgHom
          (by simpa only [BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_toBialgHom] using
            EquivLike.surjective e''.symm)) at hback
    have he := HopfIdeal.comapOfSurjective_bialgEquiv_symm_apply I e''.symm
    have he_symm_symm : e''.symm.symm = e'' := by
      ext
      rfl
    simp only [he_symm_symm] at he
    rw [he] at hback
    exact hback
  · exact fun hI ↦ hI.comapOfIso e

end IsMaximalTorus

end HopfIdeal

end TauCeti
