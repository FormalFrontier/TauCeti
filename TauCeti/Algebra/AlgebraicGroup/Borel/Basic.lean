/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic

/-!
# Borel subgroups in Hopf coordinates

A closed subgroup of a finite-type affine group over a field is encoded contravariantly by a
Hopf ideal in its coordinate algebra. This file defines a Borel subgroup to be a smooth,
geometrically connected, geometrically solvable closed subgroup whose base change to an
algebraic closure is maximal among closed subgroups with those properties.

Smoothness remains explicit: the ambient affine group need not be smooth, and geometric
connectedness and solvability alone do not exclude nonreduced subgroup schemes. Because Hopf
ideals reverse subgroup inclusion, maximality of the represented subgroup is minimality of its
defining ideal among ideals satisfying the three geometric properties after base change to an
algebraic closure. This geometric maximality is essential over a non-algebraically-closed field:
maximality only among subgroups defined over the ground field is not the Borel condition.

## Main declarations

* `TauCeti.HopfIdeal.IsBorel`: the Borel-subgroup predicate in Hopf coordinates.
* `TauCeti.HopfIdeal.IsBorel.comapOfIso_iff`: Borel status is invariant under an ambient
  Hopf-algebra isomorphism.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 17.a.
* T. A. Springer, *Linear Algebraic Groups*, Sections 6.2--6.3.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v

namespace HopfIdeal

/-- The isomorphism-invariant property imposed on coordinate quotients in the definition of a
Borel subgroup. -/
private def borelQuotientProperty (k : Type u) [Field k] :
    ObjectProperty (FiniteTypeCommHopfAlgCat.{u, v} k) :=
  ((smoothCommHopfAlgProperty k ⊓
    (geometricallyConnectedCommHopfAlgProperty k ⊓
      geometricallySolvablePointsCommHopfAlgProperty k)) :
    ObjectProperty (_root_.CommHopfAlgCat.{v} k)).inverseImage
      (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} k) (_root_.CommHopfAlgCat.{v} k))

private instance (k : Type u) [Field k] :
    (borelQuotientProperty k :
      ObjectProperty (FiniteTypeCommHopfAlgCat.{u, v} k)).IsClosedUnderIsomorphisms := by
  unfold borelQuotientProperty
  infer_instance

/-- A Hopf ideal defines a Borel subgroup when, after base change to an algebraic closure, its
quotient coordinate algebra is smooth, geometrically connected, and geometrically solvable, and
no strictly larger closed subgroup has all three properties.

The order is contravariant: `J ≤ I` says that the subgroup cut out by `I` is contained in the
subgroup cut out by `J`. -/
def IsBorel (k : Type u) [Field k] (H : _root_.CommHopfAlgCat.{v} k)
    [Algebra.FiniteType k H] (I : HopfIdeal k H) : Prop :=
  let K := AlgebraicClosure k
  let H' := FiniteTypeCommHopfAlgCat.baseChange (K := K)
    ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩
  let I' := CommHopfAlgCat.baseChangeHopfIdeal (K := K) I
  Minimal (fun J : HopfIdeal K H'.obj ↦
    borelQuotientProperty K (FiniteTypeCommHopfAlgCat.quotient H' J)) I'

/-- The Hopf-ideal criterion for a Borel subgroup: after algebraic-closure base change, its
quotient is smooth, geometrically connected, and geometrically solvable, and it is maximal among
such closed subgroups. -/
@[simp]
theorem isBorel_iff (k : Type u) [Field k] (H : _root_.CommHopfAlgCat.{v} k)
    [Algebra.FiniteType k H] (I : HopfIdeal k H) :
    let K := AlgebraicClosure k
    let H' := FiniteTypeCommHopfAlgCat.baseChange (K := K)
      ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩
    let I' := CommHopfAlgCat.baseChangeHopfIdeal (K := K) I
    IsBorel k H I ↔
      smoothCommHopfAlgProperty K
          (FiniteTypeCommHopfAlgCat.quotient
            H' I').obj ∧
        geometricallyConnectedCommHopfAlgProperty K
          (FiniteTypeCommHopfAlgCat.quotient
            H' I').obj ∧
        geometricallySolvablePointsCommHopfAlgProperty K
          (FiniteTypeCommHopfAlgCat.quotient
            H' I').obj ∧
        ∀ J : HopfIdeal K H'.obj,
          smoothCommHopfAlgProperty K
              (FiniteTypeCommHopfAlgCat.quotient
                H' J).obj →
            geometricallyConnectedCommHopfAlgProperty K
              (FiniteTypeCommHopfAlgCat.quotient
                H' J).obj →
            geometricallySolvablePointsCommHopfAlgProperty K
              (FiniteTypeCommHopfAlgCat.quotient
                H' J).obj →
            J ≤ I' → I' ≤ J := by
  constructor
  · rintro ⟨⟨hsmooth, hconnected, hsolvable⟩, hmax⟩
    exact ⟨hsmooth, hconnected, hsolvable,
      fun J hJsmooth hJconnected hJsolvable hJI ↦
        hmax ⟨hJsmooth, hJconnected, hJsolvable⟩ hJI⟩
  · rintro ⟨hsmooth, hconnected, hsolvable, hmax⟩
    exact ⟨⟨hsmooth, hconnected, hsolvable⟩,
      fun J hJ hJI ↦ hmax J hJ.1 hJ.2.1 hJ.2.2 hJI⟩

private theorem minimal_borelQuotientProperty_comapOfIso
    {k : Type u} [Field k]
    {H L : FiniteTypeCommHopfAlgCat.{u, v} k} {I : HopfIdeal k L.obj}
    (hI : Minimal
      (fun J : HopfIdeal (AlgebraicClosure k)
          (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) L).obj ↦
        borelQuotientProperty (AlgebraicClosure k)
          (FiniteTypeCommHopfAlgCat.quotient
            (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) L) J))
      (CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k) I))
    (e : H ≅ L) :
    Minimal
      (fun J : HopfIdeal (AlgebraicClosure k)
          (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H).obj ↦
        borelQuotientProperty (AlgebraicClosure k)
          (FiniteTypeCommHopfAlgCat.quotient
            (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) J))
      (CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k)
        (I.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
          (ConcreteCategory.bijective_of_isIso e.hom).2)) := by
  let eK := (FiniteTypeCommHopfAlgCat.baseChangeFunctor
    (K := AlgebraicClosure k)).mapIso e
  have htransport := FiniteTypeCommHopfAlgCat.minimal_quotientProperty_comapOfIso
    (H := FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)
    (K := FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) L)
    (borelQuotientProperty (AlgebraicClosure k))
    (CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k) I) hI eK
  have hbaseChange :
      CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k)
          (I.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
            (ConcreteCategory.bijective_of_isIso e.hom).2) =
        (CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k) I).comapOfSurjective
          (FiniteTypeCommHopfAlgCat.toBialgHom eK.hom)
          (ConcreteCategory.bijective_of_isIso eK.hom).2 :=
    CommHopfAlgCat.baseChangeHopfIdeal_comapOfIso (K := AlgebraicClosure k) I
      ((forget₂ (FiniteTypeCommHopfAlgCat.{u, v} k)
        (_root_.CommHopfAlgCat.{v} k)).mapIso e)
  rw [hbaseChange]
  exact htransport

namespace IsBorel

variable {k : Type u} [Field k]
variable {H L : FiniteTypeCommHopfAlgCat.{u, v} k} {I : HopfIdeal k L.obj}

/-- Pulling a Borel subgroup back across an ambient Hopf-algebra isomorphism gives a Borel
subgroup in the source. -/
theorem comapOfIso (hI : IsBorel k L.obj I) (e : H ≅ L) :
    IsBorel k H.obj
      (I.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
        (ConcreteCategory.bijective_of_isIso e.hom).2) := by
  -- `IsBorel` is definitionally this minimal quotient property; no private `Iff.rfl`
  -- wrapper is retained solely to unfold and refold it for transport.
  change Minimal
    (fun J : HopfIdeal (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H).obj ↦
      borelQuotientProperty (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.quotient
          (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) J))
    (CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k)
      (I.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
        (ConcreteCategory.bijective_of_isIso e.hom).2))
  exact minimal_borelQuotientProperty_comapOfIso hI e

/-- Borel status is invariant under pulling the defining ideal back across an ambient
Hopf-algebra isomorphism. -/
theorem comapOfIso_iff (e : H ≅ L) (I : HopfIdeal k L.obj) :
    IsBorel k H.obj
        (I.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
          (ConcreteCategory.bijective_of_isIso e.hom).2) ↔
      IsBorel k L.obj I := by
  constructor
  · intro hI
    have hback := hI.comapOfIso e.symm
    let e' := (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} k)
      (_root_.CommHopfAlgCat.{v} k)).mapIso e
    let e'' := _root_.CommHopfAlgCat.ofIso e'
    -- `toBialgHom` for a finite-type morphism is definitionally the bialgebra morphism of
    -- its image under this forgetful functor; the full-subcategory wrapper has no separate
    -- propositional compatibility lemma.
    change IsBorel k L.obj
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
    rwa [he] at hback
  · exact fun hI ↦ hI.comapOfIso e

end IsBorel

end HopfIdeal

end TauCeti
