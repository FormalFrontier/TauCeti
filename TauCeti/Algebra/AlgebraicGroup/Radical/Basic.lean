/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation

/-!
# Geometric normal-subgroup-freeness properties

This file packages the common construction behind the reductive and semisimple predicates. Given
an isomorphism-invariant property `P` of finite-type commutative Hopf algebras over an algebraic
closure, `geometricNormalSubgroupFreeCommHopfAlgProperty k P` says that the ambient group is
smooth and geometrically connected and that every connected normal closed subgroup satisfying
`P` is trivial.

The construction is invariant under isomorphism. Its shared API also shows that, when the whole
geometric fibre satisfies `P`, its zero Hopf ideal is the augmentation ideal and its coordinate
algebra is bialgebra-equivalent to the algebraic closure via the counit.

## Main declarations

* `TauCeti.geometricNormalSubgroupFreeCommHopfAlgProperty`: the generic normal-subgroup-freeness
  property.
* `TauCeti.geometricNormalSubgroupFreeCommHopfAlgProperty.eq_augmentation`: candidate normal
  subgroups are trivial.
* `TauCeti.geometricNormalSubgroupFreeCommHopfAlgProperty.geometricFiberCounitBialgEquiv`: a
  geometric fibre satisfying the candidate property is trivial.

This is shared infrastructure for the reductive and semisimple definitions in Layer 6,
"Reductive and semisimple groups", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

/-- The object property selecting smooth geometrically connected finite-type affine groups whose
connected normal geometric subgroups satisfying `P` are all trivial.

The candidate property `P` is imposed on the coordinate Hopf algebra of the subgroup, represented
contravariantly as a quotient by a normal Hopf ideal. -/
def geometricNormalSubgroupFreeCommHopfAlgProperty (k : Type u) [Field k]
    (P : ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k))) :
    ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} k) :=
  fun H ↦
    Algebra.Smooth k H ∧
      geometricallyConnectedCommHopfAlgProperty k H.obj ∧
        ∀ I : HopfIdeal (AlgebraicClosure k)
            (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H),
          I.IsNormal →
            geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)
              (FiniteTypeCommHopfAlgCat.quotient
                (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I).obj →
            P (FiniteTypeCommHopfAlgCat.quotient
              (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I) →
            I = HopfIdeal.augmentation (AlgebraicClosure k)
              (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)

/-- Membership in the generic geometric normal-subgroup-freeness property. -/
@[simp]
theorem geometricNormalSubgroupFreeCommHopfAlgProperty_iff (k : Type u) [Field k]
    (P : ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k)))
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    geometricNormalSubgroupFreeCommHopfAlgProperty k P H ↔
      Algebra.Smooth k H ∧
        geometricallyConnectedCommHopfAlgProperty k H.obj ∧
          ∀ I : HopfIdeal (AlgebraicClosure k)
              (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H),
            I.IsNormal →
              geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)
                (FiniteTypeCommHopfAlgCat.quotient
                  (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I).obj →
              P (FiniteTypeCommHopfAlgCat.quotient
                (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I) →
              I = HopfIdeal.augmentation (AlgebraicClosure k)
                (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :=
  Iff.rfl

/-- Geometric normal-subgroup-freeness is invariant under isomorphism when the candidate subgroup
property is invariant under isomorphism. -/
instance (k : Type u) [Field k]
    (P : ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k)))
    [P.IsClosedUnderIsomorphisms] :
    (geometricNormalSubgroupFreeCommHopfAlgProperty k P).IsClosedUnderIsomorphisms where
  of_iso {H K} e hH := by
    let e₀ := (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
      (CommHopfAlgCat.{u} k)).mapIso e
    let Hbar := FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H
    let Kbar := FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) K
    let ebar := (FiniteTypeCommHopfAlgCat.baseChangeFunctor
      (K := AlgebraicClosure k)).mapIso e
    let ebar₀ := (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k))
      (CommHopfAlgCat.{u} (AlgebraicClosure k))).mapIso ebar
    let f : Hbar →ₐc[AlgebraicClosure k] Kbar := ebar₀.hom.hom
    have hfinjective : Function.Injective f :=
      (ConcreteCategory.bijective_of_isIso ebar₀.hom).1
    have hfsurjective : Function.Surjective f :=
      (ConcreteCategory.bijective_of_isIso ebar₀.hom).2
    refine ⟨(smoothCommHopfAlgProperty_iff K.obj).mp <|
        (smoothCommHopfAlgProperty k).prop_of_iso e₀
          ((smoothCommHopfAlgProperty_iff H.obj).mpr hH.1),
      (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e₀ hH.2.1, ?_⟩
    intro I hnormal hconnected hP
    let J := I.comap f hfsurjective
    have hnormalJ : J.IsNormal :=
      hnormal.comap_of_bijective f hfinjective hfsurjective
    let qIso : FiniteTypeCommHopfAlgCat.quotient Hbar J ≅
        FiniteTypeCommHopfAlgCat.quotient Kbar I :=
      FiniteTypeCommHopfAlgCat.quotientIsoOfIso ebar I
    let qIso₀ := (forget₂
      (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k))
      (CommHopfAlgCat.{u} (AlgebraicClosure k))).mapIso qIso
    have hconnectedJ : geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.quotient Hbar J).obj :=
      (geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso
        qIso₀.symm hconnected
    have hPJ : P (FiniteTypeCommHopfAlgCat.quotient Hbar J) :=
      P.prop_of_iso qIso.symm hP
    have hJ := hH.2.2 J hnormalJ hconnectedJ hPJ
    rw [← HopfIdeal.comap_eq_comap_iff_of_surjective f hfsurjective,
      HopfIdeal.comap_augmentation]
    exact hJ

namespace geometricNormalSubgroupFreeCommHopfAlgProperty

variable {k : Type u} [Field k]
  {P : ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k))}
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- A group satisfying a geometric normal-subgroup-freeness property is smooth. -/
theorem smooth (hH : geometricNormalSubgroupFreeCommHopfAlgProperty k P H) :
    Algebra.Smooth k H :=
  hH.1

/-- A group satisfying a geometric normal-subgroup-freeness property is geometrically connected. -/
theorem geometricallyConnected (hH : geometricNormalSubgroupFreeCommHopfAlgProperty k P H) :
    geometricallyConnectedCommHopfAlgProperty k H.obj :=
  hH.2.1

/-- Every connected normal closed subgroup of the geometric fibre satisfying `P` is trivial. -/
theorem eq_augmentation (hH : geometricNormalSubgroupFreeCommHopfAlgProperty k P H)
    (I : HopfIdeal (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H))
    (hI : I.IsNormal)
    (hconnected : geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I).obj)
    (hP : P (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I)) :
    I = HopfIdeal.augmentation (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :=
  hH.2.2 I hI hconnected hP

/-- If the whole geometric fibre satisfies `P`, its zero Hopf ideal is the augmentation ideal. -/
theorem bot_eq_augmentation [P.IsClosedUnderIsomorphisms]
    (hH : geometricNormalSubgroupFreeCommHopfAlgProperty k P H)
    (hP : P (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)) :
    (⊥ : HopfIdeal (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)) =
        HopfIdeal.augmentation (AlgebraicClosure k)
          (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) := by
  let Hbar := FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H
  let qIso := FiniteTypeCommHopfAlgCat.quotientBotIso Hbar
  let qIso₀ := (forget₂
    (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k))
    (CommHopfAlgCat.{u} (AlgebraicClosure k))).mapIso qIso
  apply hH.eq_augmentation (I := (⊥ : HopfIdeal (AlgebraicClosure k) Hbar))
  · exact HopfIdeal.isNormal_bot
  · exact (geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso
      qIso₀.symm
      (geometricallyConnectedCommHopfAlgProperty.baseChange k (AlgebraicClosure k) H.obj
        hH.geometricallyConnected)
  · exact P.prop_of_iso qIso.symm hP

/-- If the whole geometric fibre satisfies `P`, its coordinate algebra is bialgebra-equivalent
to the algebraic closure via the counit. -/
noncomputable def geometricFiberCounitBialgEquiv [P.IsClosedUnderIsomorphisms]
    (hH : geometricNormalSubgroupFreeCommHopfAlgProperty k P H)
    (hP : P (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)) :
    FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H
        ≃ₐc[AlgebraicClosure k] AlgebraicClosure k :=
  HopfIdeal.counitBialgEquivOfAugmentationEqBot
    (hH.bot_eq_augmentation hP).symm

/-- The generic trivial-geometric-fibre equivalence is the counit. -/
@[simp]
theorem geometricFiberCounitBialgEquiv_apply [P.IsClosedUnderIsomorphisms]
    (hH : geometricNormalSubgroupFreeCommHopfAlgProperty k P H)
    (hP : P (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H))
    (x : FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :
    hH.geometricFiberCounitBialgEquiv hP x =
      Bialgebra.counitBialgHom (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) x := by
  rw [geometricFiberCounitBialgEquiv]
  exact HopfIdeal.counitBialgEquivOfAugmentationEqBot_apply _ _

/-- The inverse of the generic trivial-geometric-fibre equivalence is the structure map. -/
@[simp]
theorem geometricFiberCounitBialgEquiv_symm_apply [P.IsClosedUnderIsomorphisms]
    (hH : geometricNormalSubgroupFreeCommHopfAlgProperty k P H)
    (hP : P (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H))
    (r : AlgebraicClosure k) :
    (hH.geometricFiberCounitBialgEquiv hP).symm r =
      algebraMap (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) r := by
  rw [geometricFiberCounitBialgEquiv]
  exact HopfIdeal.counitBialgEquivOfAugmentationEqBot_symm_apply _ _

end geometricNormalSubgroupFreeCommHopfAlgProperty

end

end TauCeti
