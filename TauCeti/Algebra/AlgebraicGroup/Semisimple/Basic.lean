/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation

/-!
# Semisimple affine groups

A finite-type affine group over a field is semisimple when it is smooth and geometrically
connected and, after extension to an algebraic closure, it has no nontrivial connected normal
smooth solvable closed subgroup. In coordinate-Hopf-algebra terms, a closed subgroup of the
geometric fibre is represented contravariantly by a Hopf-ideal quotient. The subgroup is trivial
exactly when its defining Hopf ideal is the augmentation ideal.

This formulation is equivalent to triviality of the geometric radical once that radical has been
constructed, but makes the semisimple predicate available without choosing a maximal subgroup.
Smoothness of the candidate subgroup is essential: in positive characteristic a semisimple group
can have non-smooth connected central subgroup schemes.

As a basic consequence, if the geometric fibre of a semisimple group is itself solvable, then it
is trivial. The resulting bialgebra equivalence identifies its coordinate algebra with the
algebraic closure of the ground field via the counit.

## Main declarations

* `TauCeti.semisimpleCommHopfAlgProperty`: semisimplicity for finite-type commutative Hopf
  algebras over a field.
* `TauCeti.semisimpleCommHopfAlgProperty.eq_augmentation`: every connected normal smooth
  solvable closed subgroup of a semisimple group's geometric fibre is trivial.
* `TauCeti.semisimpleCommHopfAlgProperty.geometricFiberCounitBialgEquiv`: a semisimple group
  with solvable geometric fibre has trivial geometric fibre.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§6.46 and 21.10.
* T. A. Springer, *Linear Algebraic Groups*, Chapter 8.

This is the semisimple-group definition target in Layer 6, "Reductive and semisimple groups", of
the ReductiveGroups roadmap. It states triviality of the geometric radical through its defining
universal property while the radical construction is still being developed.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

/-- The object property selecting semisimple finite-type commutative Hopf algebras over a field.

The first two conjuncts express smoothness and geometric connectedness of the ambient group. The
last says that every connected normal smooth closed subgroup with solvable geometric points is
the identity subgroup. A Hopf ideal `I` cuts out that subgroup contravariantly, so identity means
`I` is the augmentation ideal, not the zero ideal. -/
def semisimpleCommHopfAlgProperty (k : Type u) [Field k] :
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
            Algebra.Smooth (AlgebraicClosure k)
              (FiniteTypeCommHopfAlgCat.quotient
                (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I) →
            geometricallySolvablePointsCommHopfAlgProperty (AlgebraicClosure k)
              (FiniteTypeCommHopfAlgCat.quotient
                (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I).obj →
            I = HopfIdeal.augmentation (AlgebraicClosure k)
              (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)

/-- Semisimplicity means smoothness, geometric connectedness, and absence of nontrivial connected
normal smooth solvable closed subgroups after extension to an algebraic closure. -/
@[simp]
theorem semisimpleCommHopfAlgProperty_iff (k : Type u) [Field k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    semisimpleCommHopfAlgProperty k H ↔
      Algebra.Smooth k H ∧
        geometricallyConnectedCommHopfAlgProperty k H.obj ∧
          ∀ I : HopfIdeal (AlgebraicClosure k)
              (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H),
            I.IsNormal →
              geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)
                (FiniteTypeCommHopfAlgCat.quotient
                  (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I).obj →
              Algebra.Smooth (AlgebraicClosure k)
                (FiniteTypeCommHopfAlgCat.quotient
                  (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I) →
              geometricallySolvablePointsCommHopfAlgProperty (AlgebraicClosure k)
                (FiniteTypeCommHopfAlgCat.quotient
                  (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I).obj →
              I = HopfIdeal.augmentation (AlgebraicClosure k)
                (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :=
  Iff.rfl

/-- Semisimplicity is invariant under isomorphisms of finite-type commutative Hopf algebras. -/
instance (k : Type u) [Field k] :
    (semisimpleCommHopfAlgProperty k).IsClosedUnderIsomorphisms where
  of_iso {H K} e hH := by
    rw [semisimpleCommHopfAlgProperty_iff] at hH ⊢
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
    intro I hnormal hconnected hsmooth hsolvable
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
    have hsmoothJ : Algebra.Smooth (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.quotient Hbar J) :=
      (smoothCommHopfAlgProperty_iff
        (FiniteTypeCommHopfAlgCat.quotient Hbar J).obj).mp <|
          (smoothCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso qIso₀.symm <|
            (smoothCommHopfAlgProperty_iff
              (FiniteTypeCommHopfAlgCat.quotient Kbar I).obj).mpr hsmooth
    have hsolvableJ : geometricallySolvablePointsCommHopfAlgProperty (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.quotient Hbar J).obj :=
      (geometricallySolvablePointsCommHopfAlgProperty
        (AlgebraicClosure k)).prop_of_iso qIso₀.symm hsolvable
    have hJ := hH.2.2 J hnormalJ hconnectedJ hsmoothJ hsolvableJ
    rw [← HopfIdeal.comap_eq_comap_iff_of_surjective f hfsurjective,
      HopfIdeal.comap_augmentation]
    exact hJ

namespace semisimpleCommHopfAlgProperty

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- A semisimple finite-type commutative Hopf algebra is smooth over its ground field. -/
theorem smooth (hH : semisimpleCommHopfAlgProperty k H) : Algebra.Smooth k H :=
  hH.1

/-- A semisimple finite-type commutative Hopf algebra is geometrically connected. -/
theorem geometricallyConnected (hH : semisimpleCommHopfAlgProperty k H) :
    geometricallyConnectedCommHopfAlgProperty k H.obj :=
  hH.2.1

/-- Every connected normal smooth solvable closed subgroup of the geometric fibre of a
semisimple group is the identity subgroup. -/
theorem eq_augmentation (hH : semisimpleCommHopfAlgProperty k H)
    (I : HopfIdeal (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H))
    (hI : I.IsNormal)
    (hconnected : geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I).obj)
    (hsmooth : Algebra.Smooth (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I))
    (hsolvable : geometricallySolvablePointsCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I).obj) :
    I = HopfIdeal.augmentation (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :=
  hH.2.2 I hI hconnected hsmooth hsolvable

/-- If the geometric fibre of a semisimple group has solvable geometric points, its zero Hopf
ideal is the augmentation ideal. Equivalently, the whole geometric fibre is the identity
subgroup. -/
theorem bot_eq_augmentation (hH : semisimpleCommHopfAlgProperty k H)
    (hsolvable : geometricallySolvablePointsCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H).obj) :
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
  · exact (smoothCommHopfAlgProperty_iff
      (FiniteTypeCommHopfAlgCat.quotient Hbar ⊥).obj).mp <|
        (smoothCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso qIso₀.symm <|
          (smoothCommHopfAlgProperty_iff Hbar.obj).mpr
            (@Algebra.Smooth.baseChange k _ H (AlgebraicClosure k) _ _ _ _ hH.smooth)
  · exact (geometricallySolvablePointsCommHopfAlgProperty
      (AlgebraicClosure k)).prop_of_iso qIso₀.symm hsolvable

/-- A semisimple group with solvable geometric fibre has trivial geometric fibre: its coordinate
Hopf algebra is bialgebra-equivalent to the algebraic closure of the ground field via the
counit. -/
noncomputable def geometricFiberCounitBialgEquiv
    (hH : semisimpleCommHopfAlgProperty k H)
    (hsolvable : geometricallySolvablePointsCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H).obj) :
    FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H
        ≃ₐc[AlgebraicClosure k] AlgebraicClosure k :=
  HopfIdeal.counitBialgEquivOfAugmentationEqBot
    (hH.bot_eq_augmentation hsolvable).symm

/-- The equivalence from the geometric fibre to the algebraic closure is its counit. -/
@[simp]
theorem geometricFiberCounitBialgEquiv_apply
    (hH : semisimpleCommHopfAlgProperty k H)
    (hsolvable : geometricallySolvablePointsCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H).obj)
    (x : FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :
    hH.geometricFiberCounitBialgEquiv hsolvable x =
      Bialgebra.counitBialgHom (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) x := by
  rw [geometricFiberCounitBialgEquiv]
  exact HopfIdeal.counitBialgEquivOfAugmentationEqBot_apply _ _

/-- The inverse equivalence from the algebraic closure is the geometric fibre's structure map. -/
@[simp]
theorem geometricFiberCounitBialgEquiv_symm_apply
    (hH : semisimpleCommHopfAlgProperty k H)
    (hsolvable : geometricallySolvablePointsCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H).obj)
    (r : AlgebraicClosure k) :
    (hH.geometricFiberCounitBialgEquiv hsolvable).symm r =
      algebraMap (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) r := by
  rw [geometricFiberCounitBialgEquiv]
  exact HopfIdeal.counitBialgEquivOfAugmentationEqBot_symm_apply _ _

end semisimpleCommHopfAlgProperty

end

end TauCeti
