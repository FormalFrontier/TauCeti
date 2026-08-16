/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation

/-!
# Reductive affine groups

A finite-type affine group over a field is reductive when it is smooth and geometrically
connected and, after extension to an algebraic closure, it has no nontrivial connected normal
smooth unipotent closed subgroup. In coordinate-Hopf-algebra terms, a closed subgroup of the
geometric fibre is a Hopf-ideal quotient. The subgroup is trivial exactly when its defining Hopf
ideal is the augmentation ideal.

This formulation is equivalent to triviality of the geometric unipotent radical once that radical
has been constructed, but it does not make the definition wait for that construction. It also
avoids asserting descent of the geometric unipotent radical over an imperfect field.

The first structural consequence verifies that the predicate has its intended force: if the
geometric fibre of a reductive group is itself unipotent, its coordinate Hopf algebra is the base
field. The resulting bialgebra equivalence is the precise affine-group statement that the
geometric fibre is the trivial group.

## Main declarations

* `TauCeti.reductiveCommHopfAlgProperty`: reductivity for finite-type commutative Hopf algebras
  over a field.
* `TauCeti.reductiveCommHopfAlgProperty.eq_augmentation`: every connected normal smooth
  unipotent closed subgroup of a reductive group's geometric fibre is trivial.
* `TauCeti.reductiveCommHopfAlgProperty.geometricFiberBialgEquivBase`: a reductive group with
  geometrically unipotent geometric fibre has trivial geometric fibre.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definition 17.1.
* T. A. Springer, *Linear Algebraic Groups*, Chapter 8.
* B. Conrad, *Reductive Group Schemes*, Section 3.

This is the definition target in Layer 6, "Reductive and semisimple groups", of the
ReductiveGroups roadmap. The geometric formulation is the roadmap's prescribed alternative while
the descended unipotent radical is unavailable.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

/-- The object property selecting reductive finite-type commutative Hopf algebras over a field.

The first two conjuncts express smoothness and geometric connectedness of the ambient group. The
last says that every connected normal smooth unipotent closed subgroup of the geometric fibre is
the identity subgroup. A Hopf ideal `I` cuts out that subgroup contravariantly, so identity means
`I` is the augmentation ideal, not the zero ideal. -/
def reductiveCommHopfAlgProperty (k : Type u) [Field k] :
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
            smoothUnipotentCommHopfAlgProperty (AlgebraicClosure k)
              (FiniteTypeCommHopfAlgCat.quotient
                (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I) →
            I = HopfIdeal.augmentation (AlgebraicClosure k)
              (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)

/-- Reductivity means smoothness, geometric connectedness, and absence of nontrivial connected
normal smooth unipotent closed subgroups after extension to an algebraic closure. -/
theorem reductiveCommHopfAlgProperty_iff (k : Type u) [Field k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    reductiveCommHopfAlgProperty k H ↔
      Algebra.Smooth k H ∧
        geometricallyConnectedCommHopfAlgProperty k H.obj ∧
          ∀ I : HopfIdeal (AlgebraicClosure k)
              (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H),
            I.IsNormal →
              geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)
                (FiniteTypeCommHopfAlgCat.quotient
                  (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I).obj →
              smoothUnipotentCommHopfAlgProperty (AlgebraicClosure k)
                (FiniteTypeCommHopfAlgCat.quotient
                  (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I) →
              I = HopfIdeal.augmentation (AlgebraicClosure k)
                (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :=
  Iff.rfl

namespace reductiveCommHopfAlgProperty

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- A reductive finite-type commutative Hopf algebra is smooth over its ground field. -/
theorem smooth (hH : reductiveCommHopfAlgProperty k H) : Algebra.Smooth k H :=
  hH.1

/-- A reductive finite-type commutative Hopf algebra is geometrically connected. -/
theorem geometricallyConnected (hH : reductiveCommHopfAlgProperty k H) :
    geometricallyConnectedCommHopfAlgProperty k H.obj :=
  hH.2.1

/-- Every connected normal smooth unipotent closed subgroup of the geometric fibre of a
reductive group is the identity subgroup. -/
theorem eq_augmentation (hH : reductiveCommHopfAlgProperty k H)
    (I : HopfIdeal (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H))
    (hI : I.IsNormal)
    (hconnected : geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I).obj)
    (hunipotent : smoothUnipotentCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I)) :
    I = HopfIdeal.augmentation (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :=
  hH.2.2 I hI hconnected hunipotent

/-- If the geometric fibre of a reductive group has only unipotent geometric points, its zero
Hopf ideal is the augmentation ideal. Equivalently, the whole geometric fibre is the identity
subgroup. -/
theorem bot_eq_augmentation (hH : reductiveCommHopfAlgProperty k H)
    (hunipotent : geometricallyUnipotentPointsCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H).obj) :
    (⊥ : HopfIdeal (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)) =
        HopfIdeal.augmentation (AlgebraicClosure k)
          (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) := by
  let Hbar := FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H
  apply hH.eq_augmentation (I := (⊥ : HopfIdeal (AlgebraicClosure k) Hbar))
  · exact HopfIdeal.isNormal_bot
  · exact (geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso
      ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k))
        (CommHopfAlgCat.{u} (AlgebraicClosure k))).mapIso
          (FiniteTypeCommHopfAlgCat.quotientBotIso Hbar)).symm
      (geometricallyConnectedCommHopfAlgProperty.baseChange k (AlgebraicClosure k) H.obj
        hH.geometricallyConnected)
  · apply (smoothUnipotentCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso
      (FiniteTypeCommHopfAlgCat.quotientBotIso Hbar).symm
    rw [smoothUnipotentCommHopfAlgProperty_iff]
    refine ⟨@Algebra.Smooth.baseChange k _ H (AlgebraicClosure k) _ _ _ _ hH.smooth, ?_⟩
    exact (geometricallyUnipotentPointsCommHopfAlgProperty_iff
      (AlgebraicClosure k) Hbar.obj).mp hunipotent

/-- A reductive group whose geometric fibre has only unipotent geometric points has trivial
geometric fibre: its coordinate Hopf algebra is bialgebra-equivalent to the algebraic closure of
the ground field via the counit. -/
noncomputable def geometricFiberBialgEquivBase
    (hH : reductiveCommHopfAlgProperty k H)
    (hunipotent : geometricallyUnipotentPointsCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H).obj) :
    FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H ≃ₐc[AlgebraicClosure k]
      AlgebraicClosure k := by
  let Hbar := FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H
  have hbijective : Function.Bijective
      (Bialgebra.counitBialgHom (AlgebraicClosure k) Hbar) := by
    constructor
    · apply (HopfIdeal.ker_eq_bot_iff
        (Bialgebra.counitBialgHom (AlgebraicClosure k) Hbar)
        Bialgebra.counit_surjective).mp
      rw [← HopfIdeal.augmentation_def]
      exact (hH.bot_eq_augmentation hunipotent).symm
    · exact Bialgebra.counit_surjective
  exact BialgEquiv.ofBijective
    (Bialgebra.counitBialgHom (AlgebraicClosure k) Hbar) hbijective

end reductiveCommHopfAlgProperty

end

end TauCeti
