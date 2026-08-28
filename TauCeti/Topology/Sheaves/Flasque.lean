/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.Basic
public import TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Terminal
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Flasque sheaves are acyclic

A sheaf of abelian groups on a topological space is flasque when all of its restriction maps are
surjective. This file proves that a flasque sheaf has no higher cohomology.

## Main declarations

* `TauCeti.Topology.isFlasque_of_injective`: an injective object in the category of abelian
  sheaves is flasque;
* `TauCeti.Topology.subsingleton_H'_succ_of_isFlasque`: a flasque sheaf has vanishing
  cohomology in every positive degree over every open subset;
* `TauCeti.Topology.subsingleton_H_succ_of_isFlasque`: the same statement for the cohomology
  of the whole space;
* `TauCeti.Topology.isFlasque_skyscraperSheaf`: skyscraper sheaves are flasque, and hence acyclic.

The proof is the classical dimension shift. Embedding a flasque sheaf `F` in an injective sheaf
`I` gives a short exact sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0`, and the covariant long exact sequence of
`Ext` presents `Hⁿ⁺¹(U, F)` as a quotient of `Hⁿ(U, Q)`. In degree zero, the sections of `Q` over
`U` lift to sections of `I` because `F` is flasque, so the quotient vanishes; in higher degrees
`Q` is again flasque, because `I` is, and induction applies. That `I` is flasque is the point at
which `TauCeti/CategoryTheory/Sites/SheafCohomology/FreeYoneda.lean` enters: an inclusion of open
subsets induces a monomorphism of the free abelian sheaves they generate, and `Hom(-, I)` turns it
into the restriction map of `I`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer B, "coherent sheaves and
cohomology `Hⁱ(X, ℱ)`: acyclicity of affines, …, vanishing above dimension": it is the first
acyclicity theorem of the lane, and the acyclic skyscraper sheaves are the coefficients in which
the Riemann-Roch induction over the points of a divisor reads the additivity of
`TauCeti/AlgebraicGeometry/Cohomology/EulerCharacteristic.lean`.

No formalization is vendored: flasqueness, the surjectivity of sections out of a flasque
subsheaf, the stability of flasqueness under quotients and the flasqueness of skyscraper sheaves
are Mathlib's `Mathlib/Topology/Sheaves/Flasque.lean`, and the long exact sequence is Mathlib's
`CategoryTheory.Abelian.Ext.covariant_sequence_exact₁`.

## References

* R. Hartshorne, *Algebraic Geometry*, III.2.4–2.5.
* The Stacks Project, tag 09SY, Lemma 20.12.3, *Flasque sheaves*.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace
open TauCeti.CategoryTheory (freeYonedaSheafFunctor freeYonedaSheafSectionsEquiv sheafH'_eq
  freeYonedaSheafSectionsEquiv_naturality_left freeYonedaSheafSectionsEquiv_naturality_right)

universe u

namespace TauCeti

namespace Topology

variable {X : TopCat.{u}}

noncomputable section

/-- An injective object in the category of sheaves of abelian groups is flasque. -/
instance isFlasque_of_injective
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective F] :
    TopCat.Presheaf.IsFlasque F.obj where
  -- Given `s : I(V)` and `V ≤ U`, represent `s` by `ℤ_V ⟶ I`, extend it along the
  -- monomorphism `ℤ_V ⟶ ℤ_U` using injectivity, and translate the extension back to a section.
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    refine ⟨freeYonedaSheafSectionsEquiv _ U.unop F
      (Injective.factorThru ((freeYonedaSheafSectionsEquiv _ V.unop F).symm s)
        ((freeYonedaSheafFunctor (Opens.grothendieckTopology X)).map i.unop)), ?_⟩
    have h := freeYonedaSheafSectionsEquiv_naturality_left
      (Opens.grothendieckTopology X) i.unop F
      (Injective.factorThru ((freeYonedaSheafSectionsEquiv _ V.unop F).symm s)
        ((freeYonedaSheafFunctor (Opens.grothendieckTopology X)).map i.unop))
    rw [Injective.comp_factorThru, AddEquiv.apply_symm_apply] at h
    exact h.symm

private instance isFlasque_injectiveCokernelSequence_X₂
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    TopCat.Presheaf.IsFlasque (injectiveCokernelSequence F).X₂.obj :=
  isFlasque_of_injective _

/-- The dimension-shifting induction: a flasque sheaf has no cohomology in positive degrees over
any open subset. -/
private lemma subsingleton_H'_succ_of_isFlasque_aux (n : ℕ) :
    ∀ (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}),
      TopCat.Presheaf.IsFlasque F.obj → ∀ U : Opens X,
      Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F (n + 1) U) := by
  induction n with
  | zero =>
    intro F hF U
    rw [sheafH'_eq]
    apply subsingleton_ext_succ_of_injectiveCokernelSequence
    intro x₃
    let S := injectiveCokernelSequence F
    have hS₁ : TopCat.Presheaf.IsFlasque S.X₁.obj := by dsimp [S]; exact hF
    let _ : TopCat.Presheaf.IsFlasque S.X₁.obj := hS₁
    have hS := injectiveCokernelSequence_shortExact F
    have hepi : Epi (S.g.hom.app (op U)) :=
      TopCat.Sheaf.IsFlasque.epi_of_shortExact hS
    rw [AddCommGrpCat.epi_iff_surjective] at hepi
    obtain ⟨t, ht⟩ := hepi
      (freeYonedaSheafSectionsEquiv _ U S.X₃ (Abelian.Ext.addEquiv₀ x₃))
    have hx₃ : x₃ =
        (Abelian.Ext.mk₀ ((freeYonedaSheafSectionsEquiv _ U S.X₂).symm t)).comp
        (Abelian.Ext.mk₀ S.g) (add_zero 0) := by
      rw [Abelian.Ext.mk₀_comp_mk₀]
      refine (Abelian.Ext.mk₀_addEquiv₀_apply x₃).symm.trans (congrArg Abelian.Ext.mk₀ ?_)
      refine (freeYonedaSheafSectionsEquiv _ U S.X₃).injective ?_
      rw [freeYonedaSheafSectionsEquiv_naturality_right, AddEquiv.apply_symm_apply, ht]
    rw [hx₃, Abelian.Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass,
      Abelian.Ext.comp_zero]
  | succ n ih =>
    intro F hF U
    rw [sheafH'_eq]
    apply subsingleton_ext_succ_of_injectiveCokernelSequence
    intro x₃
    let S := injectiveCokernelSequence F
    have hS₁ : TopCat.Presheaf.IsFlasque S.X₁.obj := by dsimp [S]; exact hF
    let _ : TopCat.Presheaf.IsFlasque S.X₁.obj := hS₁
    have hS := injectiveCokernelSequence_shortExact F
    have hS₃ : TopCat.Presheaf.IsFlasque S.X₃.obj :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS
    have hH : Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} S.X₃ (n + 1) U) :=
      ih S.X₃ hS₃ U
    have hExt : Subsingleton
        (Abelian.Ext.{u}
          ((freeYonedaSheafFunctor (Opens.grothendieckTopology X)).obj U) S.X₃ (n + 1)) :=
      by simpa only [sheafH'_eq] using hH
    rw [@Subsingleton.elim _ hExt x₃ 0, Abelian.Ext.zero_comp]

/-- A flasque sheaf of abelian groups has vanishing cohomology in every positive degree over
every open subset. -/
instance subsingleton_H'_succ_of_isFlasque
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Presheaf.IsFlasque F.obj] (n : ℕ) (U : Opens X) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F (n + 1) U) :=
  subsingleton_H'_succ_of_isFlasque_aux n F inferInstance U

/-- A flasque sheaf of abelian groups has vanishing cohomology in every positive degree. -/
instance subsingleton_H_succ_of_isFlasque
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Presheaf.IsFlasque F.obj] (n : ℕ) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H.{u} F (n + 1)) := by
  have := subsingleton_H'_succ_of_isFlasque F n (⊤ : Opens X)
  exact Function.Injective.subsingleton
    (f := ConcreteCategory.hom
      (TauCeti.CategoryTheory.Sheaf.cohomologyPresheafObjIsoH (n + 1) isTerminalTop F).inv)
    ((ConcreteCategory.bijective_of_isIso _).injective)

/-- A skyscraper sheaf of abelian groups is flasque. -/
instance isFlasque_skyscraperSheaf (p₀ : X) (A : AddCommGrpCat.{u})
    [(U : Opens X) → Decidable (p₀ ∈ U)] :
    TopCat.Presheaf.IsFlasque (skyscraperSheaf p₀ A).obj :=
  isFlasque_skyscraperSheaf_of_hasZeroObject p₀ A

end

end Topology

end TauCeti
