/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Basic

/-!
# Finite presentation of invertible sheaves

An invertible sheaf is locally free on a one-element basis, so it is locally finitely presented.
This file makes that implication available to the scheme-level sheaf API.

The general finite-presentation theorem for locally free data is in
`TauCeti/Algebra/Category/ModuleCat/Sheaf/FinitePresentation.lean`. The only additional step for
an invertible sheaf is finiteness of the local bases, supplied by their `Subsingleton` instances.

The main result is the instance
`TauCeti.SheafOfModules.IsInvertible.isFinitePresentation`. It applies over an arbitrary site;
the scheme-level finitely-presented-sheaf packaging is in
`TauCeti/AlgebraicGeometry/FinitelyPresentedSheaf/Basic.lean`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, from Layer A's invertible sheaves to
Layer B's coherent sheaves. No formalization is vendored.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R}

/-- An invertible sheaf of modules is finitely presented.

The rank-one local bases give finite generating families, and the locally free presentations
have no relations. -/
instance IsInvertible.isFinitePresentation [hM : IsInvertible M] : M.IsFinitePresentation := by
  obtain ⟨q, hq⟩ := hM.exists_isInvertible
  apply LocalGeneratorsData.IsLocallyFreeData.isFinitePresentation hq.isLocallyFreeData
  exact ⟨fun i ↦ by
    let : Subsingleton (q.generators i).I := hq.basisSubsingleton i
    exact ⟨Finite.of_subsingleton⟩⟩

end SheafOfModules

end

end TauCeti
