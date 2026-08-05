/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Basic

/-!
# Finite presentation of invertible sheaves

An invertible sheaf is locally free on a one-element basis, so it is locally finitely presented.
This file makes that implication available to the scheme-level sheaf API.

Mathlib constructs a finite presentation from locally free data by using the chosen basis as
generators and no relations. The only missing step for an invertible sheaf is finiteness of the
local bases. Their `Subsingleton` instances supply this directly, while the empty relation types
are already finite.

The main result is the instance
`TauCeti.SheafOfModules.IsInvertible.isFinitePresentation`. It applies over an arbitrary site;
the scheme-level finitely-presented-sheaf packaging is in
`TauCeti/AlgebraicGeometry/FinitelyPresentedSheaf/Basic.lean`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, from Layer A's invertible sheaves to
Layer B's coherent sheaves. No formalization is vendored. The proof reuses Mathlib's
`SheafOfModules.LocalGeneratorsData.quasiCoherentData`, whose local presentations have no
relations.
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

/-- Locally free data with finite local bases exhibits a finitely presented sheaf.

Mathlib's presentation associated to locally free data uses the local bases as generators and
has no relations. -/
theorem LocalGeneratorsData.IsLocallyFreeData.isFinitePresentation
    {q : _root_.SheafOfModules.LocalGeneratorsData.{u₁} M} (hfree : q.IsLocallyFreeData)
    (hfinite : q.IsFiniteType) :
    M.IsFinitePresentation := by
  let : q.IsLocallyFreeData := hfree
  refine ⟨q.quasiCoherentData, ⟨fun i ↦ ?_⟩⟩
  refine
    { isFiniteType_generators := ?_
      isFiniteType_relations := ?_ }
  · -- `quasiCoherentData` retains `q.generators i`, but the goal displays it through the
    -- generated presentation projection, for which there is no rewriting lemma.
    change (q.generators i).IsFiniteType
    exact hfinite.isFiniteType i
  · refine ⟨?_⟩
    -- The locally free presentation uses `ULift Empty` as its relation-index type.
    change Finite (ULift Empty)
    infer_instance

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
