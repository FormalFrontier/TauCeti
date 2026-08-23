/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid

/-!
# Smooth monoid morphisms

Identity and composition for bundled smooth monoid morphisms.
-/

public section

open Function Manifold
open scoped ContDiff Manifold

namespace ContMDiffMonoidMorphism

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Monoid G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Monoid G']

/-- The identity smooth monoid morphism. -/
def id : ContMDiffMonoidMorphism I I n G G where
  toMonoidHom := MonoidHom.id G
  contMDiff_toFun := contMDiff_id

@[simp]
theorem coe_id : ⇑(id (n := n) (I := I) (G := G)) = _root_.id := (rfl)

/-- Composition of smooth monoid morphisms. -/
def comp
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
    {G'' : Type*} [TopologicalSpace G''] [ChartedSpace H'' G''] [Monoid G'']
    (ψ : ContMDiffMonoidMorphism I' I'' n G' G'')
    (φ : ContMDiffMonoidMorphism I I' n G G') :
    ContMDiffMonoidMorphism I I'' n G G'' where
  toMonoidHom := ψ.toMonoidHom.comp φ.toMonoidHom
  contMDiff_toFun := ψ.contMDiff_toFun.comp φ.contMDiff_toFun

@[simp]
theorem coe_comp
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
    {G'' : Type*} [TopologicalSpace G''] [ChartedSpace H'' G''] [Monoid G'']
    (ψ : ContMDiffMonoidMorphism I' I'' n G' G'')
    (φ : ContMDiffMonoidMorphism I I' n G G') :
    ⇑(ψ.comp φ) = ⇑ψ ∘ ⇑φ := (rfl)

end ContMDiffMonoidMorphism
