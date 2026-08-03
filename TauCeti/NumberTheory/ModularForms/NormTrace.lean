/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.ModularForms.NormTrace

/-!
# Analytic properties of the translate package

For a modular form `f`, each translate in the package `SlashInvariantForm.quotientFunc` is
holomorphic, and — when the cusp `∞` is a cusp of `ℋ` of finite relative index — bounded at
infinity.

## Main declarations

* `TauCeti.SlashInvariantForm.mdifferentiable_quotientFunc`.
* `TauCeti.SlashInvariantForm.isBoundedAtImInfty_quotientFunc`.

## References

* [Mathlib PR #39083](https://github.com/leanprover-community/mathlib4/pull/39083)
  (Chris Birkbeck) — the upstream draft this file ports onto the current Mathlib pin.
-/

public noncomputable section

open UpperHalfPlane SlashInvariantForm

open scoped ModularForm Topology Filter Manifold

variable {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} (f : F) [FunLike F ℍ ℂ] {k : ℤ}
  [ModularFormClass F 𝒢 k]

local notation "𝒬" => ℋ ⧸ (𝒢.subgroupOf ℋ)

namespace TauCeti.SlashInvariantForm

/-- Each translate in the package `quotientFunc` of a modular form is holomorphic. -/
lemma mdifferentiable_quotientFunc (q : 𝒬) : MDiff (quotientFunc f q) :=
  Quotient.inductionOn q fun r ↦ (ModularForm.translate f r.val⁻¹).holo'

/-- Each translate in the package `quotientFunc` of a modular form is bounded at infinity,
when `∞` is a cusp of `ℋ` and the relative index is finite. -/
lemma isBoundedAtImInfty_quotientFunc [𝒢.IsFiniteRelIndex ℋ] [Fact (IsCusp OnePoint.infty ℋ)]
    (q : 𝒬) : IsBoundedAtImInfty (quotientFunc f q) :=
  Quotient.inductionOn q fun ⟨_, hr⟩ ↦ OnePoint.isBoundedAt_infty_iff.mp <|
    (ModularForm.translate f _).bdd_at_cusps'
      ((Fact.out : IsCusp _ _).of_isFiniteRelIndex_conj hr)

end TauCeti.SlashInvariantForm

end
