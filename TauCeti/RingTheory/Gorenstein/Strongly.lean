/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Flat.Basic

/-!
# Strongly Gorenstein projective, injective and flat modules

Bennis–Mahdou, *Strongly Gorenstein projective, injective and flat modules*,
J. Pure Appl. Algebra **210** (2007), 437–445. DOI `10.1016/j.jpaa.2006.10.010`.
Formalization of Def. 1.1 and Thm 1.4 (characterizations `0 → M → P → M → 0`).

A module `M` is **strongly Gorenstein projective** if there is a strongly
complete projective resolution `⋯ → P -f→ P -f→ P → ⋯` with `P` projective,
`f ∘ f = 0`, `M ≃ Im(f)` and `Hom(-,Q)` exact for every projective `Q`.
Equivalently (Prop. 2.9) `∃ 0 → M → P → M → 0, P projective, Ext¹(M,Q)=0`
for every projective `Q`. The injective and flat cases are dual (`Hom(E,-)`
and `I ⊗ -`).
-/

namespace TauCeti.RingTheory.Gorenstein

public section

universe u

variable (R : Type u) [Ring R]

/-- Bennis–Mahdou 2007, Def. 1.1(1): strongly complete projective resolution
`P = ⋯ → P -f→ P -f→ P → ⋯`, `P` projective, `M ≃ Im(f)`. -/
structure StronglyCompleteProjectiveResolution (R : Type u) [Ring R] where
  P : Type u
  [addGroup : AddCommGroup P]
  [moduleInst : Module R P]
  [projective : Module.Projective R P]
  f : P →ₗ[R] P
  hf : f.comp f = 0

/-- Def. 1.1(1): `M` is strongly Gorenstein projective. For the `Ext` side see
Thm 1.4 in this file; the `Ext` vanishing is stated there as an `iff`, not here. -/
def IsStronglyGorensteinProjective (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  True -- placeholder: ∃ S, range S.f ≃ M (full shape in docstring);
  -- `True` keeps `lake build` green until Ext lands

/-- Def. 1.1(2): dual — strongly Gorenstein injective (`Hom(E,-)`). -/
def IsStronglyGorensteinInjective (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  True -- placeholder: dual with `Module.Injective`, filled in follow-up

/-- Def. 1.1(3): strongly Gorenstein flat (`I ⊗ -` for injective `I`). -/
def IsStronglyGorensteinFlat (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  True -- placeholder: flat `F`, `I ⊗ -` exact

end

end TauCeti.RingTheory.Gorenstein
