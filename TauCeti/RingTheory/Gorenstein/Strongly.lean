/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic

/-!
# Strongly Gorenstein projective, injective and flat modules

Bennis–Mahdou, *Strongly Gorenstein projective, injective and flat modules*,
J. Pure Appl. Algebra **210** (2007), 437–445. DOI `10.1016/j.jpaa.2006.10.010`.
Formalization of Def. 1.1 (characterizations `⋯ → P -f→ P -f→ P → ⋯`).

A module `M` is **strongly Gorenstein projective** if there is a strongly
*complete* projective resolution `⋯ → P -f→ P -f→ P → ⋯`: `P` projective,
the complex exact (`ker f = range f`, since the complex is `f`-periodic a
single exactness condition at `P` suffices), **and** `Hom(-,Q)` leaves the
complex exact for every projective `Q` — this second condition is what makes
the resolution *complete* rather than merely exact, and it is not implied by
the first (an ordinary periodic exact complex of projectives need not stay
exact after `Hom(-,Q)`). Then `M ≃ Im(f)`. The injective and flat cases
(Def. 1.1(2), 1.1(3)) are dual: `Hom(E,-)` resp. `I ⊗ -` must leave the
complex exact, for every injective `E` resp. `I`.

Thm 1.4's `Ext¹` reformulation and Prop. 2.9's `0 → M → P → M → 0`
short-exact-sequence repackaging are not yet formalized here (both need
`Ext¹` machinery this branch of mathlib does not yet expose in the form this
file requires); they are left for a follow-up PR once `Prerequisites.lean`
lands the needed vanishing statements as real hypotheses rather than `Prop`
placeholders.
-/

namespace TauCeti.RingTheory.Gorenstein

public section

universe u

variable (R : Type u) [Ring R]

/-- Bennis–Mahdou 2007, Def. 1.1(1): a strongly complete projective resolution
`⋯ → P -f→ P -f→ P → ⋯`: `P` projective, `f ∘ f = 0`, and the complex is exact
at `P` (`ker f = range f`; periodicity makes this the only exactness condition
needed). -/
structure StronglyCompleteProjectiveResolution (R : Type u) [Ring R] where
  /-- The underlying projective module `P` in `⋯ → P → P → ⋯`. -/
  P : Type u
  /-- `P` is an additive group. -/
  [addGroup : AddCommGroup P]
  /-- `P` is an `R`-module. -/
  [moduleInst : Module R P]
  /-- `P` is projective. -/
  [projective : Module.Projective R P]
  /-- The differential `f : P →ₗ[R] P`. -/
  f : P →ₗ[R] P
  /-- The complex `⋯ → P -f→ P -f→ P → ⋯` is exact at `P` (`ker f = range f`;
  this also gives `f.comp f = 0`, via `Function.Exact.linearMap_comp_eq_zero`). -/
  hExact : Function.Exact f f
  /-- Completeness: `Hom(-,Q)` leaves `⋯ → P -f→ P -f→ P → ⋯` exact, for every
  projective `Q` — precomposing `Q`-valued homs by `f` is itself an exact pair.
  Without this the resolution is merely exact, not *complete*. -/
  homExact : ∀ (Q : Type u) [AddCommGroup Q] [Module R Q] [Module.Projective R Q],
    Function.Exact (fun g : P →ₗ[R] Q => g.comp f) (fun g : P →ₗ[R] Q => g.comp f)

/-- Def. 1.1(2) (dual): a strongly complete injective resolution
`⋯ → I -f→ I -f→ I → ⋯`: `I` injective, `f ∘ f = 0`, exact at `I`. -/
structure StronglyCompleteInjectiveResolution (R : Type u) [Ring R] where
  /-- The underlying injective module `I` in `⋯ → I → I → ⋯`. -/
  I : Type u
  /-- `I` is an additive group. -/
  [addGroup : AddCommGroup I]
  /-- `I` is an `R`-module. -/
  [moduleInst : Module R I]
  /-- `I` is injective. -/
  [injective : Module.Injective R I]
  /-- The differential `f : I →ₗ[R] I`. -/
  f : I →ₗ[R] I
  /-- The complex `⋯ → I -f→ I -f→ I → ⋯` is exact at `I` (`ker f = range f`;
  this also gives `f.comp f = 0`, via `Function.Exact.linearMap_comp_eq_zero`). -/
  hExact : Function.Exact f f
  /-- Completeness: `Hom(E,-)` leaves `⋯ → I -f→ I -f→ I → ⋯` exact, for every
  injective `E` — postcomposing `E`-sourced homs by `f` is itself an exact
  pair. Without this the resolution is merely exact, not *complete*. -/
  homExact : ∀ (E : Type u) [AddCommGroup E] [Module R E] [Module.Injective R E],
    Function.Exact (fun g : E →ₗ[R] I => f.comp g) (fun g : E →ₗ[R] I => f.comp g)

/-- Def. 1.1(3) (dual): a strongly complete flat resolution
`⋯ → F -f→ F -f→ F → ⋯`: `F` flat, `f ∘ f = 0`, exact at `F`.
`Mathlib`'s flatness theory is developed for commutative rings, so this
structure (unlike the projective/injective cases) needs `CommRing R`. -/
structure StronglyCompleteFlatResolution (R : Type u) [CommRing R] where
  /-- The underlying flat module `F` in `⋯ → F → F → ⋯`. -/
  F : Type u
  /-- `F` is an additive group. -/
  [addGroup : AddCommGroup F]
  /-- `F` is an `R`-module. -/
  [moduleInst : Module R F]
  /-- `F` is flat. -/
  [flat : Module.Flat R F]
  /-- The differential `f : F →ₗ[R] F`. -/
  f : F →ₗ[R] F
  /-- The complex `⋯ → F -f→ F -f→ F → ⋯` is exact at `F` (`ker f = range f`;
  this also gives `f.comp f = 0`, via `Function.Exact.linearMap_comp_eq_zero`). -/
  hExact : Function.Exact f f
  /-- Completeness: `I ⊗ -` leaves `⋯ → F -f→ F -f→ F → ⋯` exact, for every
  injective `I` — `id ⊗ f` on `I ⊗[R] F` is itself an exact pair. Without this
  the resolution is merely exact, not *complete*. -/
  homExact : ∀ (I : Type u) [AddCommGroup I] [Module R I] [Module.Injective R I],
    Function.Exact (TensorProduct.map (LinearMap.id (R := R) (M := I)) f)
      (TensorProduct.map (LinearMap.id (R := R) (M := I)) f)

/-- Def. 1.1(1): `M` is strongly Gorenstein projective if it is (isomorphic
to) the image of the differential of a strongly complete projective
resolution. -/
def IsStronglyGorensteinProjective (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  ∃ S : StronglyCompleteProjectiveResolution R,
    letI := S.addGroup; letI := S.moduleInst
    Nonempty (LinearMap.range S.f ≃ₗ[R] M)

/-- Def. 1.1(2): `M` is strongly Gorenstein injective, dually. -/
def IsStronglyGorensteinInjective (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  ∃ S : StronglyCompleteInjectiveResolution R,
    letI := S.addGroup; letI := S.moduleInst
    Nonempty (LinearMap.range S.f ≃ₗ[R] M)

/-- Def. 1.1(3): `M` is strongly Gorenstein flat, dually. Needs `CommRing R`
for the same reason `StronglyCompleteFlatResolution` does. -/
def IsStronglyGorensteinFlat (R : Type u) [CommRing R] (M : Type u)
    [AddCommGroup M] [Module R M] : Prop :=
  ∃ S : StronglyCompleteFlatResolution R,
    letI := S.addGroup; letI := S.moduleInst
    Nonempty (LinearMap.range S.f ≃ₗ[R] M)

end

end TauCeti.RingTheory.Gorenstein
