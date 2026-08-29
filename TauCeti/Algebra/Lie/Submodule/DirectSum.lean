/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.DirectSum
public import TauCeti.Algebra.Lie.Basic

public section

/-!
# An internal direct sum of Lie submodules is an external one

A family `N : ι → LieSubmodule R L M` whose underlying submodules decompose `M`
(`DirectSum.IsInternal`) presents `M` as the external direct sum `⨁ i, N i`, which carries
Mathlib's Lie module structure on a direct sum. This file records the comparison: the sum map
`⨁ i, N i → M` is a morphism of Lie modules (`TauCeti.LieSubmodule.directSumCoe`), and it is an
equivalence exactly when the decomposition is internal (`TauCeti.LieSubmodule.directSumEquiv`).

`DirectSum.IsInternal` is a statement about the underlying `Submodule`s, so it carries no
equivariance on its own; that is what is added here. With the equivalence in hand, a construction
applied to `M` can be computed summand by summand, which is how the multiplicity of an irreducible
in `M` is read off a decomposition of `M` into irreducibles in
`TauCeti/Algebra/Lie/Multiplicity.lean`.

Mathlib's inclusion and projection for an external direct sum of Lie modules,
`DirectSum.lieModuleOf` and `DirectSum.lieModuleComponent`, come with no application lemmas; the
two that say they are the underlying `DirectSum.of` and evaluation are recorded here, so that no
consumer has to unfold either definition.

## Main definitions

* `TauCeti.LieSubmodule.directSumCoe`: the sum map `⨁ i, N i →ₗ⁅R,L⁆ M`.
* `TauCeti.LieSubmodule.directSumEquiv`: the resulting equivalence of Lie modules
  `⨁ i, N i ≃ₗ⁅R,L⁆ M`, for an internal decomposition.

## Main results

* `DirectSum.lieModuleOf_apply` and `DirectSum.lieModuleComponent_apply`: the inclusion and the
  projection of an external direct sum of Lie modules are `DirectSum.of` and evaluation.

## Roadmap

This is infrastructure for the decomposition toolkit of Layer 6 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, whose multiplicity target
`isotypicMultiplicity` counts the summands of a decomposition of `M` into irreducibles; the
decompositions it counts are produced by `TauCeti.exists_isInternal_isIrreducible` of
`TauCeti/Algebra/Lie/Submodule/Decomposition.lean`, in exactly the `DirectSum.IsInternal` form
consumed here.
-/

open scoped DirectSum

universe u v w w₁

namespace DirectSum

section LieModules

variable (R : Type u) (ι : Type w₁) (L : Type v) (P : ι → Type w)
variable [CommRing R] [LieRing L]
variable [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
variable [∀ i, LieRingModule L (P i)]

/-- The inclusion of a summand into an external direct sum of Lie modules is `DirectSum.of`. -/
@[simp]
theorem lieModuleOf_apply [DecidableEq ι] (i : ι) (x : P i) :
    lieModuleOf R ι L P i x = of P i x :=
  (rfl)

/-- The projection of an external direct sum of Lie modules onto a summand is evaluation. -/
@[simp]
theorem lieModuleComponent_apply (i : ι) (x : ⨁ i, P i) :
    lieModuleComponent R ι L P i x = x i :=
  (rfl)

end LieModules

end DirectSum

namespace TauCeti.LieSubmodule

variable {R : Type u} {L : Type v} {M : Type w} {ι : Type w₁} [DecidableEq ι]
variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M] [LieRingModule L M]
variable (N : ι → LieSubmodule R L M)

-- The `LieModuleHom` bundling below needs these two computation rules while `directSumCoe` is
-- still being elaborated, so neither can be stated as a lemma about `directSumCoe` itself.
private theorem coeLinearMap_of (i : ι) (y : N i) :
    DirectSum.coeLinearMap (fun i ↦ (N i).toSubmodule)
        (DirectSum.of (fun i ↦ (N i : Type w)) i y) = (y : M) :=
  DirectSum.coeLinearMap_of (fun i ↦ (N i).toSubmodule) i y

private theorem lie_of (x : L) (i : ι) (y : N i) :
    ⁅x, DirectSum.of (fun i ↦ (N i : Type w)) i y⁆
      = DirectSum.of (fun i ↦ (N i : Type w)) i ⁅x, y⁆ := by
  refine DFinsupp.ext fun j ↦ ?_
  rw [DirectSum.lie_module_bracket_apply]
  by_cases h : j = i
  · subst h; rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
  · rw [DirectSum.of_eq_of_ne _ _ _ h, DirectSum.of_eq_of_ne _ _ _ h, lie_zero]

/-- **The sum map of a family of Lie submodules**, `⨁ i, N i → M`, as a morphism of Lie modules.
Its underlying linear map is `DirectSum.coeLinearMap`, so `DirectSum.IsInternal` is exactly the
statement that it is bijective. -/
noncomputable def directSumCoe : (⨁ i, N i) →ₗ⁅R,L⁆ M :=
  { DirectSum.coeLinearMap (fun i ↦ (N i).toSubmodule) with
    map_lie' := by
      intro x m
      simp only [LinearMap.toFun_eq_coe]
      induction m using DirectSum.induction_on with
      | zero => simp
      | of i y => rw [lie_of N x i y, coeLinearMap_of, coeLinearMap_of]; simp
      | add a b ha hb => simp [ha, hb] }

@[simp]
theorem directSumCoe_of (i : ι) (y : N i) :
    directSumCoe N (DirectSum.of (fun i ↦ (N i : Type w)) i y) = (y : M) :=
  coeLinearMap_of N i y

/-- The sum map of a family of Lie submodules is bijective exactly when the family decomposes `M`
internally: the two statements are about the same underlying linear map. -/
theorem directSumCoe_bijective_iff :
    Function.Bijective (directSumCoe N) ↔ DirectSum.IsInternal fun i ↦ (N i).toSubmodule :=
  Iff.rfl

/-- **An internal direct sum of Lie submodules, as an external one.** A family of Lie submodules
whose underlying submodules decompose `M` presents `M` as the direct sum of the family, as Lie
modules. -/
noncomputable def directSumEquiv (h : DirectSum.IsInternal fun i ↦ (N i).toSubmodule) :
    (⨁ i, N i) ≃ₗ⁅R,L⁆ M :=
  LieModuleEquiv.ofBijective (directSumCoe N) ((directSumCoe_bijective_iff N).mpr h)

@[simp]
theorem directSumEquiv_apply (h : DirectSum.IsInternal fun i ↦ (N i).toSubmodule)
    (m : ⨁ i, N i) : directSumEquiv N h m = directSumCoe N m :=
  LieModuleEquiv.ofBijective_apply _ _ _

end TauCeti.LieSubmodule
