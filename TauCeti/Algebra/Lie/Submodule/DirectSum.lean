/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.Algebra.Lie.DirectSum

public section

/-!
# An internal direct sum of Lie submodules is an external one

A family `N : ι → LieSubmodule R L M` whose underlying submodules decompose `M`
(`DirectSum.IsInternal`) presents `M` as the external direct sum `⨁ i, N i`, which carries
Mathlib's Lie module structure on a direct sum. This file records the comparison: the sum map
`⨁ i, N i → M` is a morphism of Lie modules (`DirectSum.coeLieModuleHom`), and it is an equivalence
exactly when the decomposition is internal (`DirectSum.lieModuleEquivOfIsInternal`).

`DirectSum.IsInternal` is a statement about the underlying `Submodule`s, so it carries no
equivariance on its own; that is what is added here. With the equivalence in hand, a construction
applied to `M` can be computed summand by summand, which is how the multiplicity of an irreducible
in `M` is read off a decomposition of `M` into irreducibles in
`TauCeti/Algebra/Lie/Multiplicity.lean`.

## Main definitions

* `DirectSum.coeLieModuleHom`: the sum map `⨁ i, N i →ₗ⁅R,L⁆ M`, refining Mathlib's
  `DirectSum.coeLinearMap`.
* `DirectSum.lieModuleEquivOfIsInternal`: the resulting equivalence of Lie modules
  `⨁ i, N i ≃ₗ⁅R,L⁆ M`, for an internal decomposition.

## Main results

* `DirectSum.coeLieModuleHom_toLinearMap` and `DirectSum.coeLieModuleHom_bijective_iff`: the sum
  map refines `DirectSum.coeLinearMap`, so its bijectivity is `DirectSum.IsInternal`.
* `TauCeti.LieModule.finrank_lieModuleHom_eq_sum_of_isInternal`: the finrank of a morphism space
  is additive over an internal decomposition of its target.

## Roadmap

This is infrastructure for the decomposition toolkit of Layer 6 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, whose multiplicity target
`isotypicMultiplicity` counts the summands of a decomposition of `M` into irreducibles; the
decompositions it counts are produced by `TauCeti.exists_isInternal_isIrreducible` of
`TauCeti/Algebra/Lie/Submodule/Decomposition.lean`, in exactly the `DirectSum.IsInternal` form
consumed here.
-/

open scoped DirectSum

universe u v w w₁ w₂

namespace DirectSum

variable {R : Type u} {L : Type v} {M : Type w} {ι : Type w₁} [DecidableEq ι]
variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M] [LieRingModule L M]
variable (N : ι → LieSubmodule R L M)

/-- **The sum map of a family of Lie submodules**, `⨁ i, N i → M`, as a morphism of Lie modules.
Its underlying linear map is `DirectSum.coeLinearMap`
(`DirectSum.coeLieModuleHom_toLinearMap`), so `DirectSum.IsInternal` is exactly the statement that
it is bijective. -/
noncomputable def coeLieModuleHom : (⨁ i, N i) →ₗ⁅R,L⁆ M :=
  { coeLinearMap (fun i ↦ (N i).toSubmodule) with
    map_lie' := by
      intro x m
      simp only [LinearMap.toFun_eq_coe]
      induction m using DirectSum.induction_on with
      | zero => simp
      | of i y =>
        -- The inclusion of a summand is a morphism of Lie modules, and it is `DirectSum.of`.
        have hlie : ⁅x, of (fun i ↦ (N i : Type w)) i y⁆
            = of (fun i ↦ (N i : Type w)) i ⁅x, y⁆ := by
          simpa only [lieModuleOf_apply] using
            ((lieModuleOf R ι L (fun i ↦ (N i : Type w)) i).map_lie x y).symm
        -- `DirectSum.coeLinearMap_of` reads the type family off `A`, so it needs restating over
        -- `fun i ↦ (N i : Type w)` before it can be rewritten with here.
        have key : ∀ (j : ι) (z : N j),
            coeLinearMap (fun i ↦ (N i).toSubmodule) (of (fun i ↦ (N i : Type w)) j z) = (z : M) :=
          fun j z ↦ coeLinearMap_of (fun i ↦ (N i).toSubmodule) j z
        rw [hlie, key, key]
        simp
      | add a b ha hb => simp [ha, hb] }

/-- The underlying linear map of the sum map of a family of Lie submodules is Mathlib's
`DirectSum.coeLinearMap` of the underlying submodules. -/
@[simp]
theorem coeLieModuleHom_toLinearMap :
    (coeLieModuleHom N : (⨁ i, N i) →ₗ[R] M) = coeLinearMap fun i ↦ (N i).toSubmodule :=
  (rfl)

@[simp]
theorem coeLieModuleHom_of (i : ι) (y : N i) :
    coeLieModuleHom N (of (fun i ↦ (N i : Type w)) i y) = (y : M) :=
  coeLinearMap_of (fun i ↦ (N i).toSubmodule) i y

/-- The sum map of a family of Lie submodules is bijective exactly when the family decomposes `M`
internally: by `DirectSum.coeLieModuleHom_toLinearMap` the two statements are about the same
underlying map. -/
theorem coeLieModuleHom_bijective_iff :
    Function.Bijective (coeLieModuleHom N) ↔ IsInternal fun i ↦ (N i).toSubmodule := by
  -- The preceding lemma equates bundled linear maps, whereas `Function.Bijective` exposes their
  -- coerced functions, so transport that equality across the coercion before applying `Iff.rfl`.
  rw [show ⇑(coeLieModuleHom N) = ⇑(coeLinearMap fun i ↦ (N i).toSubmodule) from
    congrArg DFunLike.coe (coeLieModuleHom_toLinearMap N)]
  exact Iff.rfl

/-- **An internal direct sum of Lie submodules, as an external one.** A family of Lie submodules
whose underlying submodules decompose `M` presents `M` as the direct sum of the family, as Lie
modules. -/
noncomputable def lieModuleEquivOfIsInternal (h : IsInternal fun i ↦ (N i).toSubmodule) :
    (⨁ i, N i) ≃ₗ⁅R,L⁆ M :=
  TauCeti.LieModuleEquiv.ofBijective (coeLieModuleHom N)
    ((coeLieModuleHom_bijective_iff N).mpr h)

@[simp]
theorem lieModuleEquivOfIsInternal_apply (h : IsInternal fun i ↦ (N i).toSubmodule)
    (m : ⨁ i, N i) : lieModuleEquivOfIsInternal N h m = coeLieModuleHom N m :=
  TauCeti.LieModuleEquiv.ofBijective_apply _ _ _

end DirectSum

namespace TauCeti.LieModule

open Module (finrank)

section Internal

variable {K : Type u} {L : Type v} {M : Type w} {ι : Type w₁} [DecidableEq ι] [Fintype ι]
variable [Field K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M] [_root_.LieModule K L M]
variable (S : Type w₂) [AddCommGroup S] [Module K S] [LieRingModule L S]
  [_root_.LieModule K L S]

omit [_root_.LieModule K L S] in
/-- **Additivity of the morphism space over a decomposition of the target.** If the Lie submodules
`N i` decompose `M` and every component morphism space is finite-dimensional, the finrank of
`S →ₗ⁅K,L⁆ M` is the sum of the finranks of the `S →ₗ⁅K,L⁆ N i`. -/
theorem finrank_lieModuleHom_eq_sum_of_isInternal (N : ι → LieSubmodule K L M)
    (h : DirectSum.IsInternal fun i ↦ (N i).toSubmodule)
    (hfin : ∀ i, FiniteDimensional K (S →ₗ⁅K,L⁆ N i)) :
    finrank K (S →ₗ⁅K,L⁆ M) = ∑ i, finrank K (S →ₗ⁅K,L⁆ N i) := by
  let _ : ∀ i, FiniteDimensional K (S →ₗ⁅K,L⁆ N i) := hfin
  rw [← (LieModuleEquiv.congrRight (M := S)
      (DirectSum.lieModuleEquivOfIsInternal N h)).finrank_eq,
    (lieModuleHomDirectSumEquiv K L S fun i ↦ (N i : Type w)).finrank_eq,
    Module.finrank_pi_fintype]

end Internal

end TauCeti.LieModule
