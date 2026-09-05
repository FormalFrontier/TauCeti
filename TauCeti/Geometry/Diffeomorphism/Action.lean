/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Topology.Algebra.ConstMulAction

/-!
# The tautological action of the diffeomorphism group

The self-diffeomorphism group `M ≃ₘ^n⟮I, I⟯ M` acts on the underlying manifold by evaluation:
`φ • x = φ x`. This file records that action, its faithfulness, and continuity in the point.

The action formalization mirrors Mathlib's `Homeomorph.applyMulAction`
(`Mathlib.Topology.Algebra.ConstMulAction`, added in Kim Morrison's mathlib4#40135), which
generalizes `Equiv.Perm.applyMulAction`.

The evaluation action and the forgetful homomorphism `Diff(M) → Homeomorph(M)` are the basic
API relating the abstract group `Diff(M)` to the space it acts on: faithfulness identifies a
diffeomorphism with the permutation of `M` it induces, and continuity in the point records that
each diffeomorphism acts by a homeomorphism.

## Main definitions

* `Diffeomorph.applyMulAction`: the `MulAction (M ≃ₘ^n⟮I, I⟯ M) M` with
  `φ • x = φ x`.
* `Diffeomorph.applyFaithfulSMul`: the action is faithful.
* `Diffeomorph.applyContinuousConstSMul`: each diffeomorphism acts continuously.
* `Diffeomorph.applySubgroupContinuousConstSMul`: subgroups inherit continuity in the
  point.
-/

public section

open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- The tautological action of the self-diffeomorphism group on the manifold by evaluation. -/
instance applyMulAction : MulAction (M ≃ₘ^n⟮I, I⟯ M) M where
  smul f x := f x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The tautological action of `M ≃ₘ^n⟮I, I⟯ M` on `M` is given by evaluation. -/
@[simp]
theorem smul_def (f : M ≃ₘ^n⟮I, I⟯ M) (x : M) : f • x = f x := rfl

/-- The action homomorphism of the tautological diffeomorphism action is the forgetful homomorphism
to permutations. -/
@[simp]
theorem toPermHom_eq_toPerm :
    MulAction.toPermHom (M ≃ₘ^n⟮I, I⟯ M) M = toPerm := by
  ext f x
  simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, smul_def, toPerm_apply,
    coe_toEquiv]

/-- The tautological action of `M ≃ₘ^n⟮I, I⟯ M` on `M` is faithful. -/
instance applyFaithfulSMul : FaithfulSMul (M ≃ₘ^n⟮I, I⟯ M) M :=
  ⟨fun h => Diffeomorph.ext h⟩

/-- The action of each self-diffeomorphism on `M` is continuous. -/
instance applyContinuousConstSMul : ContinuousConstSMul (M ≃ₘ^n⟮I, I⟯ M) M :=
  ⟨fun f => f.continuous⟩

/-- A subgroup of the self-diffeomorphism group acts continuously on `M` in the point, by the
generic subgroup transfer for `ContinuousConstSMul`. -/
abbrev applySubgroupContinuousConstSMul (G : Subgroup (M ≃ₘ^n⟮I, I⟯ M)) :
    ContinuousConstSMul G M :=
  inferInstance

end Diffeomorph
