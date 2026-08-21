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

The action formalization mirrors `TauCeti.Homeomorph.applyMulAction` in
`TauCeti.Topology.Algebra.Homeomorph.Action`,
which in turn follows `Equiv.Perm.applyMulAction` and the construction in Kim Morrison's
mathlib4#40135.

This is a small prerequisite for the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`, layer 3, "diffeomorphism groups with the C^∞
topology"). The layer builds `Diff(M)` as a group first and then equips it with the `C^∞`
topology; the evaluation action and the map `Diff(M) → Homeomorph(M)` are basic API for relating
that future topological group to the underlying space.

## Main definitions

* `TauCeti.Diffeomorph.applyMulAction`: the `MulAction (M ≃ₘ^n⟮I, I⟯ M) M` with
  `φ • x = φ x`.
* `TauCeti.Diffeomorph.applyFaithfulSMul`: the action is faithful.
* `TauCeti.Diffeomorph.applyContinuousConstSMul`: each diffeomorphism acts continuously.
* `TauCeti.Diffeomorph.applySubgroupContinuousConstSMul`: subgroups inherit continuity in the
  point.
-/

public section

namespace TauCeti

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
  rfl

/-- The tautological action of `M ≃ₘ^n⟮I, I⟯ M` on `M` is faithful. -/
instance applyFaithfulSMul : FaithfulSMul (M ≃ₘ^n⟮I, I⟯ M) M :=
  ⟨fun h => _root_.Diffeomorph.ext h⟩

/-- The action of each self-diffeomorphism on `M` is continuous. -/
instance applyContinuousConstSMul : ContinuousConstSMul (M ≃ₘ^n⟮I, I⟯ M) M :=
  ⟨fun f => f.continuous⟩

/-- A subgroup of the self-diffeomorphism group acts continuously on `M` in the point, by the
generic subgroup transfer for `ContinuousConstSMul`. -/
abbrev applySubgroupContinuousConstSMul (G : Subgroup (M ≃ₘ^n⟮I, I⟯ M)) :
    ContinuousConstSMul G M :=
  inferInstance

end Diffeomorph

end TauCeti
