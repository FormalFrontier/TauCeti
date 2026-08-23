/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.OpenMapping.Complete
public import TauCeti.Topology.Algebra.Nonarchimedean.FirstCountable

/-!
# Henkel's open mapping theorem

A surjective equivariant additive map out of a complete first-countable nonarchimedean group is
open, provided the scalars carry a zero sequence of units and the target is a Baire space. This
file assembles that statement from the pieces built around it.

Each hypothesis pays for one step and no other.

* The zero sequence of units and the Baire property give
  `TauCeti.HasZeroSequenceOfUnits.closure_image_mem_nhds_zero`: the *closure* of the image of a
  neighbourhood of zero is a neighbourhood of zero. Supplying that closure step is the only use
  the Baire hypothesis is put to here; whether a weaker hypothesis would do is not addressed.
* Nonarchimedean plus countable generation of `𝓝 0` turn that into a sequence of subgroups
  (`TauCeti.NonarchimedeanAddGroup.exists_antitone_basis_openAddSubgroup`) along which the
  approximation can run.
* Completeness removes the closure, in `TauCeti.mem_image_of_mem_closure_image`.

What is left is bookkeeping: shift the basis so its zeroth term lies inside the given
neighbourhood, and feed the result to the group-theoretic criterion for openness.

## Main results

* `TauCeti.HasZeroSequenceOfUnits.isOpenMap`: Henkel's open mapping theorem.
* `TauCeti.HasZeroSequenceOfUnits.isQuotientMap`: the same map induces the quotient topology on
  its target — the form the strict-morphism material will consume, where what matters is not that
  images are open but that the target's topology is determined by the source's.

Mathlib's `MonoidHom.isOpenMap_of_sigmaCompact` proves openness for a continuous surjection from
a σ-compact source onto a T2 Baire target group (locally compact groups being the standard
example of such a target). Neither theorem implies the other: both ask the target to be Baire,
but this one asks the *source* to be complete, first countable and nonarchimedean where that one
asks it to be σ-compact, and neither of those conditions implies the other.

## References

* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  [arXiv:1407.5647](https://arxiv.org/abs/1407.5647).
* T. Wedhorn, *Adic Spaces*, Theorem 6.16.
-/

public section

open Filter Topology

namespace TauCeti

variable {A M N : Type*} [MonoidWithZero A] [TopologicalSpace A] [HasZeroSequenceOfUnits A]
  [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
  [(𝓝 (0 : M)).IsCountablyGenerated] [NonarchimedeanAddGroup M] [MulActionWithZero A M]
  [AddGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N] [T0Space N] [BaireSpace N]
  [MulAction A N] [ContinuousConstSMul A N]

/-- **Henkel's open mapping theorem.** A surjective `A`-equivariant additive map from a complete
first-countable nonarchimedean group to a Baire space is open, when `A` has a zero sequence of
units.

Only continuity at zero is asked of `f`, and only continuity in the scalar at zero is asked of
the action, in the form `hc` that the Baire step already uses. -/
theorem HasZeroSequenceOfUnits.isOpenMap {F : Type*} [FunLike F M N] [MulActionHomClass F A M N]
    [AddMonoidHomClass F M N] (f : F) (hf : Function.Surjective f)
    (hfc : ContinuousAt (f : M → N) 0) (hc : ∀ x : M, ContinuousAt (fun a : A ↦ a • x) 0) :
    IsOpenMap (f : M → N) := by
  refine IsTopologicalAddGroup.isOpenMap_iff_nhds_zero.mpr fun S hS ↦ ?_
  rw [Filter.mem_map] at hS
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.exists_antitone_basis_openAddSubgroup (G := M)
  obtain ⟨n₀, -, hn₀⟩ := hV.toHasBasis.mem_iff.mp hS
  -- Shift the basis so that its zeroth term already lies inside `f ⁻¹' S`.
  have hW : (𝓝 (0 : M)).HasAntitoneBasis fun n ↦ ((V (n₀ + n)).toAddSubgroup : Set M) :=
    hV.comp_mono (fun _ _ hab ↦ Nat.add_le_add_left hab _)
      (by simpa [Nat.add_comm] using tendsto_add_atTop_nat n₀)
  have hnhds : ∀ n, closure ((f : M → N) ''
      ((V (n₀ + n)).toAddSubgroup : Set M)) ∈ 𝓝 (0 : N) := fun n ↦
    HasZeroSequenceOfUnits.closure_image_mem_nhds_zero f hf hc
      (hW.toHasBasis.mem_of_mem (i := n) trivial)
  refine Filter.mem_of_superset (hnhds 0) fun y hy ↦ ?_
  obtain ⟨x, hx, rfl⟩ := mem_image_of_mem_closure_image f hfc hW (fun n ↦ hnhds (n + 1)) hy
  exact hn₀ hx

/-- **Henkel's theorem in quotient form.** Under exactly the hypotheses of
`TauCeti.HasZeroSequenceOfUnits.isOpenMap`, the map does not merely carry open sets to open sets:
the topology of `N` is the one coinduced from `M`, so a map out of `N` is continuous exactly when
its composite with `f` is.

The quotient conclusion needs `f` continuous everywhere, but that is not an extra hypothesis: an
additive homomorphism out of a topological group is continuous as soon as it is continuous at `0`
(`continuous_of_continuousAt_zero`), so `hfc` is the same assumption the open-mapping theorem
makes. This is the shape Wedhorn's strict morphisms will use. -/
theorem HasZeroSequenceOfUnits.isQuotientMap {F : Type*} [FunLike F M N]
    [MulActionHomClass F A M N] [AddMonoidHomClass F M N] (f : F) (hf : Function.Surjective f)
    (hfc : ContinuousAt (f : M → N) 0) (hc : ∀ x : M, ContinuousAt (fun a : A ↦ a • x) 0) :
    IsQuotientMap (f : M → N) :=
  have hcont : Continuous (f : M → N) := continuous_of_continuousAt_zero f hfc
  (HasZeroSequenceOfUnits.isOpenMap f hf hfc hc).isQuotientMap hcont hf

end TauCeti

end
