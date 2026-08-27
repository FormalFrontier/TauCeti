/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ShortExact

/-!
# The degree-zero segment of the explicit long exact sequence

A short exact sequence `0 → A → B → C → 0` of discrete modules over a group induces
exactness at the first two degree-zero nodes of

```text
0 → H⁰(G, A) → H⁰(G, B) → H⁰(G, C) → H¹(G, A).
```

No topology on `G` or continuity of its actions is needed at these first two nodes. Exactness at
`H⁰(G, C)` additionally uses a topology on `G` and continuous actions on `A` and `B`, as required
by the construction of `explicitDelta0` and its codomain `H¹(G, A)`.

This file proves exactness at all three degree-zero nodes of the explicit continuous-cochain
model. At the first two nodes the proof is the ordinary exactness argument restricted to fixed
points. At `H⁰(G, C)`, a class killed by the connecting map has a preimage `b : B` whose
coboundary is itself a coboundary lifted from `A`; subtracting that lift makes `b` invariant.

## Main statements

* `TauCeti.ContCohomology.DiscreteShortExact.explicitLongExact_H0A`: the coefficient inclusion is
  injective on `H⁰`.
* `TauCeti.ContCohomology.DiscreteShortExact.explicitLongExact_H0B`: exactness at `H⁰(G, B)`.
* `TauCeti.ContCohomology.DiscreteShortExact.explicitLongExact_H0C`: exactness at `H⁰(G, C)`.

The maps and their normalization are those of
`TauCeti/RepresentationTheory/Homological/ContCohomology/LowDegree.lean` and
`ShortExact.lean`. This implements the degree-zero nodes of the long exact sequence milestone of
Layer 5 of the human-authored roadmap at `TauCetiRoadmap/ProfiniteCohomology/README.md`, whose
`Suggested.lean` fixes the names `explicitLongExact_H0A`, `explicitLongExact_H0B` and
`explicitLongExact_H0C`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.3.2): the
  low-degree long exact sequence used here.
-/

public section

namespace TauCeti.ContCohomology

universe u vA vB vC

namespace DiscreteShortExact

section

variable {G : Type u} [Group G] [TopologicalSpace G]
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A]
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B] [ContinuousSMul G B]
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C]
  (S : DiscreteShortExact G A B C)

omit [TopologicalSpace G] [ContinuousSMul G A] [ContinuousSMul G B] in
/-- Exactness at `H⁰(G, A)`: the coefficient inclusion remains injective on invariants. -/
theorem explicitLongExact_H0A :
    Function.Injective (explicitCoeff0 G A S.inclDistribMulActionHom) := by
  intro a a' h
  apply Subtype.ext
  apply S.incl_injective
  simpa only [coe_explicitCoeff0, inclDistribMulActionHom_apply] using congrArg Subtype.val h

omit [TopologicalSpace G] [ContinuousSMul G A] [ContinuousSMul G B] in
/-- Exactness at `H⁰(G, B)`: the invariant elements killed by the projection are precisely
the invariant elements coming from `A`. -/
theorem explicitLongExact_H0B :
    (explicitCoeff0 G A S.inclDistribMulActionHom).range =
      (explicitCoeff0 G B S.projDistribMulActionHom).ker := by
  apply le_antisymm
  · rintro b ⟨a, rfl⟩
    apply AddMonoidHom.mem_ker.2
    apply Subtype.ext
    simp only [coe_explicitCoeff0, inclDistribMulActionHom_apply,
      projDistribMulActionHom_apply, S.proj_incl,
      AddSubgroup.coe_zero]
  · intro b hb
    have hproj : S.proj (b : B) = 0 := by
      have := congrArg Subtype.val (AddMonoidHom.mem_ker.1 hb)
      simpa only [coe_explicitCoeff0, projDistribMulActionHom_apply,
        AddSubgroup.coe_zero] using this
    obtain ⟨a, ha⟩ := S.exists_incl_eq hproj
    have ha_fixed : a ∈ H0 G A := (FixedPoints.mem_addSubgroup G A a).2 fun g => by
      apply S.incl_injective
      rw [S.incl_equivariant, ha]
      exact (FixedPoints.mem_addSubgroup G B (b : B)).1 b.2 g
    refine ⟨⟨a, ha_fixed⟩, Subtype.ext ?_⟩
    simpa only [coe_explicitCoeff0, inclDistribMulActionHom_apply] using ha

/-- The image of `H⁰(G, B)` lies in the kernel of the connecting map. -/
private theorem range_coeff0_le_ker_delta0 :
    (explicitCoeff0 G B S.projDistribMulActionHom).range ≤ S.explicitDelta0.ker := by
  rintro c ⟨b, rfl⟩
  apply AddMonoidHom.mem_ker.2
  have hb : S.proj (b : B) =
      ((explicitCoeff0 G B S.projDistribMulActionHom b : H0 G C) : C) := by
    simp only [coe_explicitCoeff0, projDistribMulActionHom_apply]
  have hzero : (0 : G → A) ∈ Z1 G A := zero_mem _
  rw [S.explicitDelta0_apply (explicitCoeff0 G B S.projDistribMulActionHom b) hb hzero]
  · exact map_zero (H1pi G A)
  · intro g
    rw [Pi.zero_apply, map_zero, (FixedPoints.mem_addSubgroup G B (b : B)).1 b.2 g,
      sub_self]

/-- If `δ⁰(c) = 0`, then `c` has an invariant preimage in `B`. -/
private theorem ker_delta0_le_range_coeff0 :
    S.explicitDelta0.ker ≤ (explicitCoeff0 G B S.projDistribMulActionHom).range := by
  intro c hc
  obtain ⟨b, hb⟩ := S.proj_surjective (c : C)
  have hb_fixed : S.proj b ∈ H0 G C := by
    rw [hb]
    exact c.2
  obtain ⟨a, _, ha_incl⟩ :=
    S.exists_continuous_incl_comp_eq (continuous_d0_apply (G := G) b)
      (S.proj_d0_eq_zero hb_fixed)
  have ha_cocycle : a ∈ Z1 G A := S.mem_Z1_of_incl_comp_eq_d0 fun g => by
    simpa only [d0_apply] using ha_incl g
  have ha_class : H1pi G A ⟨a, ha_cocycle⟩ = 0 := by
    rw [← S.explicitDelta0_apply c hb ha_cocycle (fun g => by
      simpa only [d0_apply] using ha_incl g)]
    exact AddMonoidHom.mem_ker.1 hc
  obtain ⟨a₀, ha₀⟩ := mem_B1_iff.1 (H1pi_eq_zero_iff.1 ha_class)
  let b₀ : B := b - S.incl a₀
  have hb₀_fixed : b₀ ∈ H0 G B := (FixedPoints.mem_addSubgroup G B b₀).2 fun g => by
    have ha₀' : a g = g • a₀ - a₀ := by simpa using (ha₀ g).symm
    have hdiff : g • b - b = g • S.incl a₀ - S.incl a₀ := by
      rw [← d0_apply b g, ← ha_incl g, ha₀', map_sub, S.incl_equivariant]
    dsimp only [b₀]
    rw [smul_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mpr hdiff
  refine ⟨⟨b₀, hb₀_fixed⟩, ?_⟩
  apply Subtype.ext
  dsimp only [b₀]
  simp only [coe_explicitCoeff0, projDistribMulActionHom_apply, map_sub, S.proj_incl, sub_zero, hb]

/-- Exactness at `H⁰(G, C)`: the image of the projection on invariants is the kernel of the
connecting homomorphism `δ⁰ : H⁰(G, C) → H¹(G, A)`. -/
theorem explicitLongExact_H0C :
    (explicitCoeff0 G B S.projDistribMulActionHom).range = S.explicitDelta0.ker :=
  le_antisymm S.range_coeff0_le_ker_delta0 S.ker_delta0_le_range_coeff0

end

end DiscreteShortExact

end TauCeti.ContCohomology
