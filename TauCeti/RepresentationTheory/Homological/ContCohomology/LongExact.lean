/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ShortExact

/-!
# The explicit long exact sequence in low degrees

A short exact sequence `0 → A → B → C → 0` of discrete modules over a topological group `G`
induces the exact sequence

```text
0 → H⁰(G, A) → H⁰(G, B) → H⁰(G, C) →δ⁰→ H¹(G, A) → H¹(G, B) → H¹(G, C) →δ¹→ H²(G, A) → H²(G, B)
```

of the explicit continuous-cochain model. This file proves exactness at each of its eight nodes.

The two leftmost nodes need no topology on `G` at all; the remaining six carry exactly the
hypotheses their maps require, so the three nodes touching `H²` also ask for a continuous
multiplication on `G`.

The arguments are the ordinary diagram chases, run on continuous cochains. The topological input
is entirely in `ShortExact.lean`: a continuous cochain into the discrete `C` lifts to a continuous
cochain into `B`, and a continuous cochain into `B` killed by the projection retracts to a
continuous cochain into `A`. Once a chase has produced a cochain, `mem_Z1_of_incl_comp_mem_Z1`
and `mem_Z2_of_incl_comp_mem_Z2` are what put it back into the continuous cocycles.

## Main statements

* `TauCeti.ContCohomology.DiscreteShortExact.explicitLongExact_H0A`: the coefficient inclusion is
  injective on `H⁰`.
* `TauCeti.ContCohomology.DiscreteShortExact.explicitLongExact_H0B`: exactness at `H⁰(G, B)`.
* `TauCeti.ContCohomology.DiscreteShortExact.explicitLongExact_H0C`: exactness at `H⁰(G, C)`.
* `TauCeti.ContCohomology.DiscreteShortExact.explicitLongExact_H1A`: exactness at `H¹(G, A)`.
* `TauCeti.ContCohomology.DiscreteShortExact.explicitLongExact_H1B`: exactness at `H¹(G, B)`.
* `TauCeti.ContCohomology.DiscreteShortExact.explicitLongExact_H1C`: exactness at `H¹(G, C)`.
* `TauCeti.ContCohomology.DiscreteShortExact.explicitLongExact_H2A`: exactness at `H²(G, A)`.
* `TauCeti.ContCohomology.DiscreteShortExact.explicitLongExact_H2B`: exactness at `H²(G, B)`.

The maps and their normalization are those of
`TauCeti/RepresentationTheory/Homological/ContCohomology/LowDegree.lean`,
`ExplicitFunctoriality.lean` and `ShortExact.lean`. This implements the eight exactness nodes of
the long exact sequence milestone of Layer 5 of the human-authored roadmap at
`TauCetiRoadmap/ProfiniteCohomology/README.md`, whose `Suggested.lean` fixes the eight names
above.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.3.2): the
  low-degree long exact sequence used here.
-/

public section

namespace TauCeti.ContCohomology

universe u vA vB vC

/-! ### Coefficient maps on chosen representatives

Every chase below hands a cocycle to a coefficient map and has to recognize the result as the
class of a cocycle already in hand. These two lemmas do that recognition once; they are the
`explicitCoeff` counterpart of `explicitDelta0_apply` and `explicitDelta1_apply`. -/

section Representatives

variable (G : Type u) [Group G] [TopologicalSpace G]
  {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]

/-- A coefficient map sends the class of `c` to the class of any cocycle lying under `c`. -/
private theorem explicitCoeff1_eq_of_apply (f : M →+[G] N) (hf : Continuous f)
    (c : Z1 G M) (d : Z1 G N) (h : ∀ g : G, (d : G → N) g = f ((c : G → M) g)) :
    explicitCoeff1 G M f hf (c : H1 G M) = (d : H1 G N) := by
  rw [explicitCoeff1_mk]
  refine congrArg (fun z : Z1 G N => (z : H1 G N)) (Subtype.ext (funext fun g => ?_))
  exact (cocyclesMap1_apply G M G N (ContinuousMonoidHom.id G) (f : M →+ N) hf
    (fun g m => f.map_smul g m) c g).trans (h g).symm

/-- The degree-`2` counterpart of `explicitCoeff1_eq_of_apply`. -/
private theorem explicitCoeff2_eq_of_apply [ContinuousMul G] (f : M →+[G] N) (hf : Continuous f)
    (c : Z2 G M) (d : Z2 G N)
    (h : ∀ p : G × G, (d : G × G → N) p = f ((c : G × G → M) p)) :
    explicitCoeff2 G M f hf (c : H2 G M) = (d : H2 G N) := by
  rw [explicitCoeff2_mk]
  refine congrArg (fun z : Z2 G N => (z : H2 G N)) (Subtype.ext (funext fun p => ?_))
  exact (cocyclesMap2_apply G M G N (ContinuousMonoidHom.id G) (f : M →+ N) hf
    (fun g m => f.map_smul g m) c p.1 p.2).trans (h p).symm

/-- A class dies under a coefficient map exactly when its image cochain is a coboundary. -/
private theorem explicitCoeff1_eq_zero_iff (f : M →+[G] N) (hf : Continuous f) (c : Z1 G M) :
    explicitCoeff1 G M f hf (c : H1 G M) = 0 ↔
      ∃ n : N, ∀ g : G, g • n - n = f ((c : G → M) g) := by
  rw [explicitCoeff1_mk, H1pi_eq_zero_iff]
  constructor
  · intro hmem
    obtain ⟨n, hn⟩ := mem_B1_iff.1 hmem
    exact ⟨n, fun g => (hn g).trans (cocyclesMap1_apply G M G N (ContinuousMonoidHom.id G)
      (f : M →+ N) hf (fun g m => f.map_smul g m) c g)⟩
  · rintro ⟨n, hn⟩
    exact mem_B1_iff.2 ⟨n, fun g => (hn g).trans (cocyclesMap1_apply G M G N
      (ContinuousMonoidHom.id G) (f : M →+ N) hf (fun g m => f.map_smul g m) c g).symm⟩

/-- The degree-`2` counterpart of `explicitCoeff1_eq_zero_iff`; the primitive is continuous, `B²`
being the image of the continuous `1`-cochains. -/
private theorem explicitCoeff2_eq_zero_iff [ContinuousMul G] (f : M →+[G] N) (hf : Continuous f)
    (c : Z2 G M) :
    explicitCoeff2 G M f hf (c : H2 G M) = 0 ↔
      ∃ u : G → N, Continuous u ∧
        ∀ g h : G, g • u h - u (g * h) + u g = f ((c : G × G → M) (g, h)) := by
  rw [explicitCoeff2_mk, H2pi_eq_zero_iff]
  constructor
  · intro hmem
    obtain ⟨u, hu, hcu⟩ := mem_B2_iff'.1 hmem
    exact ⟨u, hu, fun g h => (hcu g h).trans (cocyclesMap2_apply G M G N
      (ContinuousMonoidHom.id G) (f : M →+ N) hf (fun g m => f.map_smul g m) c g h)⟩
  · rintro ⟨u, hu, hcu⟩
    exact mem_B2_iff'.2 ⟨u, hu, fun g h => (hcu g h).trans (cocyclesMap2_apply G M G N
      (ContinuousMonoidHom.id G) (f : M →+ N) hf (fun g m => f.map_smul g m) c g h).symm⟩

end Representatives

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

/-! ### The degree-one nodes

Exactness at `H¹(G, A)` and at `H¹(G, B)`. Neither node mentions `H²`, so neither needs a
continuous multiplication on `G`. -/

section DegreeOne

variable {G : Type u} [Group G] [TopologicalSpace G]
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A]
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B] [ContinuousSMul G B]
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C] [ContinuousSMul G C]
  (S : DiscreteShortExact G A B C)

omit [ContinuousSMul G C] in
/-- The image of the connecting map lies in the kernel of the coefficient inclusion: a
representative of `δ⁰ c` lies under the coboundary of a preimage of `c`. -/
private theorem range_delta0_le_ker_coeff1 :
    S.explicitDelta0.range ≤
      (explicitCoeff1 G A S.inclDistribMulActionHom continuous_of_discreteTopology).ker := by
  rintro _ ⟨c, rfl⟩
  obtain ⟨b, hb⟩ := S.proj_surjective (c : C)
  have hbinv : S.proj b ∈ H0 G C := hb ▸ c.2
  obtain ⟨a, -, haincl⟩ :=
    S.exists_continuous_incl_comp_eq (continuous_d0_apply (G := G) b) (S.proj_d0_eq_zero hbinv)
  have hab : ∀ g : G, S.incl (a g) = g • b - b := fun g => (haincl g).trans (d0_apply b g)
  have hd0 : d0 G B b ∈ B1 G B := mem_B1_iff.2 ⟨b, fun g => (d0_apply b g).symm⟩
  refine AddMonoidHom.mem_ker.2 ?_
  rw [S.explicitDelta0_apply c hb (S.mem_Z1_of_incl_comp_eq_d0 hab) hab,
    QuotientAddGroup.mk'_apply,
    explicitCoeff1_eq_of_apply G S.inclDistribMulActionHom continuous_of_discreteTopology
      ⟨a, S.mem_Z1_of_incl_comp_eq_d0 hab⟩ ⟨d0 G B b, B1_le_Z1 G B hd0⟩
      fun g => by rw [inclDistribMulActionHom_apply, haincl g]]
  exact H1pi_eq_zero_iff.2 hd0

omit [ContinuousSMul G C] in
/-- A class killed by the coefficient inclusion is a value of the connecting map: a representative
`a` becomes the coboundary of some `b : B`, whose image in `C` is then invariant, and `δ⁰` of that
invariant is the class of `a`. -/
private theorem ker_coeff1_le_range_delta0 :
    (explicitCoeff1 G A S.inclDistribMulActionHom continuous_of_discreteTopology).ker ≤
      S.explicitDelta0.range := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ a =>
    intro hx
    obtain ⟨b, hb⟩ := (explicitCoeff1_eq_zero_iff G S.inclDistribMulActionHom
      continuous_of_discreteTopology a).1 (AddMonoidHom.mem_ker.1 hx)
    have hab : ∀ g : G, S.incl ((a : G → A) g) = g • b - b := fun g => by
      rw [← inclDistribMulActionHom_apply]
      exact (hb g).symm
    have hbinv : S.proj b ∈ H0 G C := (FixedPoints.mem_addSubgroup G C (S.proj b)).2 fun g => by
      have h := congrArg S.proj (hab g)
      rw [S.proj_incl, map_sub, S.proj_equivariant] at h
      exact sub_eq_zero.1 h.symm
    exact ⟨⟨S.proj b, hbinv⟩, by
      rw [S.explicitDelta0_apply ⟨S.proj b, hbinv⟩ rfl a.2 hab, QuotientAddGroup.mk'_apply]⟩

omit [ContinuousSMul G C] in
/-- **Exactness at `H¹(G, A)`**, the node where `δ⁰` lands. -/
theorem explicitLongExact_H1A :
    S.explicitDelta0.range =
      (explicitCoeff1 G A S.inclDistribMulActionHom continuous_of_discreteTopology).ker :=
  le_antisymm S.range_delta0_le_ker_coeff1 S.ker_coeff1_le_range_delta0

/-- The composite `A → B → C` being zero, so is the composite of the two coefficient maps. -/
private theorem range_coeff1_le_ker_coeff1 :
    (explicitCoeff1 G A S.inclDistribMulActionHom continuous_of_discreteTopology).range ≤
      (explicitCoeff1 G B S.projDistribMulActionHom continuous_of_discreteTopology).ker := by
  rintro _ ⟨x, rfl⟩
  induction x using QuotientAddGroup.induction_on with
  | _ a =>
    have hmem : (fun g => S.incl ((a : G → A) g)) ∈ Z1 G B :=
      mem_Z1_iff.2 ⟨continuous_of_discreteTopology.comp (mem_Z1_iff.1 a.2).1, fun g h => by
        simp only [(mem_Z1_iff.1 a.2).2 g h, map_add, S.incl_equivariant]⟩
    refine AddMonoidHom.mem_ker.2 ?_
    rw [explicitCoeff1_eq_of_apply G S.inclDistribMulActionHom continuous_of_discreteTopology a
        ⟨_, hmem⟩ (fun g => by rw [inclDistribMulActionHom_apply]),
      explicitCoeff1_eq_of_apply G S.projDistribMulActionHom continuous_of_discreteTopology
        ⟨_, hmem⟩ 0 fun g => by
          rw [ZeroMemClass.coe_zero, Pi.zero_apply, projDistribMulActionHom_apply]
          exact (S.proj_incl _).symm]
    exact map_zero (H1pi G C)

/-- A class killed by the projection has a representative lying in the image of `A`: correcting a
representative by the coboundary of a preimage of its primitive in `C` makes it vanish in `C`, and
what remains retracts to a continuous `1`-cocycle on `A`. -/
private theorem ker_coeff1_le_range_coeff1 :
    (explicitCoeff1 G B S.projDistribMulActionHom continuous_of_discreteTopology).ker ≤
      (explicitCoeff1 G A S.inclDistribMulActionHom continuous_of_discreteTopology).range := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ e =>
    intro hx
    obtain ⟨c₀, hc₀⟩ := (explicitCoeff1_eq_zero_iff G S.projDistribMulActionHom
      continuous_of_discreteTopology e).1 (AddMonoidHom.mem_ker.1 hx)
    obtain ⟨b₀, hb₀⟩ := S.proj_surjective c₀
    have hd0 : d0 G B b₀ ∈ B1 G B := mem_B1_iff.2 ⟨b₀, fun g => (d0_apply b₀ g).symm⟩
    obtain ⟨e', hcoe⟩ : ∃ e' : Z1 G B, (e' : G → B) = (e : G → B) - d0 G B b₀ :=
      ⟨e - ⟨d0 G B b₀, B1_le_Z1 G B hd0⟩, by rw [AddSubgroup.coe_sub]⟩
    have hproj : ∀ g : G, S.proj ((e' : G → B) g) = 0 := fun g => by
      rw [hcoe, Pi.sub_apply, map_sub, d0_apply, map_sub, S.proj_equivariant, hb₀,
        ← projDistribMulActionHom_apply, ← hc₀ g, sub_self]
    obtain ⟨a, -, haincl⟩ := S.exists_continuous_incl_comp_eq (mem_Z1_iff.1 e'.2).1 hproj
    refine ⟨(⟨a, mem_Z1_of_incl_comp_mem_Z1 haincl e'.2⟩ : Z1 G A), ?_⟩
    rw [explicitCoeff1_eq_of_apply G S.inclDistribMulActionHom continuous_of_discreteTopology
      ⟨a, mem_Z1_of_incl_comp_mem_Z1 haincl e'.2⟩ e'
      (fun g => by rw [inclDistribMulActionHom_apply, haincl g])]
    refine H1pi_eq_iff.2 ?_
    rw [hcoe, sub_sub_cancel_left]
    exact neg_mem hd0

/-- **Exactness at `H¹(G, B)`.** -/
theorem explicitLongExact_H1B :
    (explicitCoeff1 G A S.inclDistribMulActionHom continuous_of_discreteTopology).range =
      (explicitCoeff1 G B S.projDistribMulActionHom continuous_of_discreteTopology).ker :=
  le_antisymm S.range_coeff1_le_ker_coeff1 S.ker_coeff1_le_range_coeff1

end DegreeOne

/-! ### The nodes touching degree two

Exactness at `H¹(G, C)`, where `δ¹` leaves, and at `H²(G, A)` and `H²(G, B)`. All three mention
`H²`, hence carry the continuous multiplication on `G` that makes `d¹` preserve continuity. -/

section DegreeTwo

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A]
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B] [ContinuousSMul G B]
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C] [ContinuousSMul G C]
  (S : DiscreteShortExact G A B C)

/-- A class coming from `H¹(G, B)` is killed by `δ¹`: it is represented by a cocycle on `C` that
lifts to a *cocycle* on `B`, so the `2`-cochain computing `δ¹` from that lift vanishes. -/
private theorem range_coeff1_le_ker_delta1 :
    (explicitCoeff1 G B S.projDistribMulActionHom continuous_of_discreteTopology).range ≤
      S.explicitDelta1.ker := by
  rintro _ ⟨x, rfl⟩
  induction x using QuotientAddGroup.induction_on with
  | _ e =>
    have hmem : (fun g => S.proj ((e : G → B) g)) ∈ Z1 G C :=
      mem_Z1_iff.2 ⟨continuous_of_discreteTopology.comp (mem_Z1_iff.1 e.2).1, fun g h => by
        simp only [(mem_Z1_iff.1 e.2).2 g h, map_add, S.proj_equivariant]⟩
    have hdelta : S.explicitDelta1 ((⟨_, hmem⟩ : Z1 G C) : H1 G C) =
        H2pi G A ⟨0, zero_mem (Z2 G A)⟩ :=
      S.explicitDelta1_apply ⟨_, hmem⟩ (mem_Z1_iff.1 e.2).1 (fun _ => rfl) (zero_mem (Z2 G A))
        fun g h => by
          rw [Pi.zero_apply, map_zero, (mem_Z1_iff.1 e.2).2 g h]
          abel
    refine AddMonoidHom.mem_ker.2 ?_
    rw [explicitCoeff1_eq_of_apply G S.projDistribMulActionHom continuous_of_discreteTopology e
        ⟨_, hmem⟩ (fun g => by rw [projDistribMulActionHom_apply]), hdelta]
    exact H2pi_eq_zero_iff.2 (zero_mem (B2 G A))

/-- A class killed by `δ¹` comes from `H¹(G, B)`: a continuous lift of a representative has a
`d¹` that is the coboundary of a continuous `1`-cochain on `A`, and subtracting that cochain turns
the lift into a cocycle. -/
private theorem ker_delta1_le_range_coeff1 :
    S.explicitDelta1.ker ≤
      (explicitCoeff1 G B S.projDistribMulActionHom continuous_of_discreteTopology).range := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ f =>
    intro hx
    obtain ⟨e, hecont, hef⟩ := exists_continuous_lift S.proj_surjective (mem_Z1_iff.1 f.2).1
    obtain ⟨a, -, haincl⟩ := S.exists_continuous_incl_comp_eq (continuous_d1_apply hecont)
      (proj_d1_eq_zero hef (mem_Z1_iff.1 f.2).2)
    have hae : ∀ g h : G, S.incl (a (g, h)) = g • e h - e (g * h) + e g := fun g h =>
      (haincl (g, h)).trans (d1_apply e g h)
    have hdelta : S.explicitDelta1 (f : H1 G C) =
        H2pi G A ⟨a, S.mem_Z2_of_incl_comp_eq_d1 hecont hae⟩ :=
      S.explicitDelta1_apply f hecont hef (S.mem_Z2_of_incl_comp_eq_d1 hecont hae) hae
    have hzero : ((⟨a, S.mem_Z2_of_incl_comp_eq_d1 hecont hae⟩ : Z2 G A) : H2 G A) = 0 :=
      hdelta.symm.trans (AddMonoidHom.mem_ker.1 hx)
    have hcob : a ∈ B2 G A := H2pi_eq_zero_iff.1 hzero
    obtain ⟨u, hu, hcu⟩ := mem_B2_iff'.1 hcob
    -- Subtracting the image of the primitive `u` from the lift `e` makes it a cocycle.
    have hcocycle : ∀ g h : G, e (g * h) - S.incl (u (g * h)) =
        g • (e h - S.incl (u h)) + (e g - S.incl (u g)) := fun g h => by
      have heq : g • e h - e (g * h) + e g =
          g • S.incl (u h) - S.incl (u (g * h)) + S.incl (u g) := by
        rw [← hae g h, ← hcu g h, map_add, map_sub, S.incl_equivariant]
      have hgh : e (g * h) = g • e h + e g -
          (g • S.incl (u h) - S.incl (u (g * h)) + S.incl (u g)) := by
        rw [← heq]
        abel
      rw [hgh, smul_sub]
      abel
    have hmem : (fun g => e g - S.incl (u g)) ∈ Z1 G B :=
      mem_Z1_iff.2 ⟨hecont.sub (continuous_of_discreteTopology.comp hu), hcocycle⟩
    refine ⟨((⟨_, hmem⟩ : Z1 G B) : H1 G B), ?_⟩
    rw [explicitCoeff1_eq_of_apply G S.projDistribMulActionHom continuous_of_discreteTopology
      ⟨_, hmem⟩ f fun g => by
        rw [projDistribMulActionHom_apply, map_sub, S.proj_incl, sub_zero, hef g]]

/-- **Exactness at `H¹(G, C)`**, the node where `δ¹` leaves. -/
theorem explicitLongExact_H1C :
    (explicitCoeff1 G B S.projDistribMulActionHom continuous_of_discreteTopology).range =
      S.explicitDelta1.ker :=
  le_antisymm S.range_coeff1_le_ker_delta1 S.ker_delta1_le_range_coeff1

/-- The image of `δ¹` lies in the kernel of the coefficient inclusion: a representative of
`δ¹` of a class lies under the `d¹` of a continuous lift of that class. -/
private theorem range_delta1_le_ker_coeff2 :
    S.explicitDelta1.range ≤
      (explicitCoeff2 G A S.inclDistribMulActionHom continuous_of_discreteTopology).ker := by
  rintro _ ⟨x, rfl⟩
  induction x using QuotientAddGroup.induction_on with
  | _ f =>
    obtain ⟨e, hecont, hef⟩ := exists_continuous_lift S.proj_surjective (mem_Z1_iff.1 f.2).1
    obtain ⟨a, -, haincl⟩ := S.exists_continuous_incl_comp_eq (continuous_d1_apply hecont)
      (proj_d1_eq_zero hef (mem_Z1_iff.1 f.2).2)
    have hae : ∀ g h : G, S.incl (a (g, h)) = g • e h - e (g * h) + e g := fun g h =>
      (haincl (g, h)).trans (d1_apply e g h)
    have hd1 : d1 G B e ∈ B2 G B := mem_B2_iff.2 ⟨e, hecont, rfl⟩
    have hdelta : S.explicitDelta1 (f : H1 G C) =
        H2pi G A ⟨a, S.mem_Z2_of_incl_comp_eq_d1 hecont hae⟩ :=
      S.explicitDelta1_apply f hecont hef (S.mem_Z2_of_incl_comp_eq_d1 hecont hae) hae
    refine AddMonoidHom.mem_ker.2 ?_
    rw [hdelta, QuotientAddGroup.mk'_apply,
      explicitCoeff2_eq_of_apply G S.inclDistribMulActionHom continuous_of_discreteTopology
        ⟨a, S.mem_Z2_of_incl_comp_eq_d1 hecont hae⟩ ⟨d1 G B e, B2_le_Z2 G B hd1⟩
        fun p => by rw [inclDistribMulActionHom_apply, haincl p]]
    exact H2pi_eq_zero_iff.2 hd1

/-- A class killed by the coefficient inclusion is a value of `δ¹`: a representative becomes the
`d¹` of a continuous `1`-cochain on `B`, whose image in `C` is then a continuous `1`-cocycle, and
`δ¹` of its class is the class one started with. -/
private theorem ker_coeff2_le_range_delta1 :
    (explicitCoeff2 G A S.inclDistribMulActionHom continuous_of_discreteTopology).ker ≤
      S.explicitDelta1.range := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ a =>
    intro hx
    obtain ⟨e, hecont, hae⟩ := (explicitCoeff2_eq_zero_iff G S.inclDistribMulActionHom
      continuous_of_discreteTopology a).1 (AddMonoidHom.mem_ker.1 hx)
    have hae' : ∀ g h : G, S.incl ((a : G × G → A) (g, h)) = g • e h - e (g * h) + e g :=
      fun g h => by
        rw [← inclDistribMulActionHom_apply]
        exact (hae g h).symm
    have hmem : (fun g => S.proj (e g)) ∈ Z1 G C :=
      mem_Z1_iff.2 ⟨continuous_of_discreteTopology.comp hecont, fun g h => by
        have h₀ := congrArg S.proj (hae' g h)
        rw [S.proj_incl, map_add, map_sub, S.proj_equivariant] at h₀
        have h₁ : g • S.proj (e h) + S.proj (e g) - S.proj (e (g * h)) = 0 := by
          rw [h₀]
          abel
        exact (sub_eq_zero.1 h₁).symm⟩
    exact ⟨((⟨_, hmem⟩ : Z1 G C) : H1 G C),
      S.explicitDelta1_apply ⟨_, hmem⟩ hecont (fun _ => rfl) a.2 hae'⟩

/-- **Exactness at `H²(G, A)`**, the node where `δ¹` lands. -/
theorem explicitLongExact_H2A :
    S.explicitDelta1.range =
      (explicitCoeff2 G A S.inclDistribMulActionHom continuous_of_discreteTopology).ker :=
  le_antisymm S.range_delta1_le_ker_coeff2 S.ker_coeff2_le_range_delta1

/-- The degree-`2` form of `range_coeff1_le_ker_coeff1`. -/
private theorem range_coeff2_le_ker_coeff2 :
    (explicitCoeff2 G A S.inclDistribMulActionHom continuous_of_discreteTopology).range ≤
      (explicitCoeff2 G B S.projDistribMulActionHom continuous_of_discreteTopology).ker := by
  rintro _ ⟨x, rfl⟩
  induction x using QuotientAddGroup.induction_on with
  | _ a =>
    have hmem : (fun p => S.incl ((a : G × G → A) p)) ∈ Z2 G B :=
      mem_Z2_iff.2 ⟨continuous_of_discreteTopology.comp (mem_Z2_iff.1 a.2).1, fun g h j => by
        simp only [← S.incl_equivariant, ← map_add]
        exact congrArg S.incl ((mem_Z2_iff.1 a.2).2 g h j)⟩
    refine AddMonoidHom.mem_ker.2 ?_
    rw [explicitCoeff2_eq_of_apply G S.inclDistribMulActionHom continuous_of_discreteTopology a
        ⟨_, hmem⟩ (fun p => by rw [inclDistribMulActionHom_apply]),
      explicitCoeff2_eq_of_apply G S.projDistribMulActionHom continuous_of_discreteTopology
        ⟨_, hmem⟩ 0 fun p => by
          rw [ZeroMemClass.coe_zero, Pi.zero_apply, projDistribMulActionHom_apply]
          exact (S.proj_incl _).symm]
    exact map_zero (H2pi G C)

/-- The degree-`2` form of `ker_coeff1_le_range_coeff1`, the correcting cochain now being the `d¹`
of a continuous lift of the primitive in `C`. -/
private theorem ker_coeff2_le_range_coeff2 :
    (explicitCoeff2 G B S.projDistribMulActionHom continuous_of_discreteTopology).ker ≤
      (explicitCoeff2 G A S.inclDistribMulActionHom continuous_of_discreteTopology).range := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    intro hx
    obtain ⟨v, hv, hvz⟩ := (explicitCoeff2_eq_zero_iff G S.projDistribMulActionHom
      continuous_of_discreteTopology z).1 (AddMonoidHom.mem_ker.1 hx)
    obtain ⟨w, hw, hwv⟩ := exists_continuous_lift S.proj_surjective hv
    have hd1 : d1 G B w ∈ B2 G B := mem_B2_iff.2 ⟨w, hw, rfl⟩
    obtain ⟨z', hcoe⟩ : ∃ z' : Z2 G B, (z' : G × G → B) = (z : G × G → B) - d1 G B w :=
      ⟨z - ⟨d1 G B w, B2_le_Z2 G B hd1⟩, by rw [AddSubgroup.coe_sub]⟩
    have hproj : ∀ p : G × G, S.proj ((z' : G × G → B) p) = 0 := by
      rintro ⟨g, h⟩
      rw [hcoe, Pi.sub_apply, map_sub, d1_apply, map_add, map_sub, S.proj_equivariant]
      simp only [hwv]
      rw [← projDistribMulActionHom_apply, ← hvz g h, sub_self]
    obtain ⟨a, -, haincl⟩ := S.exists_continuous_incl_comp_eq (mem_Z2_iff.1 z'.2).1 hproj
    refine ⟨(⟨a, mem_Z2_of_incl_comp_mem_Z2 haincl z'.2⟩ : Z2 G A), ?_⟩
    rw [explicitCoeff2_eq_of_apply G S.inclDistribMulActionHom continuous_of_discreteTopology
      ⟨a, mem_Z2_of_incl_comp_mem_Z2 haincl z'.2⟩ z'
      (fun p => by rw [inclDistribMulActionHom_apply, haincl p])]
    refine H2pi_eq_iff.2 ?_
    rw [hcoe, sub_sub_cancel_left]
    exact neg_mem hd1

/-- **Exactness at `H²(G, B)`**, the eighth and last node. -/
theorem explicitLongExact_H2B :
    (explicitCoeff2 G A S.inclDistribMulActionHom continuous_of_discreteTopology).range =
      (explicitCoeff2 G B S.projDistribMulActionHom continuous_of_discreteTopology).ker :=
  le_antisymm S.range_coeff2_le_ker_coeff2 S.ker_coeff2_le_range_coeff2

end DegreeTwo

end DiscreteShortExact

end TauCeti.ContCohomology
