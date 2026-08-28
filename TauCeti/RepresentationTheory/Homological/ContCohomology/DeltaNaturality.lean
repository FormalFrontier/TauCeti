/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ShortExact

/-!
# Naturality of the low-degree connecting maps

The connecting maps `δ⁰ : H⁰(G, C) → H¹(G, A)` and `δ¹ : H¹(G, C) → H²(G, A)` of a short exact
sequence `0 → A → B → C → 0` of discrete `G`-modules are natural in the sequence and in the group.
Both statements are instances of a single square: a continuous homomorphism `φ : H →ₜ* G` together
with coefficient maps `fA`, `fB`, `fC` that are equivariant along `φ` and commute with the two
maps of the sequences carries `δ` for the sequence over `G` to `δ` for a sequence over `H`.

```text
H⁰(G, C) --δ⁰--> H¹(G, A)          H¹(G, C) --δ¹--> H²(G, A)
   |                 |                 |                |
   fC                fA                fC               fA
   v                 v                 v                v
H⁰(H, C') -δ⁰-> H¹(H, A')          H¹(H, C') -δ¹-> H²(H, A')
```

Taking `φ` to be the inclusion of a subgroup and the three coefficient maps to be the identity
gives naturality of `δ` under restriction, and taking `φ` to be the identity of `G` gives its
naturality in a morphism of short exact sequences. Inflation is the same square at the quotient
homomorphism `G → G ⧸ N`, but this file exports no inflation theorem: the invariants of a short
exact sequence need not be exact, so the sequence over `G ⧸ N` is data a caller supplies rather
than something constructible here, and inflation is left as a direct specialization of the two
general squares.

There is no compatible-pair map in degree zero to state the left-hand leg against: the
degree-zero carrier `H⁰(G, C) = C^G` has the two named maps `explicitRes0` and `explicitCoeff0`
and no general one. Only `explicitDelta0_naturality` is affected: it takes the image `c'` of the
invariant `c` as an argument, together with the hypothesis `(c' : C') = fC c` identifying it, and
so does not assume `fC` equivariant at all; each named degree-zero instance discharges that
hypothesis by the `coe_` lemma of its own degree-zero map. In degree one both legs are
compatible-pair maps, so `explicitDelta1_naturality` takes only the class `x : H¹(G, C)`.

Continuity of a coefficient map is never a hypothesis here: every module in sight is discrete.

Mathlib's discrete `groupCohomology.δ_naturality` is the corresponding statement for `Rep k G`; it
keeps the group fixed and varies only the short complex, so it covers the `explicitDelta0_coeffMap`
and `explicitDelta1_coeffMap` half and not the change of group.

## Main statements

* `TauCeti.ContCohomology.DiscreteShortExact.explicitDelta0_naturality` and
  `explicitDelta1_naturality`: the two squares above.
* `TauCeti.ContCohomology.DiscreteShortExact.explicitDelta0_res` and
  `explicitDelta1_res`: restriction to a subgroup commutes with the connecting maps.
* `TauCeti.ContCohomology.DiscreteShortExact.explicitDelta0_coeffMap` and
  `explicitDelta1_coeffMap`: a morphism of short exact sequences commutes with the connecting
  maps.

## Implementation notes

The named instances `explicitRes1`, `explicitRes2`, `explicitCoeff1` and `explicitCoeff2` are
definitions of `TauCeti/RepresentationTheory/Homological/ContCohomology/ExplicitFunctoriality.lean`
whose bodies are not exposed, so they are not definitionally the compatible-pair pullbacks the two
general squares are stated against. The four private lemmas at the head of this file identify them,
each by evaluating both sides on a cocycle class with the `_mk` lemmas that file exports.

This implements the naturality half of the long exact sequence milestone of Layer 5 of the
human-authored roadmap at `TauCetiRoadmap/ProfiniteCohomology/README.md`, whose `Suggested.lean`
fixes the names `explicitDelta0_res` and `explicitDelta1_res`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.3.2) and
  (1.5.2): the low-degree long exact sequence and the naturality of its connecting maps.
-/

public section

namespace TauCeti.ContCohomology

universe uG uH vA vB vC vA' vB' vC'

section NamedInstances

variable (G : Type uG) [Group G] [TopologicalSpace G]
  (M : Type vA) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M]
  {N : Type vA'} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]

/-- Restriction on `H¹` is the compatible-pair pullback along the subgroup inclusion. -/
private theorem explicitRes1_eq (T : Subgroup G) :
    explicitRes1 G M T = explicitMap1 G M T M (ContinuousMonoidHom.subgroupSubtype T)
      (AddMonoidHom.id M) continuous_of_discreteTopology (id_subgroupSubtype_smul G M T) := by
  refine AddMonoidHom.ext fun y => ?_
  induction y using QuotientAddGroup.induction_on with
  | _ c => rw [explicitRes1_mk, explicitMap1_mk]

/-- Restriction on `H²` is the compatible-pair pullback along the subgroup inclusion. -/
private theorem explicitRes2_eq (T : Subgroup G) [ContinuousMul G] [ContinuousMul T] :
    explicitRes2 G M T = explicitMap2 G M T M (ContinuousMonoidHom.subgroupSubtype T)
      (AddMonoidHom.id M) continuous_of_discreteTopology (id_subgroupSubtype_smul G M T) := by
  refine AddMonoidHom.ext fun y => ?_
  induction y using QuotientAddGroup.induction_on with
  | _ c => rw [explicitRes2_mk, explicitMap2_mk]

/-- A coefficient map on `H¹` is the compatible-pair pullback along the identity of `G`. -/
private theorem explicitCoeff1_eq (f : M →+[G] N) :
    explicitCoeff1 G M f continuous_of_discreteTopology =
      explicitMap1 G M G N (ContinuousMonoidHom.id G) (f : M →+ N)
        continuous_of_discreteTopology fun g m => f.map_smul g m := by
  refine AddMonoidHom.ext fun y => ?_
  induction y using QuotientAddGroup.induction_on with
  | _ c =>
      exact (explicitCoeff1_mk G M f continuous_of_discreteTopology c).trans
        (explicitMap1_mk G M G N _ _ _ _ c).symm

/-- A coefficient map on `H²` is the compatible-pair pullback along the identity of `G`. -/
private theorem explicitCoeff2_eq [ContinuousMul G] (f : M →+[G] N) :
    explicitCoeff2 G M f continuous_of_discreteTopology =
      explicitMap2 G M G N (ContinuousMonoidHom.id G) (f : M →+ N)
        continuous_of_discreteTopology fun g m => f.map_smul g m := by
  refine AddMonoidHom.ext fun y => ?_
  induction y using QuotientAddGroup.induction_on with
  | _ c =>
      exact (explicitCoeff2_mk G M f continuous_of_discreteTopology c).trans
        (explicitMap2_mk G M G N _ _ _ _ c).symm

end NamedInstances

namespace DiscreteShortExact

section Naturality

variable {G : Type uG} [Monoid G] [TopologicalSpace G]
  {H : Type uH} [Monoid H] [TopologicalSpace H]
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A]
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B] [ContinuousSMul G B]
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C]
  {A' : Type vA'} [AddCommGroup A'] [TopologicalSpace A'] [DiscreteTopology A']
    [DistribMulAction H A'] [ContinuousSMul H A']
  {B' : Type vB'} [AddCommGroup B'] [TopologicalSpace B'] [DiscreteTopology B']
    [DistribMulAction H B'] [ContinuousSMul H B']
  {C' : Type vC'} [AddCommGroup C'] [TopologicalSpace C'] [DiscreteTopology C']
    [DistribMulAction H C']
  (S : DiscreteShortExact G A B C) (S' : DiscreteShortExact H A' B' C')
  (φ : H →ₜ* G) (fA : A →+ A') (fB : B →+ B') (fC : C →+ C')

/-- **`δ⁰` is natural in compatible pairs.** For a continuous homomorphism `φ : H →ₜ* G` and
coefficient maps `fA` and `fB` equivariant along it and commuting with the two maps of the
sequences, the square

```text
H⁰(G, C) --δ⁰--> H¹(G, A)
   |                 |
 c ↦ c'              fA
   v                 v
H⁰(H, C') -δ⁰-> H¹(H, A')
```

commutes. Degree zero carries no general compatible-pair map, so the left-hand leg is not `fC` but
an invariant `c'` of `C'` supplied together with the relation `(c' : C') = fC c`. Only `fA` and
`fB` are assumed equivariant; `fC` enters through that relation alone. -/
theorem explicitDelta0_naturality
    (hfA : ∀ (h : H) (a : A), fA (φ h • a) = h • fA a)
    (hfB : ∀ (h : H) (b : B), fB (φ h • b) = h • fB b)
    (hincl : ∀ a : A, fB (S.incl a) = S'.incl (fA a))
    (hproj : ∀ b : B, fC (S.proj b) = S'.proj (fB b))
    (c : H0 G C) (c' : H0 H C') (hc : (c' : C') = fC (c : C)) :
    explicitMap1 G A H A' φ fA continuous_of_discreteTopology hfA (S.explicitDelta0 c) =
      S'.explicitDelta0 c' := by
  obtain ⟨b, hb⟩ := S.proj_surjective (c : C)
  have hbmem : S.proj b ∈ H0 G C := hb ▸ c.2
  obtain ⟨a, -, hai⟩ :=
    S.exists_continuous_incl_comp_eq (continuous_d0_apply (G := G) b) (proj_d0_eq_zero hbmem)
  have hai' : ∀ g : G, S.incl (a g) = g • b - b := fun g => (hai g).trans (d0_apply b g)
  have ha : a ∈ Z1 G A := S.mem_Z1_of_incl_comp_eq_d0 hai'
  have hpush : ∀ h : H, S'.incl (fA (a (φ h))) = h • fB b - fB b := fun h => by
    rw [← hincl, hai' (φ h), map_sub, hfB]
  have ha' : (fun h : H => fA (a (φ h))) ∈ Z1 H A' := S'.mem_Z1_of_incl_comp_eq_d0 hpush
  rw [S.explicitDelta0_apply c hb ha hai',
    S'.explicitDelta0_apply c' (b := fB b) (by rw [← hproj, hb, hc]) ha' hpush,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, explicitMap1_mk]
  exact congrArg (fun z : Z1 H A' => (z : H1 H A')) (Subtype.ext (by ext h; simp))

/-- **`δ¹` is natural in compatible pairs**, the degree-one counterpart of
`TauCeti.ContCohomology.DiscreteShortExact.explicitDelta0_naturality`. Both legs are
compatible-pair pullbacks here, `explicitMap1` on the source and `explicitMap2` on the target. -/
theorem explicitDelta1_naturality [ContinuousMul G] [ContinuousMul H]
    [ContinuousSMul G C] [ContinuousSMul H C']
    (hfA : ∀ (h : H) (a : A), fA (φ h • a) = h • fA a)
    (hfB : ∀ (h : H) (b : B), fB (φ h • b) = h • fB b)
    (hfC : ∀ (h : H) (x : C), fC (φ h • x) = h • fC x)
    (hincl : ∀ a : A, fB (S.incl a) = S'.incl (fA a))
    (hproj : ∀ b : B, fC (S.proj b) = S'.proj (fB b))
    (x : H1 G C) :
    explicitMap2 G A H A' φ fA continuous_of_discreteTopology hfA (S.explicitDelta1 x) =
      S'.explicitDelta1
        (explicitMap1 G C H C' φ fC continuous_of_discreteTopology hfC x) := by
  induction x using QuotientAddGroup.induction_on with
  | _ f =>
    obtain ⟨e, hecont, he⟩ := exists_continuous_lift S.proj_surjective (mem_Z1_iff.1 f.2).1
    have hf1 : groupCohomology.IsCocycle₁ (f : G → C) := (mem_Z1_iff.1 f.2).2
    obtain ⟨a, -, hai⟩ := S.exists_continuous_incl_comp_eq (X := G × G)
      (continuous_d1_apply hecont) (proj_d1_eq_zero he hf1)
    have hai' : ∀ g h : G, S.incl (a (g, h)) = g • e h - e (g * h) + e g := fun g h => by
      rw [hai (g, h), d1_apply]
    have ha : a ∈ Z2 G A := S.mem_Z2_of_incl_comp_eq_d1 hecont hai'
    -- The lift of the pushed-forward cocycle is the pushed-forward lift.
    have hecont' : Continuous fun h : H => fB (e (φ h)) :=
      continuous_of_discreteTopology.comp (hecont.comp φ.continuous)
    have hpush : ∀ h k : H, S'.incl (fA (a (φ h, φ k))) =
        h • fB (e (φ k)) - fB (e (φ (h * k))) + fB (e (φ h)) := fun h k => by
      rw [map_mul φ, ← hincl, hai' (φ h) (φ k), map_add, map_sub, hfB]
    have ha' : (fun p : H × H => fA (a (φ p.1, φ p.2))) ∈ Z2 H A' :=
      S'.mem_Z2_of_incl_comp_eq_d1 hecont' hpush
    have hleft := S.explicitDelta1_apply f hecont he ha hai'
    have hright := S'.explicitDelta1_apply
      (cocyclesMap1 G C H C' φ fC continuous_of_discreteTopology hfC f) hecont'
      (fun h => by rw [cocyclesMap1_apply, ← hproj, he]) ha' hpush
    -- Both descriptions are stated against `H1pi`/`H2pi`, the goal against the quotient
    -- coercion; `mk'_apply` is the identification of the two spellings.
    simp only [QuotientAddGroup.mk'_apply] at hleft hright
    rw [hleft, explicitMap1_mk, hright, explicitMap2_mk]
    exact congrArg (fun z : Z2 H A' => (z : H2 H A')) (Subtype.ext (by ext ⟨h, k⟩; simp))

end Naturality

section Restriction

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A]
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B] [ContinuousSMul G B]
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C]
  (S : DiscreteShortExact G A B C) (T : Subgroup G)

/-- **Restriction commutes with `δ⁰`.** The compatible pair is the inclusion of `T` together with
the identity on the coefficients, and the sequence over `T` is
`TauCeti.ContCohomology.DiscreteShortExact.restrict`. -/
@[simp]
theorem explicitDelta0_res (c : H0 G C) :
    explicitRes1 G A T (S.explicitDelta0 c) =
      (S.restrict T).explicitDelta0 (explicitRes0 G C T c) := by
  rw [explicitRes1_eq]
  exact S.explicitDelta0_naturality (S.restrict T) (ContinuousMonoidHom.subgroupSubtype T)
    (AddMonoidHom.id A) (AddMonoidHom.id B) (AddMonoidHom.id C)
    (id_subgroupSubtype_smul G A T) (id_subgroupSubtype_smul G B T) (fun _ => by simp)
    (fun _ => by simp) c _ (by simp)

/-- **Restriction commutes with `δ¹`**, the degree-one counterpart of
`TauCeti.ContCohomology.DiscreteShortExact.explicitDelta0_res`. -/
@[simp]
theorem explicitDelta1_res [ContinuousMul G] [ContinuousMul T] [ContinuousSMul G C]
    (x : H1 G C) :
    explicitRes2 G A T (S.explicitDelta1 x) =
      (S.restrict T).explicitDelta1 (explicitRes1 G C T x) := by
  rw [explicitRes2_eq, explicitRes1_eq]
  exact S.explicitDelta1_naturality (S.restrict T) (ContinuousMonoidHom.subgroupSubtype T)
    (AddMonoidHom.id A) (AddMonoidHom.id B) (AddMonoidHom.id C)
    (id_subgroupSubtype_smul G A T) (id_subgroupSubtype_smul G B T)
    (id_subgroupSubtype_smul G C T) (fun _ => by simp) (fun _ => by simp) x

end Restriction

section CoefficientMaps

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A]
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B] [ContinuousSMul G B]
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C]
  {A' : Type vA'} [AddCommGroup A'] [TopologicalSpace A'] [DiscreteTopology A']
    [DistribMulAction G A'] [ContinuousSMul G A']
  {B' : Type vB'} [AddCommGroup B'] [TopologicalSpace B'] [DiscreteTopology B']
    [DistribMulAction G B'] [ContinuousSMul G B']
  {C' : Type vC'} [AddCommGroup C'] [TopologicalSpace C'] [DiscreteTopology C']
    [DistribMulAction G C']
  (S : DiscreteShortExact G A B C) (S' : DiscreteShortExact G A' B' C')
  (fA : A →+[G] A') (fB : B →+[G] B') (fC : C →+[G] C')

/-- **A morphism of short exact sequences commutes with `δ⁰`.** This is
`TauCeti.ContCohomology.DiscreteShortExact.explicitDelta0_naturality` at the identity
homomorphism of `G`, where the two legs of the square are the named coefficient maps. -/
theorem explicitDelta0_coeffMap
    (hincl : ∀ a : A, fB (S.incl a) = S'.incl (fA a))
    (hproj : ∀ b : B, fC (S.proj b) = S'.proj (fB b))
    (c : H0 G C) :
    explicitCoeff1 G A fA continuous_of_discreteTopology (S.explicitDelta0 c) =
      S'.explicitDelta0 (explicitCoeff0 G C fC c) := by
  rw [explicitCoeff1_eq]
  exact S.explicitDelta0_naturality S' (ContinuousMonoidHom.id G) (fA : A →+ A')
    (fB : B →+ B') (fC : C →+ C') (fun g a => fA.map_smul g a)
    (fun g b => fB.map_smul g b) hincl hproj c _ (by simp)

/-- **A morphism of short exact sequences commutes with `δ¹`**, the degree-one counterpart of
`TauCeti.ContCohomology.DiscreteShortExact.explicitDelta0_coeffMap`. -/
theorem explicitDelta1_coeffMap [ContinuousMul G] [ContinuousSMul G C] [ContinuousSMul G C']
    (hincl : ∀ a : A, fB (S.incl a) = S'.incl (fA a))
    (hproj : ∀ b : B, fC (S.proj b) = S'.proj (fB b))
    (x : H1 G C) :
    explicitCoeff2 G A fA continuous_of_discreteTopology (S.explicitDelta1 x) =
      S'.explicitDelta1 (explicitCoeff1 G C fC continuous_of_discreteTopology x) := by
  rw [explicitCoeff2_eq, explicitCoeff1_eq]
  exact S.explicitDelta1_naturality S' (ContinuousMonoidHom.id G) (fA : A →+ A')
    (fB : B →+ B') (fC : C →+ C') (fun g a => fA.map_smul g a)
    (fun g b => fB.map_smul g b) (fun g y => fC.map_smul g y) hincl hproj x

end CoefficientMaps

end DiscreteShortExact

end TauCeti.ContCohomology
