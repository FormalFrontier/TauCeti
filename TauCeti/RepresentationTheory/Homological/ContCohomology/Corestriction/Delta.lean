/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ShortExact

/-!
# Corestriction commutes with the degree-zero connecting map

Let `0 → A → B → C → 0` be a short exact sequence of discrete modules over a topological group `G`
and let `U ≤ G` be an open subgroup of finite index. Corestriction and the connecting map of the
long exact sequence commute:

```text
H⁰(U, C) --δ⁰--> H¹(U, A)
   |                 |
  cor⁰              cor¹
   v                 v
H⁰(G, C) --δ⁰--> H¹(G, A)
```

This is `TauCeti.ContCohomology.DiscreteShortExact.explicitCor_delta0`, the degree-zero half of the
`cor ∘ δ = δ ∘ cor` identity of Neukirch--Schmidt--Wingberg (1.5.2).

The square commutes already on cochains, and that is how it is proved. Choose a preimage `b ∈ B` of
an invariant `c ∈ C^U`, so that `x ↦ x • b - b` takes its values in the image of `A` and lifts to a
cochain `a : U → A` representing `δ⁰ c`. Then `TauCeti.ContCohomology.map_cochainsCor1` followed by
`TauCeti.ContCohomology.cochainsCor1_d0` gives

```text
incl ((cor¹_t a) γ) = (cor¹_t (d⁰ b)) γ = γ • (∑ u, t u • b) - (∑ u, t u • b),
```

so the cochain `cor¹_t a` lies under the coboundary of the norm `∑ u, t u • b`, which is a preimage
of `cor⁰_t c`. Both descriptions of `δ⁰` on representatives then identify the two sides. No
reindexing is done here: the translation `∑ u, t u • b ↦ γ • ∑ u, t u • b` that the identity needs
is exactly the content of the already merged `cochainsCor1_d0`, and the representative factor
`t u •` is carried throughout.

As everywhere in this directory the transversal is kept variable first
(`explicitCorTransversal_delta0`) and the public statement is its specialization at
`Quotient.out`; the two are related by the transversal independence already proved in
`Corestriction/Basic.lean`, not by a second argument.

The degree-one half `cor² ∘ δ¹ = δ¹ ∘ cor¹` is not stated here: it needs corestriction in degree
two, which the explicit model does not yet have.

## Main statements

* `TauCeti.ContCohomology.DiscreteShortExact.explicitCorTransversal_delta0`: the commuting square
  for a variable transversal.
* `TauCeti.ContCohomology.DiscreteShortExact.explicitCor_delta0`: the commuting square for the
  canonical corestrictions.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.2): the
  compatibility of corestriction with the connecting maps of the long exact sequence.
-/

public section

namespace TauCeti.ContCohomology

universe u vA vB vC

namespace DiscreteShortExact

section Delta0

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G]
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A]
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B] [ContinuousSMul G B]
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C]
  (S : DiscreteShortExact G A B C) (U : Subgroup G) [U.FiniteIndex]
  (t : G ⧸ U → G) (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)
  (hU : IsOpen (U : Set G))

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **Corestriction commutes with `δ⁰`, for a variable transversal.** The two composites
`H⁰(U, C) → H¹(G, A)` agree, the corestriction of a cochain representing `δ⁰` over `U` being a
cochain representing `δ⁰` over `G` at the norm of the chosen preimage. -/
theorem explicitCorTransversal_delta0 (c : H0 U C) :
    explicitCor1Transversal G A U t ht hU ((S.restrict U).explicitDelta0 c) =
      S.explicitDelta0 (explicitCor0Transversal G C U t ht c) := by
  obtain ⟨b, hb⟩ := S.proj_surjective (c : C)
  have hbU : (S.restrict U).proj b = (c : C) := by rw [restrict_proj]; exact hb
  -- A cochain on `U` lying under `d⁰ b` represents `δ⁰ c` over `U`.
  obtain ⟨a, -, haincl⟩ := (S.restrict U).exists_continuous_incl_comp_eq
    (continuous_d0_apply (G := U) b) ((S.restrict U).proj_d0_eq_zero (hbU ▸ c.2))
  have hab : ∀ x : U, (S.restrict U).incl (a x) = x • b - b :=
    fun x => (haincl x).trans (d0_apply b x)
  have ha : a ∈ Z1 U A := (S.restrict U).mem_Z1_of_incl_comp_eq_d0 hab
  have hcor : cochainsCor1 G A U t ht a ∈ Z1 G A := cochainsCor1_mem_Z1 G A U t ht hU ha
  -- The norm of the chosen preimage is a preimage of the corestricted invariant.
  have hproj : S.proj (∑ u : G ⧸ U, t u • b) = (explicitCor0Transversal G C U t ht c : C) := by
    rw [coe_explicitCor0Transversal, map_sum]
    exact Finset.sum_congr rfl fun u _ => by rw [S.proj_equivariant, hb]
  -- The corestricted cochain lies under the coboundary of that norm.
  have hd : (fun x : U => S.incl (a x)) = d0 U B b :=
    funext fun x => by rw [← S.restrict_incl U, d0_apply]; exact hab x
  have hincl : ∀ γ : G, S.incl (cochainsCor1 G A U t ht a γ) =
      γ • (∑ u : G ⧸ U, t u • b) - ∑ u : G ⧸ U, t u • b := fun γ => by
    rw [map_cochainsCor1 G A U t ht S.incl S.incl_equivariant a γ, hd, cochainsCor1_d0, d0_apply]
  have hleft : explicitCor1Transversal G A U t ht hU ((S.restrict U).explicitDelta0 c) =
      H1pi G A ⟨cochainsCor1 G A U t ht a, hcor⟩ := by
    rw [(S.restrict U).explicitDelta0_apply c hbU ha hab]
    refine (explicitCor1Transversal_mk G A U t ht hU ⟨a, ha⟩).trans ?_
    exact congrArg (H1pi G A) (Subtype.ext (coe_cocyclesCor1 G A U t ht hU ⟨a, ha⟩))
  exact hleft.trans (S.explicitDelta0_apply _ hproj hcor hincl).symm

/-- **Corestriction commutes with `δ⁰`.** For a short exact sequence of discrete `G`-modules and an
open subgroup `U` of finite index, `cor¹ ∘ δ⁰ = δ⁰ ∘ cor⁰` as maps `H⁰(U, C) → H¹(G, A)`, the
connecting map on the left being that of the restricted sequence
`TauCeti.ContCohomology.DiscreteShortExact.restrict`. This is
Neukirch--Schmidt--Wingberg (1.5.2) in degree zero. -/
theorem explicitCor_delta0 (c : H0 U C) :
    explicitCor1 G A U hU ((S.restrict U).explicitDelta0 c) =
      S.explicitDelta0 (explicitCor0 G C U c) := by
  rw [explicitCor1_eq_transversal G A U Quotient.out Quotient.out_eq hU,
    explicitCor0_eq_transversal G C U Quotient.out Quotient.out_eq]
  exact S.explicitCorTransversal_delta0 U Quotient.out Quotient.out_eq hU c

end Delta0

end DiscreteShortExact

end TauCeti.ContCohomology
