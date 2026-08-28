/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CupProduct

/-!
# The projection formula for the explicit low-degree cup products

The corestriction of a finite-index subgroup `U ≤ G` is not linear over the cohomology of `G`, but
it is a map of modules over it: restricting a class of `G` to `U`, cupping there, and corestricting
back is the same as cupping with the corestricted class. That is the **projection formula**

```text
cor (res a ⌣ b) = a ⌣ cor b,        cor (b ⌣ res n) = cor b ⌣ n,
```

proved here in all six low-degree shapes.

In the five shapes with a degree-`0` factor that factor is invariant, so partial application of the
pairing at it is an *equivariant* additive map — `TauCeti.ContCohomology.pairingLeft` in the first
display and `TauCeti.ContCohomology.pairingRight` in the second — and the cup with a degree-`0`
class is the coefficient map that equivariant map induces. In positive degrees the projection
formula is therefore exactly naturality of the corestriction cochain in an equivariant coefficient
map, `TauCeti.ContCohomology.map_cochainsCor1` and `map_cochainsCor2`, and in those five shapes it
holds already on cochains, with no coboundary correction. Those two cochain identities are stated
for a variable transversal, so the statements below transport to any other transversal through
`TauCeti.ContCohomology.explicitCor1_eq_transversal` and `explicitCor2_eq_transversal`. In the
`(1,0)` and `(2,0)` shapes
the translation factors `g •` and `(g * h) •` of the cup formula are absorbed by the invariance of
the degree-`0` factor before that naturality is applied; in degree `0` the same absorption is
`TauCeti.ContCohomology.pairingLeft_smul` applied to each summand of the norm.

The `(1,1)` shape, the one shape of the six without a degree-`0` factor, is the one shape where
the two sides do *not* agree on cochains: the degree-two corestriction pairs the transversal word
of the first variable with the *translated* transversal word of the second, so the two sides
differ by a coboundary. That coboundary is exhibited by the explicit `1`-cochain
`TauCeti.ContCohomology.cup11ProjectionHomotopy`,

```text
kᵗ(γ) = ∑ u : G ⧸ U, μ (a (t u)) (t u • b (ℓᵗ_u γ)),
```

whose `d¹` is the difference of the two sides
(`TauCeti.ContCohomology.cup11ProjectionHomotopy_spec`); the identity on classes follows.

## Main statements

* `TauCeti.ContCohomology.explicitCup_projection`: the `(0,1)` shape
  `cor¹ (res⁰ a ⌣ b) = a ⌣ cor¹ b`. The roadmap's `Suggested.lean` fixes the unsuffixed name for
  this shape, which is why the five companions below carry their bidegree and this one does not.
* `TauCeti.ContCohomology.explicitCup_projection00`,
  `TauCeti.ContCohomology.explicitCup_projection10`,
  `TauCeti.ContCohomology.explicitCup_projection02` and
  `TauCeti.ContCohomology.explicitCup_projection20`: the same identity in the four remaining
  low-degree shapes with a degree-`0` factor.
* `TauCeti.ContCohomology.explicitCup_projection11`: the `(1,1)` shape
  `cor² (res¹ a ⌣ b) = a ⌣ cor¹ b`, deduced from
  `TauCeti.ContCohomology.cup11ProjectionHomotopy_spec`.

This implements the projection-formula item of the "compatibilities" milestone of Layer 8 of the
human-authored roadmap at `TauCetiRoadmap/ProfiniteCohomology/README.md`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.3)(iv): the
  projection formula for the cup product and the corestriction.
* L. Ribes, P. Zalesskii, *Profinite Groups*, 2nd ed., 7.9.6 and 7.9.7.
* K. Brown, *Cohomology of Groups*, V (3.8).
-/

public section

namespace TauCeti.ContCohomology

universe u v w x

section DegreeZero

/-! ### The degree-zero shape

`H⁰` is a subgroup and not a quotient, so neither a topology on `G` nor continuity of the pairing
is involved. -/

variable (G : Type u) [Group G]
  (M : Type v) [AddCommGroup M] [DistribMulAction G M]
  (N : Type w) [AddCommGroup N] [DistribMulAction G N]
  (P : Type x) [AddCommGroup P] [DistribMulAction G P]
  (U : Subgroup G) [U.FiniteIndex]
  (μ : M →+ N →+ P)
  (hequiv : ∀ (g : G) (m : M) (y : N), μ (g • m) (g • y) = g • μ m y)

/-- **The `(0,0)` projection formula**, `cor⁰ (res⁰ a ⌣ n) = a ⌣ cor⁰ n`: the norm of a pairing
with a `G`-invariant first argument is that pairing applied to the norm. The whole content is that
the transversal factors cross the pairing, which is
`TauCeti.ContCohomology.pairingLeft_smul`. -/
theorem explicitCup_projection00 (a : H0 G M) (n : H0 U N) :
    explicitCor0 G P U
        (explicitCup00 U M N P μ (fun g m y => hequiv (g : G) m y) (explicitRes0 G M U a) n) =
      explicitCup00 G M N P μ hequiv a (explicitCor0 G N U n) := by
  refine Subtype.ext ?_
  simp only [coe_explicitCor0, coe_explicitCup00, coe_explicitRes0]
  rw [map_sum]
  exact Finset.sum_congr rfl fun u _ => (pairingLeft_smul μ hequiv a _ _).symm

end DegreeZero

section DegreeOne

/-! ### The degree-one shapes

Openness of `U` enters exactly as in `TauCeti.ContCohomology.explicitCor1`: it is what makes the
corestriction of a continuous cochain continuous. -/

variable (G : Type u) [Group G] [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type w) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type x) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (y : N), μ (g • m) (g • y) = g • μ m y)

include hU hμ hequiv

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- **The `(0,1)` projection formula**, `cor¹ (res⁰ a ⌣ b) = a ⌣ cor¹ b` for an open subgroup `U`
of finite index. The roadmap's `Suggested.lean` fixes the name `explicitCup_projection` for this
shape, and it fixes the normalization of the four companion shapes. -/
theorem explicitCup_projection (a : H0 G M) (b : H1 U N) :
    explicitCor1 G P U hU
        (explicitCup01 U M N P μ hμ (fun g m y => hequiv (g : G) m y)
          (explicitRes0 G M U a) b) =
      explicitCup01 G M N P μ hμ hequiv a (explicitCor1 G N U hU b) := by
  -- Replace `res⁰ a` by an element whose underlying coefficient is literally `a`, so that the
  -- cup cochains on the two sides are pairings against the same element of `M`.
  have hres : explicitRes0 G M U a = ⟨(a : M), fun g : U => a.2 (g : G)⟩ :=
    Subtype.ext (coe_explicitRes0 G M U a)
  induction b using QuotientAddGroup.induction_on with
  | _ c =>
    rw [hres, explicitCup01_mk, explicitCor1_mk, explicitCor1_mk, explicitCup01_mk]
    refine congrArg (fun z : Z1 G P => (z : H1 G P)) (Subtype.ext ?_)
    simp only [coe_cocyclesCor1]
    funext γ
    exact (map_cochainsCor1 G N U Quotient.out Quotient.out_eq (μ (a : M))
      (fun g y => pairingLeft_smul μ hequiv a g y) (c : U → N) γ).symm

omit [IsTopologicalAddGroup N] [ContinuousSMul G N] in
/-- **The `(1,0)` projection formula**, `cor¹ (b ⌣ res⁰ n) = cor¹ b ⌣ n`. The translation factors
of the `(1,0)` cochain formula act trivially on the invariant `n`, which is what leaves a plain
naturality statement behind. -/
theorem explicitCup_projection10 (b : H1 U M) (n : H0 G N) :
    explicitCor1 G P U hU
        (explicitCup10 U M N P μ hμ (fun g m y => hequiv (g : G) m y) b
          (explicitRes0 G N U n)) =
      explicitCup10 G M N P μ hμ hequiv (explicitCor1 G M U hU b) n := by
  have hn : ∀ g : G, g • (n : N) = (n : N) := n.2
  have hres : explicitRes0 G N U n = ⟨(n : N), fun g : U => n.2 (g : G)⟩ :=
    Subtype.ext (coe_explicitRes0 G N U n)
  induction b using QuotientAddGroup.induction_on with
  | _ c =>
    rw [hres, explicitCup10_mk, explicitCor1_mk, explicitCor1_mk, explicitCup10_mk]
    refine congrArg (fun z : Z1 G P => (z : H1 G P)) (Subtype.ext ?_)
    simp only [coe_cocyclesCor1, Subgroup.smul_def, hn]
    funext γ
    have key := map_cochainsCor1 G M U Quotient.out Quotient.out_eq (μ.flip (n : N))
      (fun g m => pairingRight_smul μ hequiv n g m) (c : U → M) γ
    simp only [AddMonoidHom.flip_apply] at key
    exact key.symm

end DegreeOne

section DegreeTwo

/-! ### The degree-two shapes

The `2`-cochains of the subgroup are functions on `U × U`, so the cup products over `U` need `U`
to be a topological group; that is where `[IsTopologicalGroup G]` replaces the weaker pair of
hypotheses carried in degree one. -/

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type w) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type x) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (y : N), μ (g • m) (g • y) = g • μ m y)

include hU hμ hequiv

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- **The `(0,2)` projection formula**, `cor² (res⁰ a ⌣ b) = a ⌣ cor² b`. -/
theorem explicitCup_projection02 (a : H0 G M) (b : H2 U N) :
    explicitCor2 G P U hU
        (explicitCup02 U M N P μ hμ (fun g m y => hequiv (g : G) m y)
          (explicitRes0 G M U a) b) =
      explicitCup02 G M N P μ hμ hequiv a (explicitCor2 G N U hU b) := by
  have hres : explicitRes0 G M U a = ⟨(a : M), fun g : U => a.2 (g : G)⟩ :=
    Subtype.ext (coe_explicitRes0 G M U a)
  induction b using QuotientAddGroup.induction_on with
  | _ c =>
    rw [hres, explicitCup02_mk, explicitCor2_mk, explicitCor2_mk, explicitCup02_mk]
    refine congrArg (fun z : Z2 G P => (z : H2 G P)) (Subtype.ext ?_)
    simp only [coe_cocyclesCor2]
    funext q
    obtain ⟨γ, η⟩ := q
    exact (map_cochainsCor2 G N U Quotient.out Quotient.out_eq (μ (a : M))
      (fun g y => pairingLeft_smul μ hequiv a g y) (c : U × U → N) γ η).symm

omit [IsTopologicalAddGroup N] [ContinuousSMul G N] in
/-- **The `(2,0)` projection formula**, `cor² (b ⌣ res⁰ n) = cor² b ⌣ n`. -/
theorem explicitCup_projection20 (b : H2 U M) (n : H0 G N) :
    explicitCor2 G P U hU
        (explicitCup20 U M N P μ hμ (fun g m y => hequiv (g : G) m y) b
          (explicitRes0 G N U n)) =
      explicitCup20 G M N P μ hμ hequiv (explicitCor2 G M U hU b) n := by
  have hn : ∀ g : G, g • (n : N) = (n : N) := n.2
  have hres : explicitRes0 G N U n = ⟨(n : N), fun g : U => n.2 (g : G)⟩ :=
    Subtype.ext (coe_explicitRes0 G N U n)
  induction b using QuotientAddGroup.induction_on with
  | _ c =>
    rw [hres, explicitCup20_mk, explicitCor2_mk, explicitCor2_mk, explicitCup20_mk]
    refine congrArg (fun z : Z2 G P => (z : H2 G P)) (Subtype.ext ?_)
    simp only [coe_cocyclesCor2, Subgroup.smul_def, hn]
    funext q
    obtain ⟨γ, η⟩ := q
    have key := map_cochainsCor2 G M U Quotient.out Quotient.out_eq (μ.flip (n : N))
      (fun g m => pairingRight_smul μ hequiv n g m) (c : U × U → M) γ η
    simp only [AddMonoidHom.flip_apply] at key
    exact key.symm

end DegreeTwo

section CupOneOneHomotopy

/-! ### The `(1,1)` homotopy

The `(1,1)` shape is the one shape of the six in which neither factor is invariant, and the two
sides of the projection formula are genuinely different cochains. Their difference is a
coboundary, and this section writes down a primitive for it. Nothing here needs a topology: the
identity `TauCeti.ContCohomology.cup11ProjectionHomotopy_spec` is an identity of plain cochains,
just like the corestriction cochain identities it is proved from. -/

variable (G : Type u) [Group G]
  (M : Type v) [AddCommGroup M] [DistribMulAction G M]
  (N : Type w) [AddCommGroup N] [DistribMulAction G N]
  (P : Type x) [AddCommGroup P] [DistribMulAction G P]
  (U : Subgroup G) [U.FiniteIndex]
  (μ : M →+ N →+ P)
  (t : G ⧸ U → G) (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **The `(1,1)` projection-formula homotopy** for a transversal `t`,

```text
kᵗ(γ) = ∑ u : G ⧸ U, μ (α (t u)) (t u • β (ℓᵗ_u γ)),
```

where `ℓᵗ` is the transversal word `TauCeti.lWord`. It is the corestriction sum of the pairing of
`α` against `β`, evaluated at the transversal representatives in the first variable and at the
transversal words in the second. Its `d¹` is the difference of the two sides of the `(1,1)`
projection formula, `TauCeti.ContCohomology.cup11ProjectionHomotopy_spec`. -/
noncomputable def cup11ProjectionHomotopy (α : G → M) (β : U → N) (γ : G) : P :=
  ∑ u : G ⧸ U, μ (α (t u)) (t u • β ⟨lWord U t u γ, lWord_mem U t ht u γ⟩)

omit [DistribMulAction G M] [DistribMulAction G P] in
/-- The defining formula for the `(1,1)` projection-formula homotopy. -/
@[simp]
theorem cup11ProjectionHomotopy_apply (α : G → M) (β : U → N) (γ : G) :
    cup11ProjectionHomotopy G M N P U μ t ht α β γ =
      ∑ u : G ⧸ U, μ (α (t u)) (t u • β ⟨lWord U t u γ, lWord_mem U t ht u γ⟩) := (rfl)

/-- **The `(1,1)` projection formula on cochains, up to the explicit coboundary.** For a `1`-cocycle
`α` of `G` and a `1`-cocycle `β` of `U`, the difference between the corestriction of the cup of
`α|_U` with `β` and the cup of `α` with the corestriction of `β` is `d¹` of
`TauCeti.ContCohomology.cup11ProjectionHomotopy`.

The whole content is the transversal identity `TauCeti.transversal_smul_mul_lWord`, applied twice:
once to move the factor `t u •` of the corestriction across the pairing on the left-hand side, and
once, through the cocycle law for `α`, to turn the value `t (γ • u) • α (ℓᵗ_{γ • u} γ)` that
appears there into `γ • α (t u) - α (t (γ • u)) + α γ`. The first two of those three terms are
what `d¹` of the homotopy contributes and the third is the right-hand side. -/
theorem cup11ProjectionHomotopy_spec
    (hequiv : ∀ (g : G) (m : M) (y : N), μ (g • m) (g • y) = g • μ m y)
    {α : G → M} (hα : groupCohomology.IsCocycle₁ α)
    {β : U → N} (hβ : groupCohomology.IsCocycle₁ β) (γ η : G) :
    γ • cup11ProjectionHomotopy G M N P U μ t ht α β η -
        cup11ProjectionHomotopy G M N P U μ t ht α β (γ * η) +
        cup11ProjectionHomotopy G M N P U μ t ht α β γ =
      cochainsCor2 G P U t ht (fun q : U × U => μ (α (q.1 : G)) ((q.1 : G) • β q.2)) (γ, η) -
        μ (α γ) (γ • cochainsCor1 G N U t ht β η) := by
  -- The four sums below are all indexed so that their second pairing argument is
  -- `(γ * t u) • β (ℓᵗ_u η)`; only the first argument differs.
  have h1 : γ • cup11ProjectionHomotopy G M N P U μ t ht α β η =
      ∑ u : G ⧸ U, μ (γ • α (t u))
        ((γ * t u) • β ⟨lWord U t u η, lWord_mem U t ht u η⟩) := by
    rw [cup11ProjectionHomotopy_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun u _ => by rw [← hequiv, mul_smul]
  have h2 : cup11ProjectionHomotopy G M N P U μ t ht α β (γ * η) =
      cup11ProjectionHomotopy G M N P U μ t ht α β γ +
        ∑ u : G ⧸ U, μ (α (t (γ • u)))
          ((γ * t u) • β ⟨lWord U t u η, lWord_mem U t ht u η⟩) := by
    have hsplit : ∀ u : G ⧸ U,
        μ (α (t u)) (t u • β ⟨lWord U t u (γ * η), lWord_mem U t ht u (γ * η)⟩) =
          μ (α (t u)) (t u • β ⟨lWord U t u γ, lWord_mem U t ht u γ⟩) +
            μ (α (t u)) ((γ * t (γ⁻¹ • u)) •
              β ⟨lWord U t (γ⁻¹ • u) η, lWord_mem U t ht (γ⁻¹ • u) η⟩) := by
      intro u
      have hmul : (⟨lWord U t u γ, lWord_mem U t ht u γ⟩ : U) *
          ⟨lWord U t (γ⁻¹ • u) η, lWord_mem U t ht (γ⁻¹ • u) η⟩ =
            ⟨lWord U t u (γ * η), lWord_mem U t ht u (γ * η)⟩ :=
        Subtype.ext (lWord_mul_lWord U t u γ η)
      rw [← hmul, hβ, Subgroup.smul_def, smul_add, smul_smul, transversal_mul_lWord, map_add]
      abel
    rw [cup11ProjectionHomotopy_apply, cup11ProjectionHomotopy_apply,
      Finset.sum_congr rfl fun u _ => hsplit u, Finset.sum_add_distrib]
    refine congrArg _ (Fintype.sum_equiv (MulAction.toPerm γ) _ _ fun u => ?_).symm
    simp only [MulAction.toPerm_apply, inv_smul_smul]
  -- The cocycle law for `α` at the factorization `t (γ • u) * ℓᵗ_{γ • u}(γ) = γ * t u`.
  have hkey : ∀ u : G ⧸ U, t (γ • u) • α (lWord U t (γ • u) γ) =
      γ • α (t u) - α (t (γ • u)) + α γ := by
    intro u
    have h := hα (t (γ • u)) (lWord U t (γ • u) γ)
    rw [transversal_smul_mul_lWord, hα γ (t u)] at h
    have h' : t (γ • u) • α (lWord U t (γ • u) γ) = γ • α (t u) + α γ - α (t (γ • u)) := by
      rw [h]; abel
    rw [h']; abel
  have h3 : cochainsCor2 G P U t ht
      (fun q : U × U => μ (α (q.1 : G)) ((q.1 : G) • β q.2)) (γ, η) =
        ∑ u : G ⧸ U, μ (γ • α (t u) - α (t (γ • u)) + α γ)
          ((γ * t u) • β ⟨lWord U t u η, lWord_mem U t ht u η⟩) := by
    rw [cochainsCor2_apply]
    refine (Fintype.sum_equiv (MulAction.toPerm γ) _ _ fun u => ?_).symm
    rw [← hkey u]
    simp only [MulAction.toPerm_apply, inv_smul_smul]
    rw [← hequiv, smul_smul, transversal_smul_mul_lWord]
  have h4 : μ (α γ) (γ • cochainsCor1 G N U t ht β η) =
      ∑ u : G ⧸ U, μ (α γ) ((γ * t u) • β ⟨lWord U t u η, lWord_mem U t ht u η⟩) := by
    rw [cochainsCor1_apply, Finset.smul_sum, map_sum]
    exact Finset.sum_congr rfl fun u _ => by rw [mul_smul]
  rw [h1, h2, h3, h4]
  simp only [map_sub, map_add, AddMonoidHom.sub_apply, AddMonoidHom.add_apply,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

end CupOneOneHomotopy

section CupOneOne

/-! ### The `(1,1)` shape

Continuity of the homotopy is what makes it a primitive in `B²`, which is the image of the
*continuous* `1`-cochains, and it comes — as everywhere in this file — from openness of `U`
through `TauCeti.continuous_lWord`. -/

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type w) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type x) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (t : G ⧸ U → G) (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

include hU hμ

omit [IsTopologicalAddGroup M] [DistribMulAction G M] [ContinuousSMul G M]
  [IsTopologicalAddGroup N] [DistribMulAction G P] [ContinuousSMul G P] in
/-- The `(1,1)` projection-formula homotopy of continuous data is continuous. As for the
corestriction cochains themselves, no continuity is required of the transversal `t`. -/
theorem continuous_cup11ProjectionHomotopy (α : G → M) {β : U → N} (hβ : Continuous β) :
    Continuous (cup11ProjectionHomotopy G M N P U μ t ht α β) := by
  -- Put the cochain in the pointwise-sum form `continuous_finsetSum` expects.
  rw [funext (cup11ProjectionHomotopy_apply G M N P U μ t ht α β)]
  exact continuous_finsetSum _ fun u _ =>
    hμ.comp (continuous_const.prodMk
      ((hβ.comp ((continuous_lWord U t hU u).subtype_mk _)).const_smul (t u)))

variable (hequiv : ∀ (g : G) (m : M) (y : N), μ (g • m) (g • y) = g • μ m y)

include hequiv

/-- **The `(1,1)` projection formula**, `cor² (res¹ a ⌣ b) = a ⌣ cor¹ b`. Unlike the five shapes
with a degree-`0` factor, this one is not an identity of cochains: the two sides differ by `d¹` of
`TauCeti.ContCohomology.cup11ProjectionHomotopy`, which is
`TauCeti.ContCohomology.cup11ProjectionHomotopy_spec`. -/
theorem explicitCup_projection11 (a : H1 G M) (b : H1 U N) :
    explicitCor2 G P U hU
        (explicitCup11 U M N P μ hμ (fun g m y => hequiv (g : G) m y)
          (explicitRes1 G M U a) b) =
      explicitCup11 G M N P μ hμ hequiv a (explicitCor1 G N U hU b) := by
  induction a using QuotientAddGroup.induction_on with
  | _ α =>
    induction b using QuotientAddGroup.induction_on with
    | _ c =>
      simp only [explicitRes1_mk, explicitCor1_mk, explicitCup11_mk, explicitCor2_mk,
        H2pi_eq_iff]
      refine mem_B2_iff'.2 ⟨cup11ProjectionHomotopy G M N P U μ Quotient.out Quotient.out_eq
        (α : G → M) (c : U → N),
        continuous_cup11ProjectionHomotopy G M N P U hU μ hμ Quotient.out Quotient.out_eq
          (α : G → M) (mem_Z1_iff.1 c.2).1, fun γ η => ?_⟩
      -- Restriction is evaluation of the cochain at the inclusion, by `cocyclesMap1_apply`.
      simp only [Pi.sub_apply, coe_cocyclesCor2, coe_cocyclesCor1, cocyclesMap1_apply,
        Subgroup.smul_def]
      exact cup11ProjectionHomotopy_spec G M N P U μ Quotient.out Quotient.out_eq hequiv
        (mem_Z1_iff.1 α.2).2 (mem_Z1_iff.1 c.2).2 γ η

end CupOneOne

end TauCeti.ContCohomology
