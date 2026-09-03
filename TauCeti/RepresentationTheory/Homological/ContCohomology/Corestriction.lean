/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.Topology.Algebra.Group.TransversalWord

import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.GroupTheory.Index

/-!
# Corestriction in degrees zero, one and two

For a finite-index subgroup `U` of a group `G` acting on an abelian group `M`, the corestriction
attached to a transversal `t : G ⧸ U → G` is, in the three lowest degrees,

```text
cor⁰_t(m) = ∑ u : G ⧸ U, t u • m,
(cor¹_t f) γ = ∑ u : G ⧸ U, t u • f (ℓᵗ_u γ),
(cor²_t f) (γ, η) = ∑ u : G ⧸ U, t u • f (ℓᵗ_u γ, ℓᵗ_{γ⁻¹ • u} η),
```

where `ℓᵗ_u(γ) = (t u)⁻¹ * γ * t (γ⁻¹ • u)` is the transversal word `TauCeti.lWord`.  In degree
zero, if `m` is fixed by `U` then the sum is fixed by `G`; in degrees one and two, if `f` is a
cocycle on `U` then `corⁱ_t f` is a cocycle on `G`, and `corⁱ_t` carries coboundaries to
coboundaries.  All three therefore descend to additive maps `Hⁱ(U, M) → Hⁱ(G, M)`.  The transversal
is kept variable until its independence has been proved, and the public maps `explicitCor0`,
`explicitCor1` and `explicitCor2` then use `Quotient.out`.

The factor `t u •` is essential for nontrivial coefficient actions.  It is exactly the identity
`t u * ℓᵗ_u(γ) = γ * t (γ⁻¹ • u)` of `TauCeti.transversal_mul_lWord` that turns the `U`-cocycle
law for `f` into the `G`-cocycle law for `cor¹_t f`; without the action factor the sums are not
cocycles.  A trivial-action formula that omits it is correct for trivial coefficients and wrong in
general.

Degree one is where the two normalizations start to differ from degree zero.  Independence of the
transversal is no longer an equality of cochains but an explicit coboundary
(`cochainsCor1_changeTransversal`), and `cor¹ ∘ res¹` is not the index on cochains either: it
differs from it by the coboundary of `∑ u, c (t u)` (`cochainsCor1_res`).  Only after passing to
cohomology do the clean statements `explicitCor1_changeTransversal` and `explicitCor1_comp_res1`
hold.  Degree two repeats that pattern with longer correction terms: the two transversals differ
by the coboundary of `γ ↦ ∑ u, t u • (f (d_u, ℓᵗ'_u γ) - f (ℓᵗ_u γ, d_{γ⁻¹ • u}))`
(`cochainsCor2_changeTransversal`), and `cor² ∘ res²` differs from the index by the coboundary of
`γ ↦ ∑ u, (c (t u, ℓᵗ_u γ) - c (γ, t u))` (`cochainsCor2_res`).

Continuity is needed only for the passage from cochains to `H¹` and `H²`, and only through
openness of `U`: `TauCeti.continuous_lWord` makes `γ ↦ ℓᵗ_u(γ)` continuous for an open `U` and
*any* map `t`, and `TauCeti.continuous_lWord_inv_smul` does the same for the second transversal
word of the degree-two sum, whose coset index moves with the first variable.  So no continuity is
required of the transversal itself.

This is the degree-zero, degree-one and degree-two part of Layer 6 of the Profinite Cohomology
roadmap.  The degree-zero formulas and proof organization are adapted from the earlier, unmerged
degree-zero portion of Tau Ceti PR #4061, which was removed there because the canonical `H0`
carrier had not yet landed.

## Main declarations

* `TauCeti.ContCohomology.explicitCor0Transversal`: the norm for a variable transversal.
* `TauCeti.ContCohomology.explicitCor0_changeTransversal`: independence of that transversal.
* `TauCeti.ContCohomology.explicitCor0`: the canonical degree-zero corestriction.
* `TauCeti.ContCohomology.explicitCor0_comp_res0`: the normalization
  `cor⁰ ∘ res⁰ = (G : U) • id`.
* `TauCeti.ContCohomology.cochainsCor1`: the degree-one corestriction cochain for a variable
  transversal, with `cochainsCor1_isCocycle₁` and `cochainsCor1_mem_B1`.
* `TauCeti.ContCohomology.cochainsCor1_changeTransversal` and
  `TauCeti.ContCohomology.cochainsCor1_res`: the two cochain-level correction terms.
* `TauCeti.ContCohomology.explicitCor1Transversal` and
  `TauCeti.ContCohomology.explicitCor1`: degree-one corestriction on `H¹`, for a variable and for
  the canonical transversal.
* `TauCeti.ContCohomology.explicitCor1_comp_res1`: the normalization
  `cor¹ ∘ res¹ = (G : U) • id` on `H¹`.
* `TauCeti.ContCohomology.cochainsCor2`: the degree-two corestriction cochain for a variable
  transversal, with `cochainsCor2_isCocycle₂` and `cochainsCor2_mem_B2`.
* `TauCeti.ContCohomology.cochainsCor2_changeTransversal` and
  `TauCeti.ContCohomology.cochainsCor2_res`: the two degree-two cochain-level correction terms.
* `TauCeti.ContCohomology.explicitCor2Transversal` and
  `TauCeti.ContCohomology.explicitCor2`: degree-two corestriction on `H²`, for a variable and for
  the canonical transversal.
* `TauCeti.ContCohomology.explicitCor2_comp_res2`: the normalization
  `cor² ∘ res² = (G : U) • id` on `H²`.

## References

The normalization is Neukirch--Schmidt--Wingberg, *Cohomology of Number Fields*, 2nd ed.,
(1.5.7), and Serre, *Local Fields*, VII §7 Proposition 6.  In positive degrees it is an identity
of cohomology classes; in degree zero, a cocycle is already an invariant element.
-/

public section

open scoped Pointwise

namespace TauCeti.ContCohomology

universe u v w

variable (G : Type u) [Group G] (M : Type v) [AddCommGroup M] [DistribMulAction G M]
  (U : Subgroup G)

/-- A `U`-fixed element is fixed by any element whose underlying value belongs to `U`. -/
private theorem smul_eq_self_of_mem {m : M} (hm : m ∈ H0 U M) {x : G} (hx : x ∈ U) :
    x • m = m :=
  (FixedPoints.mem_addSubgroup U M m).1 hm ⟨x, hx⟩

section Reindex

variable [U.FiniteIndex] {N : Type w} [AddCommMonoid N]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Translating the index of a finite sum over `G ⧸ U` permutes its terms. Every corestriction
formula below reindexes by translation exactly once. -/
private theorem sum_translate (F : G ⧸ U → N) (γ : G) :
    ∑ u : G ⧸ U, F (γ • u) = ∑ u : G ⧸ U, F u :=
  Fintype.sum_equiv (MulAction.toPerm γ) _ _ fun _ => rfl

end Reindex

section Transversal

variable [U.FiniteIndex] (t : G ⧸ U → G)
  (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

include ht

/-- The transversal norm of a `U`-invariant element is `G`-invariant. -/
theorem sum_transversal_smul_mem_H0 {m : M} (hm : m ∈ H0 U M) :
    ∑ u : G ⧸ U, t u • m ∈ H0 G M := by
  refine (FixedPoints.mem_addSubgroup G M _).2 fun γ => ?_
  calc
    γ • ∑ u : G ⧸ U, t u • m = ∑ u : G ⧸ U, t (γ • u) • m := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [smul_smul, ← transversal_smul_mul_lWord U t u γ, ← smul_smul,
        smul_eq_self_of_mem G M U hm (lWord_mem U t ht (γ • u) γ)]
    _ = ∑ u : G ⧸ U, t u • m := sum_translate G U (fun u => t u • m) γ

/-- **Corestriction in degree zero for a variable transversal**, the norm
`m ↦ ∑ u, t u • m : H⁰(U, M) → H⁰(G, M)`. -/
noncomputable def explicitCor0Transversal : H0 U M →+ H0 G M where
  toFun m := ⟨∑ u : G ⧸ U, t u • (m : M), sum_transversal_smul_mem_H0 G M U t ht m.2⟩
  map_zero' := by ext; simp
  map_add' a b := by ext; simp [smul_add, Finset.sum_add_distrib]

/-- The underlying coefficient of the transversal corestriction is its defining norm sum. -/
@[simp]
theorem coe_explicitCor0Transversal (m : H0 U M) :
    (explicitCor0Transversal G M U t ht m : M) = ∑ u : G ⧸ U, t u • (m : M) := (rfl)

/-- For a trivial coefficient action, the transversal norm is multiplication by the index. -/
theorem coe_explicitCor0Transversal_of_smul_eq_self
    (htriv : ∀ (g : G) (m : M), g • m = m) (m : H0 U M) :
    (explicitCor0Transversal G M U t ht m : M) = U.index • (m : M) := by
  simp [htriv, U.index_eq_card, Nat.card_eq_fintype_card]

/-- Naturality of the transversal norm in an equivariant coefficient homomorphism. -/
theorem map_explicitCor0Transversal {N : Type w} [AddCommGroup N]
    [DistribMulAction G N] (f : M →+[G] N) (m : H0 U M) :
    explicitCoeff0 G M f (explicitCor0Transversal G M U t ht m) =
      explicitCor0Transversal G N U t ht (fixedPointsMap f U m) := by
  apply Subtype.ext
  rw [coe_explicitCoeff0, coe_explicitCor0Transversal]
  -- `fixedPointsMap` is bundled on `addSubmonoid`, whereas `H0` uses `addSubgroup`;
  -- expose the underlying coefficient after Lean inserts the carrier-preserving coercions.
  change f (∑ u : G ⧸ U, t u • (m : M)) =
    ∑ u : G ⧸ U, t u • (fixedPointsMap f U m : N)
  have hfm : (fixedPointsMap f U m : N) = f (m : M) := coe_fixedPointsMap f U m
  rw [hfm]
  simp [map_sum]

/-- **`cor⁰_t ∘ res⁰ = (G : U) • id`** for a variable transversal. -/
theorem explicitCor0Transversal_comp_res0 (m : H0 G M) :
    explicitCor0Transversal G M U t ht (explicitRes0 G M U m) = U.index • m := by
  have hm : ∀ u : G ⧸ U, t u • (m : M) = m := fun u =>
    (FixedPoints.mem_addSubgroup G M m).1 m.2 (t u)
  ext
  simp [hm, U.index_eq_card, Nat.card_eq_fintype_card]

end Transversal

variable [U.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **Independence of the transversal in degree zero.** Two transversals differ by a `U`-valued
factor, which acts trivially on `H⁰(U, M)`, so their norms agree on the nose. -/
theorem explicitCor0_changeTransversal (t t' : G ⧸ U → G)
    (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)
    (ht' : ∀ u : G ⧸ U, (QuotientGroup.mk (t' u) : G ⧸ U) = u) :
    explicitCor0Transversal G M U t ht = explicitCor0Transversal G M U t' ht' := by
  ext m
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← transversal_mul_transversalDiff U t t' u, ← smul_smul,
    smul_eq_self_of_mem G M U m.2 (transversalDiff_mem U t t' ht ht' u)]

/-- **Corestriction in degree zero**, the canonical norm
`m ↦ ∑ u, Quotient.out u • m : H⁰(U, M) → H⁰(G, M)`. -/
noncomputable def explicitCor0 : H0 U M →+ H0 G M :=
  explicitCor0Transversal G M U Quotient.out Quotient.out_eq

/-- The underlying coefficient of canonical degree-zero corestriction is the norm over
`Quotient.out`. -/
@[simp]
theorem coe_explicitCor0 (m : H0 U M) :
    (explicitCor0 G M U m : M) = ∑ u : G ⧸ U, Quotient.out u • (m : M) := (rfl)

/-- For a trivial coefficient action, canonical degree-zero corestriction is multiplication by
the subgroup index. -/
theorem coe_explicitCor0_of_smul_eq_self (htriv : ∀ (g : G) (m : M), g • m = m)
    (m : H0 U M) :
    (explicitCor0 G M U m : M) = U.index • (m : M) := by
  simpa [explicitCor0] using
    coe_explicitCor0Transversal_of_smul_eq_self G M U Quotient.out Quotient.out_eq htriv m

/-- The canonical degree-zero corestriction can be computed using any transversal. -/
theorem explicitCor0_eq_transversal (t : G ⧸ U → G)
    (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u) :
    explicitCor0 G M U = explicitCor0Transversal G M U t ht :=
  explicitCor0_changeTransversal G M U _ t _ ht

/-- Naturality of canonical degree-zero corestriction in an equivariant coefficient homomorphism. -/
theorem map_explicitCor0 {N : Type w} [AddCommGroup N] [DistribMulAction G N]
    (f : M →+[G] N) (m : H0 U M) :
    explicitCoeff0 G M f (explicitCor0 G M U m) =
      explicitCor0 G N U (fixedPointsMap f U m) :=
  map_explicitCor0Transversal G M U Quotient.out Quotient.out_eq f m

/-- **`cor⁰ ∘ res⁰ = (G : U) • id`** on `H⁰(G, M)`. -/
theorem explicitCor0_comp_res0 (m : H0 G M) :
    explicitCor0 G M U (explicitRes0 G M U m) = U.index • m :=
  explicitCor0Transversal_comp_res0 G M U Quotient.out Quotient.out_eq m

section DegreeOneCochain

/-! ### The degree-one corestriction cochain

No topology is needed to write `cor¹_t` down, to check that it carries `1`-cocycles to
`1`-cocycles and `1`-coboundaries to `1`-coboundaries, or to compare two transversals. Continuity
enters only in the next section, where the cochain is pushed to `H¹`. -/

variable (t : G ⧸ U → G)
  (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)

/-- **The degree-one corestriction cochain** for a transversal `t`,
`(cor¹_t f) γ = ∑ u : G ⧸ U, t u • f (ℓᵗ_u γ)`, where `ℓᵗ` is the transversal word
`TauCeti.lWord`, which lands in `U` by `TauCeti.lWord_mem`. -/
noncomputable def cochainsCor1 : (U → M) →+ (G → M) where
  toFun f γ := ∑ u : G ⧸ U, t u • f ⟨lWord U t u γ, lWord_mem U t ht u γ⟩
  map_zero' := by ext γ; simp
  map_add' f g := by ext γ; simp [smul_add, Finset.sum_add_distrib]

/-- The defining formula for the degree-one corestriction cochain. -/
@[simp]
theorem cochainsCor1_apply (f : U → M) (γ : G) :
    cochainsCor1 G M U t ht f γ =
      ∑ u : G ⧸ U, t u • f ⟨lWord U t u γ, lWord_mem U t ht u γ⟩ := (rfl)

/-- For a trivial coefficient action the representative factor `t u •` disappears, and the
degree-one corestriction is the plain sum of the values of the cochain on the transversal words. -/
theorem cochainsCor1_apply_of_smul_eq_self (htriv : ∀ (g : G) (m : M), g • m = m)
    (f : U → M) (γ : G) :
    cochainsCor1 G M U t ht f γ = ∑ u : G ⧸ U, f ⟨lWord U t u γ, lWord_mem U t ht u γ⟩ := by
  simp [htriv]

/-- Naturality of the degree-one corestriction cochain in an equivariant coefficient
homomorphism. -/
theorem map_cochainsCor1 {N : Type w} [AddCommGroup N] [DistribMulAction G N] (φ : M →+ N)
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) (f : U → M) (γ : G) :
    φ (cochainsCor1 G M U t ht f γ) = cochainsCor1 G N U t ht (fun x => φ (f x)) γ := by
  simp [map_sum, hφ]

/-- **The corestriction of a `1`-cocycle is a `1`-cocycle.** The factor `t u •` is what makes this
true: the transversal identity `t u * ℓᵗ_u(γ) = γ * t (γ⁻¹ • u)` of
`TauCeti.transversal_mul_lWord` is what converts the `U`-cocycle law for `f` into the `G`-cocycle
law for `cor¹_t f`, and the reindexed sum is what produces the leading `γ •`. -/
theorem cochainsCor1_isCocycle₁ {f : U → M} (hf : groupCohomology.IsCocycle₁ f) :
    groupCohomology.IsCocycle₁ (cochainsCor1 G M U t ht f) := by
  intro γ η
  -- The cocycle law for `f` at the factorization `ℓᵗ_u(γη) = ℓᵗ_u(γ) * ℓᵗ_{γ⁻¹ • u}(η)`.
  have key : ∀ u : G ⧸ U,
      t u • f ⟨lWord U t u (γ * η), lWord_mem U t ht u (γ * η)⟩ =
        γ • (t (γ⁻¹ • u) • f ⟨lWord U t (γ⁻¹ • u) η, lWord_mem U t ht (γ⁻¹ • u) η⟩) +
          t u • f ⟨lWord U t u γ, lWord_mem U t ht u γ⟩ := by
    intro u
    have hmul : (⟨lWord U t u γ, lWord_mem U t ht u γ⟩ : U) *
        ⟨lWord U t (γ⁻¹ • u) η, lWord_mem U t ht (γ⁻¹ • u) η⟩ =
          ⟨lWord U t u (γ * η), lWord_mem U t ht u (γ * η)⟩ :=
      Subtype.ext (lWord_mul_lWord U t u γ η)
    rw [← hmul, hf, smul_add, Subgroup.mk_smul, smul_smul, transversal_mul_lWord, mul_smul]
  simp only [cochainsCor1_apply]
  rw [Finset.sum_congr rfl fun u _ => key u, Finset.sum_add_distrib, ← Finset.smul_sum,
    sum_translate G U
      (fun u => t u • f ⟨lWord U t u η, lWord_mem U t ht u η⟩) γ⁻¹]

/-- The degree-one corestriction of a coboundary is the coboundary of the degree-zero
corestriction. -/
theorem cochainsCor1_d0 (m : M) :
    cochainsCor1 G M U t ht (d0 U M m) = d0 G M (∑ u : G ⧸ U, t u • m) := by
  ext γ
  rw [d0_apply, cochainsCor1_apply]
  have key : ∀ u : G ⧸ U,
      t u • d0 U M m ⟨lWord U t u γ, lWord_mem U t ht u γ⟩ =
        γ • (t (γ⁻¹ • u) • m) - t u • m := by
    intro u
    rw [d0_apply, smul_sub, Subgroup.mk_smul, smul_smul, transversal_mul_lWord, mul_smul]
  rw [Finset.sum_congr rfl fun u _ => key u, Finset.sum_sub_distrib, ← Finset.smul_sum,
    sum_translate G U (fun u => t u • m) γ⁻¹]

/-- The degree-one corestriction cochain preserves `1`-coboundaries. -/
theorem cochainsCor1_mem_B1 {f : U → M} (hf : f ∈ B1 U M) :
    cochainsCor1 G M U t ht f ∈ B1 G M := by
  obtain ⟨m, hm⟩ := mem_B1_iff.1 hf
  have hfd : f = d0 U M m := funext fun x => by rw [d0_apply, hm]
  rw [hfd, cochainsCor1_d0]
  exact d0_mem_B1 _

/-- **Change of transversal in degree one, as an explicit coboundary.** Two transversals give
corestriction cochains differing by `d⁰` of the degree-zero corestriction of the values of `f` on
the transversal difference `TauCeti.transversalDiff`. Unlike in degree zero, the two cochains are
genuinely different; only their classes in `H¹(G, M)` agree. -/
theorem cochainsCor1_changeTransversal (t' : G ⧸ U → G)
    (ht' : ∀ u : G ⧸ U, (QuotientGroup.mk (t' u) : G ⧸ U) = u)
    {f : U → M} (hf : groupCohomology.IsCocycle₁ f) :
    cochainsCor1 G M U t' ht' f = cochainsCor1 G M U t ht f +
      d0 G M (∑ v : G ⧸ U,
        t v • f ⟨transversalDiff U t t' v, transversalDiff_mem U t t' ht ht' v⟩) := by
  ext γ
  set D : G ⧸ U → U := fun v =>
    ⟨transversalDiff U t t' v, transversalDiff_mem U t t' ht ht' v⟩ with hD
  have key : ∀ u : G ⧸ U,
      t' u • f ⟨lWord U t' u γ, lWord_mem U t' ht' u γ⟩ =
        γ • (t (γ⁻¹ • u) • f (D (γ⁻¹ • u))) +
          t u • f ⟨lWord U t u γ, lWord_mem U t ht u γ⟩ - t u • f (D u) := by
    intro u
    set L : U := ⟨lWord U t u γ, lWord_mem U t ht u γ⟩ with hL
    set L' : U := ⟨lWord U t' u γ, lWord_mem U t' ht' u γ⟩
    -- The two words are intertwined by the transversal difference: `D u * L' = L * D (γ⁻¹ • u)`.
    have hmul : D u * L' = L * D (γ⁻¹ • u) :=
      Subtype.ext (transversalDiff_mul_lWord U t t' u γ)
    have h1 := hf (D u) L'
    rw [hmul, hf L (D (γ⁻¹ • u))] at h1
    -- `h1 : ℓᵗ_u(γ) • f (D (γ⁻¹ • u)) + f ℓᵗ_u(γ) = d_u • f ℓᵗ'_u(γ) + f (D u)`.
    have h2 : (D u : G) • f L' =
        (L : G) • f (D (γ⁻¹ • u)) + f L - f (D u) := by
      rw [← Subgroup.smul_def, ← Subgroup.smul_def]
      exact eq_sub_of_add_eq h1.symm
    calc t' u • f L'
        = (t u * (D u : G)) • f L' := by rw [hD, transversal_mul_transversalDiff]
      _ = t u • ((D u : G) • f L') := mul_smul _ _ _
      _ = t u • ((L : G) • f (D (γ⁻¹ • u))) + t u • f L - t u • f (D u) := by
          rw [h2, smul_sub, smul_add]
      _ = (t u * lWord U t u γ) • f (D (γ⁻¹ • u)) + t u • f L - t u • f (D u) := by
          rw [← mul_smul, hL]
      _ = γ • (t (γ⁻¹ • u) • f (D (γ⁻¹ • u))) + t u • f L - t u • f (D u) := by
          rw [transversal_mul_lWord, mul_smul]
  simp only [cochainsCor1_apply, Pi.add_apply, d0_apply]
  rw [Finset.sum_congr rfl fun u _ => key u, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.smul_sum, sum_translate G U (fun u => t u • f (D u)) γ⁻¹]
  abel

/-- **`cor¹_t ∘ res¹` on cochains**, with its correction term: for a `1`-cocycle `c` on `G`,
`cor¹_t (res c) = (G : U) • c + d⁰ (∑ u, c (t u))`. The correction term is genuinely there — unlike
in degree zero, `cor ∘ res` is *not* multiplication by the index on cochains — and it is a
coboundary, which is what makes `TauCeti.ContCohomology.explicitCor1_comp_res1` true on classes. -/
theorem cochainsCor1_res {c : G → M} (hc : groupCohomology.IsCocycle₁ c) :
    cochainsCor1 G M U t ht (fun x : U => c (x : G)) =
      U.index • c + d0 G M (∑ u : G ⧸ U, c (t u)) := by
  ext γ
  have key : ∀ u : G ⧸ U,
      t u • c (lWord U t u γ) = γ • c (t (γ⁻¹ • u)) + c γ - c (t u) := by
    intro u
    have h1 := hc (t u) (lWord U t u γ)
    rw [transversal_mul_lWord, hc γ (t (γ⁻¹ • u))] at h1
    exact eq_sub_of_add_eq h1.symm
  simp only [cochainsCor1_apply, Pi.add_apply, Pi.smul_apply, d0_apply]
  rw [Finset.sum_congr rfl fun u _ => key u, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.smul_sum, sum_translate G U (fun u => c (t u)) γ⁻¹, Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, ← U.index_eq_card]
  abel

end DegreeOneCochain

section DegreeOne

/-! ### Corestriction on `H¹`

Openness of `U` makes every corestriction cochain continuous, so the cochain layer above descends
to `H¹ = Z¹/B¹`. -/

variable [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul G M]
  (t : G ⧸ U → G) (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)
  (hU : IsOpen (U : Set G))

include hU

/-- The corestriction of a continuous cochain along an *open* subgroup is continuous. Continuity
of the transversal `t` is not required: `TauCeti.continuous_lWord` needs only openness of `U`. -/
theorem continuous_cochainsCor1 {f : U → M} (hf : Continuous f) :
    Continuous (cochainsCor1 G M U t ht f) := by
  -- Put the cochain in the pointwise-sum form `continuous_finsetSum` expects.
  rw [funext (cochainsCor1_apply G M U t ht f)]
  exact continuous_finsetSum _ fun u _ =>
    ((hf.comp ((continuous_lWord U t hU u).subtype_mk _)).const_smul (t u))

/-- The degree-one corestriction cochain preserves continuous `1`-cocycles. -/
theorem cochainsCor1_mem_Z1 {f : U → M} (hf : f ∈ Z1 U M) :
    cochainsCor1 G M U t ht f ∈ Z1 G M :=
  mem_Z1_iff.2 ⟨continuous_cochainsCor1 G M U t ht hU (mem_Z1_iff.1 hf).1,
    cochainsCor1_isCocycle₁ G M U t ht (mem_Z1_iff.1 hf).2⟩

/-- **Corestriction in degree one for a variable transversal, on continuous cocycles.** -/
noncomputable def cocyclesCor1 : Z1 U M →+ Z1 G M :=
  AddMonoidHom.codRestrict ((cochainsCor1 G M U t ht).domRestrict (Z1 U M)) (Z1 G M)
    fun f => cochainsCor1_mem_Z1 G M U t ht hU f.property

/-- The underlying cochain of the corestriction of a continuous cocycle. -/
@[simp]
theorem coe_cocyclesCor1 (f : Z1 U M) :
    (cocyclesCor1 G M U t ht hU f : G → M) = cochainsCor1 G M U t ht f := (rfl)

/-- **Corestriction in degree one for a variable transversal.** -/
noncomputable def explicitCor1Transversal : H1 U M →+ H1 G M :=
  QuotientAddGroup.map ((B1 U M).addSubgroupOf (Z1 U M)) ((B1 G M).addSubgroupOf (Z1 G M))
    (cocyclesCor1 G M U t ht hU) fun _ hc => cochainsCor1_mem_B1 G M U t ht hc

/-- Degree-one corestriction sends the class of a continuous `1`-cocycle to the class of its
corestriction cochain. -/
@[simp]
theorem explicitCor1Transversal_mk (f : Z1 U M) :
    explicitCor1Transversal G M U t ht hU (f : H1 U M) =
      (cocyclesCor1 G M U t ht hU f : H1 G M) :=
  QuotientAddGroup.map_mk _ _ _ _ f

/-- **Independence of the transversal in degree one.** Two transversals give the same map on
`H¹(U, M)`, because by `TauCeti.ContCohomology.cochainsCor1_changeTransversal` their corestriction
cochains differ by a `1`-coboundary. -/
theorem explicitCor1_changeTransversal (t' : G ⧸ U → G)
    (ht' : ∀ u : G ⧸ U, (QuotientGroup.mk (t' u) : G ⧸ U) = u) :
    explicitCor1Transversal G M U t ht hU = explicitCor1Transversal G M U t' ht' hU := by
  refine AddMonoidHom.ext fun x => ?_
  induction x using QuotientAddGroup.induction_on with
  | _ f =>
    rw [explicitCor1Transversal_mk, explicitCor1Transversal_mk, H1pi_eq_iff,
      coe_cocyclesCor1, coe_cocyclesCor1,
      cochainsCor1_changeTransversal G M U t ht t' ht' (mem_Z1_iff.1 f.2).2,
      sub_add_eq_sub_sub, sub_self, zero_sub]
    exact neg_mem (d0_mem_B1 _)

/-- **Corestriction in degree one**, at the canonical transversal `Quotient.out`. -/
noncomputable def explicitCor1 : H1 U M →+ H1 G M :=
  explicitCor1Transversal G M U Quotient.out Quotient.out_eq hU

/-- The canonical degree-one corestriction can be computed using any transversal. -/
theorem explicitCor1_eq_transversal :
    explicitCor1 G M U hU = explicitCor1Transversal G M U t ht hU :=
  explicitCor1_changeTransversal G M U Quotient.out Quotient.out_eq hU t ht

/-- Canonical degree-one corestriction sends the class of a continuous `1`-cocycle to the class of
its corestriction cochain over `Quotient.out`. -/
@[simp]
theorem explicitCor1_mk (f : Z1 U M) :
    explicitCor1 G M U hU (f : H1 U M) =
      (cocyclesCor1 G M U Quotient.out Quotient.out_eq hU f : H1 G M) :=
  explicitCor1Transversal_mk G M U Quotient.out Quotient.out_eq hU f

/-- **`cor¹_t ∘ res¹ = (G : U) • id`** on `H¹(G, M)`, for a variable transversal. On cochains the
two sides differ by the coboundary recorded in `TauCeti.ContCohomology.cochainsCor1_res`. -/
theorem explicitCor1Transversal_comp_res1 (x : H1 G M) :
    explicitCor1Transversal G M U t ht hU (explicitRes1 G M U x) = U.index • x := by
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    have hns : ((U.index • c : Z1 G M) : H1 G M) = U.index • (c : H1 G M) :=
      map_nsmul (H1pi G M) U.index c
    -- Restriction is evaluation of the cochain at the inclusion, by `cocyclesMap1_apply`; the
    -- identity coefficient map and the inclusion contribute nothing.
    have hres : ((cocyclesMap1 G M U M (ContinuousMonoidHom.subgroupSubtype U)
        (AddMonoidHom.id M) continuous_id (fun _ _ => rfl) c : Z1 U M) : U → M) =
          fun x : U => (c : G → M) (x : G) :=
      funext fun x => cocyclesMap1_apply G M U M (ContinuousMonoidHom.subgroupSubtype U)
        (AddMonoidHom.id M) continuous_id (fun _ _ => rfl) c x
    rw [explicitRes1_mk, explicitCor1Transversal_mk, ← hns, H1pi_eq_iff,
      coe_cocyclesCor1, hres, cochainsCor1_res G M U t ht (mem_Z1_iff.1 c.2).2]
    have hcoe : ((U.index • c : Z1 G M) : G → M) = U.index • (c : G → M) := by
      simp
    rw [hcoe, add_sub_cancel_left]
    exact d0_mem_B1 _

/-- **`cor¹ ∘ res¹ = (G : U) • id`** on `H¹(G, M)`. -/
theorem explicitCor1_comp_res1 (x : H1 G M) :
    explicitCor1 G M U hU (explicitRes1 G M U x) = U.index • x :=
  explicitCor1Transversal_comp_res1 G M U Quotient.out Quotient.out_eq hU x

end DegreeOne

section DegreeTwoCochain

/-! ### The degree-two corestriction cochain

As in degree one, nothing in this section needs a topology: the `2`-cocycle law for `cor²_t`, the
comparison of two transversals and the correction term of `cor² ∘ res²` are all identities of
plain cochains. Continuity enters only in the next section, where the cochain is pushed to `H²`. -/

variable (t : G ⧸ U → G)
  (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)

/-- **The degree-two corestriction cochain** for a transversal `t`,
`(cor²_t f) (γ, η) = ∑ u : G ⧸ U, t u • f (ℓᵗ_u γ, ℓᵗ_{γ⁻¹ • u} η)`.

Both transversal words lie in `U` by `TauCeti.lWord_mem`. The coset index of the *second* one is
translated by `γ⁻¹`, exactly as in the transversal cocycle law
`TauCeti.lWord_mul_lWord`; that translation is what makes the sum a `2`-cocycle. -/
noncomputable def cochainsCor2 : (U × U → M) →+ (G × G → M) where
  toFun f q := ∑ u : G ⧸ U, t u • f (⟨lWord U t u q.1, lWord_mem U t ht u q.1⟩,
    ⟨lWord U t (q.1⁻¹ • u) q.2, lWord_mem U t ht (q.1⁻¹ • u) q.2⟩)
  map_zero' := by ext q; simp
  map_add' f g := by ext q; simp [smul_add, Finset.sum_add_distrib]

/-- The defining formula for the degree-two corestriction cochain. -/
@[simp]
theorem cochainsCor2_apply (f : U × U → M) (γ η : G) :
    cochainsCor2 G M U t ht f (γ, η) =
      ∑ u : G ⧸ U, t u • f (⟨lWord U t u γ, lWord_mem U t ht u γ⟩,
        ⟨lWord U t (γ⁻¹ • u) η, lWord_mem U t ht (γ⁻¹ • u) η⟩) := (rfl)

/-- For a trivial coefficient action the representative factor `t u •` disappears, and the
degree-two corestriction is the plain sum of the values of the cochain on the transversal words. -/
theorem cochainsCor2_apply_of_smul_eq_self (htriv : ∀ (g : G) (m : M), g • m = m)
    (f : U × U → M) (γ η : G) :
    cochainsCor2 G M U t ht f (γ, η) =
      ∑ u : G ⧸ U, f (⟨lWord U t u γ, lWord_mem U t ht u γ⟩,
        ⟨lWord U t (γ⁻¹ • u) η, lWord_mem U t ht (γ⁻¹ • u) η⟩) := by
  simp [htriv]

/-- Naturality of the degree-two corestriction cochain in an equivariant coefficient
homomorphism. -/
theorem map_cochainsCor2 {N : Type w} [AddCommGroup N] [DistribMulAction G N] (φ : M →+ N)
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) (f : U × U → M) (γ η : G) :
    φ (cochainsCor2 G M U t ht f (γ, η)) =
      cochainsCor2 G N U t ht (fun q => φ (f q)) (γ, η) := by
  simp [map_sum, hφ]

/-- **The corestriction of a `2`-cocycle is a `2`-cocycle.** The three arguments to which the
`U`-cocycle law of `f` is applied are `ℓᵗ_u(γ)`, `ℓᵗ_{γ⁻¹ • u}(η)` and `ℓᵗ_{(γη)⁻¹ • u}(ζ)`; their
two consecutive products are `ℓᵗ_u(γη)` and `ℓᵗ_{γ⁻¹ • u}(ηζ)` by
`TauCeti.lWord_mul_lWord`, which is what matches the four terms of the law with the four
corestriction sums. The leading `γ •` comes, as in degree one, from
`TauCeti.transversal_mul_lWord` together with a translation of the summation index. -/
theorem cochainsCor2_isCocycle₂ {f : U × U → M} (hf : groupCohomology.IsCocycle₂ f) :
    groupCohomology.IsCocycle₂ (cochainsCor2 G M U t ht f) := by
  intro γ η ζ
  have key : ∀ u : G ⧸ U,
      t u • f (⟨lWord U t u (γ * η), lWord_mem U t ht u (γ * η)⟩,
          ⟨lWord U t ((γ * η)⁻¹ • u) ζ, lWord_mem U t ht ((γ * η)⁻¹ • u) ζ⟩) +
        t u • f (⟨lWord U t u γ, lWord_mem U t ht u γ⟩,
          ⟨lWord U t (γ⁻¹ • u) η, lWord_mem U t ht (γ⁻¹ • u) η⟩) =
      γ • (t (γ⁻¹ • u) • f (⟨lWord U t (γ⁻¹ • u) η, lWord_mem U t ht (γ⁻¹ • u) η⟩,
          ⟨lWord U t (η⁻¹ • γ⁻¹ • u) ζ, lWord_mem U t ht (η⁻¹ • γ⁻¹ • u) ζ⟩)) +
        t u • f (⟨lWord U t u γ, lWord_mem U t ht u γ⟩,
          ⟨lWord U t (γ⁻¹ • u) (η * ζ), lWord_mem U t ht (γ⁻¹ • u) (η * ζ)⟩) := by
    intro u
    have hab : (⟨lWord U t u γ, lWord_mem U t ht u γ⟩ : U) *
        ⟨lWord U t (γ⁻¹ • u) η, lWord_mem U t ht (γ⁻¹ • u) η⟩ =
          ⟨lWord U t u (γ * η), lWord_mem U t ht u (γ * η)⟩ :=
      Subtype.ext (lWord_mul_lWord U t u γ η)
    have hbc : (⟨lWord U t (γ⁻¹ • u) η, lWord_mem U t ht (γ⁻¹ • u) η⟩ : U) *
        ⟨lWord U t (η⁻¹ • γ⁻¹ • u) ζ, lWord_mem U t ht (η⁻¹ • γ⁻¹ • u) ζ⟩ =
          ⟨lWord U t (γ⁻¹ • u) (η * ζ), lWord_mem U t ht (γ⁻¹ • u) (η * ζ)⟩ :=
      Subtype.ext (lWord_mul_lWord U t (γ⁻¹ • u) η ζ)
    have hcc : (⟨lWord U t ((γ * η)⁻¹ • u) ζ, lWord_mem U t ht ((γ * η)⁻¹ • u) ζ⟩ : U) =
        ⟨lWord U t (η⁻¹ • γ⁻¹ • u) ζ, lWord_mem U t ht (η⁻¹ • γ⁻¹ • u) ζ⟩ :=
      Subtype.ext (by rw [mul_inv_rev, mul_smul])
    rw [hcc, ← hab, ← hbc, ← smul_add, hf, smul_add, Subgroup.mk_smul, smul_smul,
      transversal_mul_lWord, mul_smul]
  simp only [cochainsCor2_apply]
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun u _ => key u, Finset.sum_add_distrib,
    ← Finset.smul_sum,
    sum_translate G U (fun u : G ⧸ U => t u • f (⟨lWord U t u η, lWord_mem U t ht u η⟩,
      ⟨lWord U t (η⁻¹ • u) ζ, lWord_mem U t ht (η⁻¹ • u) ζ⟩)) γ⁻¹]

/-- **The degree-two corestriction is a chain map**: it turns the degree-one corestriction of a
`1`-cochain into the degree-two corestriction of its coboundary. This is the identity that carries
`2`-coboundaries to `2`-coboundaries. -/
theorem cochainsCor2_d1 (c : U → M) :
    cochainsCor2 G M U t ht (d1 U M c) = d1 G M (cochainsCor1 G M U t ht c) := by
  ext q
  obtain ⟨γ, η⟩ := q
  have key : ∀ u : G ⧸ U,
      t u • d1 U M c (⟨lWord U t u γ, lWord_mem U t ht u γ⟩,
          ⟨lWord U t (γ⁻¹ • u) η, lWord_mem U t ht (γ⁻¹ • u) η⟩) =
        γ • (t (γ⁻¹ • u) • c ⟨lWord U t (γ⁻¹ • u) η, lWord_mem U t ht (γ⁻¹ • u) η⟩) -
            t u • c ⟨lWord U t u (γ * η), lWord_mem U t ht u (γ * η)⟩ +
          t u • c ⟨lWord U t u γ, lWord_mem U t ht u γ⟩ := by
    intro u
    have hab : (⟨lWord U t u γ, lWord_mem U t ht u γ⟩ : U) *
        ⟨lWord U t (γ⁻¹ • u) η, lWord_mem U t ht (γ⁻¹ • u) η⟩ =
          ⟨lWord U t u (γ * η), lWord_mem U t ht u (γ * η)⟩ :=
      Subtype.ext (lWord_mul_lWord U t u γ η)
    rw [d1_apply, hab, smul_add, smul_sub, Subgroup.mk_smul, smul_smul,
      transversal_mul_lWord, mul_smul]
  rw [d1_apply]
  simp only [cochainsCor2_apply, cochainsCor1_apply]
  rw [Finset.sum_congr rfl fun u _ => key u, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.smul_sum,
    sum_translate G U
      (fun u : G ⧸ U => t u • c ⟨lWord U t u η, lWord_mem U t ht u η⟩) γ⁻¹]

/-- **Change of transversal in degree two, as an explicit coboundary.** Two transversals give
degree-two corestriction cochains differing by `d¹` of the `1`-cochain

```text
γ ↦ ∑ u, t u • (f (d_u, ℓᵗ'_u γ) - f (ℓᵗ_u γ, d_{γ⁻¹ • u})),
```

built from the transversal difference `TauCeti.transversalDiff`. As in degree one the two cochains
are genuinely different; only their classes in `H²(G, M)` agree. -/
theorem cochainsCor2_changeTransversal (t' : G ⧸ U → G)
    (ht' : ∀ u : G ⧸ U, (QuotientGroup.mk (t' u) : G ⧸ U) = u)
    {f : U × U → M} (hf : groupCohomology.IsCocycle₂ f) :
    cochainsCor2 G M U t' ht' f = cochainsCor2 G M U t ht f +
      d1 G M (fun γ => ∑ u : G ⧸ U, t u •
        (f (⟨transversalDiff U t t' u, transversalDiff_mem U t t' ht ht' u⟩,
            ⟨lWord U t' u γ, lWord_mem U t' ht' u γ⟩) -
          f (⟨lWord U t u γ, lWord_mem U t ht u γ⟩,
            ⟨transversalDiff U t t' (γ⁻¹ • u),
              transversalDiff_mem U t t' ht ht' (γ⁻¹ • u)⟩))) := by
  ext q
  obtain ⟨γ, η⟩ := q
  set D : G ⧸ U → U := fun v =>
    ⟨transversalDiff U t t' v, transversalDiff_mem U t t' ht ht' v⟩ with hD
  have key : ∀ u : G ⧸ U,
      t' u • f (⟨lWord U t' u γ, lWord_mem U t' ht' u γ⟩,
          ⟨lWord U t' (γ⁻¹ • u) η, lWord_mem U t' ht' (γ⁻¹ • u) η⟩) =
        γ • (t (γ⁻¹ • u) •
              (f (D (γ⁻¹ • u), ⟨lWord U t' (γ⁻¹ • u) η, lWord_mem U t' ht' (γ⁻¹ • u) η⟩) -
                f (⟨lWord U t (γ⁻¹ • u) η, lWord_mem U t ht (γ⁻¹ • u) η⟩,
                  D (η⁻¹ • γ⁻¹ • u)))) -
            t u • (f (D u, ⟨lWord U t' u (γ * η), lWord_mem U t' ht' u (γ * η)⟩) -
              f (⟨lWord U t u (γ * η), lWord_mem U t ht u (γ * η)⟩, D ((γ * η)⁻¹ • u))) +
            t u • (f (D u, ⟨lWord U t' u γ, lWord_mem U t' ht' u γ⟩) -
              f (⟨lWord U t u γ, lWord_mem U t ht u γ⟩, D (γ⁻¹ • u))) +
          t u • f (⟨lWord U t u γ, lWord_mem U t ht u γ⟩,
            ⟨lWord U t (γ⁻¹ • u) η, lWord_mem U t ht (γ⁻¹ • u) η⟩) := by
    intro u
    set a : U := ⟨lWord U t u γ, lWord_mem U t ht u γ⟩ with ha
    set b : U := ⟨lWord U t (γ⁻¹ • u) η, lWord_mem U t ht (γ⁻¹ • u) η⟩
    set a' : U := ⟨lWord U t' u γ, lWord_mem U t' ht' u γ⟩
    set b' : U := ⟨lWord U t' (γ⁻¹ • u) η, lWord_mem U t' ht' (γ⁻¹ • u) η⟩
    -- The five identities between words that the three cocycle applications are matched along.
    have hDa : D u * a' = a * D (γ⁻¹ • u) :=
      Subtype.ext (transversalDiff_mul_lWord U t t' u γ)
    have hDb : D (γ⁻¹ • u) * b' = b * D (η⁻¹ • γ⁻¹ • u) :=
      Subtype.ext (transversalDiff_mul_lWord U t t' (γ⁻¹ • u) η)
    have ha'b' : a' * b' = ⟨lWord U t' u (γ * η), lWord_mem U t' ht' u (γ * η)⟩ :=
      Subtype.ext (lWord_mul_lWord U t' u γ η)
    have hab : a * b = ⟨lWord U t u (γ * η), lWord_mem U t ht u (γ * η)⟩ :=
      Subtype.ext (lWord_mul_lWord U t u γ η)
    have hDmul : D ((γ * η)⁻¹ • u) = D (η⁻¹ • γ⁻¹ • u) := by rw [mul_inv_rev, mul_smul]
    -- Three applications of the `U`-cocycle law, solved for the term each one contributes.
    have h1 := hf (D u) a' b'
    rw [hDa, ha'b'] at h1
    have e1 : (D u : U) • f (a', b') =
        f (a * D (γ⁻¹ • u), b') + f (D u, a') -
          f (D u, ⟨lWord U t' u (γ * η), lWord_mem U t' ht' u (γ * η)⟩) := by
      rw [h1]; abel
    have h2 := hf a (D (γ⁻¹ • u)) b'
    rw [hDb] at h2
    have e2 : f (a * D (γ⁻¹ • u), b') =
        a • f (D (γ⁻¹ • u), b') + f (a, b * D (η⁻¹ • γ⁻¹ • u)) - f (a, D (γ⁻¹ • u)) := by
      rw [← h2]; abel
    have h3 := hf a b (D (η⁻¹ • γ⁻¹ • u))
    rw [hab] at h3
    have e3 : f (a, b * D (η⁻¹ • γ⁻¹ • u)) =
        f (⟨lWord U t u (γ * η), lWord_mem U t ht u (γ * η)⟩, D (η⁻¹ • γ⁻¹ • u)) + f (a, b) -
          a • f (b, D (η⁻¹ • γ⁻¹ • u)) := by
      rw [h3]; abel
    have hstep : (D u : U) • f (a', b') =
        a • f (D (γ⁻¹ • u), b') - a • f (b, D (η⁻¹ • γ⁻¹ • u)) -
              f (D u, ⟨lWord U t' u (γ * η), lWord_mem U t' ht' u (γ * η)⟩) +
              f (⟨lWord U t u (γ * η), lWord_mem U t ht u (γ * η)⟩, D (η⁻¹ • γ⁻¹ • u)) +
            f (D u, a') - f (a, D (γ⁻¹ • u)) + f (a, b) := by
      rw [e1, e2, e3]; abel
    have hta : t' u • f (a', b') = t u • ((D u : U) • f (a', b')) := by
      rw [Subgroup.smul_def, ← mul_smul, hD, transversal_mul_transversalDiff]
    rw [hta, hstep, hDmul, ha]
    simp only [smul_add, smul_sub, Subgroup.mk_smul, smul_smul]
    rw [transversal_mul_lWord]
    abel
  simp only [cochainsCor2_apply, Pi.add_apply, d1_apply]
  rw [Finset.sum_congr rfl fun u _ => key u, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.smul_sum,
    sum_translate G U (fun v : G ⧸ U => t v •
      (f (D v, ⟨lWord U t' v η, lWord_mem U t' ht' v η⟩) -
        f (⟨lWord U t v η, lWord_mem U t ht v η⟩, D (η⁻¹ • v)))) γ⁻¹]
  abel

/-- **`cor²_t ∘ res²` on cochains**, with its correction term: for a continuous `2`-cocycle `c` on
`G`, `cor²_t (res c) = (G : U) • c + d¹ k` with
`k γ = ∑ u, (c (t u, ℓᵗ_u γ) - c (γ, t u))`.
The correction term is again genuinely there, and it is a coboundary, which is what makes
`TauCeti.ContCohomology.explicitCor2_comp_res2` true on classes. -/
theorem cochainsCor2_res {c : G × G → M} (hc : groupCohomology.IsCocycle₂ c) :
    cochainsCor2 G M U t ht (fun q : U × U => c ((q.1 : G), (q.2 : G))) =
      U.index • c + d1 G M (fun γ => ∑ u : G ⧸ U, (c (t u, lWord U t u γ) - c (γ, t u))) := by
  ext q
  obtain ⟨γ, η⟩ := q
  have key : ∀ u : G ⧸ U,
      t u • c (lWord U t u γ, lWord U t (γ⁻¹ • u) η) =
        γ • c (t (γ⁻¹ • u), lWord U t (γ⁻¹ • u) η) - γ • c (η, t (η⁻¹ • γ⁻¹ • u)) +
              c (γ * η, t ((γ * η)⁻¹ • u)) - c (t u, lWord U t u (γ * η)) +
            c (t u, lWord U t u γ) - c (γ, t (γ⁻¹ • u)) + c (γ, η) := by
    intro u
    -- The three applications of the `G`-cocycle law of `c`, along the factorizations
    -- `t u * ℓᵗ_u(γ) = γ * t (γ⁻¹ • u)` and `t v * ℓᵗ_v(η) = η * t (η⁻¹ • v)`.
    have hsmul : ((γ * η)⁻¹ • u : G ⧸ U) = η⁻¹ • γ⁻¹ • u := by rw [mul_inv_rev, mul_smul]
    have h1 := hc (t u) (lWord U t u γ) (lWord U t (γ⁻¹ • u) η)
    rw [transversal_mul_lWord, lWord_mul_lWord] at h1
    have e1 : t u • c (lWord U t u γ, lWord U t (γ⁻¹ • u) η) =
        c (γ * t (γ⁻¹ • u), lWord U t (γ⁻¹ • u) η) + c (t u, lWord U t u γ) -
          c (t u, lWord U t u (γ * η)) := by
      rw [h1]; abel
    have h2 := hc γ (t (γ⁻¹ • u)) (lWord U t (γ⁻¹ • u) η)
    rw [transversal_mul_lWord] at h2
    have e2 : c (γ * t (γ⁻¹ • u), lWord U t (γ⁻¹ • u) η) =
        γ • c (t (γ⁻¹ • u), lWord U t (γ⁻¹ • u) η) + c (γ, η * t (η⁻¹ • γ⁻¹ • u)) -
          c (γ, t (γ⁻¹ • u)) := by
      rw [← h2]; abel
    have h3 := hc γ η (t (η⁻¹ • γ⁻¹ • u))
    have e3 : c (γ, η * t (η⁻¹ • γ⁻¹ • u)) =
        c (γ * η, t (η⁻¹ • γ⁻¹ • u)) + c (γ, η) - γ • c (η, t (η⁻¹ • γ⁻¹ • u)) := by
      rw [h3]; abel
    rw [e1, e2, e3, hsmul]
    abel
  simp only [cochainsCor2_apply, Pi.add_apply, Pi.smul_apply, d1_apply]
  rw [Finset.sum_congr rfl fun u _ => key u]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum, smul_sub,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, ← U.index_eq_card,
    sum_translate G U (fun v : G ⧸ U => c (t v, lWord U t v η)) γ⁻¹,
    sum_translate G U (fun v : G ⧸ U => c (η, t (η⁻¹ • v))) γ⁻¹,
    sum_translate G U (fun v : G ⧸ U => c (η, t v)) η⁻¹,
    sum_translate G U (fun v : G ⧸ U => c (γ * η, t v)) (γ * η)⁻¹,
    sum_translate G U (fun v : G ⧸ U => c (γ, t v)) γ⁻¹]
  abel

end DegreeTwoCochain

section DegreeTwo

/-! ### Corestriction on `H²`

Openness of `U` makes every degree-two corestriction cochain continuous — through
`TauCeti.continuous_lWord` and `TauCeti.continuous_lWord_inv_smul`, one for each of the two
transversal words — so the cochain layer above descends to `H² = Z²/B²`.

Unlike degree one, this section takes the bundled `IsTopologicalGroup G` rather than
`ContinuousMul G` together with `ContinuousInv G`. The two carry the same content, but only the
bundled form triggers the instance `IsTopologicalGroup ↥U` that `Z²(U, M)` needs, `B²` being the
image of the *continuous* `1`-cochains on `U`. -/

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul G M]
  (t : G ⧸ U → G) (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)
  (hU : IsOpen (U : Set G))

include hU

/-- The degree-two corestriction of a continuous cochain along an *open* subgroup is continuous.
As in degree one, no continuity is required of the transversal `t`. -/
theorem continuous_cochainsCor2 {f : U × U → M} (hf : Continuous f) :
    Continuous (cochainsCor2 G M U t ht f) := by
  -- Put the cochain in the pointwise-sum form `continuous_finsetSum` expects.
  have h : cochainsCor2 G M U t ht f = fun q : G × G =>
      ∑ u : G ⧸ U, t u • f (⟨lWord U t u q.1, lWord_mem U t ht u q.1⟩,
        ⟨lWord U t (q.1⁻¹ • u) q.2, lWord_mem U t ht (q.1⁻¹ • u) q.2⟩) :=
    funext fun q => cochainsCor2_apply G M U t ht f q.1 q.2
  rw [h]
  refine continuous_finsetSum _ fun u _ => Continuous.const_smul ?_ (t u)
  exact hf.comp ((((continuous_lWord U t hU u).comp continuous_fst).subtype_mk _).prodMk
    ((continuous_lWord_inv_smul U t hU u).subtype_mk _))

/-- The degree-two corestriction cochain preserves continuous `2`-cocycles. -/
theorem cochainsCor2_mem_Z2 {f : U × U → M} (hf : f ∈ Z2 U M) :
    cochainsCor2 G M U t ht f ∈ Z2 G M :=
  mem_Z2_iff.2 ⟨continuous_cochainsCor2 G M U t ht hU (mem_Z2_iff.1 hf).1,
    cochainsCor2_isCocycle₂ G M U t ht (mem_Z2_iff.1 hf).2⟩

/-- The degree-two corestriction cochain preserves `2`-coboundaries: by
`TauCeti.ContCohomology.cochainsCor2_d1` it sends `d¹ c` to `d¹` of the degree-one corestriction of
`c`, which is continuous because `U` is open. -/
theorem cochainsCor2_mem_B2 {f : U × U → M} (hf : f ∈ B2 U M) :
    cochainsCor2 G M U t ht f ∈ B2 G M := by
  obtain ⟨c, hc, rfl⟩ := mem_B2_iff.1 hf
  rw [cochainsCor2_d1]
  exact mem_B2_iff.2 ⟨_, continuous_cochainsCor1 G M U t ht hU hc, rfl⟩

/-- **Corestriction in degree two for a variable transversal, on continuous cocycles.** -/
noncomputable def cocyclesCor2 : Z2 U M →+ Z2 G M :=
  AddMonoidHom.codRestrict ((cochainsCor2 G M U t ht).domRestrict (Z2 U M)) (Z2 G M)
    fun f => cochainsCor2_mem_Z2 G M U t ht hU f.property

/-- The underlying cochain of the corestriction of a continuous `2`-cocycle. -/
@[simp]
theorem coe_cocyclesCor2 (f : Z2 U M) :
    (cocyclesCor2 G M U t ht hU f : G × G → M) = cochainsCor2 G M U t ht f := (rfl)

/-- **Corestriction in degree two for a variable transversal.** -/
noncomputable def explicitCor2Transversal : H2 U M →+ H2 G M :=
  QuotientAddGroup.map ((B2 U M).addSubgroupOf (Z2 U M)) ((B2 G M).addSubgroupOf (Z2 G M))
    (cocyclesCor2 G M U t ht hU) fun _ hc => cochainsCor2_mem_B2 G M U t ht hU hc

/-- Degree-two corestriction sends the class of a continuous `2`-cocycle to the class of its
corestriction cochain. -/
@[simp]
theorem explicitCor2Transversal_mk (f : Z2 U M) :
    explicitCor2Transversal G M U t ht hU (f : H2 U M) =
      (cocyclesCor2 G M U t ht hU f : H2 G M) :=
  QuotientAddGroup.map_mk _ _ _ _ f

/-- **Independence of the transversal in degree two.** Two transversals give the same map on
`H²(U, M)`, because by `TauCeti.ContCohomology.cochainsCor2_changeTransversal` their corestriction
cochains differ by a `2`-coboundary. -/
theorem explicitCor2_changeTransversal (t' : G ⧸ U → G)
    (ht' : ∀ u : G ⧸ U, (QuotientGroup.mk (t' u) : G ⧸ U) = u) :
    explicitCor2Transversal G M U t ht hU = explicitCor2Transversal G M U t' ht' hU := by
  refine AddMonoidHom.ext fun x => ?_
  induction x using QuotientAddGroup.induction_on with
  | _ f =>
    rw [explicitCor2Transversal_mk, explicitCor2Transversal_mk, H2pi_eq_iff,
      coe_cocyclesCor2, coe_cocyclesCor2,
      cochainsCor2_changeTransversal G M U t ht t' ht' (mem_Z2_iff.1 f.2).2,
      sub_add_eq_sub_sub, sub_self, zero_sub]
    have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
    refine neg_mem (mem_B2_iff.2 ⟨_, ?_, rfl⟩)
    refine continuous_finsetSum _ fun u _ => Continuous.const_smul ?_ (t u)
    have hdiff : Continuous fun γ : G => transversalDiff U t t' (γ⁻¹ • u) :=
      continuous_of_discreteTopology.comp (continuous_inv.smul continuous_const)
    exact ((mem_Z2_iff.1 f.2).1.comp
        (continuous_const.prodMk ((continuous_lWord U t' hU u).subtype_mk _))).sub
      ((mem_Z2_iff.1 f.2).1.comp
        (((continuous_lWord U t hU u).subtype_mk _).prodMk (hdiff.subtype_mk _)))

/-- **Corestriction in degree two**, at the canonical transversal `Quotient.out`. -/
noncomputable def explicitCor2 : H2 U M →+ H2 G M :=
  explicitCor2Transversal G M U Quotient.out Quotient.out_eq hU

/-- The canonical degree-two corestriction can be computed using any transversal. -/
theorem explicitCor2_eq_transversal :
    explicitCor2 G M U hU = explicitCor2Transversal G M U t ht hU :=
  explicitCor2_changeTransversal G M U Quotient.out Quotient.out_eq hU t ht

/-- Canonical degree-two corestriction sends the class of a continuous `2`-cocycle to the class of
its corestriction cochain over `Quotient.out`. -/
@[simp]
theorem explicitCor2_mk (f : Z2 U M) :
    explicitCor2 G M U hU (f : H2 U M) =
      (cocyclesCor2 G M U Quotient.out Quotient.out_eq hU f : H2 G M) :=
  explicitCor2Transversal_mk G M U Quotient.out Quotient.out_eq hU f

/-- **`cor²_t ∘ res² = (G : U) • id`** on `H²(G, M)`, for a variable transversal. On cochains the
two sides differ by the coboundary recorded in `TauCeti.ContCohomology.cochainsCor2_res`. -/
theorem explicitCor2Transversal_comp_res2 (x : H2 G M) :
    explicitCor2Transversal G M U t ht hU (explicitRes2 G M U x) = U.index • x := by
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    have hns : ((U.index • c : Z2 G M) : H2 G M) = U.index • (c : H2 G M) :=
      map_nsmul (H2pi G M) U.index c
    -- Restriction is evaluation of the cochain at the inclusion, by `cocyclesMap2_apply`; the
    -- identity coefficient map and the inclusion contribute nothing.
    have hres : ((cocyclesMap2 G M U M (ContinuousMonoidHom.subgroupSubtype U)
        (AddMonoidHom.id M) continuous_id (fun _ _ => rfl) c : Z2 U M) : U × U → M) =
          fun q : U × U => (c : G × G → M) ((q.1 : G), (q.2 : G)) :=
      funext fun q => cocyclesMap2_apply G M U M (ContinuousMonoidHom.subgroupSubtype U)
        (AddMonoidHom.id M) continuous_id (fun _ _ => rfl) c q.1 q.2
    rw [explicitRes2_mk, explicitCor2Transversal_mk, ← hns, H2pi_eq_iff,
      coe_cocyclesCor2, hres, cochainsCor2_res G M U t ht (mem_Z2_iff.1 c.2).2]
    have hcoe : ((U.index • c : Z2 G M) : G × G → M) = U.index • (c : G × G → M) := by
      simp
    rw [hcoe, add_sub_cancel_left]
    refine mem_B2_iff.2 ⟨_, ?_, rfl⟩
    refine continuous_finsetSum _ fun u _ => ?_
    exact ((mem_Z2_iff.1 c.2).1.comp
        (continuous_const.prodMk (continuous_lWord U t hU u))).sub
      ((mem_Z2_iff.1 c.2).1.comp (continuous_id.prodMk continuous_const))

/-- **`cor² ∘ res² = (G : U) • id`** on `H²(G, M)`. -/
theorem explicitCor2_comp_res2 (x : H2 G M) :
    explicitCor2 G M U hU (explicitRes2 G M U x) = U.index • x :=
  explicitCor2Transversal_comp_res2 G M U Quotient.out Quotient.out_eq hU x

end DegreeTwo

end TauCeti.ContCohomology
