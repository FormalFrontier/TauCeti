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
# Corestriction in degrees zero and one

For a finite-index subgroup `U` of a group `G` acting on an abelian group `M`, the corestriction
attached to a transversal `t : G ⧸ U → G` is, in the two lowest degrees,

```text
cor⁰_t(m) = ∑ u : G ⧸ U, t u • m,
(cor¹_t f) γ = ∑ u : G ⧸ U, t u • f (ℓᵗ_u γ),
```

where `ℓᵗ_u(γ) = (t u)⁻¹ * γ * t (γ⁻¹ • u)` is the transversal word `TauCeti.lWord`.  In degree
zero, if `m` is fixed by `U` then the sum is fixed by `G`; in degree one, if `f` is a `1`-cocycle
on `U` then `cor¹_t f` is a `1`-cocycle on `G`, and `cor¹_t` carries coboundaries to coboundaries.
Both therefore descend to additive maps `Hⁱ(U, M) → Hⁱ(G, M)`.  The transversal is kept variable
until its independence has been proved, and the public maps `explicitCor0` and `explicitCor1` then
use `Quotient.out`.

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
hold.

Continuity is needed only for the passage from cochains to `H¹`, and only through openness of `U`:
`TauCeti.continuous_lWord` makes `γ ↦ ℓᵗ_u(γ)` continuous for an open `U` and *any* map `t`, so no
continuity is required of the transversal itself.

This is the degree-zero and degree-one part of Layer 6 of the Profinite Cohomology roadmap.  The
degree-zero formulas and proof organization are adapted from the earlier, unmerged degree-zero
portion of Tau Ceti PR #4061, which was removed there because the canonical `H0` carrier had not
yet landed.

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

end TauCeti.ContCohomology
