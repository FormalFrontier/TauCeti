/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree

import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.GroupTheory.Index
import TauCeti.GroupTheory.TransversalWord

/-!
# Corestriction in degree zero

For a finite-index subgroup `U` of a group `G` acting on an abelian group `M`, the norm attached
to a transversal `t : G ⧸ U → G` is

```text
cor⁰_t(m) = ∑ u : G ⧸ U, t u • m.
```

If `m` is fixed by `U`, this sum is fixed by `G`; it therefore defines an additive map
`H⁰(U, M) → H⁰(G, M)`.  The transversal is kept variable until its independence has been proved,
and the public map `explicitCor0` then uses `Quotient.out`.  The factor `t u •` is essential for
nontrivial coefficient actions: translating the sum permutes its terms only after applying the
transversal-word identity from `TauCeti.GroupTheory.TransversalWord`.

This is the degree-zero part of Layer 6 of the Profinite Cohomology roadmap.  The formulas and the
proof organization are adapted from the earlier, unmerged degree-zero portion of Tau Ceti PR
#4061, which was removed there because the canonical `H0` carrier had not yet landed.  This version
is stated against `TauCeti.ContCohomology.H0` and reuses the fixed-point functoriality now on
`main`.

## Main declarations

* `TauCeti.ContCohomology.explicitCor0Transversal`: the norm for a variable transversal.
* `TauCeti.ContCohomology.explicitCor0_changeTransversal`: independence of that transversal.
* `TauCeti.ContCohomology.explicitCor0`: the canonical degree-zero corestriction.
* `TauCeti.ContCohomology.explicitCor0_comp_res0`: the normalization
  `cor⁰ ∘ res⁰ = (G : U) • id`.

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
    _ = ∑ u : G ⧸ U, t u • m :=
      Fintype.sum_equiv (MulAction.toPerm γ) _ _ fun _ => rfl

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

end TauCeti.ContCohomology
