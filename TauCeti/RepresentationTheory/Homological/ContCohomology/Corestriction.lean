/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Ring.Action.Submonoid
public import Mathlib.GroupTheory.Index
public import TauCeti.GroupTheory.TransversalWord

/-!
# Corestriction in degree zero

For a subgroup `U` of finite index in a group `G` acting on an abelian group `M`, the **norm**
```
cor⁰_t m = ∑_{u : G ⧸ U} t u • m
```
attached to a transversal `t : G ⧸ U → G` carries the `U`-invariants `M^U` into the
`G`-invariants `M^G`. This is corestriction in degree `0` of the low-degree cohomology of `G` with
coefficients in `M`, degree `0` being the one in which the cochain complex plays no role:
`H⁰(G, M)` *is* `M^G`, so no continuity condition appears and the statements below are those of
an abstract group.

The main declarations are:

* `TauCeti.ContCohomology.explicitCor0Transversal`, the norm for a variable transversal, together
  with `TauCeti.ContCohomology.explicitCor0_changeTransversal`, which says it does not depend on
  the transversal chosen;
* `TauCeti.ContCohomology.explicitCor0`, its specialization at `t = Quotient.out`;
* `TauCeti.ContCohomology.explicitRes0`, restriction in degree `0`, and
  `TauCeti.ContCohomology.explicitCor_comp_res0`, the normalization
  `cor⁰ ∘ res⁰ = (G : U) • id`;
* `TauCeti.ContCohomology.mapFixedPoints`, the map of invariants induced by an equivariant map of
  coefficients, with the naturality squares
  `TauCeti.ContCohomology.mapFixedPoints_explicitRes0`,
  `TauCeti.ContCohomology.mapFixedPoints_explicitCor0Transversal` and
  `TauCeti.ContCohomology.mapFixedPoints_explicitCor0`.

The factor `t u •` in the formula is not decoration: without it the sum is not `G`-invariant, and
the proof of `TauCeti.ContCohomology.sum_transversal_smul_mem_fixedPoints` is exactly the
rewriting `t (γ • u) * ℓᵗ_{γ • u}(γ) = γ * t u` of `TauCeti.transversal_smul_mul_lWord`, followed
by reindexing the sum along `u ↦ γ • u`. A trivial-action formula that omits the factor is
correct for trivial coefficients and wrong in general.

Independence of the transversal is a theorem and not a definitional convenience, which is why the
transversal is a variable of `explicitCor0Transversal` before the public `explicitCor0` fixes it.
In positive degrees the corresponding statement changes the cochain by a coboundary; in degree `0`
the cochain itself is unchanged.

This implements the degree-`0` part of the Layer 6 milestone "Corestriction in degrees `0, 1, 2`"
of the human-authored roadmap at `TauCetiRoadmap/ProfiniteCohomology/README.md`, whose §3 fixes
the displayed formula and the normalization `cor ∘ res = index • id`.

## References

The normalization `cor ∘ res = (G : U) • id` is Neukirch–Schmidt–Wingberg, *Cohomology of Number
Fields*, 2nd ed., (1.5.7), and Serre, *Local Fields*, VII §7 Prop. 6. Both state it as an identity
of cohomology classes; degree `0` is the one degree in which it already holds on cochains, because
a degree-`0` cochain is an invariant element.
-/

public section

namespace TauCeti.ContCohomology

variable (G : Type*) [Group G] (M : Type*) [AddCommGroup M] [DistribMulAction G M]
  (U : Subgroup G)

/-- Unfolding helper: membership in `M^U` read as a statement about elements of `G` lying in `U`,
rather than about elements of the subtype `↥U`. -/
private theorem smul_eq_self_of_mem {m : M} (hm : m ∈ FixedPoints.addSubgroup U M) {x : G}
    (hx : x ∈ U) : x • m = m := by
  simpa using (FixedPoints.mem_addSubgroup _ _ _).mp hm ⟨x, hx⟩

/-- An element fixed by every element of `G` is fixed by every element of a subgroup `U`, so
`M^G ≤ M^U`. -/
theorem fixedPoints_addSubgroup_le : FixedPoints.addSubgroup G M ≤ FixedPoints.addSubgroup U M :=
  fun _ hm => (FixedPoints.mem_addSubgroup _ _ _).mpr fun x => by
    obtain ⟨x, hx⟩ := x
    simpa using (FixedPoints.mem_addSubgroup _ _ _).mp hm x

/-- **Restriction in degree `0`**: the inclusion `M^G ↪ M^U` of invariants along a subgroup
`U ≤ G`. -/
def explicitRes0 : FixedPoints.addSubgroup G M →+ FixedPoints.addSubgroup U M :=
  AddSubgroup.inclusion (fixedPoints_addSubgroup_le G M U)

@[simp]
theorem coe_explicitRes0 (m : FixedPoints.addSubgroup G M) :
    (explicitRes0 G M U m : M) = (m : M) := (rfl)

section Coefficients

variable {H A B : Type*} [Monoid H] [AddCommGroup A] [AddCommGroup B] [DistribMulAction H A]
  [DistribMulAction H B]

/-- **The map of invariants induced by an equivariant map of coefficients.** An additive map
`f : A →+ B` commuting with the action of `H` carries `A^H` into `B^H`. This is the vertical
arrow of the naturality squares for restriction and corestriction below. -/
def mapFixedPoints (f : A →+ B) (hf : ∀ (h : H) (a : A), f (h • a) = h • f a) :
    FixedPoints.addSubgroup H A →+ FixedPoints.addSubgroup H B where
  toFun a := ⟨f a, (FixedPoints.mem_addSubgroup _ _ _).mpr fun h => by
    rw [← hf, (FixedPoints.mem_addSubgroup _ _ _).mp a.2 h]⟩
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

@[simp]
theorem coe_mapFixedPoints (f : A →+ B) (hf : ∀ (h : H) (a : A), f (h • a) = h • f a)
    (a : FixedPoints.addSubgroup H A) : (mapFixedPoints f hf a : B) = f (a : A) := (rfl)

end Coefficients

/-- **Naturality of the degree-`0` restriction in the coefficients.** The map of invariants
induced by a `G`-equivariant additive map `f : M →+ N` of coefficients commutes with `res⁰`; on
the source of `res⁰` the induced map is taken for the action of `G`, on its target for the action
of `U`. -/
theorem mapFixedPoints_explicitRes0 {N : Type*} [AddCommGroup N] [DistribMulAction G N]
    (f : M →+ N) (hf : ∀ (g : G) (x : M), f (g • x) = g • f x)
    (m : FixedPoints.addSubgroup G M) :
    mapFixedPoints f (fun u : U => hf u) (explicitRes0 G M U m) =
      explicitRes0 G N U (mapFixedPoints f hf m) := by
  ext
  simp

section Transversal

variable [Fintype (G ⧸ U)] (t : G ⧸ U → G)
  (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)
include ht

/-- The norm `∑_{u : G ⧸ U} t u • m` of a `U`-invariant element is `G`-invariant. This is where
the factor `t u •` is used: `γ * t u` is `t (γ • u)` times a transversal word, which lies in `U`
and therefore fixes `m`, so translating by `γ` merely permutes the summands. -/
theorem sum_transversal_smul_mem_fixedPoints {m : M} (hm : m ∈ FixedPoints.addSubgroup U M) :
    ∑ u : G ⧸ U, t u • m ∈ FixedPoints.addSubgroup G M := by
  refine (FixedPoints.mem_addSubgroup _ _ _).mpr fun γ => ?_
  calc γ • ∑ u : G ⧸ U, t u • m
      = ∑ u : G ⧸ U, t (γ • u) • m := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [smul_smul, ← transversal_smul_mul_lWord U t u γ, ← smul_smul,
          smul_eq_self_of_mem G M U hm (lWord_mem U t ht (γ • u) γ)]
    _ = ∑ u : G ⧸ U, t u • m :=
        Fintype.sum_equiv (MulAction.toPerm γ) _ _ fun _ => rfl

/-- **Corestriction in degree `0` for a variable transversal**, the norm
`m ↦ ∑_{u : G ⧸ U} t u • m` from `M^U` to `M^G`. The transversal is a variable because
independence of it is a theorem (`TauCeti.ContCohomology.explicitCor0_changeTransversal`) and
cannot even be stated otherwise. -/
def explicitCor0Transversal :
    FixedPoints.addSubgroup U M →+ FixedPoints.addSubgroup G M where
  toFun m := ⟨∑ u : G ⧸ U, t u • (m : M), sum_transversal_smul_mem_fixedPoints G M U t ht m.2⟩
  map_zero' := by ext; simp
  map_add' a b := by ext; simp [smul_add, Finset.sum_add_distrib]

@[simp]
theorem coe_explicitCor0Transversal (m : FixedPoints.addSubgroup U M) :
    (explicitCor0Transversal G M U t ht m : M) = ∑ u : G ⧸ U, t u • (m : M) := (rfl)

/-- **Naturality of the degree-`0` corestriction in the coefficients.** The map of invariants
induced by a `G`-equivariant additive map `f : M →+ N` of coefficients commutes with the norm:
`cor⁰_t (f m) = f (cor⁰_t m)`. On the source the induced map is taken for the action of `U`,
on the target for the action of `G`. -/
theorem mapFixedPoints_explicitCor0Transversal {N : Type*} [AddCommGroup N]
    [DistribMulAction G N] (f : M →+ N) (hf : ∀ (g : G) (x : M), f (g • x) = g • f x)
    (m : FixedPoints.addSubgroup U M) :
    mapFixedPoints f hf (explicitCor0Transversal G M U t ht m) =
      explicitCor0Transversal G N U t ht (mapFixedPoints f (fun u : U => hf u) m) := by
  ext
  simp [map_sum, hf]

/-- **`cor⁰ ∘ res⁰ = (G : U) • id`**, for a variable transversal: on an element fixed by all of
`G` every summand of the norm is the element itself. Unlike its counterparts in degrees `1` and
`2`, this identity already holds on cochains, because a degree-`0` cochain is an invariant
element. -/
theorem explicitCor0Transversal_comp_res0 (m : FixedPoints.addSubgroup G M) :
    explicitCor0Transversal G M U t ht (explicitRes0 G M U m) = U.index • m := by
  have hm : ∀ u : G ⧸ U, t u • (m : M) = (m : M) := fun u =>
    (FixedPoints.mem_addSubgroup _ _ _).mp m.2 (t u)
  ext
  simp [hm, U.index_eq_card, Nat.card_eq_fintype_card]

end Transversal

variable [Fintype (G ⧸ U)]

/-- **Independence of the transversal in degree `0`.** Two transversals differ by a `U`-valued
factor, which acts trivially on `M^U`, so the two norms agree on the nose. In positive degrees the
corresponding statement holds only up to a coboundary. -/
theorem explicitCor0_changeTransversal (t t' : G ⧸ U → G)
    (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)
    (ht' : ∀ u : G ⧸ U, (QuotientGroup.mk (t' u) : G ⧸ U) = u) :
    explicitCor0Transversal G M U t ht = explicitCor0Transversal G M U t' ht' := by
  ext m
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← transversal_mul_transversalDiff U t t' u, ← smul_smul,
    smul_eq_self_of_mem G M U m.2 (transversalDiff_mem U t t' ht ht' u)]

/-- **Corestriction in degree `0`**, the norm `m ↦ ∑_{u : G ⧸ U} u.out • m` from `M^U` to `M^G`.
By `TauCeti.ContCohomology.explicitCor0_eq_transversal` it is computed by any transversal. -/
noncomputable def explicitCor0 :
    FixedPoints.addSubgroup U M →+ FixedPoints.addSubgroup G M :=
  explicitCor0Transversal G M U Quotient.out fun u => Quotient.out_eq u

@[simp]
theorem coe_explicitCor0 (m : FixedPoints.addSubgroup U M) :
    (explicitCor0 G M U m : M) = ∑ u : G ⧸ U, Quotient.out u • (m : M) := (rfl)

/-- The canonical degree-`0` corestriction is computed by *any* transversal `t`: the norm built
from `t` agrees with the one built from `Quotient.out`. -/
theorem explicitCor0_eq_transversal (t : G ⧸ U → G)
    (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u) :
    explicitCor0 G M U = explicitCor0Transversal G M U t ht :=
  explicitCor0_changeTransversal G M U _ t _ ht

/-- **Naturality of the canonical degree-`0` corestriction in the coefficients.** The map of
invariants induced by a `G`-equivariant additive map `f : M →+ N` of coefficients commutes with
`cor⁰`. -/
theorem mapFixedPoints_explicitCor0 {N : Type*} [AddCommGroup N] [DistribMulAction G N]
    (f : M →+ N) (hf : ∀ (g : G) (x : M), f (g • x) = g • f x)
    (m : FixedPoints.addSubgroup U M) :
    mapFixedPoints f hf (explicitCor0 G M U m) =
      explicitCor0 G N U (mapFixedPoints f (fun u : U => hf u) m) :=
  mapFixedPoints_explicitCor0Transversal G M U _ _ f hf m

/-- **`cor⁰ ∘ res⁰ = (G : U) • id`.** -/
theorem explicitCor_comp_res0 (m : FixedPoints.addSubgroup G M) :
    explicitCor0 G M U (explicitRes0 G M U m) = U.index • m := by
  rw [explicitCor0_eq_transversal G M U Quotient.out fun u => Quotient.out_eq u]
  exact explicitCor0Transversal_comp_res0 G M U _ _ m

end TauCeti.ContCohomology
