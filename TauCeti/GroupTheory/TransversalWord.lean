/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Tactic.Group
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The transversal word of a subgroup

Let `U` be a subgroup of a group `G` and let `t : G ⧸ U → G` be a *transversal*, that is, a map
picking a representative of each coset. The **transversal word**
```
ℓᵗ_u(γ) = (t u)⁻¹ * γ * t (γ⁻¹ • u)
```
measures the failure of `γ * t u` to be the chosen representative of its own coset. It lies in `U`
whenever `t` really is a transversal, and it is a `1`-cocycle for the action of `G` on `G ⧸ U`:
```
ℓᵗ_u(γ) * ℓᵗ_{γ⁻¹ • u}(η) = ℓᵗ_u(γ * η).
```

This file records that calculus: `TauCeti.lWord` and the three identities that make it useful,
namely `TauCeti.lWord_mem`, `TauCeti.lWord_mul_lWord`, and
`TauCeti.transversal_mul_lWord`, the last of which is the rewriting rule
`t u * ℓᵗ_u(γ) = γ * t (γ⁻¹ • u)` that turns a `U`-cocycle relation into a `G`-cocycle relation.
It also records how the word changes when the transversal does (`TauCeti.transversalDiff` and
`TauCeti.transversalDiff_mul_lWord`), and continuity of `γ ↦ ℓᵗ_u(γ)` for an open subgroup of a
topological group.

The transversal is a variable throughout, and no condition is imposed on it except where one is
needed: only `lWord_mem` and `transversalDiff_mem` ask that `t` be a transversal at all.

## Implementation notes

Mathlib's `Subgroup.LeftTransversal` bundles a *set* of coset representatives, with
`Subgroup.leftQuotientEquiv` turning it into a map `G ⧸ U ≃ S`. The formulas that consume the
transversal word index sums by `G ⧸ U`, so a transversal is taken here in the equivalent form of a
map `t : G ⧸ U → G` satisfying `↑(t u) = u`; `Quotient.out` is the canonical example.

This material is the group-theoretic input to the corestriction maps of the roadmap at
`TauCetiRoadmap/ProfiniteCohomology/README.md`, Layer 6, whose §3 fixes the displayed formula.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] (U : Subgroup G) (t t' : G ⧸ U → G)

/-- The **transversal word** `ℓᵗ_u(γ) = (t u)⁻¹ * γ * t (γ⁻¹ • u)` of a subgroup `U ≤ G`, a map
`t : G ⧸ U → G`, a coset `u` and a group element `γ`. It lies in `U` as soon as `t` is a
transversal (`TauCeti.lWord_mem`). -/
def lWord (u : G ⧸ U) (γ : G) : G := (t u)⁻¹ * γ * t (γ⁻¹ • u)

theorem lWord_def (u : G ⧸ U) (γ : G) : lWord U t u γ = (t u)⁻¹ * γ * t (γ⁻¹ • u) := (rfl)

@[simp]
theorem lWord_one (u : G ⧸ U) : lWord U t u 1 = 1 := by simp [lWord_def]

/-- The rewriting rule `t u * ℓᵗ_u(γ) = γ * t (γ⁻¹ • u)`. It is what turns the cocycle relation of
a function on `U` into the cocycle relation of the corresponding sum over `G ⧸ U`. -/
theorem transversal_mul_lWord (u : G ⧸ U) (γ : G) :
    t u * lWord U t u γ = γ * t (γ⁻¹ • u) := by
  rw [lWord_def]
  group

/-- The rewriting rule at the translated coset: `t (γ • u) * ℓᵗ_{γ • u}(γ) = γ * t u`. -/
theorem transversal_smul_mul_lWord (u : G ⧸ U) (γ : G) :
    t (γ • u) * lWord U t (γ • u) γ = γ * t u := by
  rw [transversal_mul_lWord, inv_smul_smul]

/-- The **transversal 1-cocycle law** `ℓᵗ_u(γ) * ℓᵗ_{γ⁻¹ • u}(η) = ℓᵗ_u(γ * η)`. It holds for an
arbitrary map `t`, with no normality, no finite index and no transversal condition. -/
theorem lWord_mul_lWord (u : G ⧸ U) (γ η : G) :
    lWord U t u γ * lWord U t (γ⁻¹ • u) η = lWord U t u (γ * η) := by
  simp only [lWord_def, mul_inv_rev, mul_smul]
  group

/-- The transversal word of `γ⁻¹` is the inverse of the transversal word of `γ`, at the translated
coset. This is the cocycle law at `η = γ⁻¹`. -/
theorem lWord_inv (u : G ⧸ U) (γ : G) : lWord U t u γ⁻¹ = (lWord U t (γ • u) γ)⁻¹ := by
  have h := lWord_mul_lWord U t u γ⁻¹ γ
  rw [inv_inv, inv_mul_cancel, lWord_one] at h
  exact mul_eq_one_iff_eq_inv.mp h

/-- At the coset of the identity, and for a transversal normalized by `t 1 = 1`, the transversal
word of an element of `U` is that element again. This is the reduction that identifies the
restriction of a cochain to `U` inside a corestriction sum. -/
theorem lWord_mk_one_of_mem (h1 : t (QuotientGroup.mk 1) = 1) {γ : G} (hγ : γ ∈ U) :
    lWord U t (QuotientGroup.mk 1) γ = γ := by
  have h : (γ⁻¹ • (QuotientGroup.mk 1 : G ⧸ U)) = QuotientGroup.mk 1 := by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq, inv_inv, mul_one]
    exact hγ
  rw [lWord_def, h, h1, inv_one, one_mul, mul_one]

section IsTransversal

variable (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)
include ht

/-- The transversal word of a genuine transversal lies in `U`. -/
theorem lWord_mem (u : G ⧸ U) (γ : G) : lWord U t u γ ∈ U := by
  have h : (QuotientGroup.mk (γ * t (γ⁻¹ • u)) : G ⧸ U) = QuotientGroup.mk (t u) := by
    rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, ht, smul_inv_smul, ht]
  rw [lWord_def, mul_assoc, ← QuotientGroup.eq, h]

end IsTransversal

/-- The **difference of two transversals**, `d^{t,t'}_u = (t u)⁻¹ * t' u`. It lies in `U` when both
are transversals, and it conjugates one transversal word into the other. -/
def transversalDiff (u : G ⧸ U) : G := (t u)⁻¹ * t' u

theorem transversalDiff_def (u : G ⧸ U) : transversalDiff U t t' u = (t u)⁻¹ * t' u := (rfl)

@[simp]
theorem transversalDiff_self (u : G ⧸ U) : transversalDiff U t t u = 1 := by
  simp [transversalDiff_def]

/-- The chosen representative of the second transversal, recovered from the first. -/
@[simp]
theorem transversal_mul_transversalDiff (u : G ⧸ U) : t u * transversalDiff U t t' u = t' u := by
  rw [transversalDiff_def, ← mul_assoc, mul_inv_cancel, one_mul]

theorem transversalDiff_mem (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)
    (ht' : ∀ u : G ⧸ U, (QuotientGroup.mk (t' u) : G ⧸ U) = u) (u : G ⧸ U) :
    transversalDiff U t t' u ∈ U := by
  rw [transversalDiff_def, ← QuotientGroup.eq, ht, ht']

/-- **Change of transversal.** The two transversal words differ by the transversal difference,
in the twisted form the change-of-transversal computations use. No hypothesis on `t` or `t'` is
needed for the identity itself. -/
theorem transversalDiff_mul_lWord (u : G ⧸ U) (γ : G) :
    transversalDiff U t t' u * lWord U t' u γ =
      lWord U t u γ * transversalDiff U t t' (γ⁻¹ • u) := by
  rw [transversalDiff_def, transversalDiff_def, lWord_def, lWord_def]
  group

section Topology

variable [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G]

/-- For an *open* subgroup `U` the transversal word `γ ↦ ℓᵗ_u(γ)` is continuous, for any map `t`
at all: the quotient `G ⧸ U` is discrete, so `γ ↦ t (γ⁻¹ • u)` is locally constant. -/
theorem continuous_lWord (hU : IsOpen (U : Set G)) (u : G ⧸ U) : Continuous (lWord U t u) := by
  have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  have h : lWord U t u = fun γ : G => (t u)⁻¹ * γ * t (γ⁻¹ • u) := funext (lWord_def U t u)
  rw [h]
  exact (continuous_const.mul continuous_id).mul
    (continuous_of_discreteTopology.comp (continuous_inv.smul continuous_const))

end Topology

end TauCeti
