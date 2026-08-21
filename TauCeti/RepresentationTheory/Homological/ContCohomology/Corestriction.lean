/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.GroupTheory.Complement

/-!
# The corestriction cochain formulas in low degrees

For a finite-index subgroup `U` of a group `G` acting on an abelian group `M`, and a section
`t : G ⧸ U → G` of `G → G ⧸ U`, corestriction is given on inhomogeneous cochains by the three
transversal sums
```
cor⁰_t m = ∑ u, t u • m,
(cor¹_t f) γ = ∑ u, t u • f (ℓᵗ_u γ),
(cor²_t f) (γ, η) = ∑ u, t u • f (ℓᵗ_u γ, ℓᵗ_{γ⁻¹ • u} η),
```
where `ℓᵗ` is the transversal word `TauCeti.lWord`. This file defines those three cochains and
proves the facts that make them descend to cohomology: they carry cocycles to cocycles and
coboundaries to coboundaries, they are additive in the cochain, they are continuous when `U` is
open and the cochain is continuous, and composing with restriction multiplies a class by the
index.

## Main definitions and results

* `TauCeti.corCochain₀`, `TauCeti.corCochain₁`, `TauCeti.corCochain₂`: the three transversal sums.
* `TauCeti.smul_corCochain₀`: the degree-zero sum carries `U`-invariants to `G`-invariants, so
  `cor⁰` is the norm map `Mᵁ → M^G`.
* `TauCeti.isCocycle₁_corCochain₁`, `TauCeti.isCocycle₂_corCochain₂`: cocycles go to cocycles.
* `TauCeti.corCochain₁_smul_sub`, `TauCeti.corCochain₂_smul_sub_add`: the corestriction of a
  coboundary is the coboundary of the corestriction, with its witness computed.
* `TauCeti.corCochain₁_comp_subtype_apply`: `cor¹ ∘ res¹` differs from multiplication by the index
  by the explicit coboundary of `∑ v, f (t v)`.
* `TauCeti.continuous_corCochain₁`, `TauCeti.continuous_corCochain₂`: continuity for an open `U`.

## Implementation notes

The action factor `t u •` in each formula is forced, not decoration: the proofs that the sums are
cocycles rewrite `t u * ℓᵗ_u(γ) = γ * t (γ⁻¹ • u)` (`TauCeti.mul_lWord`) and then reindex the sum
along `u ↦ γ • u`. A formula without the factor is correct for a trivial action and false in
general.

"Corestriction" here is the classical cohomological transfer of Neukirch-Schmidt-Wingberg I §5,
not the covariant functoriality of group *homology* that
`Mathlib/RepresentationTheory/Homological/GroupHomology/Functoriality.lean` calls by the same name.

Cocycles and coboundaries are Mathlib's unbundled `groupCohomology.IsCocycle₁`,
`IsCocycle₂`, `IsCoboundary₁` and `IsCoboundary₂`, so the statements apply verbatim to the
subgroup `U` and to `G`. Continuity is a predicate on the cochain rather than part of its type.

This implements the transversal half of Layer 6 of the human-authored roadmap at
`TauCetiRoadmap/ProfiniteCohomology/README.md`.
-/

public section

namespace TauCeti

open groupCohomology

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [DistribMulAction G M]

section TransversalWordContinuity

variable [TopologicalSpace G] [IsTopologicalGroup G] {X : Type*} [TopologicalSpace X]

/-- The transversal word of an **open** subgroup is continuous in both of its arguments: the
quotient `G ⧸ U` is then discrete, so the chosen representatives vary locally constantly. This is
the topological input of `TauCeti.continuous_corCochain₁` and `TauCeti.continuous_corCochain₂`. -/
theorem continuous_lWord (U : Subgroup G) (t : G ⧸ U → G) (hU : IsOpen (U : Set G))
    {a : X → G ⧸ U} {b : X → G} (ha : Continuous a) (hb : Continuous b) :
    Continuous fun x => lWord U t (a x) (b x) := by
  have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  have h₁ : Continuous fun x => t (a x) := continuous_of_discreteTopology.comp ha
  have h₂ : Continuous fun x => t ((b x)⁻¹ • a x) :=
    continuous_of_discreteTopology.comp (hb.inv.smul ha)
  simp only [lWord_def]
  exact (h₁.inv.mul hb).mul h₂

end TransversalWordContinuity

variable (U : Subgroup G) [Fintype (G ⧸ U)] (t : G ⧸ U → G)

/-- **Corestriction in degree 0** for the section `t`: the norm `∑ u, t u • m`. -/
@[expose] def corCochain₀ (m : M) : M := ∑ u : G ⧸ U, t u • m

theorem corCochain₀_def (m : M) : corCochain₀ U t m = ∑ u : G ⧸ U, t u • m := rfl

variable (ht : ∀ x : G ⧸ U, (t x : G ⧸ U) = x)

/-- **Corestriction in degree 1** for the section `t`:
`(cor¹_t f) γ = ∑ u, t u • f (ℓᵗ_u γ)`, where `f` is a `1`-cochain on `U`. -/
@[expose] def corCochain₁ (f : U → M) (γ : G) : M :=
  ∑ u : G ⧸ U, t u • f ⟨lWord U t u γ, lWord_mem ht u γ⟩

theorem corCochain₁_def (f : U → M) (γ : G) :
    corCochain₁ U t ht f γ = ∑ u : G ⧸ U, t u • f ⟨lWord U t u γ, lWord_mem ht u γ⟩ := rfl

/-- **Corestriction in degree 2** for the section `t`:
`(cor²_t f) (γ, η) = ∑ u, t u • f (ℓᵗ_u γ, ℓᵗ_{γ⁻¹ • u} η)`, where `f` is a `2`-cochain on `U`. -/
@[expose] def corCochain₂ (f : U × U → M) (p : G × G) : M :=
  ∑ u : G ⧸ U, t u • f (⟨lWord U t u p.1, lWord_mem ht u p.1⟩,
    ⟨lWord U t (p.1⁻¹ • u) p.2, lWord_mem ht _ p.2⟩)

theorem corCochain₂_def (f : U × U → M) (p : G × G) :
    corCochain₂ U t ht f p = ∑ u : G ⧸ U, t u • f (⟨lWord U t u p.1, lWord_mem ht u p.1⟩,
      ⟨lWord U t (p.1⁻¹ • u) p.2, lWord_mem ht _ p.2⟩) := rfl

theorem corCochain₂_apply (f : U × U → M) (γ η : G) :
    corCochain₂ U t ht f (γ, η) = ∑ u : G ⧸ U, t u • f (⟨lWord U t u γ, lWord_mem ht u γ⟩,
      ⟨lWord U t (γ⁻¹ • u) η, lWord_mem ht _ η⟩) := rfl

section Additive

@[simp]
theorem corCochain₀_zero : corCochain₀ U t (0 : M) = 0 := by simp [corCochain₀_def]

/-- Corestriction in degree 0 is additive. -/
theorem corCochain₀_add (m n : M) :
    corCochain₀ U t (m + n) = corCochain₀ U t m + corCochain₀ U t n := by
  simp [corCochain₀_def, smul_add, Finset.sum_add_distrib]

@[simp]
theorem corCochain₁_zero : corCochain₁ U t ht (0 : U → M) = 0 := by
  funext γ; simp [corCochain₁_def]

/-- Corestriction in degree 1 is additive in the cochain. -/
theorem corCochain₁_add (f g : U → M) :
    corCochain₁ U t ht (f + g) = corCochain₁ U t ht f + corCochain₁ U t ht g := by
  funext γ; simp [corCochain₁_def, smul_add, Finset.sum_add_distrib]

@[simp]
theorem corCochain₂_zero : corCochain₂ U t ht (0 : U × U → M) = 0 := by
  funext p; simp [corCochain₂_def]

/-- Corestriction in degree 2 is additive in the cochain. -/
theorem corCochain₂_add (f g : U × U → M) :
    corCochain₂ U t ht (f + g) = corCochain₂ U t ht f + corCochain₂ U t ht g := by
  funext p; simp [corCochain₂_def, smul_add, Finset.sum_add_distrib]

end Additive

section Degree0

include ht in
/-- The degree-zero corestriction of a `U`-invariant element is `G`-invariant: `cor⁰` is the norm
map `Mᵁ → M^G`. -/
theorem smul_corCochain₀ {m : M} (hm : ∀ a ∈ U, a • m = m) (γ : G) :
    γ • corCochain₀ U t m = corCochain₀ U t m := by
  rw [corCochain₀_def, Finset.smul_sum]
  refine Fintype.sum_equiv (MulAction.toPerm γ) _ _ fun u => ?_
  have h : t (γ • u) * lWord U t (γ • u) γ = γ * t u := by rw [mul_lWord, inv_smul_smul]
  rw [MulAction.toPerm_apply, smul_smul, ← h, ← smul_smul, hm _ (lWord_mem ht _ γ)]

/-- **`cor⁰ ∘ res⁰` is multiplication by the index.** On a `G`-invariant element the transversal
sum collapses. -/
theorem corCochain₀_eq_index_smul {m : M} (hm : ∀ g : G, g • m = m) :
    corCochain₀ U t m = U.index • m := by
  rw [corCochain₀_def, Finset.sum_congr rfl fun u _ => hm (t u), Finset.sum_const,
    Finset.card_univ, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

end Degree0

section Cocycles

/-- The key reindexing step behind every statement in this file: after rewriting
`t u * ℓᵗ_u(γ) = γ * t (γ⁻¹ • u)`, the sum over `u` of the `γ`-twisted terms is `γ` acting on the
sum. -/
private theorem sum_smul_comp_inv_smul (γ : G) (F : G ⧸ U → M) :
    ∑ u : G ⧸ U, γ • F (γ⁻¹ • u) = γ • ∑ u : G ⧸ U, F u := by
  rw [Finset.smul_sum]
  exact Fintype.sum_equiv (MulAction.toPerm γ⁻¹) _ _ fun u => rfl

/-- **Corestriction preserves 1-cocycles.** The proof uses the action factor `t u •`: it turns
`t u * ℓᵗ_u(γ)` into `γ * t (γ⁻¹ • u)`, which is what produces the `γ •` of the cocycle law. -/
theorem isCocycle₁_corCochain₁ {f : U → M} (hf : IsCocycle₁ f) :
    IsCocycle₁ (corCochain₁ U t ht f) := by
  intro γ η
  rw [corCochain₁_def, corCochain₁_def, corCochain₁_def,
    ← sum_smul_comp_inv_smul U γ fun u => (t u : G) • f ⟨lWord U t u η, lWord_mem ht u η⟩,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hsplit : (⟨lWord U t u (γ * η), lWord_mem ht u (γ * η)⟩ : U)
      = ⟨lWord U t u γ, lWord_mem ht u γ⟩ * ⟨lWord U t (γ⁻¹ • u) η, lWord_mem ht _ η⟩ :=
    Subtype.ext (lWord_mul U t u γ η)
  rw [hsplit, hf, smul_add, add_left_inj, smul_smul, Submonoid.smul_def, smul_smul, mul_lWord,
    ← smul_smul]

/-- **Corestriction preserves 2-cocycles.** As in degree 1 the action factor `t u •` is what makes
the sum a cocycle; the two transversal words are chained by `TauCeti.lWord_mul`. -/
theorem isCocycle₂_corCochain₂ {f : U × U → M} (hf : IsCocycle₂ f) :
    IsCocycle₂ (corCochain₂ U t ht f) := by
  intro γ η θ
  rw [corCochain₂_def, corCochain₂_def, corCochain₂_def, corCochain₂_def,
    ← sum_smul_comp_inv_smul U γ fun u => (t u : G) • f
      (⟨lWord U t u η, lWord_mem ht u η⟩, ⟨lWord U t (η⁻¹ • u) θ, lWord_mem ht _ θ⟩),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hfst : (⟨lWord U t u (γ * η), lWord_mem ht u (γ * η)⟩ : U)
      = ⟨lWord U t u γ, lWord_mem ht u γ⟩ * ⟨lWord U t (γ⁻¹ • u) η, lWord_mem ht _ η⟩ :=
    Subtype.ext (lWord_mul U t u γ η)
  have hsnd : (⟨lWord U t ((γ * η)⁻¹ • u) θ, lWord_mem ht _ θ⟩ : U)
      = ⟨lWord U t (η⁻¹ • γ⁻¹ • u) θ, lWord_mem ht _ θ⟩ := by
    rw [Subtype.mk_eq_mk, mul_inv_rev, mul_smul]
  have hthd : (⟨lWord U t (γ⁻¹ • u) (η * θ), lWord_mem ht _ (η * θ)⟩ : U)
      = ⟨lWord U t (γ⁻¹ • u) η, lWord_mem ht _ η⟩ *
        ⟨lWord U t (η⁻¹ • γ⁻¹ • u) θ, lWord_mem ht _ θ⟩ :=
    Subtype.ext (lWord_mul U t (γ⁻¹ • u) η θ)
  rw [hfst, hsnd, hthd, ← smul_add, hf, smul_add, add_left_inj, smul_smul, Submonoid.smul_def,
    smul_smul, mul_lWord, ← smul_smul]

end Cocycles

section Coboundaries

/-- **Corestriction carries coboundaries to coboundaries in degree 1,** with the witness computed:
the corestriction of `d⁰ m` is `d⁰` of the degree-zero corestriction of `m`. -/
theorem corCochain₁_smul_sub (m : M) (γ : G) :
    corCochain₁ U t ht (fun a : U => (a : G) • m - m) γ
      = γ • corCochain₀ U t m - corCochain₀ U t m := by
  rw [corCochain₁_def, corCochain₀_def,
    ← sum_smul_comp_inv_smul U γ fun u => (t u : G) • m, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [smul_sub, sub_left_inj, smul_smul, smul_smul, mul_lWord]

/-- Corestriction descends to `H¹`: it carries 1-coboundaries to 1-coboundaries. -/
theorem isCoboundary₁_corCochain₁ {f : U → M} (hf : IsCoboundary₁ f) :
    IsCoboundary₁ (corCochain₁ U t ht f) := by
  obtain ⟨m, hm⟩ := hf
  refine ⟨corCochain₀ U t m, fun γ => ?_⟩
  rw [← corCochain₁_smul_sub U t ht m γ]
  exact congrFun (congrArg _ (funext fun a => hm a)) γ

/-- **Corestriction carries coboundaries to coboundaries in degree 2,** with the witness computed:
the corestriction of `d¹ c` is `d¹` of the degree-one corestriction of `c`. -/
theorem corCochain₂_smul_sub_add (c : U → M) (γ η : G) :
    corCochain₂ U t ht (fun p : U × U => (p.1 : G) • c p.2 - c (p.1 * p.2) + c p.1) (γ, η)
      = γ • corCochain₁ U t ht c η - corCochain₁ U t ht c (γ * η) + corCochain₁ U t ht c γ := by
  rw [corCochain₂_apply, corCochain₁_def, corCochain₁_def, corCochain₁_def,
    ← sum_smul_comp_inv_smul U γ fun u => (t u : G) • c ⟨lWord U t u η, lWord_mem ht u η⟩,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hsplit : (⟨lWord U t u γ, lWord_mem ht u γ⟩ : U) *
      ⟨lWord U t (γ⁻¹ • u) η, lWord_mem ht _ η⟩
      = ⟨lWord U t u (γ * η), lWord_mem ht u (γ * η)⟩ :=
    Subtype.ext (lWord_mul U t u γ η).symm
  rw [hsplit, smul_add, smul_sub, add_left_inj, sub_left_inj, smul_smul, smul_smul, mul_lWord]

/-- Corestriction descends to `H²`: it carries 2-coboundaries to 2-coboundaries. -/
theorem isCoboundary₂_corCochain₂ {f : U × U → M} (hf : IsCoboundary₂ f) :
    IsCoboundary₂ (corCochain₂ U t ht f) := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨corCochain₁ U t ht c, fun γ η => ?_⟩
  rw [← corCochain₂_smul_sub_add U t ht c γ η]
  exact congrFun (congrArg _ (funext fun p : U × U => hc p.1 p.2)) (γ, η)

end Coboundaries

section CompRestriction

/-- **The cochain-level form of `cor¹ ∘ res¹`.** For a 1-cocycle `f` on `G` the corestriction of
its restriction to `U` is `(G : U) • f` plus the coboundary of the element `∑ v, f (t v)`. The
correction term is what makes `cor ∘ res = (G : U) • id` a statement about cohomology classes
rather than about cochains. -/
theorem corCochain₁_comp_subtype_apply {f : G → M} (hf : IsCocycle₁ f) (γ : G) :
    corCochain₁ U t ht (fun a : U => f a) γ
      = U.index • f γ + (γ • (∑ v : G ⧸ U, f (t v)) - ∑ v : G ⧸ U, f (t v)) := by
  have step : ∀ u : G ⧸ U, (t u : G) • f (lWord U t u γ)
      = γ • f (t (γ⁻¹ • u)) + f γ - f (t u) := by
    intro u
    rw [lWord_def, mul_assoc, hf, hf, smul_add, smul_smul, mul_inv_cancel, one_smul,
      map_inv_of_isCocycle₁ hf, ← sub_eq_add_neg]
  rw [corCochain₁_def, Finset.sum_congr rfl fun u _ => step u,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Subgroup.index_eq_card, Nat.card_eq_fintype_card,
    sum_smul_comp_inv_smul U γ fun v => f (t v)]
  abel

end CompRestriction

section Continuity

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul G M]

/-- The degree-one corestriction of a continuous cochain over an **open** subgroup is
continuous. -/
theorem continuous_corCochain₁ (hU : IsOpen (U : Set G)) {f : U → M} (hf : Continuous f) :
    Continuous (corCochain₁ U t ht f) := by
  refine continuous_finsetSum _ fun u _ => Continuous.const_smul ?_ _
  exact hf.comp (((continuous_lWord U t hU continuous_const continuous_id).subtype_mk _))

/-- The degree-two corestriction of a continuous cochain over an **open** subgroup is
continuous. -/
theorem continuous_corCochain₂ (hU : IsOpen (U : Set G)) {f : U × U → M} (hf : Continuous f) :
    Continuous (corCochain₂ U t ht f) := by
  refine continuous_finsetSum _ fun u _ => Continuous.const_smul ?_ _
  refine hf.comp (Continuous.prodMk ?_ ?_)
  · exact (continuous_lWord U t hU continuous_const continuous_fst).subtype_mk _
  · exact (continuous_lWord U t hU
      (continuous_fst.inv.smul continuous_const) continuous_snd).subtype_mk _

end Continuity

end TauCeti
