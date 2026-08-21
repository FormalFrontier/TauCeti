/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Fundamental domains for subgroups by coset tiling

If `s` is a fundamental domain for a group `G` acting on `α`, a subgroup `H ≤ G` with
countable coset space has the `[G : H]`-fold tiling `⋃ q : G ⧸ H, (q.out)⁻¹ • s` as a
fundamental domain. This is how a fundamental domain for a finite-index subgroup (a
congruence subgroup, say) is manufactured from a fundamental domain of the ambient group;
countability of `G ⧸ H` — automatic at finite index — is what makes the tiling a countable
union.

## Main results

* `MeasureTheory.IsFundamentalDomain.iUnion_smul_of_transversal`: for any family `r : ι → G`
  with `i ↦ ⟦(r i)⁻¹⟧` bijective onto `G ⧸ H`, the tiling `⋃ i, r i • s` is an
  `H`-fundamental domain.
* `MeasureTheory.IsFundamentalDomain.subgroup_iUnion_out_inv_smul`: the special case of the
  canonical representatives, `⋃ q : G ⧸ H, (q.out)⁻¹ • s`.
* `MeasureTheory.IsFundamentalDomain.smul_of_eq_conjAct_pointwise_smul`: an `H₁`-fundamental domain
  translates to a `g H₁ g⁻¹`-fundamental domain under `g`.
* `MeasureTheory.IsFundamentalDomain.aedisjoint_smul_of_inv_mul_mem`: translates `g₁ • D`,
  `g₂ • D` of an `H`-fundamental domain are a.e. disjoint whenever `g₁ ≠ g₂` and
  `g₁⁻¹ * g₂ ∈ H` (needing only quasi-measure-preservation of the one translation).

Ported from the
[AINTLIB `LeanModularForms` project](https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms),
`projects/LeanModularForms/Modularforms/PeterssonLevelN.lean` (measure-theory section), as a
prerequisite for fundamental domains of congruence subgroups.
-/

public section

namespace MeasureTheory

open Measure Set

open scoped Pointwise

@[to_additive]
private theorem eq_of_mul_transversal {G : Type*} [Group G] {H : Subgroup G}
    {ι : Type*} {r : ι → G}
    (he : Function.Injective (fun i ↦ (QuotientGroup.mk ((r i)⁻¹) : G ⧸ H)))
    {i j : ι} {a b : H} (hh : (a : G) * r i = (b : G) * r j) : a = b ∧ i = j := by
  have hmem : (r j : G) * (r i)⁻¹ ∈ H := by
    have he' : (b : G)⁻¹ * (a : G) = (r j : G) * (r i)⁻¹ := by
      have h2 : (b : G)⁻¹ * ((a : G) * r i) * (r i)⁻¹
          = (b : G)⁻¹ * ((b : G) * r j) * (r i)⁻¹ := by rw [hh]
      simpa [mul_assoc] using h2
    rw [← he']
    exact H.mul_mem (H.inv_mem b.2) a.2
  obtain rfl : i = j := he <| by
    rw [eq_comm, QuotientGroup.eq]
    simpa [inv_inv] using hmem
  exact ⟨Subtype.ext (mul_right_cancel hh), rfl⟩

/-- **Transversal coset tiling of a fundamental domain.** If `s` is a fundamental domain
for a group `G` acting on `α`, `H ≤ G` a subgroup, and `r : ι → G` a family such that
`i ↦ ⟦(r i)⁻¹⟧` enumerates the left cosets `G ⧸ H` bijectively, then `⋃ i, r i • s` is a
fundamental domain for the restricted `H`-action. The inverses make `r` a *right*
transversal: each `x ∈ G` factors as `h * r i` with `h ∈ H` for exactly one `i`.

The index type must be countable (`[Countable ι]`), so that the tiling is a countable union.
Beyond that, the *only* measure-theoretic hypothesis is null-measurability of the individual
translates `r i • s`: measurability and invariance of the whole ambient action are not needed.
`subgroup_iUnion_out_inv_smul` is the convenience form that supplies `hnull` from
`[MeasurableConstSMul G α]` and `[SMulInvariantMeasure G α μ]`. -/
@[to_additive /-- **Transversal coset tiling of a fundamental domain.** If `s` is a fundamental
domain for an additive group `G` acting on `α`, `H ≤ G` a subgroup, and `r : ι → G` a family
over a **countable** index type (`[Countable ι]`) such that `i ↦ ⟦-(r i)⟧` enumerates the
cosets `G ⧸ H` bijectively, then `⋃ i, r i +ᵥ s` is a fundamental domain for the restricted
`H`-action. Beyond countability the only measure-theoretic hypothesis is null-measurability
of the individual translates `r i +ᵥ s`. -/]
theorem IsFundamentalDomain.iUnion_smul_of_transversal
    {G α ι : Type*} [Group G] [MeasurableSpace α] [MulAction G α] [Countable ι]
    {μ : Measure α}
    {H : Subgroup G} {s : Set α} (hs : IsFundamentalDomain G s μ)
    {r : ι → G} (hnull : ∀ i, NullMeasurableSet (r i • s) μ)
    (hr : Function.Bijective fun i ↦ (QuotientGroup.mk ((r i)⁻¹) : G ⧸ H)) :
    IsFundamentalDomain H (⋃ i, r i • s) μ := by
  set T : Set α := ⋃ i, r i • s with hT_def
  refine ⟨.iUnion hnull, ?_, ?_⟩
  · filter_upwards [hs.ae_covers] with τ ⟨g, hg⟩
    obtain ⟨i, hi⟩ := hr.surjective (QuotientGroup.mk g)
    have hmem : (r i) * g ∈ H := by
      rw [QuotientGroup.eq] at hi
      simpa [inv_inv] using hi
    refine ⟨⟨(r i) * g, hmem⟩, ?_⟩
    rw [Submonoid.mk_smul, mul_smul]
    exact Set.mem_iUnion.mpr ⟨i, Set.smul_mem_smul_set hg⟩
  · intro h₁ h₂ hne
    simp only [Function.onFun]
    rw [MulAction.subgroup_smul_def h₁, MulAction.subgroup_smul_def h₂, hT_def]
    simp only [Set.smul_set_iUnion, AEDisjoint.iUnion_left_iff, AEDisjoint.iUnion_right_iff,
      ← mul_smul]
    exact fun i₁ i₂ ↦ hs.aedisjoint fun heq ↦ hne (eq_of_mul_transversal hr.injective heq).1

/-- **Subgroup coset tiling of a fundamental domain.** If `s` is a fundamental
domain for a group `G` acting on `α`, then for any subgroup `H ≤ G`, the union of
`[G : H]`-many translates `(q.out)⁻¹ • s` (for `q ∈ G ⧸ H`) is a fundamental
domain for the restricted `H`-action on `α`: the inverses `(q.out)⁻¹` of the canonical
representatives form the right transversal. The coset space must be countable
(`[Countable (G ⧸ H)]`) — in particular this covers every finite-index subgroup. This is
`IsFundamentalDomain.iUnion_smul_of_transversal` at `r q = (q.out)⁻¹`. -/
@[to_additive /-- **Subgroup coset tiling of a fundamental domain.** If `s` is a fundamental
domain for an additive group `G` acting on `α`, then for any subgroup `H ≤ G` whose coset
space is **countable** (`[Countable (G ⧸ H)]`, automatic at finite index), the union of the
translates `-q.out +ᵥ s` (for `q ∈ G ⧸ H`) is a fundamental domain for the restricted
`H`-action on `α`. -/]
theorem IsFundamentalDomain.subgroup_iUnion_out_inv_smul
    {G α : Type*} [Group G] [MeasurableSpace α] [MulAction G α]
    [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]
    (H : Subgroup G) [Countable (G ⧸ H)] {s : Set α}
    (hs : IsFundamentalDomain G s μ) :
    IsFundamentalDomain H (⋃ q : G ⧸ H, ((q.out : G))⁻¹ • s) μ :=
  hs.iUnion_smul_of_transversal (r := fun q : G ⧸ H ↦ (q.out : G)⁻¹)
      (fun q ↦ hs.nullMeasurableSet_smul _) <| by
    have h_id : (fun q : G ⧸ H ↦ (QuotientGroup.mk (((q.out : G))⁻¹⁻¹) : G ⧸ H)) = id := by
      funext q
      simp [inv_inv]
    rw [h_id]
    exact Function.bijective_id

/-- **Conjugation-shift of a fundamental domain.** If `s` is an `H₁`-fundamental
domain (where `H₁ ≤ G`) and `H₂` is the pointwise conjugate `g · H₁ · g⁻¹`
(in `Subgroup` pointwise smul form, via the `ConjAct G`-action), then
`g • s` is an `H₂`-fundamental domain. Only quasi-measure-preservation of the single
translation `x ↦ g⁻¹ • x` is required, not invariance under the whole group. -/
theorem IsFundamentalDomain.smul_of_eq_conjAct_pointwise_smul
    {G α : Type*} [Group G] [MeasurableSpace α] [MulAction G α]
    {μ : Measure α}
    {H₁ H₂ : Subgroup G} {s : Set α} (hs : IsFundamentalDomain H₁ s μ)
    {g : G} (hg : Measure.QuasiMeasurePreserving (fun x : α ↦ g⁻¹ • x) μ μ)
    (hgH : H₂ = ConjAct.toConjAct g • H₁) :
    IsFundamentalDomain H₂ (g • s) μ := by
  subst hgH
  -- `Subgroup.pointwise_smul_def` is `rfl`, and the `ConjAct` monoid endomorphism at `g` is
  -- definitionally `MulAut.conj g`; naming the target form here (rather than letting the
  -- lemma leave it as `toMonoidEnd …`) is what lets `MulEquiv.subgroupMap_symm_apply`
  -- rewrite below, since simp matches the subgroup index syntactically.
  rw [show ConjAct.toConjAct g • H₁ = H₁.map (MulAut.conj g : G ≃* G) from
    Subgroup.pointwise_smul_def _]
  refine hs.image_of_equiv (MulAction.toPerm g) hg
    ((MulAut.conj g).subgroupMap H₁).symm.toEquiv fun h₂ x ↦ ?_
  -- `MulEquiv.subgroupMap` sends `h₁` to `g * h₁ * g⁻¹`, so its inverse sends `h₂` to
  -- `g⁻¹ * h₂ * g`; `MulAction.subgroup_smul_def` restricts the subtype action to the
  -- ambient one on each side.
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulEquiv.subgroupMap_symm_apply,
    MulAut.conj_symm_apply, MulAction.subgroup_smul_def, MulAction.toPerm_apply, smul_smul,
    mul_inv_cancel_left, mul_assoc]

/-- **AE-disjointness of arbitrary `G`-translates related by an `H`-element.**
Let `D` be a fundamental domain for a subgroup `H ≤ G` acting on `α` with a measure `μ`.
For any distinct pair `g₁, g₂ ∈ G` whose relative
position `g₁⁻¹ * g₂` lies in `H`, the translates `g₁ • D` and `g₂ • D` are
`AE`-disjoint with respect to `μ` — needing only quasi-measure-preservation of the single
translation `x ↦ g₁⁻¹ • x`, not invariance under the whole group. -/
@[to_additive /-- **AE-disjointness of arbitrary `G`-translates related by an `H`-element.**
Let `D` be a fundamental domain for a subgroup `H ≤ G` of an additive group acting on `α`
with a measure `μ`. For any distinct pair `g₁, g₂ ∈ G` with `-g₁ + g₂ ∈ H`, the translates
`g₁ +ᵥ D` and `g₂ +ᵥ D` are `AE`-disjoint, given quasi-measure-preservation of the single
translation `x ↦ -g₁ +ᵥ x`. -/]
theorem IsFundamentalDomain.aedisjoint_smul_of_inv_mul_mem
    {G α : Type*} [Group G] [MeasurableSpace α] [MulAction G α]
    {μ : Measure α}
    {H : Subgroup G} {D : Set α} (hD : IsFundamentalDomain H D μ)
    {g₁ g₂ : G} (hg₁ : Measure.QuasiMeasurePreserving (fun x : α ↦ g₁⁻¹ • x) μ μ)
    (h_mem : g₁⁻¹ * g₂ ∈ H) (h_ne : g₁ ≠ g₂) :
    AEDisjoint μ (g₁ • D) (g₂ • D) := by
  have h_ne' : g₁⁻¹ * g₂ ≠ 1 := fun h ↦ h_ne (inv_mul_eq_one.mp h)
  have h_core : AEDisjoint μ ((1 : H) • D) ((⟨g₁⁻¹ * g₂, h_mem⟩ : H) • D) :=
    hD.aedisjoint fun heq ↦ h_ne' <| by
      simpa [Subgroup.coe_one, eq_comm] using congr_arg (Subtype.val : H → G) heq
  rw [one_smul, MulAction.subgroup_smul_def] at h_core
  -- Pull the disjointness back along `x ↦ g₁⁻¹ • x`; the two preimages are the stated translates.
  simpa [Set.preimage_smul_inv, smul_smul] using h_core.preimage hg₁

end MeasureTheory
