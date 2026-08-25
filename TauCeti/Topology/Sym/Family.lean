/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Sym.Family
public import TauCeti.Topology.PiCurry
public import TauCeti.Topology.Sym.Basic

/-!
# The symmetric power is locally a product, along a family

This file presents `Sym α n` locally as a product over a finite family `U : ι → Set α` of pairwise
disjoint open sets, and then produces the family that a *given* tuple
needs: in a Hausdorff space the distinct points of an unordered `n`-tuple have pairwise disjoint
open neighbourhoods, as small as one likes, and the tuple is a concatenation along them, with the
multiplicities as the degrees.

Together these two statements are what charts the symmetric power of a surface. A tuple with
distinct points `z₁, …, z_k` of multiplicities `n₁, …, n_k` has a neighbourhood in `Sym^n(Σ)`
homeomorphic to `Sym^{n₁}(U₁) × ⋯ × Sym^{n_k}(U_k)` for disjoint coordinate discs `U_j ∋ z_j`, and
each factor is an open subspace of affine space by
`TauCeti.Sym.isOpenEmbedding_coeffEquiv_comp_map`. Lane F4.1 of the analytic Heegaard Floer
roadmap needs exactly this to give `Sym^g(Σ)` its complex structure, after Ozsváth--Szabó
([arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.1); the charted structure itself is
in `TauCeti/Geometry/Manifold/SymmetricPower.lean`.

The open-embedding proof reduces to ordered tuples: `TauCeti.Sym.ofFn` is an open quotient map on
each member of the family, hence so is the product of those maps, and read on ordered tuples the
concatenation is the regrouping of `n` entries along a bijection `(Σ i, Fin (m i)) ≃ Fin n`, which
is a homeomorphism followed by the (open) inclusions of the members of the family.

## Main declarations

* `TauCeti.Sym.isOpenEmbedding_sumSubtype`: for a pairwise disjoint family of open sets,
  concatenation identifies the product of the symmetric powers of the members with an open
  subspace of `Sym α n`.
* `TauCeti.exists_mem_range_sumSubtype_of_t2`: in a Hausdorff space, every unordered
  tuple lies in the range of such a concatenation, along a family of arbitrarily small
  neighbourhoods of its distinct points indexed by those points.
-/

public section

open Topology

namespace TauCeti

namespace Sym

variable {α : Type*} [TopologicalSpace α] {ι : Type*} [Fintype ι] {U : ι → Set α} {m : ι → ℕ}
  {n : ℕ}

/-! ### Concatenation along a pairwise disjoint family of open sets -/

/-- The regrouping map on ordered tuples of points of the members of the family. -/
private def regroup (U : ι → Set α) (m : ι → ℕ) (e : (Σ i, Fin (m i)) ≃ Fin n)
    (f : ∀ i, Fin (m i) → U i) (j : Fin n) : α :=
  (f (e.symm j).1 (e.symm j).2 : α)

omit [Fintype ι] in
private theorem continuous_regroup (e : (Σ i, Fin (m i)) ≃ Fin n) :
    Continuous (regroup U m e) :=
  continuous_pi fun _j =>
    continuous_subtype_val.comp ((continuous_apply _).comp (continuous_apply _))

omit [Fintype ι] in
private theorem isOpenMap_regroup (hU : ∀ i, IsOpen (U i)) (e : (Σ i, Fin (m i)) ≃ Fin n) :
    IsOpenMap (regroup U m e) := by
  let R : (∀ i, Fin (m i) → U i) ≃ₜ (∀ j : Fin n, ↥(U (e.symm j).1)) :=
    piSigmaHomeomorph (fun i => ↥(U i)) e
  have hfun : regroup U m e
      = (Pi.map fun j : Fin n => (Subtype.val : ↥(U (e.symm j).1) → α)) ∘ R := by
    funext f j
    simp [regroup, R]
  rw [hfun]
  exact (IsOpenMap.piMap (fun j => (hU _).isOpenMap_subtype_val) (by simp)).comp R.isOpenMap

omit [Fintype ι] in
private theorem isOpenQuotientMap_piMap_ofFn :
    IsOpenQuotientMap (Pi.map fun i => (ofFn : (Fin (m i) → U i) → Sym (U i) (m i))) :=
  IsOpenQuotientMap.piMap fun _ => isOpenQuotientMap_ofFn

omit [TopologicalSpace α] in
private theorem sumSubtype_comp_piMap_ofFn (hn : ∑ i, m i = n) (e : (Σ i, Fin (m i)) ≃ Fin n) :
    sumSubtype U m hn ∘ (Pi.map fun i => (ofFn : (Fin (m i) → U i) → Sym (U i) (m i)))
      = ofFn ∘ regroup U m e :=
  funext fun f => sumSubtype_ofFn hn e f

/-- Concatenating unordered tuples of points of the members of a family is continuous. -/
@[continuity, fun_prop]
theorem continuous_sumSubtype (hn : ∑ i, m i = n) : Continuous (sumSubtype U m hn) := by
  obtain ⟨e⟩ := nonempty_sigmaFinEquiv hn
  rw [isOpenQuotientMap_piMap_ofFn.isQuotientMap.continuous_iff,
    sumSubtype_comp_piMap_ofFn hn e]
  exact continuous_ofFn.comp (continuous_regroup e)

/-- For a family of open sets, concatenating unordered tuples of points of its members is an open
map. -/
theorem isOpenMap_sumSubtype (hU : ∀ i, IsOpen (U i)) (hn : ∑ i, m i = n) :
    IsOpenMap (sumSubtype U m hn) := by
  obtain ⟨e⟩ := nonempty_sigmaFinEquiv hn
  rw [isOpenQuotientMap_piMap_ofFn.isOpenMap_iff, sumSubtype_comp_piMap_ofFn hn e]
  exact isOpenMap_ofFn.comp (isOpenMap_regroup hU e)

/-- **The symmetric power is locally a product.** For a pairwise disjoint family of open sets,
concatenation identifies the product of the symmetric powers of its members with an open subspace
of `Sym α n`, namely the unordered tuples supported in the union of the family with exactly `m i`
of their points in `U i` (`TauCeti.Sym.mem_range_sumSubtype`). -/
theorem isOpenEmbedding_sumSubtype (hU : ∀ i, IsOpen (U i))
    (h : Pairwise (Function.onFun Disjoint U)) (hn : ∑ i, m i = n) :
    IsOpenEmbedding (sumSubtype U m hn) :=
  .of_continuous_injective_isOpenMap (continuous_sumSubtype hn) (sumSubtype_injective h hn)
    (isOpenMap_sumSubtype hU hn)

end Sym

/-! ### The family attached to a tuple in a Hausdorff space -/

/-- **Every unordered tuple in a Hausdorff space is a concatenation along a pairwise disjoint
family of arbitrarily small open sets**, one member of the family for each of its distinct points
and that point's multiplicity as the degree.

This is the separation step that turns `TauCeti.Sym.isOpenEmbedding_sumSubtype` into an atlas: the
open sets `V i` may be taken inside any prescribed open neighbourhoods `W a ∋ a`, so in a space
charted by a fixed model they may be taken inside coordinate patches. -/
theorem exists_mem_range_sumSubtype_of_t2 {α : Type*} [TopologicalSpace α] [T2Space α]
    [DecidableEq α] {n : ℕ} (w : Sym α n) (W : α → Set α)
    (hWo : ∀ a ∈ w, IsOpen (W a)) (hWm : ∀ a ∈ w, a ∈ W a) :
    ∃ V : ↥(w : Multiset α).toFinset → Set α, (∀ i, IsOpen (V i)) ∧ (∀ i, (i : α) ∈ V i) ∧
      (∀ i, V i ⊆ W i) ∧ Pairwise (Function.onFun Disjoint V) ∧
      ∃ hm : ∑ i : ↥(w : Multiset α).toFinset,
          Multiset.count (i : α) (w : Multiset α) = n,
        w ∈ Set.range
          (Sym.sumSubtype V (fun i => Multiset.count (i : α) (w : Multiset α)) hm) := by
  classical
  obtain ⟨V₀, hV₀, hdisj⟩ :=
    (((w : Multiset α).toFinset : Finset α) : Set α).toFinite.t2_separation (X := α)
  set V : ↥(w : Multiset α).toFinset → Set α := fun i => V₀ (i : α) ∩ W (i : α)
  have hiw (i : ↥(w : Multiset α).toFinset) : (i : α) ∈ w :=
    _root_.Sym.mem_coe.1 (Multiset.mem_toFinset.1 i.2)
  have hVdisj : Pairwise (Function.onFun Disjoint V) := fun i j hij =>
    ((hdisj (by simp) (by simp) (Subtype.coe_ne_coe.2 hij)).mono
      Set.inter_subset_left Set.inter_subset_left)
  have hm : ∑ i : ↥(w : Multiset α).toFinset,
      Multiset.count (i : α) (w : Multiset α) = n := by
    rw [Finset.sum_coe_sort (w : Multiset α).toFinset
      fun a => Multiset.count a (w : Multiset α), Multiset.toFinset_sum_count_eq]
    exact w.2
  refine ⟨V, fun i => (hV₀ i).2.inter (hWo i (hiw i)),
    fun i => ⟨(hV₀ i).1, hWm i (hiw i)⟩,
    fun i => Set.inter_subset_right, hVdisj, hm, ?_⟩
  rw [Sym.mem_range_sumSubtype hVdisj]
  refine ⟨fun a ha => ⟨⟨a, Multiset.mem_toFinset.2 (_root_.Sym.mem_coe.2 ha)⟩,
    (hV₀ a).1, hWm a ha⟩, fun i => ?_⟩
  have hfilter : Multiset.filter (fun a => a ∈ V i) (w : Multiset α)
      = Multiset.filter (fun a => (i : α) = a) (w : Multiset α) := by
    refine Multiset.filter_congr fun a ha => ⟨fun haV => ?_, ?_⟩
    · by_contra hne
      exact Set.disjoint_left.1 (hdisj (Multiset.mem_toFinset.2 ha) (by simp) (Ne.symm hne))
        (hV₀ a).1 haV.1
    · rintro rfl
      exact ⟨(hV₀ _).1, hWm _ (_root_.Sym.mem_coe.1 ha)⟩
  rw [hfilter, ← Multiset.count_eq_card_filter_eq]

end TauCeti
