/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import TauCeti.Analysis.Polynomial.SymmetricPower
public import TauCeti.Topology.PiCurry
public import TauCeti.Topology.Sym.Family

/-!
# The symmetric power of a surface is a topological manifold

If a Hausdorff space `α` is charted by a proper algebraically closed normed field `K` — the case of
interest being a Riemann surface, charted by `ℂ` — then its `n`-th symmetric power `Sym α n` is
charted by `Fin n → K`. This is the statement that `Sym^g(Σ)` is a topological `2g`-manifold, the
first clause of Lane F4.1 of the analytic Heegaard Floer roadmap, after Ozsváth--Szabó
([arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.1).

The chart at an unordered tuple `s` is assembled from three inputs, each already available:

* in a Hausdorff space the distinct points `z₁, …, z_k` of `s` have pairwise disjoint open
  neighbourhoods `V₁, …, V_k` inside prescribed ones — here, inside the coordinate patches
  `(chartAt K z_j).source` — and `s` is the concatenation of unordered tuples of points of the
  `V_j`, with multiplicities `n₁, …, n_k` as the degrees
  (`TauCeti.exists_mem_range_sumSubtype_of_t2`);
* that concatenation is an open embedding
  `Sym^{n₁}(V₁) × ⋯ × Sym^{n_k}(V_k) ↪ Sym α n` (`TauCeti.Sym.isOpenEmbedding_sumSubtype`);
* each factor is an open subspace of affine space, charted by the elementary symmetric functions
  of its points read in the ambient coordinate
  (`TauCeti.Sym.isOpenEmbedding_coeffEquiv_comp_map`), and the factors regroup into `Fin n → K`
  because the multiplicities add up to `n` (`TauCeti.piFinSumHomeomorph`).

The charts so obtained depend on choices — of the separating neighbourhoods, and of the regrouping
bijection — so the atlas below is a choice of one chart per point, exactly as much as a charted
structure asks for. Upgrading it to a *complex* manifold, by exhibiting an atlas whose transition
maps are holomorphic, is the next step of Lane F4.1 and is not done here; so are the totally real
tori `T_α`, `T_β`.

## Main declarations

* `TauCeti.exists_openPartialHomeomorph_sym`: every unordered tuple lies in the source of a partial
  homeomorphism from `Sym α n` to `Fin n → K`.
* `TauCeti.instChartedSpaceSym`: `Sym α n` is a charted space over `Fin n → K`.
-/

public section

open Topology

namespace TauCeti

variable {K : Type*} [NormedField K] [IsAlgClosed K] [ProperSpace K]
variable {α : Type*} [TopologicalSpace α] [T2Space α] [ChartedSpace K α] {n : ℕ}

omit [IsAlgClosed K] [ProperSpace K] [T2Space α] [ChartedSpace K α] in
/-- A chart of `α`, restricted to an open subset of its source, is an open embedding of that
subset into the model space. -/
private theorem isOpenEmbedding_chartRestrict (e : OpenPartialHomeomorph α K) {V : Set α}
    (hVo : IsOpen V) (hVs : V ⊆ e.source) : IsOpenEmbedding fun x : ↥V => e (x : α) := by
  refine .of_continuous_injective_isOpenMap ((e.continuousOn.mono hVs).domRestrict)
    (fun x y hxy => Subtype.ext (e.injOn (hVs x.2) (hVs y.2) hxy)) fun W hW => ?_
  have himg : (fun x : ↥V => e (x : α)) '' W = e '' (Subtype.val '' W) :=
    (Set.image_image _ _ _).symm
  rw [himg]
  exact e.isOpen_image_of_subset_source (hVo.isOpenMap_subtype_val W hW)
    (((Set.image_subset_iff (f := (Subtype.val : ↥V → α))).2 fun x _ => x.2).trans hVs)

/-- **Every unordered tuple of points of a Hausdorff charted space has a chart around it.** The
chart is the elementary symmetric coordinates of the points of the tuple, taken in disjoint
coordinate patches of `α` around its distinct points and regrouped into a single `n`-tuple of
scalars. -/
theorem exists_openPartialHomeomorph_sym (s : Sym α n) :
    ∃ e : OpenPartialHomeomorph (Sym α n) (Fin n → K), s ∈ e.source := by
  classical
  obtain ⟨V, hVo, -, hVsub, hVdisj, hmem⟩ :=
    exists_mem_range_sumSubtype_of_t2 s (fun a => (chartAt K a).source)
      (fun a => (chartAt K a).open_source) fun a => mem_chart_source K a
  set m : ↥(s : Multiset α).toFinset → ℕ :=
    fun i => Multiset.count (i : α) (s : Multiset α)
  have hm : ∑ i, m i = n := by
    rw [Finset.sum_coe_sort (s : Multiset α).toFinset
      fun a => Multiset.count a (s : Multiset α), Multiset.toFinset_sum_count_eq]
    exact s.2
  have hΦ : IsOpenEmbedding (Sym.sumSubtype V m hm) :=
    Sym.isOpenEmbedding_sumSubtype hVo hVdisj _
  have hφ : ∀ i, IsOpenEmbedding fun x : ↥(V i) => chartAt K (i : α) (x : α) :=
    fun i => isOpenEmbedding_chartRestrict _ (hVo i) (hVsub i)
  have hΘ : IsOpenEmbedding (Pi.map fun i => fun t : Sym ↥(V i) (m i) =>
      Sym.coeffEquiv K (m i) (Sym.map (fun x : ↥(V i) => chartAt K (i : α) (x : α)) t)) :=
    IsOpenEmbedding.piMap fun i => Sym.isOpenEmbedding_coeffEquiv_comp_map (hφ i)
  have hΨ := (piFinSumHomeomorph K hm).isOpenEmbedding.comp hΘ
  have : Nonempty (∀ i, Sym ↥(V i) (m i)) := ⟨hmem.choose⟩
  refine ⟨(hΦ.toOpenPartialHomeomorph _).symm.trans (hΨ.toOpenPartialHomeomorph _), ?_⟩
  simpa using hmem

/-- **The symmetric power of a Hausdorff space charted by `K` is charted by `Fin n → K`.** For a
Riemann surface `Σ` and `K = ℂ` this says that `Sym^g(Σ)` is a topological `2g`-manifold. -/
noncomputable instance instChartedSpaceSym : ChartedSpace (Fin n → K) (Sym α n) where
  atlas := Set.range fun s : Sym α n => (exists_openPartialHomeomorph_sym (K := K) s).choose
  chartAt s := (exists_openPartialHomeomorph_sym (K := K) s).choose
  mem_chart_source s := (exists_openPartialHomeomorph_sym (K := K) s).choose_spec
  chart_mem_atlas s := ⟨s, rfl⟩

/-- The hypotheses are satisfiable: the model space is charted by itself, so its `n`-th symmetric
power is charted by affine `n`-space. This is the local model of `Sym^g(Σ)`. -/
noncomputable example : ChartedSpace (Fin n → K) (Sym K n) := inferInstance

end TauCeti
