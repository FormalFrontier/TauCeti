/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import TauCeti.Analysis.Polynomial.SymmetricPower
public import TauCeti.Topology.Sym.Family

/-!
# A charted-space structure on a symmetric power

If a Hausdorff space `α` is charted by a proper algebraically closed normed field `K` — the case of
interest being a Riemann surface, charted by `ℂ` — then its `n`-th symmetric power `Sym α n` is
charted by `Fin n → K`. This supplies the local-coordinate part of the topological-manifold
statement in the first clause of Lane F4.1 of the analytic Heegaard Floer roadmap, after
Ozsváth--Szabó
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
  because the multiplicities add up to `n` (`TauCeti.piSigmaConstHomeomorph`).

The charts so obtained depend on choices — of the separating neighbourhoods, and of the regrouping
bijection — so the atlas below is a choice of one chart per point, exactly as much as a charted
structure asks for. Upgrading it to a *complex* manifold, by exhibiting an atlas whose transition
maps are holomorphic, is the next step of Lane F4.1 and is not done here; so are the totally real
tori `T_α`, `T_β`. What is available towards that holomorphy is the analytic ingredient for a
single coordinate patch at a multiplicity-free coefficient tuple,
`TauCeti.Sym.analyticAt_coeffEquiv_map_coeffEquiv_symm` in
`TauCeti/Analysis/Polynomial/SimpleRoots.lean`; assembling it across the blocks that a chart below
splits a tuple into, along the regrouping `e`, is not done, and neither is the case of colliding
points — which is where the degree-`m i` elementary symmetric coordinates genuinely appear.

## Main declarations

* `TauCeti.symOpenPartialHomeomorph`: an explicit elementary-symmetric chart built from a disjoint
  family of coordinate patches.
* `TauCeti.exists_symOpenPartialHomeomorph`: every unordered tuple lies in the source of a partial
  homeomorphism from `Sym α n` to `Fin n → K`.
* `TauCeti.symChartAt`: a chosen elementary-symmetric chart around each unordered tuple.
* `TauCeti.symChartedSpace`: a charted-space structure on `Sym α n` over `Fin n → K`.
* `TauCeti.symChartedSpace_chartAt` and `TauCeti.symChartedSpace_atlas`: its preferred charts and
  atlas.
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
    (hVo : IsOpen V) (hVs : V ⊆ e.source) : IsOpenEmbedding fun x : ↥V => e (x : α) :=
  e.isOpenEmbedding_restrict.comp
    (.inclusion hVs (hVo.preimage continuous_subtype_val))

omit [T2Space α] [ChartedSpace K α] in
/-- The elementary-symmetric partial homeomorphism obtained from a disjoint family `V` of
coordinate patches `φ` and an explicit regrouping `e` of their degrees. Its source is
`Set.range (Sym.sumSubtype V m hm)`, and on a concatenated tuple it applies `φ i` to the points in
the `i`-th patch, takes their elementary-symmetric coefficients, and regroups those coefficient
vectors along `e`. The argument `hp` only supplies the nonempty domain needed for the junk value
of the inverse constructed by `IsOpenEmbedding.toOpenPartialHomeomorph`. -/
noncomputable def symOpenPartialHomeomorph {ι : Type*} [Fintype ι]
    (φ : ι → OpenPartialHomeomorph α K) (V : ι → Set α)
    (m : ι → ℕ) (hm : ∑ i, m i = n) (hVo : ∀ i, IsOpen (V i))
    (hVsub : ∀ i, V i ⊆ (φ i).source)
    (hVdisj : Pairwise (Function.onFun Disjoint V)) (e : (Σ i, Fin (m i)) ≃ Fin n)
    (hp : Nonempty (∀ i, Sym ↥(V i) (m i))) :
    OpenPartialHomeomorph (Sym α n) (Fin n → K) :=
  letI := hp
  let hΦ : IsOpenEmbedding (Sym.sumSubtype V m hm) :=
    Sym.isOpenEmbedding_sumSubtype hVo hVdisj hm
  let hφ : ∀ i, IsOpenEmbedding fun x : ↥(V i) => φ i (x : α) :=
    fun i => isOpenEmbedding_chartRestrict _ (hVo i) (hVsub i)
  let hΘ : IsOpenEmbedding (Pi.map fun i => fun t : Sym ↥(V i) (m i) =>
      Sym.coeffEquiv K (m i)
        (Sym.map (fun x : ↥(V i) => φ i (x : α)) t)) :=
    IsOpenEmbedding.piMap fun i => Sym.isOpenEmbedding_coeffEquiv_comp_map (hφ i)
  let hΨ := (piSigmaConstHomeomorph K e).isOpenEmbedding.comp hΘ
  (hΦ.toOpenPartialHomeomorph _).symm.trans (hΨ.toOpenPartialHomeomorph _)

omit [T2Space α] [ChartedSpace K α] in
/-- The source of an elementary-symmetric chart is exactly the range of the family
concatenation used to construct it. -/
@[simp]
theorem symOpenPartialHomeomorph_source {ι : Type*} [Fintype ι]
    (φ : ι → OpenPartialHomeomorph α K) (V : ι → Set α)
    (m : ι → ℕ) (hm : ∑ i, m i = n) (hVo : ∀ i, IsOpen (V i))
    (hVsub : ∀ i, V i ⊆ (φ i).source)
    (hVdisj : Pairwise (Function.onFun Disjoint V)) (e : (Σ i, Fin (m i)) ≃ Fin n)
    (hp : Nonempty (∀ i, Sym ↥(V i) (m i))) :
    (symOpenPartialHomeomorph φ V m hm hVo hVsub hVdisj e hp).source =
      Set.range (Sym.sumSubtype V m hm) := by
  rw [symOpenPartialHomeomorph, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source, IsOpenEmbedding.toOpenPartialHomeomorph_target,
    IsOpenEmbedding.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ]

omit [T2Space α] [ChartedSpace K α] in
/-- An elementary-symmetric chart evaluates a concatenated tuple by taking the coefficient vector
in each coordinate patch and regrouping those vectors along `e`. -/
@[simp]
theorem symOpenPartialHomeomorph_apply {ι : Type*} [Fintype ι]
    (φ : ι → OpenPartialHomeomorph α K) (V : ι → Set α)
    (m : ι → ℕ) (hm : ∑ i, m i = n) (hVo : ∀ i, IsOpen (V i))
    (hVsub : ∀ i, V i ⊆ (φ i).source)
    (hVdisj : Pairwise (Function.onFun Disjoint V)) (e : (Σ i, Fin (m i)) ≃ Fin n)
    (hp : Nonempty (∀ i, Sym ↥(V i) (m i))) (p : ∀ i, Sym ↥(V i) (m i)) :
    symOpenPartialHomeomorph φ V m hm hVo hVsub hVdisj e hp (Sym.sumSubtype V m hm p) =
      piSigmaConstHomeomorph K e (fun i =>
        Sym.coeffEquiv K (m i) (Sym.map (fun x : ↥(V i) => φ i (x : α)) (p i))) := by
  rw [symOpenPartialHomeomorph, OpenPartialHomeomorph.trans_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]
  rfl

omit [T2Space α] [ChartedSpace K α] in
/-- The inverse elementary-symmetric chart sends the regrouped coefficient vectors back to the
corresponding concatenated tuple. -/
@[simp]
theorem symOpenPartialHomeomorph_symm_apply {ι : Type*} [Fintype ι]
    (φ : ι → OpenPartialHomeomorph α K) (V : ι → Set α)
    (m : ι → ℕ) (hm : ∑ i, m i = n) (hVo : ∀ i, IsOpen (V i))
    (hVsub : ∀ i, V i ⊆ (φ i).source)
    (hVdisj : Pairwise (Function.onFun Disjoint V)) (e : (Σ i, Fin (m i)) ≃ Fin n)
    (hp : Nonempty (∀ i, Sym ↥(V i) (m i))) (p : ∀ i, Sym ↥(V i) (m i)) :
    (symOpenPartialHomeomorph φ V m hm hVo hVsub hVdisj e hp).symm
        (piSigmaConstHomeomorph K e (fun i =>
          Sym.coeffEquiv K (m i) (Sym.map (fun x : ↥(V i) => φ i (x : α)) (p i)))) =
      Sym.sumSubtype V m hm p := by
  rw [symOpenPartialHomeomorph, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.symm_symm]
  have hcoord :
      piSigmaConstHomeomorph K e (fun i =>
          Sym.coeffEquiv K (m i) (Sym.map (fun x : ↥(V i) => φ i (x : α)) (p i))) =
        ((piSigmaConstHomeomorph K e : (∀ i, Fin (m i) → K) ≃ₜ (Fin n → K)) ∘
          Pi.map fun i t =>
            Sym.coeffEquiv K (m i) (Sym.map (fun x : ↥(V i) => φ i (x : α)) t)) p := rfl
  rw [hcoord, IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]
  rfl

omit [T2Space α] [ChartedSpace K α] in
/-- The target of an elementary-symmetric chart is the range of its coefficient-coordinate map. -/
@[simp]
theorem symOpenPartialHomeomorph_target {ι : Type*} [Fintype ι]
    (φ : ι → OpenPartialHomeomorph α K) (V : ι → Set α)
    (m : ι → ℕ) (hm : ∑ i, m i = n) (hVo : ∀ i, IsOpen (V i))
    (hVsub : ∀ i, V i ⊆ (φ i).source)
    (hVdisj : Pairwise (Function.onFun Disjoint V)) (e : (Σ i, Fin (m i)) ≃ Fin n)
    (hp : Nonempty (∀ i, Sym ↥(V i) (m i))) :
    (symOpenPartialHomeomorph φ V m hm hVo hVsub hVdisj e hp).target =
      Set.range fun p : ∀ i, Sym ↥(V i) (m i) =>
        piSigmaConstHomeomorph K e (fun i =>
          Sym.coeffEquiv K (m i) (Sym.map (fun x : ↥(V i) => φ i (x : α)) (p i))) := by
  rw [symOpenPartialHomeomorph, OpenPartialHomeomorph.trans_target,
    IsOpenEmbedding.toOpenPartialHomeomorph_target, OpenPartialHomeomorph.symm_target,
    IsOpenEmbedding.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ]
  rfl

/-- The distinct points of an unordered tuple, used as the index of its coordinate patches. -/
noncomputable def symChartSupport (s : Sym α n) : Finset α :=
  letI := Classical.decEq α
  (s : Multiset α).toFinset

omit [TopologicalSpace α] [T2Space α] in
open scoped Classical in
/-- The support of an unordered tuple consists exactly of the points that occur in it. -/
@[simp]
theorem mem_symChartSupport {a : α} {s : Sym α n} : a ∈ symChartSupport s ↔ a ∈ s := by
  simp [symChartSupport, _root_.Sym.mem_coe]

open scoped Classical in
/-- **Every unordered tuple of points of a Hausdorff charted space has a chart around it.** The
chart is the elementary symmetric coordinates of the points of the tuple, taken in disjoint
coordinate patches of `α` around its distinct points and regrouped into a single `n`-tuple of
scalars. -/
theorem exists_symOpenPartialHomeomorph (s : Sym α n) :
    ∃ chart : OpenPartialHomeomorph (Sym α n) (Fin n → K), s ∈ chart.source ∧
      ∃ (V : ↥(symChartSupport s) → Set α)
        (m : ↥(symChartSupport s) → ℕ) (hm : ∑ i, m i = n)
        (hVo : ∀ i, IsOpen (V i))
        (hVsub : ∀ i, V i ⊆ (chartAt K (i : α)).source)
        (hVdisj : Pairwise (Function.onFun Disjoint V))
        (e : (Σ i, Fin (m i)) ≃ Fin n) (hp : Nonempty (∀ i, Sym ↥(V i) (m i))),
        chart = symOpenPartialHomeomorph
          (fun i : ↥(symChartSupport s) => chartAt K (i : α))
          V m hm hVo hVsub hVdisj e hp := by
  rw [symChartSupport]
  obtain ⟨V, hVo, -, hVsub, hVdisj, hm, hmem⟩ :=
    exists_mem_range_sumSubtype_of_t2 s (fun a => (chartAt K a).source)
      (fun a _ => (chartAt K a).open_source) fun a _ => mem_chart_source K a
  set m : ↥(s : Multiset α).toFinset → ℕ :=
    fun i => Multiset.count (i : α) (s : Multiset α)
  let e : (Σ i, Fin (m i)) ≃ Fin n := (Sym.nonempty_sigmaFinEquiv hm).some
  let hp : Nonempty (∀ i, Sym ↥(V i) (m i)) := ⟨hmem.choose⟩
  refine ⟨symOpenPartialHomeomorph
      (fun i : ↥(s : Multiset α).toFinset => chartAt K (i : α))
      V m hm hVo hVsub hVdisj e hp,
    ?_, V, m, hm, hVo, hVsub, hVdisj, e, hp, rfl⟩
  rw [symOpenPartialHomeomorph_source]
  exact hmem

/-- A chosen elementary-symmetric chart around an unordered tuple. -/
noncomputable def symChartAt (s : Sym α n) :
    OpenPartialHomeomorph (Sym α n) (Fin n → K) :=
  (exists_symOpenPartialHomeomorph (K := K) s).choose

/-- The tuple lies in the source of its chosen elementary-symmetric chart. -/
@[simp]
theorem mem_symChartAt_source (s : Sym α n) : s ∈ (symChartAt (K := K) s).source :=
  (exists_symOpenPartialHomeomorph (K := K) s).choose_spec.1

/-- The chosen chart is one of the explicit elementary-symmetric charts constructed from disjoint
coordinate patches around the tuple's distinct points. -/
theorem symChartAt_spec (s : Sym α n) :
    ∃ (V : ↥(symChartSupport s) → Set α)
      (m : ↥(symChartSupport s) → ℕ) (hm : ∑ i, m i = n)
      (hVo : ∀ i, IsOpen (V i))
      (hVsub : ∀ i, V i ⊆ (chartAt K (i : α)).source)
      (hVdisj : Pairwise (Function.onFun Disjoint V))
      (e : (Σ i, Fin (m i)) ≃ Fin n) (hp : Nonempty (∀ i, Sym ↥(V i) (m i))),
      symChartAt (K := K) s =
        symOpenPartialHomeomorph
          (fun i : ↥(symChartSupport s) => chartAt K (i : α))
          V m hm hVo hVsub hVdisj e hp :=
  (exists_symOpenPartialHomeomorph (K := K) s).choose_spec.2

/-- **The symmetric power of a Hausdorff space charted by `K` is charted by `Fin n → K`.** This
constructs only the `ChartedSpace` structure. Reading it as a topological-manifold result also
requires suitable countability hypotheses, which are not assumed here; the Hausdorff instance is
already supplied by `TauCeti.Sym.instT2Space`.

Deliberately not an instance: when `α := K`, a later canonical single-chart structure built from
`TauCeti.Sym.coeffHomeomorph` would have the same instance key. -/
@[instance_reducible]
noncomputable def symChartedSpace : ChartedSpace (Fin n → K) (Sym α n) where
  atlas := Set.range (symChartAt (K := K))
  chartAt := symChartAt (K := K)
  mem_chart_source := mem_symChartAt_source
  chart_mem_atlas s := ⟨s, rfl⟩

/-- The preferred chart of `symChartedSpace` is the chosen elementary-symmetric chart. -/
@[simp]
theorem symChartedSpace_chartAt (s : Sym α n) :
    @chartAt (Fin n → K) _ (Sym α n) _ (symChartedSpace (K := K)) s = symChartAt (K := K) s :=
  (rfl)

/-- The atlas of `symChartedSpace` consists of the chosen elementary-symmetric chart at every
unordered tuple. -/
@[simp]
theorem symChartedSpace_atlas :
    @atlas (Fin n → K) _ (Sym α n) _ (symChartedSpace (K := K)) =
      Set.range (symChartAt (K := K)) :=
  (rfl)

/-- Applying the construction with `α := K` charts the symmetric power of the model space by
affine `n`-space. This is the local model used for `Sym^g(Σ)`. -/
noncomputable example : ChartedSpace (Fin n → K) (Sym K n) := symChartedSpace

end TauCeti
