/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.DiscreteSubset
public import TauCeti.Analysis.Fredholm.Criteria

/-!
# Regular level sets of a Fredholm map

Let `f : E → F` be a map between Banach spaces which is strictly differentiable at a point `a` of
the level set `{x | f x = c}`, and whose derivative `f'` there is a **surjective Fredholm
operator**. This file shows that the level set is, near `a`, homeomorphic to an open subset of
`ker f'`, a space whose dimension is exactly the Fredholm index of `f'`; and it packages that
local model, when the index is a fixed `n` along the whole level set, as a `ChartedSpace`
structure on `{x | f x = c}` modelled on `Fin n → 𝕜`.

This is the "a moduli space is the zero set of a Fredholm section, and at a regular point it is a
manifold of dimension the index" package that Lane F0 of the analytic Heegaard Floer roadmap asks
for (McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix A.3). The linear
half of that lane is already available: `ContinuousLinearMap.IsFredholm` provides the
finite-dimensional, topologically complemented kernel, and
`TauCeti.ContinuousLinearMap.index_of_surjective` identifies its dimension with the index. What is
added here is the nonlinear half, which is Mathlib's implicit function theorem for a map with
surjective derivative and complemented kernel,
`HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented`, restricted to the level set:
that homeomorphism carries `{x | f x = c}` to the "vertical" slice `{c} × ker f'`, and the chart
below is the resulting homeomorphism of the level set with an open subset of `ker f'`.

Three consequences record that the dimension count is not vacuous. In index `0` a regular point of
the level set is **isolated** in it, so a compact piece of a regular index-`0` level set is
**finite** — the finiteness that makes a Floer-type differential, which counts index-`0` solutions,
well defined. In nonzero index a regular point is, on the contrary, never isolated, so a level set
is locally the single point `a` precisely when the index vanishes.

The charts here are only claimed to be homeomorphisms: their transition maps are smooth exactly
when `f` is, which needs the `ContDiff` form of the implicit function theorem and is left to a
later step, so no `IsManifold` instance is asserted.

## Main declarations

* `TauCeti.levelSetChart`: the chart `{x | f x = c} → ker f'` at a regular point `a`, given by
  projecting `x - a` onto `ker f'` along the chosen complement.
* `TauCeti.levelSetChartModel`: the same chart read in the model space `Fin n → 𝕜`, when
  `ker f'` has dimension `n`.
* `TauCeti.levelSetChartedSpace`: a regular level set on which the index is constantly `n` is a
  charted space modelled on `Fin n → 𝕜`; by
  `TauCeti.ContinuousLinearMap.index_of_surjective` the model dimension is the Fredholm index.
* `TauCeti.eventually_eq_of_index_eq_zero`: a regular point of the level set of an index-`0`
  Fredholm map is isolated in that level set.
* `TauCeti.finite_inter_of_index_eq_zero`: hence a compact piece of such a level set is finite.
* `TauCeti.exists_mem_ne_of_index_ne_zero`: in nonzero index, every neighbourhood of a regular
  point contains a further point of the level set.
-/

public section

namespace TauCeti

open Filter Module Set Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {f : E → F} {f' : E →L[𝕜] F} {a : E} {c : F}

/-! ### The chart of a level set at a regular point -/

open scoped Classical in
/-- The chart of the level set `{x | f x = c}` at a point `a` where `f` is strictly differentiable
with surjective derivative `f'` of complemented kernel: it sends `x` to the projection of `x - a`
onto `ker f'` along the complement chosen by `hker`, and is a homeomorphism from a neighbourhood
of `a` in the level set onto an open subset of `ker f'`.

This is Mathlib's implicit-function homeomorphism `x ↦ (f x, proj (x - a))` restricted to the
level set, on which its first component is constantly `c`. -/
noncomputable def levelSetChart (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) (ha : f a = c) :
    OpenPartialHomeomorph ↥{x | f x = c} ↥f'.ker :=
  let Φ := hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker
  { toFun := fun z => (Φ z.1).2
    invFun := fun k => if h : f (Φ.symm (c, k)) = c then ⟨Φ.symm (c, k), h⟩ else ⟨a, ha⟩
    source := Subtype.val ⁻¹' Φ.source
    target := (fun k => (c, k)) ⁻¹' Φ.target
    map_source' := by
      intro z hz
      have hz2 : f z.1 = c := z.2
      have h1 : (Φ z.1).1 = c := by
        rw [hf.implicitToOpenPartialHomeomorphOfComplemented_fst hf' hker, hz2]
      have h2 : Φ z.1 = (c, (Φ z.1).2) := Prod.ext h1 rfl
      change (c, (Φ z.1).2) ∈ Φ.target
      rw [← h2]
      exact Φ.map_source hz
    map_target' := by
      intro k hk
      have hr : Φ (Φ.symm (c, k)) = (c, k) := Φ.right_inv hk
      have hfc : f (Φ.symm (c, k)) = c := by
        rw [← hf.implicitToOpenPartialHomeomorphOfComplemented_fst hf' hker, hr]
      rw [dif_pos hfc]
      exact Φ.map_target hk
    left_inv' := by
      intro z hz
      have hz2 : f z.1 = c := z.2
      have h1 : (Φ z.1).1 = c := by
        rw [hf.implicitToOpenPartialHomeomorphOfComplemented_fst hf' hker, hz2]
      have h2 : Φ z.1 = (c, (Φ z.1).2) := Prod.ext h1 rfl
      have hs : Φ.symm (c, (Φ z.1).2) = z.1 := by rw [← h2]; exact Φ.left_inv hz
      have hfc : f (Φ.symm (c, (Φ z.1).2)) = c := by rw [hs]; exact hz2
      rw [dif_pos hfc]
      exact Subtype.ext hs
    right_inv' := by
      intro k hk
      have hr : Φ (Φ.symm (c, k)) = (c, k) := Φ.right_inv hk
      have hfc : f (Φ.symm (c, k)) = c := by
        rw [← hf.implicitToOpenPartialHomeomorphOfComplemented_fst hf' hker, hr]
      rw [dif_pos hfc]
      change (Φ (Φ.symm (c, k))).2 = k
      rw [hr]
    open_source := Φ.open_source.preimage continuous_subtype_val
    open_target := Φ.open_target.preimage (continuous_const.prodMk continuous_id)
    continuousOn_toFun :=
      (Φ.continuousOn.comp continuous_subtype_val.continuousOn fun _ hz => hz).snd
    continuousOn_invFun := by
      rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
      refine ContinuousOn.congr
        (Φ.continuousOn_symm.comp
          (continuous_const.prodMk continuous_id).continuousOn fun _ hk => hk) fun k hk => ?_
      have hr : Φ (Φ.symm (c, k)) = (c, k) := Φ.right_inv hk
      have hfc : f (Φ.symm (c, k)) = c := by
        rw [← hf.implicitToOpenPartialHomeomorphOfComplemented_fst hf' hker, hr]
      change ((if h : f (Φ.symm (c, k)) = c then ⟨_, h⟩ else ⟨a, ha⟩ :
        ↥{x | f x = c}) : E) = _
      rw [dif_pos hfc]
      rfl }

@[simp]
theorem levelSetChart_apply (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) (ha : f a = c) (z : ↥{x | f x = c}) :
    levelSetChart hf hf' hker ha z = Classical.choose hker (z.1 - a) := by
  change (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker z.1).2 = _
  rw [hf.implicitToOpenPartialHomeomorphOfComplemented_apply hf' hker]

theorem levelSetChart_apply_self (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) (ha : f a = c) :
    levelSetChart hf hf' hker ha ⟨a, ha⟩ = 0 := by
  rw [levelSetChart_apply]
  simp

theorem mem_levelSetChart_source (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) (ha : f a = c) :
    (⟨a, ha⟩ : ↥{x | f x = c}) ∈ (levelSetChart hf hf' hker ha).source :=
  hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source hf' hker

/-! ### The chart in the model space -/

section Model

variable [CompleteSpace 𝕜]

/-- The chart of a regular level set, read in the model space `Fin n → 𝕜`, where `n` is the
dimension of `ker f'` — by `TauCeti.ContinuousLinearMap.index_of_surjective`, the Fredholm index
of `f'`. -/
noncomputable def levelSetChartModel {n : ℕ} (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hFred : ContinuousLinearMap.IsFredholm f')
    (hn : finrank 𝕜 ↥f'.ker = n) (ha : f a = c) :
    OpenPartialHomeomorph ↥{x | f x = c} (Fin n → 𝕜) :=
  have := hFred.finite_ker
  (levelSetChart hf hf' hFred.closedComplemented_ker ha).transHomeomorph
    ((LinearEquiv.ofFinrankEq ↥f'.ker (Fin n → 𝕜)
      (by rw [hn, Module.finrank_fin_fun])).toContinuousLinearEquiv.toHomeomorph)

theorem mem_levelSetChartModel_source {n : ℕ} (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hFred : ContinuousLinearMap.IsFredholm f')
    (hn : finrank 𝕜 ↥f'.ker = n) (ha : f a = c) :
    (⟨a, ha⟩ : ↥{x | f x = c}) ∈ (levelSetChartModel hf hf' hFred hn ha).source :=
  mem_levelSetChart_source hf hf' hFred.closedComplemented_ker ha

/-! ### A regular level set of constant index is a charted space -/

variable {D : E → E →L[𝕜] F} {n : ℕ}

/-- The preferred chart at a point of a regular level set along which the Fredholm index is
constantly `n`. -/
noncomputable def levelSetChartAt
    (hf : ∀ x ∈ {x | f x = c}, HasStrictFDerivAt f (D x) x)
    (hFred : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.IsFredholm (D x))
    (hsurj : ∀ x ∈ {x | f x = c}, Function.Surjective (D x))
    (hindex : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.index (D x) = n)
    (z : ↥{x | f x = c}) : OpenPartialHomeomorph ↥{x | f x = c} (Fin n → 𝕜) :=
  levelSetChartModel (hf z.1 z.2) (LinearMap.range_eq_top.2 (hsurj z.1 z.2)) (hFred z.1 z.2)
    (by
      have h := ContinuousLinearMap.index_of_surjective (D z.1) (hsurj z.1 z.2)
      rw [hindex z.1 z.2] at h
      exact_mod_cast h.symm)
    z.2

/-- **A regular level set of a Fredholm map is a topological manifold of dimension its index.**
If `f` is strictly differentiable at every point of the level set `{x | f x = c}` with surjective
Fredholm derivative of index `n` there, then the level set is a charted space modelled on
`Fin n → 𝕜`, the charts being the implicit-function charts `TauCeti.levelSetChartAt`. -/
@[instance_reducible]
noncomputable def levelSetChartedSpace
    (hf : ∀ x ∈ {x | f x = c}, HasStrictFDerivAt f (D x) x)
    (hFred : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.IsFredholm (D x))
    (hsurj : ∀ x ∈ {x | f x = c}, Function.Surjective (D x))
    (hindex : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.index (D x) = n) :
    ChartedSpace (Fin n → 𝕜) ↥{x | f x = c} where
  atlas := Set.range (levelSetChartAt hf hFred hsurj hindex)
  chartAt := levelSetChartAt hf hFred hsurj hindex
  mem_chart_source z := mem_levelSetChartModel_source _ _ _ _ z.2
  chart_mem_atlas z := Set.mem_range_self z

end Model

/-! ### Index zero: isolated points and finiteness -/

/-- A point of a level set at which the derivative is surjective Fredholm **of index zero** is
isolated in that level set: the local model `ker f'` is then the zero space. -/
theorem eventually_eq_of_index_eq_zero (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hFred : ContinuousLinearMap.IsFredholm f') (hindex : ContinuousLinearMap.index f' = 0)
    (ha : f a = c) : ∀ᶠ x in 𝓝 a, f x = c → x = a := by
  have := hFred.finite_ker
  have hrank : finrank 𝕜 ↥f'.ker = 0 := by
    have h := ContinuousLinearMap.index_of_surjective f' (LinearMap.range_eq_top.1 hf')
    rw [hindex] at h
    exact_mod_cast h.symm
  have hsub : Subsingleton ↥f'.ker := Module.finrank_zero_iff.1 hrank
  have hker := hFred.closedComplemented_ker
  let Φ := hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker
  have hmem : a ∈ Φ.source :=
    hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source hf' hker
  refine eventually_of_mem (Φ.open_source.mem_nhds hmem) fun x hx hfx => ?_
  refine Φ.injOn hx hmem (Prod.ext ?_ (Subsingleton.elim _ _))
  rw [hf.implicitToOpenPartialHomeomorphOfComplemented_fst hf' hker,
    hf.implicitToOpenPartialHomeomorphOfComplemented_fst hf' hker, hfx, ha]

/-- Conversely, at a regular point of **nonzero** index the level set is not locally the single
point `a`: every neighbourhood of `a` contains a further point of the level set. With
`TauCeti.eventually_eq_of_index_eq_zero` this says that the level set reduces to the point `a`
near `a` exactly when the index vanishes, so the dimension of the local model is realised. -/
theorem exists_mem_ne_of_index_ne_zero (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hFred : ContinuousLinearMap.IsFredholm f') (hindex : ContinuousLinearMap.index f' ≠ 0)
    (ha : f a = c) {U : Set E} (hU : U ∈ 𝓝 a) : ∃ x ∈ U, f x = c ∧ x ≠ a := by
  have := hFred.finite_ker
  have hker := hFred.closedComplemented_ker
  have hrank : 0 < finrank 𝕜 ↥f'.ker := by
    have h := ContinuousLinearMap.index_of_surjective f' (LinearMap.range_eq_top.1 hf')
    refine Nat.pos_of_ne_zero fun h0 => hindex ?_
    rw [h, h0, Nat.cast_zero]
  have : Nontrivial ↥f'.ker := Module.nontrivial_of_finrank_pos hrank
  have : NeBot (𝓝[≠] (0 : ↥f'.ker)) := Module.punctured_nhds_neBot 𝕜 ↥f'.ker 0
  set Ψ := levelSetChart hf hf' hker ha with hΨ
  have hz₀ : (⟨a, ha⟩ : ↥{x | f x = c}) ∈ Ψ.source := mem_levelSetChart_source hf hf' hker ha
  have hΨ0 : Ψ ⟨a, ha⟩ = 0 := levelSetChart_apply_self hf hf' hker ha
  obtain ⟨U', hU'sub, hU'open, haU'⟩ := mem_nhds_iff.1 hU
  have hVopen : IsOpen (Ψ.source ∩ Subtype.val ⁻¹' U') :=
    Ψ.open_source.inter (hU'open.preimage continuous_subtype_val)
  have hz₀V : (⟨a, ha⟩ : ↥{x | f x = c}) ∈ Ψ.source ∩ Subtype.val ⁻¹' U' := ⟨hz₀, haU'⟩
  have hWopen : IsOpen (Ψ.target ∩ Ψ.symm ⁻¹' (Ψ.source ∩ Subtype.val ⁻¹' U')) :=
    Ψ.continuousOn_symm.isOpen_inter_preimage Ψ.open_target hVopen
  have h0W : (0 : ↥f'.ker) ∈ Ψ.target ∩ Ψ.symm ⁻¹' (Ψ.source ∩ Subtype.val ⁻¹' U') := by
    refine ⟨hΨ0 ▸ Ψ.map_source hz₀, ?_⟩
    change Ψ.symm 0 ∈ Ψ.source ∩ Subtype.val ⁻¹' U'
    rw [← hΨ0, Ψ.left_inv hz₀]
    exact hz₀V
  obtain ⟨k, hkW, hk0⟩ :=
    Filter.nonempty_of_mem (Filter.inter_mem (nhdsWithin_le_nhds (hWopen.mem_nhds h0W))
      (self_mem_nhdsWithin (a := (0 : ↥f'.ker)) (s := {0}ᶜ)))
  refine ⟨(Ψ.symm k : E), hU'sub hkW.2.2, (Ψ.symm k).2, fun hEq => hk0 ?_⟩
  have hsub : Ψ.symm k = ⟨a, ha⟩ := Subtype.ext hEq
  change k ∈ ({0} : Set ↥f'.ker)
  rw [← Ψ.right_inv hkW.1, hsub, hΨ0]
  rfl

/-- A compact piece of a level set along which the derivative is surjective Fredholm of index zero
is **finite**. This is the finiteness that makes a count of index-zero solutions, such as a Floer
differential, well defined. -/
theorem finite_inter_of_index_eq_zero {D : E → E →L[𝕜] F} {K : Set E} (hcont : Continuous f)
    (hK : IsCompact K)
    (hf : ∀ x ∈ {x | f x = c}, HasStrictFDerivAt f (D x) x)
    (hFred : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.IsFredholm (D x))
    (hsurj : ∀ x ∈ {x | f x = c}, Function.Surjective (D x))
    (hindex : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.index (D x) = 0) :
    ({x | f x = c} ∩ K).Finite := by
  have hclosed : IsClosed {x | f x = c} := isClosed_eq hcont continuous_const
  refine (hK.inter_left hclosed).finite ?_
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro y hy
  have hy' : y ∈ {x | f x = c} := hy.1
  obtain ⟨u, hu, huo, hyu⟩ := _root_.eventually_nhds_iff.1
    (eventually_eq_of_index_eq_zero (hf y hy') (LinearMap.range_eq_top.2 (hsurj y hy'))
      (hFred y hy') (hindex y hy') hy')
  exact ⟨u, huo, Set.eq_singleton_iff_unique_mem.2
    ⟨⟨hyu, hy⟩, fun x hx => hu x hx.1 hx.2.1⟩⟩

end TauCeti
