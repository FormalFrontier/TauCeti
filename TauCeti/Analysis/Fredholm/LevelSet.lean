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

This is the local half of the "a moduli space is the zero set of a Fredholm section, and at a
regular point it is a manifold of dimension the index" package that Lane F0 of the analytic
Heegaard Floer roadmap asks for (McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Appendix A.3). The linear half of that lane is already available:
`ContinuousLinearMap.IsFredholm` provides the
finite-dimensional, topologically complemented kernel, and
`TauCeti.ContinuousLinearMap.index_of_surjective` identifies its dimension with the index. What is
added here is the nonlinear half, which is Mathlib's implicit function theorem for a map with
surjective derivative and complemented kernel,
`HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented`, restricted to the level set:
that homeomorphism carries `{x | f x = c}` to the "vertical" slice `{c} × ker f'`, and the chart
below is the resulting homeomorphism of the level set with an open subset of `ker f'`.

Three consequences record that the dimension count is not vacuous, and are stated with Mathlib's
accumulation-point vocabulary `AccPt`. A point where the derivative is injective with closed range
— in particular a regular point of index `0` — is **isolated** in the level set through it, so a
compact piece of such a level set is **finite**: one ingredient in the well-definedness of a
Floer-type differential, which counts index-`0` solutions; making such a count well defined also
needs a separate compactness result placing the counted solutions inside one such piece, which is
not proved here. Where the kernel is nontrivial — in particular at a regular point of nonzero index
— the level set on the contrary accumulates at the point, so a level set is locally the single
point `a` precisely when the index vanishes.

What is proved is exactly a `ChartedSpace` structure, that is, a covering family of local models;
nothing more is claimed. In particular this is *not* the assertion that the level set is a
topological manifold in the usual sense, which would additionally need global hypotheses such as
second countability, and none are assumed here. Nor are the charts claimed to be smoothly
compatible: suitable `ContDiff` hypotheses on `f` should give smoothly compatible charts, through
the `ContDiff` form of the implicit function theorem, but that is left to a later result, so no
`IsManifold` instance is asserted either.

## Main declarations

* `TauCeti.levelSetChart`: the chart `{x | f x = c} → ker f'` at a regular point `a`, given by
  projecting `x - a` onto `ker f'` along the chosen complement.
* `TauCeti.kerModelEquiv`: the identification of `ker f'` with the model space `Fin n → 𝕜`, when
  `ker f'` has dimension `n`.
* `TauCeti.levelSetChartModel`: the chart read through that identification.
* `TauCeti.levelSetChartedSpace`: a regular level set on which the index is constantly `n` is a
  charted space modelled on `Fin n → 𝕜`; by
  `TauCeti.ContinuousLinearMap.index_of_surjective` the model dimension is the Fredholm index.
* `TauCeti.not_accPt_of_injective` and `TauCeti.not_accPt_of_index_eq_zero`: a point where the
  derivative is injective with closed range, in particular a regular point of index `0`, is
  isolated in the level set through it.
* `TauCeti.isDiscrete_levelSet_inter_of_injective`, `TauCeti.finite_levelSet_inter_of_injective`
  and `TauCeti.finite_levelSet_inter_of_index_eq_zero`: hence such a piece of a level set is
  discrete, and a compact one is finite.
* `TauCeti.accPt_of_nontrivial_ker` and `TauCeti.accPt_of_index_ne_zero`: where the kernel is
  nontrivial, in particular in nonzero index, the level set accumulates at the point.
-/

public section

namespace TauCeti

open Filter Module Set Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {f : E → F} {f' : E →L[𝕜] F} {a : E} {c : F}

/-! ### The chart of a level set at a regular point -/

/-- On the level set `{x | f x = c}` the implicit-function homeomorphism has constant first
component `c`, so it takes values in the "vertical" slice `{c} × ker f'`. -/
private theorem implicit_apply_eq_mk (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) {x : E} (hx : f x = c) :
    hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker x =
      (c, (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker x).2) :=
  Prod.ext (by rw [hf.implicitToOpenPartialHomeomorphOfComplemented_fst hf' hker, hx]) rfl

/-- A point of the slice `{c} × ker f'` in the implicit-function target is the image of a point of
the level set `{x | f x = c}`. -/
private theorem apply_implicit_symm_eq (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) {k : ↥f'.ker}
    (hk : (c, k) ∈ (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).target) :
    f ((hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm (c, k)) = c := by
  rw [← hf.implicitToOpenPartialHomeomorphOfComplemented_fst hf' hker,
    (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).right_inv hk]

open scoped Classical in
/-- The inverse of `TauCeti.levelSetChart`: the implicit function of `f` at the constant value `c`,
returned as a point of the level set. The base point `a` only serves as the irrelevant value
outside the target, where no membership proof is available. -/
private noncomputable def levelSetChartSymm (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) (ha : f a = c) (k : ↥f'.ker) : ↥{x | f x = c} :=
  if h : f ((hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm (c, k)) = c then
    ⟨_, h⟩
  else ⟨a, ha⟩

/-- On the slice `{c} × ker f'` in the implicit-function target, `TauCeti.levelSetChartSymm` is the
implicit function itself. -/
private theorem levelSetChartSymm_apply (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) (ha : f a = c) {k : ↥f'.ker}
    (hk : (c, k) ∈ (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).target) :
    (levelSetChartSymm hf hf' hker ha k : E) =
      (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm (c, k) := by
  rw [levelSetChartSymm, dif_pos (apply_implicit_symm_eq hf hf' hker hk)]

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
    invFun := levelSetChartSymm hf hf' hker ha
    source := Subtype.val ⁻¹' Φ.source
    target := (fun k => (c, k)) ⁻¹' Φ.target
    map_source' := by
      intro z hz
      have hz2 : f z.1 = c := z.2
      rw [Set.mem_preimage, ← implicit_apply_eq_mk hf hf' hker hz2]
      exact Φ.map_source hz
    map_target' := by
      intro k hk
      rw [Set.mem_preimage, levelSetChartSymm_apply hf hf' hker ha hk]
      exact Φ.map_target hk
    left_inv' := by
      intro z hz
      have hz2 : f z.1 = c := z.2
      have h2 : Φ z.1 = (c, (Φ z.1).2) := implicit_apply_eq_mk hf hf' hker hz2
      have hk : (c, (Φ z.1).2) ∈ Φ.target := by rw [← h2]; exact Φ.map_source hz
      refine Subtype.ext ?_
      rw [levelSetChartSymm_apply hf hf' hker ha hk, ← h2, Φ.left_inv hz]
    right_inv' := by
      intro k hk
      rw [levelSetChartSymm_apply hf hf' hker ha hk, Φ.right_inv hk]
    open_source := Φ.open_source.preimage continuous_subtype_val
    open_target := Φ.open_target.preimage (continuous_const.prodMk continuous_id)
    continuousOn_toFun :=
      (Φ.continuousOn.comp continuous_subtype_val.continuousOn fun _ hz => hz).snd
    continuousOn_invFun := by
      rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
      exact ContinuousOn.congr
        (Φ.continuousOn_symm.comp
          (continuous_const.prodMk continuous_id).continuousOn fun _ hk => hk)
        fun k hk => levelSetChartSymm_apply hf hf' hker ha hk }

/-- The chart of a level set is computed by the projection onto `ker f'` chosen by `hker`, applied
to `x - a`. -/
theorem levelSetChart_apply (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) (ha : f a = c) (z : ↥{x | f x = c}) :
    levelSetChart hf hf' hker ha z = Classical.choose hker (z.1 - a) := by
  -- `levelSetChart` is built as an explicit `OpenPartialHomeomorph` literal whose `toFun` field
  -- is `fun z => (Φ z.1).2`, so applying it to `z` reduces to that by unfolding the definition
  -- and projecting the structure literal — both stable reductions, since the field is written
  -- out in this file. This lemma is the only place that relies on it: everything downstream
  -- rewrites with `levelSetChart_apply` instead.
  change (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker z.1).2 = _
  rw [hf.implicitToOpenPartialHomeomorphOfComplemented_apply hf' hker]

/-- On its target, the inverse of the chart of a level set is the implicit function of `f` at the
constant value `c`: the inverse of Mathlib's implicit-function homeomorphism, read on the slice
`{c} × ker f'`. -/
theorem levelSetChart_symm_apply (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) (ha : f a = c) {k : ↥f'.ker}
    (hk : k ∈ (levelSetChart hf hf' hker ha).target) :
    (((levelSetChart hf hf' hker ha).symm k : ↥{x | f x = c}) : E) =
      (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm (c, k) :=
  levelSetChartSymm_apply hf hf' hker ha hk

/-- The chart of a level set is normalised at its base point: it sends `a` to the origin of
`ker f'`. -/
@[simp]
theorem levelSetChart_apply_self (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) (ha : f a = c) :
    levelSetChart hf hf' hker ha ⟨a, ha⟩ = 0 := by
  rw [levelSetChart_apply]
  simp

/-- The base point of the chart of a level set lies in its source. -/
theorem mem_levelSetChart_source (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) (ha : f a = c) :
    (⟨a, ha⟩ : ↥{x | f x = c}) ∈ (levelSetChart hf hf' hker ha).source :=
  hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source hf' hker

/-- The origin of `ker f'`, the value of the chart at its base point, lies in its target. -/
theorem mem_levelSetChart_target (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) (ha : f a = c) :
    (0 : ↥f'.ker) ∈ (levelSetChart hf hf' hker ha).target :=
  levelSetChart_apply_self hf hf' hker ha ▸
    (levelSetChart hf hf' hker ha).map_source (mem_levelSetChart_source hf hf' hker ha)

/-! ### The chart in the model space -/

section Model

variable [CompleteSpace 𝕜]

/-- The identification of the kernel of a Fredholm operator with the model space `Fin n → 𝕜`, when
that kernel has dimension `n` — by `TauCeti.ContinuousLinearMap.index_of_surjective`, for a
surjective operator, the Fredholm index. -/
noncomputable def kerModelEquiv {n : ℕ} (hFred : ContinuousLinearMap.IsFredholm f')
    (hn : finrank 𝕜 ↥f'.ker = n) : ↥f'.ker ≃L[𝕜] (Fin n → 𝕜) :=
  have := hFred.finite_ker
  ContinuousLinearEquiv.ofFinrankEq (by rw [hn, Module.finrank_fin_fun])

/-- The chart of a regular level set, read in the model space `Fin n → 𝕜` through
`TauCeti.kerModelEquiv`. -/
noncomputable def levelSetChartModel {n : ℕ} (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hFred : ContinuousLinearMap.IsFredholm f')
    (hn : finrank 𝕜 ↥f'.ker = n) (ha : f a = c) :
    OpenPartialHomeomorph ↥{x | f x = c} (Fin n → 𝕜) :=
  (levelSetChart hf hf' hFred.closedComplemented_ker ha).transHomeomorph
    (kerModelEquiv hFred hn).toHomeomorph

/-- The model chart is the chart of the level set read through `TauCeti.kerModelEquiv`. -/
theorem levelSetChartModel_apply {n : ℕ} (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hFred : ContinuousLinearMap.IsFredholm f')
    (hn : finrank 𝕜 ↥f'.ker = n) (ha : f a = c) (z : ↥{x | f x = c}) :
    levelSetChartModel hf hf' hFred hn ha z =
      kerModelEquiv hFred hn (levelSetChart hf hf' hFred.closedComplemented_ker ha z) := by
  rw [levelSetChartModel, OpenPartialHomeomorph.transHomeomorph_apply,
    ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_apply]

/-- The inverse of the model chart is the inverse of the chart of the level set, read through
`TauCeti.kerModelEquiv`. -/
theorem levelSetChartModel_symm_apply {n : ℕ} (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hFred : ContinuousLinearMap.IsFredholm f')
    (hn : finrank 𝕜 ↥f'.ker = n) (ha : f a = c) (k : Fin n → 𝕜) :
    (levelSetChartModel hf hf' hFred hn ha).symm k =
      (levelSetChart hf hf' hFred.closedComplemented_ker ha).symm
        ((kerModelEquiv hFred hn).symm k) := by
  rw [levelSetChartModel, OpenPartialHomeomorph.transHomeomorph_symm_apply,
    ContinuousLinearEquiv.coe_symm_toHomeomorph, Function.comp_apply]

/-- The model chart has the same source as the chart of the level set it is read from. -/
theorem levelSetChartModel_source {n : ℕ} (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hFred : ContinuousLinearMap.IsFredholm f')
    (hn : finrank 𝕜 ↥f'.ker = n) (ha : f a = c) :
    (levelSetChartModel hf hf' hFred hn ha).source =
      (levelSetChart hf hf' hFred.closedComplemented_ker ha).source := by
  rw [levelSetChartModel, OpenPartialHomeomorph.transHomeomorph_source]

/-- The model chart is normalised at its base point: it sends `a` to the origin of `Fin n → 𝕜`. -/
@[simp]
theorem levelSetChartModel_apply_self {n : ℕ} (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hFred : ContinuousLinearMap.IsFredholm f')
    (hn : finrank 𝕜 ↥f'.ker = n) (ha : f a = c) :
    levelSetChartModel hf hf' hFred hn ha ⟨a, ha⟩ = 0 := by
  rw [levelSetChartModel_apply, levelSetChart_apply_self]
  exact map_zero _

/-- The base point of the model chart lies in its source. -/
theorem mem_levelSetChartModel_source {n : ℕ} (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hFred : ContinuousLinearMap.IsFredholm f')
    (hn : finrank 𝕜 ↥f'.ker = n) (ha : f a = c) :
    (⟨a, ha⟩ : ↥{x | f x = c}) ∈ (levelSetChartModel hf hf' hFred hn ha).source := by
  rw [levelSetChartModel_source]
  exact mem_levelSetChart_source hf hf' hFred.closedComplemented_ker ha

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
    ((ContinuousLinearMap.finrank_ker_eq_iff_index_eq (D z.1) (hsurj z.1 z.2)).2
      (hindex z.1 z.2))
    z.2

/-- The preferred chart at `z` is normalised at `z`: it sends `z` to the origin of `Fin n → 𝕜`. -/
@[simp]
theorem levelSetChartAt_apply_self
    (hf : ∀ x ∈ {x | f x = c}, HasStrictFDerivAt f (D x) x)
    (hFred : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.IsFredholm (D x))
    (hsurj : ∀ x ∈ {x | f x = c}, Function.Surjective (D x))
    (hindex : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.index (D x) = n)
    (z : ↥{x | f x = c}) : levelSetChartAt hf hFred hsurj hindex z z = 0 :=
  levelSetChartModel_apply_self _ _ _ _ _

/-- A point of a regular level set lies in the source of its preferred chart. -/
theorem mem_levelSetChartAt_source
    (hf : ∀ x ∈ {x | f x = c}, HasStrictFDerivAt f (D x) x)
    (hFred : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.IsFredholm (D x))
    (hsurj : ∀ x ∈ {x | f x = c}, Function.Surjective (D x))
    (hindex : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.index (D x) = n)
    (z : ↥{x | f x = c}) : z ∈ (levelSetChartAt hf hFred hsurj hindex z).source :=
  mem_levelSetChartModel_source _ _ _ _ z.2

/-- **A regular level set of a Fredholm map is locally modelled on `Fin n → 𝕜`, `n` its index.**
If `f` is strictly differentiable at every point of the level set `{x | f x = c}` with surjective
Fredholm derivative of index `n` there, then the level set is a charted space modelled on
`Fin n → 𝕜`, the charts being the implicit-function charts `TauCeti.levelSetChartAt`.

This is a `ChartedSpace` structure only: no global hypothesis such as second countability is
assumed, so this does not by itself say that the level set is a topological manifold. -/
@[instance_reducible]
noncomputable def levelSetChartedSpace
    (hf : ∀ x ∈ {x | f x = c}, HasStrictFDerivAt f (D x) x)
    (hFred : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.IsFredholm (D x))
    (hsurj : ∀ x ∈ {x | f x = c}, Function.Surjective (D x))
    (hindex : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.index (D x) = n) :
    ChartedSpace (Fin n → 𝕜) ↥{x | f x = c} where
  atlas := Set.range (levelSetChartAt hf hFred hsurj hindex)
  chartAt := levelSetChartAt hf hFred hsurj hindex
  mem_chart_source z := mem_levelSetChartAt_source hf hFred hsurj hindex z
  chart_mem_atlas z := Set.mem_range_self z

/-- The preferred chart of the charted-space structure at `z` is `TauCeti.levelSetChartAt`. -/
theorem levelSetChartedSpace_chartAt
    (hf : ∀ x ∈ {x | f x = c}, HasStrictFDerivAt f (D x) x)
    (hFred : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.IsFredholm (D x))
    (hsurj : ∀ x ∈ {x | f x = c}, Function.Surjective (D x))
    (hindex : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.index (D x) = n)
    (z : ↥{x | f x = c}) :
    @chartAt (Fin n → 𝕜) _ ↥{x | f x = c} _ (levelSetChartedSpace hf hFred hsurj hindex) z =
      levelSetChartAt hf hFred hsurj hindex z := by
  unfold levelSetChartedSpace
  rfl

/-- The atlas of the charted-space structure is the range of its preferred charts. -/
theorem levelSetChartedSpace_atlas
    (hf : ∀ x ∈ {x | f x = c}, HasStrictFDerivAt f (D x) x)
    (hFred : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.IsFredholm (D x))
    (hsurj : ∀ x ∈ {x | f x = c}, Function.Surjective (D x))
    (hindex : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.index (D x) = n) :
    @atlas (Fin n → 𝕜) _ ↥{x | f x = c} _ (levelSetChartedSpace hf hFred hsurj hindex) =
      Set.range (levelSetChartAt hf hFred hsurj hindex) := by
  unfold atlas levelSetChartedSpace
  rfl

end Model

/-! ### Isolated points, discreteness and accumulation -/

/-- A point at which `f` is differentiable with **injective** derivative of closed range is
isolated in the level set through it: it is not an accumulation point of `{x | f x = c}`. No
relation between `f a` and `c` is assumed; if `f a ≠ c` this is the statement that `a` is not an
accumulation point of a set it does not belong to. -/
theorem not_accPt_of_injective (hf : HasFDerivAt f f' a) (hinj : Function.Injective f')
    (hclosed : IsClosed (Set.range f')) : ¬ AccPt a (𝓟 {x | f x = c}) := by
  rw [accPt_iff_frequently_nhdsNE, not_frequently]
  exact hf.eventually_ne (f'.antilipschitz_of_injective_of_isClosed_range hinj hclosed)

/-- A point at which the derivative is surjective Fredholm **of index zero** is isolated in the
level set through it: the local model `ker f'` is then the zero space. -/
theorem not_accPt_of_index_eq_zero (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hFred : ContinuousLinearMap.IsFredholm f') (hindex : ContinuousLinearMap.index f' = 0) :
    ¬ AccPt a (𝓟 {x | f x = c}) :=
  have hsurj : Function.Surjective f' := LinearMap.range_eq_top.1 hf'
  not_accPt_of_injective hf.hasFDerivAt
    (ContinuousLinearMap.bijective_of_surjective_of_index_eq_zero f' hFred hsurj hindex).injective
    (by rw [hsurj.range_eq]; exact isClosed_univ)

/-- A piece `{x | f x = c} ∩ K` of a level set along which the derivative is injective with closed
range is **discrete**. Only the points of that piece are constrained: nothing is assumed about `f`
away from it. -/
theorem isDiscrete_levelSet_inter_of_injective {D : E → E →L[𝕜] F} {K : Set E}
    (hf : ∀ x ∈ {x | f x = c} ∩ K, HasFDerivAt f (D x) x)
    (hinj : ∀ x ∈ {x | f x = c} ∩ K, Function.Injective (D x))
    (hclosed : ∀ x ∈ {x | f x = c} ∩ K, IsClosed (Set.range (D x))) :
    IsDiscrete ({x | f x = c} ∩ K) :=
  isDiscrete_iff_discreteTopology.2 <| discreteTopology_of_noAccPts fun y hy hy' =>
    not_accPt_of_injective (hf y hy) (hinj y hy) (hclosed y hy)
      (hy'.mono (principal_mono.2 Set.inter_subset_left))

/-- A **compact** piece of a level set along which the derivative is injective with closed range is
**finite**. -/
theorem finite_levelSet_inter_of_injective {D : E → E →L[𝕜] F} {K : Set E}
    (hK : IsCompact ({x | f x = c} ∩ K))
    (hf : ∀ x ∈ {x | f x = c} ∩ K, HasFDerivAt f (D x) x)
    (hinj : ∀ x ∈ {x | f x = c} ∩ K, Function.Injective (D x))
    (hclosed : ∀ x ∈ {x | f x = c} ∩ K, IsClosed (Set.range (D x))) :
    ({x | f x = c} ∩ K).Finite :=
  hK.finite (isDiscrete_levelSet_inter_of_injective hf hinj hclosed)

/-- A **compact** piece `{x | f x = c} ∩ K` of a level set along which the derivative is surjective
Fredholm of index zero is **finite**. When `f` is continuous the level set is closed, so for a
compact `K` the compactness hypothesis is `hK.inter_left (isClosed_eq hcont continuous_const)`.

This is one ingredient in the well-definedness of a count of index-zero solutions, such as a Floer
differential: it makes the counted set finite once a separate compactness result has placed the
solutions to be counted inside such a piece. -/
theorem finite_levelSet_inter_of_index_eq_zero {D : E → E →L[𝕜] F} {K : Set E}
    (hK : IsCompact ({x | f x = c} ∩ K))
    (hf : ∀ x ∈ {x | f x = c} ∩ K, HasStrictFDerivAt f (D x) x)
    (hFred : ∀ x ∈ {x | f x = c} ∩ K, ContinuousLinearMap.IsFredholm (D x))
    (hsurj : ∀ x ∈ {x | f x = c} ∩ K, Function.Surjective (D x))
    (hindex : ∀ x ∈ {x | f x = c} ∩ K, ContinuousLinearMap.index (D x) = 0) :
    ({x | f x = c} ∩ K).Finite :=
  finite_levelSet_inter_of_injective hK (fun x hx => (hf x hx).hasFDerivAt)
    (fun x hx => (ContinuousLinearMap.bijective_of_surjective_of_index_eq_zero (D x) (hFred x hx)
      (hsurj x hx) (hindex x hx)).injective)
    fun x hx => by rw [(hsurj x hx).range_eq]; exact isClosed_univ

/-- At a point of a level set where the derivative is surjective with complemented **nontrivial**
kernel, the level set is not locally the single point `a`: it accumulates at `a`. -/
theorem accPt_of_nontrivial_ker (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) [Nontrivial ↥f'.ker] (ha : f a = c) :
    AccPt a (𝓟 {x | f x = c}) := by
  have : NeBot (𝓝[≠] (0 : ↥f'.ker)) := Module.punctured_nhds_neBot 𝕜 ↥f'.ker 0
  set Ψ := levelSetChart hf hf' hker ha
  have hz₀ : (⟨a, ha⟩ : ↥{x | f x = c}) ∈ Ψ.source := mem_levelSetChart_source hf hf' hker ha
  have hΨ0 : Ψ ⟨a, ha⟩ = 0 := levelSetChart_apply_self hf hf' hker ha
  -- The chart carries the neighbourhoods of `0` in `ker f'` to those of `a` in the level set, so
  -- a point of the level set near `a` and distinct from it is the image of such a point of the
  -- kernel, of which there are some because the kernel is nontrivial.
  have hmap : map Ψ.symm (𝓝 (0 : ↥f'.ker)) = 𝓝 (⟨a, ha⟩ : ↥{x | f x = c}) := by
    rw [← hΨ0]
    exact Ψ.symm_map_nhds_eq hz₀
  rw [accPt_iff_nhds]
  intro U hU
  have hUz : Ψ.symm ⁻¹' (Subtype.val ⁻¹' U) ∈ 𝓝 (0 : ↥f'.ker) := by
    rw [← Filter.mem_map, hmap]
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds hU
  obtain ⟨k, ⟨hkU, hkT⟩, hk0⟩ := Filter.nonempty_of_mem (Filter.inter_mem
    (nhdsWithin_le_nhds (Filter.inter_mem hUz
      (Ψ.open_target.mem_nhds (mem_levelSetChart_target hf hf' hker ha))))
    (self_mem_nhdsWithin (a := (0 : ↥f'.ker)) (s := {0}ᶜ)))
  refine ⟨(Ψ.symm k : E), ⟨hkU, (Ψ.symm k).2⟩, fun hEq => ?_⟩
  have hsub : Ψ.symm k = (⟨a, ha⟩ : ↥{x | f x = c}) := Subtype.ext hEq
  exact hk0 (Set.mem_singleton_iff.2 (by rw [← Ψ.right_inv hkT, hsub, hΨ0]))

/-- At a point of a level set where the derivative is surjective Fredholm of **nonzero** index the
level set accumulates. With `TauCeti.not_accPt_of_index_eq_zero` this says that the level set
reduces to the point `a` near `a` — equivalently, that the local model `ker f'` is trivial —
exactly when the index vanishes. -/
theorem accPt_of_index_ne_zero (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hFred : ContinuousLinearMap.IsFredholm f') (hindex : ContinuousLinearMap.index f' ≠ 0)
    (ha : f a = c) : AccPt a (𝓟 {x | f x = c}) := by
  have hpos : 0 < finrank 𝕜 ↥f'.ker := by
    refine Nat.pos_of_ne_zero fun h0 => hindex ?_
    have h := (ContinuousLinearMap.finrank_ker_eq_iff_index_eq f'
      (LinearMap.range_eq_top.1 hf')).1 h0
    exact_mod_cast h
  have : Nontrivial ↥f'.ker := Module.nontrivial_of_finrank_pos hpos
  exact accPt_of_nontrivial_ker hf hf' hFred.closedComplemented_ker ha

end TauCeti
