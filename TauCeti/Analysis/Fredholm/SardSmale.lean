/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Baire.Lemmas
import TauCeti.Analysis.Calculus.Sard.OutermostStratum
import TauCeti.Analysis.Fredholm.NormalForm
import TauCeti.Analysis.Fredholm.Proper
import TauCeti.Analysis.Normed.Operator.Surjective

/-!
# The Sard--Smale theorem

A **Fredholm map** between Banach spaces is one whose Fréchet derivative is a Fredholm operator at
every point. Sard's theorem fails outright in infinite dimensions -- there is no Haar measure to
be null for, and the critical values of a smooth map on a Hilbert space can be everything -- but
Smale observed that a Fredholm map is finite-dimensional in the only direction that matters, and
that the finite-dimensional theorem therefore survives with "measure zero" replaced by "meagre":

> **Sard--Smale.** The critical values of a sufficiently smooth Fredholm map are meagre, so its
> regular values are residual, and in particular dense.

This file proves that, in the local form
`TauCeti.exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints` first and then in the
global forms `TauCeti.isMeagre_image_criticalPoints_of_isFredholm` and
`TauCeti.dense_compl_image_criticalPoints_of_isFredholm`.

## The proof

The two halves of the local statement are proved from the two halves of the substrate already in
place over the linear Fredholm theory.

*Empty interior* comes from the Lyapunov--Schmidt normal form of
`TauCeti.Analysis.Fredholm.NormalForm`. In the normal-form chart `Φ` at a point `a`, the map
reads `y ↦ y.1 + q y` where the **obstruction** `q` takes values in the finite-dimensional
complement `pkg.decCodom.X₀` of the range; the first coordinate is therefore free, and the
derivative at `Φ.symm y` is surjective exactly when the derivative of the *slice*
`z ↦ q (y.1, z)` is, a map between the two finite-dimensional spaces `pkg.decDom.X₀ = ker` and
`pkg.decCodom.X₀ = coker`. Finite-dimensional Morse--Sard
(`TauCeti.interior_image_criticalPoints_eq_empty`) applies to each slice, so the image of the
critical set meets every fibre of the product `pkg.decCodom.X₁ × pkg.decCodom.X₀` in a set with
empty interior. A set whose fibres over the second factor all have empty interior has empty
interior, because an interior point would supply a whole box; this is where the infinite
dimension of the first factor is harmless.

*Closedness* comes from Smale's local properness lemma in `TauCeti.Analysis.Fredholm.Proper`: on a
small closed ball `N` the preimage of a compact set is compact, and the critical locus is
relatively closed there -- again read off the slice, whose target is finite dimensional, where
`TauCeti.isOpen_setOf_surjective` applies. A convergent sequence of critical values then has its
sources in a compact set, and a subsequential limit produces the missing critical point. Without
this half only density, not residuality, would follow, since a countable union of sets with empty
interior need not be meagre.

The global statement follows by covering: a second-countable domain is Lindelöf, so countably many
of these balls suffice, and a countable union of closed nowhere dense sets is meagre. Density of
the regular values is then the Baire category theorem in the complete space `F`.

The regularity threshold is inherited unchanged from the finite-dimensional theorem: `C^k` with
`k ≥ (dim ker)² + 1`, rather than Smale's sharp `k > index`, because the underlying
`TauCeti.addHaar_image_criticalPoints_eq_zero` is proved with the cruder bound.

## Main results

* `TauCeti.exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints`: the local form -- near a
  point with Fredholm derivative there is a neighbourhood whose critical values are closed and
  nowhere dense.
* `TauCeti.isMeagre_image_criticalPoints_of_isFredholm`: **the Sard--Smale theorem**.
* `TauCeti.dense_compl_image_criticalPoints_of_isFredholm`: the regular values of a Fredholm map
  are dense, the form transversality arguments consume.

This is Lane F0 of the analytic Heegaard Floer roadmap, where Sard--Smale is the gateway to every
transversality argument downstream.

## References

* S. Smale, *An infinite dimensional version of Sard's theorem*, Amer. J. Math. 87 (1965),
  861--866.
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.
-/

public section

open Filter Function MeasureTheory Module Set

open scoped ContDiff Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A subset of a product has empty interior as soon as all of its vertical fibres do: an
interior point of the subset would supply a whole box, whose second factor is an open subset of a
fibre. This is the step of the Sard--Smale argument where the infinite dimension of the first
factor is harmless. -/
private theorem interior_eq_empty_of_forall_interior_fiber_eq_empty {X Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Z] {A : Set (X × Z)}
    (h : ∀ x : X, interior {z | (x, z) ∈ A} = ∅) : interior A = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ⟨x, z⟩ hxz
  have hopen : IsOpen {z' : Z | (x, z') ∈ interior A} := isOpen_interior.preimage (by fun_prop)
  have hsub : {z' : Z | (x, z') ∈ interior A} ⊆ {z' : Z | (x, z') ∈ A} :=
    fun _ hz' ↦ interior_subset (s := A) hz'
  have hz : z ∈ interior {z' : Z | (x, z') ∈ A} := interior_maximal hsub hopen hxz
  rw [h x] at hz
  exact hz

/-- Surjectivity of `w ↦ w.1 + D w`, where `D` takes values in a topological complement of the
subspace `w.1` ranges over, is decided by the partial map `z ↦ D (0, z)`: the first coordinate is
free, so only the complementary direction can obstruct. This is the linear core of the
Lyapunov--Schmidt reduction of surjectivity to a finite-dimensional condition. -/
private theorem surjective_add_coe_iff {X₁ Y₀ : Submodule ℝ F} (h : Submodule.IsTopCompl X₁ Y₀)
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (D : (X₁ × Z) →L[ℝ] Y₀) :
    Surjective (fun w : X₁ × Z ↦ ((w.1 : F) + (D w : F))) ↔ Surjective fun z : Z ↦ D (0, z) := by
  have hu : ∀ (w₁ : X₁) (w₂ : Z), ((w₁ : F) + (D (w₁, w₂) : F)) =
      Submodule.prodEquivOfIsTopCompl X₁ Y₀ h (w₁, D (w₁, w₂)) :=
    fun w₁ w₂ ↦ (Submodule.prodEquivOfIsTopCompl_apply h (w₁, D (w₁, w₂))).symm
  have hsplit : ∀ (w₁ : X₁) (w₂ : Z), D (w₁, w₂) = D (w₁, 0) + D (0, w₂) := by
    intro w₁ w₂
    rw [← map_add]
    congr 1
    simp
  constructor
  · intro hs v
    obtain ⟨⟨w₁, w₂⟩, hw⟩ := hs (Submodule.prodEquivOfIsTopCompl X₁ Y₀ h (0, v))
    have hw' : ((w₁ : F) + (D (w₁, w₂) : F)) =
        Submodule.prodEquivOfIsTopCompl X₁ Y₀ h (0, v) := hw
    rw [hu w₁ w₂] at hw'
    have hpair := (Submodule.prodEquivOfIsTopCompl X₁ Y₀ h).injective hw'
    rw [Prod.mk.injEq] at hpair
    exact ⟨w₂, by rw [← hpair.2, hpair.1]⟩
  · intro hs y
    obtain ⟨⟨p₁, p₂⟩, hp⟩ := (Submodule.prodEquivOfIsTopCompl X₁ Y₀ h).surjective y
    obtain ⟨z, hz⟩ := hs (p₂ - D (p₁, 0))
    have hz' : D (0, z) = p₂ - D (p₁, 0) := hz
    -- The goal is the value of the displayed function at `(p₁, z)`; state that value as a typed
    -- `have`, which is rewritable, and let `exact` cross the beta reduction.
    have hval : ((p₁ : F) + (D (p₁, z) : F)) = y := by
      rw [hu p₁ z, ← hp]
      congr 1
      rw [Prod.mk.injEq]
      refine ⟨rfl, ?_⟩
      rw [hsplit, hz']
      abel
    exact ⟨(p₁, z), hval⟩

/-- The inclusion of the inessential domain summand as the second factor of the normal-form
coordinates. Slicing the obstruction map through a fixed essential coordinate differentiates along
this inclusion. -/
private noncomputable def sliceIncl {T : E →L[ℝ] F}
    (pkg : ContinuousLinearMap.FredholmPackage T) :
    pkg.decDom.X₀ →L[ℝ] (pkg.decCodom.X₁ × pkg.decDom.X₀) :=
  (0 : pkg.decDom.X₀ →L[ℝ] pkg.decCodom.X₁).prod (ContinuousLinearMap.id ℝ pkg.decDom.X₀)

section Local

variable [CompleteSpace E] [CompleteSpace F] {T : E →L[ℝ] F} {f : E → F} {a : E}

omit [CompleteSpace F] in
/-- **Lyapunov--Schmidt reduction of regularity.** At a point of the normal-form chart where the
chart, the obstruction and the map itself are all differentiable and the chart has invertible
derivative, the derivative of `f` is surjective exactly when the derivative of the
finite-dimensional obstruction slice is. -/
private theorem surjective_fderiv_iff_slice (pkg : ContinuousLinearMap.FredholmPackage T)
    (hT : HasStrictFDerivAt f T a)
    {y : pkg.decCodom.X₁ × pkg.decDom.X₀}
    (hy : y ∈ (pkg.normalFormOpenPartialHomeomorph hT).target)
    (hq : DifferentiableAt ℝ (pkg.obstructionMap hT) y)
    (hinv : ∃ e : (pkg.decCodom.X₁ × pkg.decDom.X₀) ≃L[ℝ] E,
      (e : (pkg.decCodom.X₁ × pkg.decDom.X₀) →L[ℝ] E) =
        fderiv ℝ (pkg.normalFormOpenPartialHomeomorph hT).symm y)
    (hsym : DifferentiableAt ℝ (pkg.normalFormOpenPartialHomeomorph hT).symm y)
    (hfd : DifferentiableAt ℝ f ((pkg.normalFormOpenPartialHomeomorph hT).symm y)) :
    Surjective (fderiv ℝ f ((pkg.normalFormOpenPartialHomeomorph hT).symm y)) ↔
      Surjective (fderiv ℝ (fun z ↦ pkg.obstructionMap hT (y.1, z)) y.2) := by
  obtain ⟨e, he⟩ := hinv
  set Φ := pkg.normalFormOpenPartialHomeomorph hT with hΦ
  set q := pkg.obstructionMap hT with hqdef
  have hsym' : HasFDerivAt Φ.symm (e : (pkg.decCodom.X₁ × pkg.decDom.X₀) →L[ℝ] E) y := by
    rw [he]; exact hsym.hasFDerivAt
  -- The derivative of `f ∘ Φ.symm` at `y`, computed through the chart.
  have h1 : HasFDerivAt (fun y' ↦ f (Φ.symm y'))
      ((fderiv ℝ f (Φ.symm y)).comp (e : (pkg.decCodom.X₁ × pkg.decDom.X₀) →L[ℝ] E)) y :=
    hfd.hasFDerivAt.comp y hsym'
  -- The same derivative, computed through the normal form `y' ↦ y'.1 + q y'`.
  set u : (pkg.decCodom.X₁ × pkg.decDom.X₀) →L[ℝ] F :=
    (pkg.decCodom.X₁.subtypeL.comp (ContinuousLinearMap.fst ℝ _ _)) +
      (pkg.decCodom.X₀.subtypeL.comp (fderiv ℝ q y)) with hudef
  have hufun : ⇑u =
      fun w : pkg.decCodom.X₁ × pkg.decDom.X₀ ↦ ((w.1 : F) + ((fderiv ℝ q y) w : F)) := by
    funext w
    simp [hudef]
  have h2 : HasFDerivAt (fun y' ↦ f (Φ.symm y')) u y := by
    have hfst : HasFDerivAt
        (fun y' : pkg.decCodom.X₁ × pkg.decDom.X₀ ↦ ((y'.1 : F)))
        (pkg.decCodom.X₁.subtypeL.comp (ContinuousLinearMap.fst ℝ _ _)) y :=
      pkg.decCodom.X₁.subtypeL.hasFDerivAt.comp y hasFDerivAt_fst
    have hsnd : HasFDerivAt (fun y' ↦ ((q y' : F)))
        (pkg.decCodom.X₀.subtypeL.comp (fderiv ℝ q y)) y :=
      pkg.decCodom.X₀.subtypeL.hasFDerivAt.comp y hq.hasFDerivAt
    refine (hfst.add hsnd).congr_of_eventuallyEq ?_
    filter_upwards [Φ.open_target.mem_nhds hy] with y' hy'
    exact pkg.apply_normalFormOpenPartialHomeomorph_symm hT hy'
  have heq := h1.unique h2
  -- Precomposition with an equivalence does not change surjectivity.
  have hstep₁ : Surjective (fderiv ℝ f (Φ.symm y)) ↔ Surjective ⇑u := by
    rw [← heq]
    constructor
    · intro hs
      exact hs.comp e.surjective
    · intro hs
      have hs' : Surjective (⇑(fderiv ℝ f (Φ.symm y)) ∘ ⇑e) := hs
      exact hs'.of_comp
  -- The slice derivative is the restriction of `fderiv q` to the second factor.
  have hslice : HasFDerivAt (fun z ↦ q (y.1, z)) ((fderiv ℝ q y).comp (sliceIncl pkg)) y.2 := by
    have h0 : HasFDerivAt
        (fun z : pkg.decDom.X₀ ↦ ((y.1, z) : pkg.decCodom.X₁ × pkg.decDom.X₀))
        (sliceIncl pkg) y.2 :=
      (hasFDerivAt_const y.1 y.2).prodMk (hasFDerivAt_id y.2)
    exact hq.hasFDerivAt.comp y.2 h0
  rw [hstep₁, hufun, surjective_add_coe_iff pkg.decCodom.isTopCompl, hslice.fderiv]
  simp [ContinuousLinearMap.coe_comp, Function.comp_def, sliceIncl]

/-- **Sard--Smale, locally.** Near a point where a sufficiently smooth map has Fredholm
derivative there is a neighbourhood on which the critical values form a closed nowhere dense set.

The regularity threshold `(dim ker)² + 1` is the one inherited from the finite-dimensional
Morse--Sard theorem `TauCeti.interior_image_criticalPoints_eq_empty`, which the fibrewise step
applies to the obstruction slice, a map out of `ker (fderiv ℝ f a)`. -/
theorem exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints
    {f : E → F} {a : E} {n : ℕ∞ω} (hf : ContDiffAt ℝ n f a)
    (hFred : (fderiv ℝ f a).IsFredholm)
    (hn : ((finrank ℝ (fderiv ℝ f a).ker * finrank ℝ (fderiv ℝ f a).ker + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ∃ N ∈ 𝓝 a, IsClosed (f '' (N ∩ {x | ¬ Surjective (fderiv ℝ f x)})) ∧
      IsNowhereDense (f '' (N ∩ {x | ¬ Surjective (fderiv ℝ f x)})) := by
  set T := fderiv ℝ f a with hTdef
  set k : ℕ := finrank ℝ T.ker * finrank ℝ T.ker + 1 with hkdef
  have hk1 : (1 : ℕ∞ω) ≤ (k : ℕ∞ω) := by
    have : (1 : ℕ) ≤ k := by omega
    exact_mod_cast this
  have hk0 : ((k : ℕ∞ω)) ≠ 0 := by
    intro h
    exact absurd (h ▸ hk1) (by simp)
  have hkω : ((k : ℕ∞ω)) ≠ ∞ := by simp
  replace hf : ContDiffAt ℝ (k : ℕ∞ω) f a := hf.of_le hn
  have hT : HasStrictFDerivAt f T a := hf.hasStrictFDerivAt hk0
  obtain ⟨pkg⟩ := hFred.nonempty_fredholmPackage
  have : CompleteSpace pkg.decDom.X₀ := pkg.decDom.isTopCompl.isClosed'.completeSpace_coe
  have : CompleteSpace pkg.decDom.X₁ := pkg.decDom.isTopCompl.isClosed.completeSpace_coe
  have : CompleteSpace pkg.decCodom.X₁ :=
    (pkg.equiv.isUniformEmbedding.completeSpace_congr pkg.equiv.surjective).mp inferInstance
  have : FiniteDimensional ℝ pkg.decDom.X₀ := pkg.decDom.finite_X₀
  have : FiniteDimensional ℝ pkg.decCodom.X₀ := pkg.decCodom.finite_X₀
  have hkbound :
      ((finrank ℝ pkg.decDom.X₀ * finrank ℝ pkg.decDom.X₀ + 1 : ℕ) : ℕ∞ω) ≤ (k : ℕ∞ω) := by
    have hker : finrank ℝ T.ker = finrank ℝ pkg.decDom.X₀ := by rw [pkg.ker_eq]
    rw [hkdef, hker]
  set Φ := pkg.normalFormOpenPartialHomeomorph hT with hΦdef
  set q := pkg.obstructionMap hT with hqdef
  set y₀ : pkg.decCodom.X₁ × pkg.decDom.X₀ := (pkg.decCodom.proj (f a), 0) with hy₀def
  have hy₀ : y₀ ∈ Φ.target := pkg.normalFormOpenPartialHomeomorph_self_mem_target hT
  have ha : a ∈ Φ.source := pkg.mem_normalFormOpenPartialHomeomorph_source hT
  have hΦa : Φ a = y₀ := by
    rw [hΦdef, pkg.normalFormOpenPartialHomeomorph_apply hT, pkg.normalFormMap_self]
  have hsymy₀ : Φ.symm y₀ = a := by
    rw [hy₀def, hΦdef]
    simpa only [Submodule.coe_projectionOntoL] using
      pkg.normalFormOpenPartialHomeomorph_symm_self hT
  -- A neighbourhood of the base coordinate on which the chart, the obstruction and the map are
  -- all as smooth as `f` and the chart has invertible derivative.
  have hgood : ∀ᶠ y in 𝓝 y₀, y ∈ Φ.target ∧ ContDiffAt ℝ (k : ℕ∞ω) q y ∧
      ContDiffAt ℝ (k : ℕ∞ω) Φ.symm y ∧
      (∃ e : (pkg.decCodom.X₁ × pkg.decDom.X₀) ≃L[ℝ] E,
        (e : (pkg.decCodom.X₁ × pkg.decDom.X₀) →L[ℝ] E) = fderiv ℝ Φ.symm y) ∧
      ContDiffAt ℝ (k : ℕ∞ω) f (Φ.symm y) := by
    have hqC : ContDiffAt ℝ (k : ℕ∞ω) q y₀ := pkg.contDiffAt_obstructionMap_self hT hf
    have hsymC : ContDiffAt ℝ (k : ℕ∞ω) Φ.symm y₀ :=
      pkg.contDiffAt_normalFormOpenPartialHomeomorph_symm_self hT hf
    have h₄ : ∀ᶠ y in 𝓝 y₀, ∃ e : (pkg.decCodom.X₁ × pkg.decDom.X₀) ≃L[ℝ] E,
        (e : (pkg.decCodom.X₁ × pkg.decDom.X₀) →L[ℝ] E) = fderiv ℝ Φ.symm y := by
      have hcont : ContinuousAt (fderiv ℝ Φ.symm) y₀ := hsymC.continuousAt_fderiv hk0
      have hmem : Set.range ((↑) : ((pkg.decCodom.X₁ × pkg.decDom.X₀) ≃L[ℝ] E) →
          ((pkg.decCodom.X₁ × pkg.decDom.X₀) →L[ℝ] E)) ∈ 𝓝 (fderiv ℝ Φ.symm y₀) := by
        rw [(pkg.hasStrictFDerivAt_normalFormOpenPartialHomeomorph_symm_self hT).hasFDerivAt.fderiv]
        exact ContinuousLinearEquiv.nhds _
      exact hcont hmem
    have h₅ : ∀ᶠ y in 𝓝 y₀, ContDiffAt ℝ (k : ℕ∞ω) f (Φ.symm y) := by
      have hev := hf.eventually hkω
      rw [← hsymy₀] at hev
      exact hsymC.continuousAt hev
    filter_upwards [Φ.open_target.mem_nhds hy₀, hqC.eventually hkω, hsymC.eventually hkω, h₄, h₅]
      with y c₁ c₂ c₃ c₄ c₅ using ⟨c₁, c₂, c₃, c₄, c₅⟩
  rw [Filter.eventually_iff_exists_mem] at hgood
  obtain ⟨V₀, hV₀, hV₀P⟩ := hgood
  obtain ⟨V, hVV₀, hVopen, hy₀V⟩ := mem_nhds_iff.1 hV₀
  have hVP := fun y (hy : y ∈ V) ↦ hV₀P y (hVV₀ hy)
  set N : Set E := Φ.source ∩ Φ ⁻¹' V with hNdef
  have hNopen : IsOpen N := Φ.isOpen_inter_preimage hVopen
  have haN : a ∈ N := ⟨ha, by rw [Set.mem_preimage, hΦa]; exact hy₀V⟩
  have hNV : ∀ x ∈ N, Φ x ∈ V := fun x hx ↦ hx.2
  have hNsymm : ∀ x ∈ N, Φ.symm (Φ x) = x := fun x hx ↦ Φ.left_inv hx.1
  have hfN : ∀ x ∈ N, ContDiffAt ℝ (k : ℕ∞ω) f x := by
    intro x hx
    have := (hVP (Φ x) (hNV x hx)).2.2.2.2
    rwa [hNsymm x hx] at this
  -- The slice derivative is the restriction of the derivative of the obstruction.
  have hsliceD : ∀ y ∈ V,
      fderiv ℝ (fun z ↦ q (y.1, z)) y.2 = (fderiv ℝ q y).comp (sliceIncl pkg) := by
    intro y hy
    exact (((hVP y hy).2.1.differentiableAt hk0).hasFDerivAt.comp y.2
      ((hasFDerivAt_const y.1 y.2).prodMk (hasFDerivAt_id y.2))).fderiv
  -- Regularity of `f` on `N` is regularity of the finite-dimensional obstruction slice.
  have hcrit : ∀ x ∈ N, (Surjective (fderiv ℝ f x) ↔
      Surjective (fderiv ℝ (fun z ↦ q ((Φ x).1, z)) (Φ x).2)) := by
    intro x hx
    obtain ⟨c₁, c₂, c₃, c₄, c₅⟩ := hVP (Φ x) (hNV x hx)
    have hiff := surjective_fderiv_iff_slice pkg hT c₁ (c₂.differentiableAt hk0) c₄
      (c₃.differentiableAt hk0) (c₅.differentiableAt hk0)
    rwa [hNsymm x hx] at hiff
  -- The image of the critical set of `N` has empty interior, fibrewise by Morse--Sard.
  set Λ := Submodule.prodEquivOfIsTopCompl pkg.decCodom.X₁ pkg.decCodom.X₀
    pkg.decCodom.isTopCompl with hΛdef
  set A : Set (pkg.decCodom.X₁ × pkg.decCodom.X₀) :=
    {p | p.2 ∈ (fun z ↦ q (p.1, z)) ''
      ({z | (p.1, z) ∈ V} ∩ {z | ¬ Surjective (fderiv ℝ (fun z ↦ q (p.1, z)) z)})} with hAdef
  have hAint : interior A = ∅ := by
    refine interior_eq_empty_of_forall_interior_fiber_eq_empty fun p₁ ↦ ?_
    -- The fibre of `A` over `p₁` is the image of the critical set of the slice at `p₁`.
    have hfiber : {z | (p₁, z) ∈ A} = (fun z ↦ q (p₁, z)) ''
        ({z | (p₁, z) ∈ V} ∩ {z | ¬ Surjective (fderiv ℝ (fun z ↦ q (p₁, z)) z)}) := by
      rw [hAdef]
      ext z
      simp only [Set.mem_ofPred_eq]
    rw [hfiber]
    have hUopen : IsOpen {z : pkg.decDom.X₀ | (p₁, z) ∈ V} :=
      hVopen.preimage (by fun_prop)
    have hUC : ∀ z ∈ {z : pkg.decDom.X₀ | (p₁, z) ∈ V},
        ContDiffAt ℝ (k : ℕ∞ω) (fun z ↦ q (p₁, z)) z := fun z hz ↦
      ((hVP _ hz).2.1).comp z (contDiffAt_const.prodMk contDiffAt_id)
    exact interior_image_criticalPoints_eq_empty hUopen hUC hkbound
  have himg : f '' (N ∩ {x | ¬ Surjective (fderiv ℝ f x)}) ⊆ Λ '' A := by
    rintro _ ⟨x, ⟨hxN, hxc⟩, rfl⟩
    obtain ⟨c₁, -, -, -, -⟩ := hVP (Φ x) (hNV x hxN)
    refine ⟨((Φ x).1, q (Φ x)), ⟨(Φ x).2, ⟨hNV x hxN, ?_⟩, rfl⟩, ?_⟩
    · exact fun hs ↦ hxc ((hcrit x hxN).2 hs)
    · rw [hΛdef, Submodule.prodEquivOfIsTopCompl_apply]
      conv_rhs => rw [← hNsymm x hxN]
      exact (pkg.apply_normalFormOpenPartialHomeomorph_symm hT c₁).symm
  have hNint : interior (f '' (N ∩ {x | ¬ Surjective (fderiv ℝ f x)})) = ∅ := by
    have h1 : interior (Λ '' A) = ∅ := by
      have h2 := Λ.toHomeomorph.image_interior A
      simp only [ContinuousLinearEquiv.coe_toHomeomorph] at h2
      rw [← h2, hAint, Set.image_empty]
    exact Set.eq_empty_of_subset_empty (h1 ▸ interior_mono himg)
  -- The critical locus is relatively closed in `N`, again read off the finite-dimensional slice.
  have hWopen : IsOpen {y | y ∈ V ∧ Surjective ((fderiv ℝ q y).comp (sliceIncl pkg))} := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨hyV, hys⟩
    have hcont : ContinuousAt (fderiv ℝ q) y := ((hVP y hyV).2.1).continuousAt_fderiv hk0
    have hmap : ContinuousAt (fun y' ↦ (fderiv ℝ q y').comp (sliceIncl pkg)) y :=
      hcont.clm_comp continuousAt_const
    filter_upwards [hVopen.mem_nhds hyV,
      hmap (IsOpen.mem_nhds isOpen_setOf_surjective hys)] with y' d₁ d₂
    exact ⟨d₁, d₂⟩
  have hregopen : IsOpen {x | x ∈ N ∧ Surjective (fderiv ℝ f x)} := by
    have heq : {x | x ∈ N ∧ Surjective (fderiv ℝ f x)} =
        N ∩ (Φ.source ∩ Φ ⁻¹' {y | y ∈ V ∧ Surjective ((fderiv ℝ q y).comp (sliceIncl pkg))}) := by
      ext x
      constructor
      · rintro ⟨hxN, hxs⟩
        have h1 : Surjective ((fderiv ℝ q (Φ x)).comp (sliceIncl pkg)) := by
          rw [← hsliceD (Φ x) (hNV x hxN)]
          exact (hcrit x hxN).1 hxs
        exact ⟨hxN, hxN.1, hNV x hxN, h1⟩
      · rintro ⟨hxN, -, -, hs⟩
        have h2 : Surjective (fderiv ℝ (fun z ↦ q ((Φ x).1, z)) (Φ x).2) := by
          rw [hsliceD (Φ x) (hNV x hxN)]
          exact hs
        exact ⟨hxN, (hcrit x hxN).2 h2⟩
    rw [heq]
    exact hNopen.inter (Φ.isOpen_inter_preimage hWopen)
  -- Smale's local properness, on a closed ball inside `N`.
  obtain ⟨N₂, hN₂, hprop⟩ := hT.exists_mem_nhds_forall_isCompact_inter_preimage
    hFred.isClosed_range hFred.finite_ker hFred.closedComplemented_ker
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (hNopen.mem_nhds haN) hN₂)
  set N' : Set E := Metric.closedBall a (r / 2) with hN'def
  have hN'ball : N' ⊆ N ∩ N₂ := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hN'nhds : N' ∈ 𝓝 a := Metric.closedBall_mem_nhds a (by linarith)
  have hcritclosed : IsClosed (N' ∩ {x | ¬ Surjective (fderiv ℝ f x)}) := by
    have heq : N' ∩ {x | ¬ Surjective (fderiv ℝ f x)} =
        N' ∩ {x | x ∈ N ∧ Surjective (fderiv ℝ f x)}ᶜ := by
      ext x
      refine ⟨fun hx ↦ ⟨hx.1, fun hc ↦ hx.2 hc.2⟩, fun hx ↦ ⟨hx.1, fun hc ↦ hx.2 ⟨?_, hc⟩⟩⟩
      exact (hN'ball hx.1).1
    rw [heq]
    exact Metric.isClosed_closedBall.inter hregopen.isClosed_compl
  have hclosedimg : IsClosed (f '' (N' ∩ {x | ¬ Surjective (fderiv ℝ f x)})) := by
    apply IsSeqClosed.isClosed
    intro u y hu huy
    choose x hx hfx using hu
    have hLcpt : IsCompact (insert y (Set.range u)) := huy.isCompact_insert_range
    have hK : IsCompact (N' ∩ f ⁻¹' (insert y (Set.range u))) := by
      have heq : N' ∩ f ⁻¹' (insert y (Set.range u)) =
          N' ∩ (N₂ ∩ f ⁻¹' (insert y (Set.range u))) :=
        Set.ext fun z ↦ ⟨fun h ↦ ⟨h.1, (hN'ball h.1).2, h.2⟩, fun h ↦ ⟨h.1, h.2.2⟩⟩
      rw [heq]
      exact (hprop _ hLcpt).inter_left Metric.isClosed_closedBall
    have hxmem : ∀ m, x m ∈ N' ∩ f ⁻¹' (insert y (Set.range u)) := fun m ↦
      ⟨(hx m).1, by rw [Set.mem_preimage, hfx m]; exact Set.mem_insert_of_mem _ ⟨m, rfl⟩⟩
    obtain ⟨z, -, φ, hφmono, hφtend⟩ := hK.tendsto_subseq hxmem
    have hzc : z ∈ N' ∩ {x | ¬ Surjective (fderiv ℝ f x)} :=
      hcritclosed.mem_of_tendsto hφtend (Filter.Eventually.of_forall fun m ↦ hx (φ m))
    refine ⟨z, hzc, ?_⟩
    have hfcont : ContinuousAt f z := (hfN z (hN'ball hzc.1).1).continuousAt
    have h1 : Filter.Tendsto (fun m ↦ f (x (φ m))) Filter.atTop (𝓝 (f z)) :=
      hfcont.tendsto.comp hφtend
    have h2 : Filter.Tendsto (fun m ↦ f (x (φ m))) Filter.atTop (𝓝 y) := by
      simp_rw [hfx]
      exact huy.comp hφmono.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  refine ⟨N', hN'nhds, hclosedimg, ?_⟩
  rw [hclosedimg.isNowhereDense_iff]
  refine Set.eq_empty_of_subset_empty ?_
  rw [← hNint]
  exact interior_mono (Set.image_mono
    (Set.inter_subset_inter (fun z hz ↦ (hN'ball hz).1) (subset_refl _)))

end Local

section Global

variable [CompleteSpace E] [CompleteSpace F] [SecondCountableTopology E]
  {U : Set E} {f : E → F}

/-- **The Sard--Smale theorem.** The critical values of a sufficiently smooth Fredholm map on an
open subset of a separable Banach space form a meagre set.

Sard's theorem itself is false in infinite dimensions, and "measure zero" has no meaning there;
what survives is that the Fredholm condition confines the failure of regularity to a
finite-dimensional direction, in which the finite-dimensional theorem applies fibrewise.

The regularity threshold is the pointwise one of
`TauCeti.exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints`: at each point `C^k` with
`k ≥ (dim ker)² + 1`. In particular `n = ∞` needs no side condition. -/
theorem isMeagre_image_criticalPoints_of_isFredholm {n : ℕ∞ω} (hU : IsOpen U)
    (hf : ∀ x ∈ U, ContDiffAt ℝ n f x) (hFred : ∀ x ∈ U, (fderiv ℝ f x).IsFredholm)
    (hn : ∀ x ∈ U, ((finrank ℝ (fderiv ℝ f x).ker * finrank ℝ (fderiv ℝ f x).ker + 1 : ℕ) : ℕ∞ω)
      ≤ n) :
    IsMeagre (f '' (U ∩ {x | ¬ Surjective (fderiv ℝ f x)})) := by
  have hloc : ∀ x ∈ U, ∃ N ⊆ U, N ∈ 𝓝 x ∧
      IsNowhereDense (f '' (N ∩ {x | ¬ Surjective (fderiv ℝ f x)})) := by
    intro x hx
    obtain ⟨N, hN, -, hNnd⟩ := exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints
      (hf x hx) (hFred x hx) (hn x hx)
    refine ⟨N ∩ U, Set.inter_subset_right, Filter.inter_mem hN (hU.mem_nhds hx), ?_⟩
    exact hNnd.mono (Set.image_mono (Set.inter_subset_inter Set.inter_subset_left le_rfl))
  choose! N hNU hNnhds hNnd using hloc
  obtain ⟨t, htU, htc, htcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := N) (s := U) fun x hx ↦ nhdsWithin_le_nhds (hNnhds x hx)
  have hsub : f '' (U ∩ {x | ¬ Surjective (fderiv ℝ f x)}) ⊆
      ⋃ x ∈ t, f '' (N x ∩ {x | ¬ Surjective (fderiv ℝ f x)}) := by
    rintro _ ⟨z, ⟨hzU, hzc⟩, rfl⟩
    obtain ⟨x, hx, hzN⟩ := Set.mem_iUnion₂.1 (htcover hzU)
    exact Set.mem_iUnion₂.2 ⟨x, hx, ⟨z, ⟨hzN, hzc⟩, rfl⟩⟩
  exact IsMeagre.mono hsub (isMeagre_biUnion htc fun x hx ↦ (hNnd x (htU hx)).isMeagre)

/-- **Sard--Smale**, in the form transversality arguments consume: the regular values of a
sufficiently smooth Fredholm map are dense, being the complement of a meagre set in a Baire
space. The regularity threshold is that of
`TauCeti.isMeagre_image_criticalPoints_of_isFredholm`. -/
theorem dense_compl_image_criticalPoints_of_isFredholm {n : ℕ∞ω} (hU : IsOpen U)
    (hf : ∀ x ∈ U, ContDiffAt ℝ n f x) (hFred : ∀ x ∈ U, (fderiv ℝ f x).IsFredholm)
    (hn : ∀ x ∈ U, ((finrank ℝ (fderiv ℝ f x).ker * finrank ℝ (fderiv ℝ f x).ker + 1 : ℕ) : ℕ∞ω)
      ≤ n) :
    Dense (f '' (U ∩ {x | ¬ Surjective (fderiv ℝ f x)}))ᶜ :=
  dense_of_mem_residual (isMeagre_image_criticalPoints_of_isFredholm hU hf hFred hn)

end Global

end TauCeti

end
