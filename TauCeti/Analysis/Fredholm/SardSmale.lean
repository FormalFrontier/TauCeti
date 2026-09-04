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
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
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

> **Sard--Smale.** The critical values of a sufficiently smooth Fredholm map on an open subset of
> a separable Banach space are meagre, so its regular values are residual, and in particular
> dense.

This file proves that, in the local form
`TauCeti.exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints` first and then in the
global forms `TauCeti.isMeagre_image_criticalPoints_of_isFredholm` and
`TauCeti.dense_compl_image_criticalPoints_of_isFredholm`. The local form needs no separability;
the global ones assume the domain second countable, since their proof covers it by countably many
of the local neighbourhoods.

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
the regular values is then the Baire category theorem. The `CompleteSpace F` assumption supplies
both the Baire instance and the local properness used above to prove closedness.

The regularity threshold is inherited unchanged from the finite-dimensional theorem: `C^k` with
`k ≥ (dim ker)² + 1`, rather than Smale's sharp `k > index`, because the underlying
`TauCeti.addHaar_image_criticalPoints_eq_zero` is proved with the cruder bound.

## Main results

* `TauCeti.exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints`: the local form -- inside
  any neighbourhood of a point with Fredholm derivative there is a neighbourhood whose critical
  values are closed and nowhere dense.
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

section Local

variable [CompleteSpace E] [CompleteSpace F] {T : E →L[ℝ] F} {f : E → F} {a : E}

omit [CompleteSpace F] in
/-- Fixing the essential coordinate differentiates the obstruction along the inclusion of the
inessential domain summand as the second normal-form factor: the derivative of
`ContinuousLinearMap.FredholmPackage.obstructionSlice` is the derivative of the obstruction map
precomposed with `ContinuousLinearMap.inr`. -/
private theorem hasFDerivAt_obstructionSlice (pkg : ContinuousLinearMap.FredholmPackage T)
    (hT : HasStrictFDerivAt f T a) {y : pkg.decCodom.X₁ × pkg.decDom.X₀}
    (hq : DifferentiableAt ℝ (pkg.obstructionMap hT) y) :
    HasFDerivAt (pkg.obstructionSlice hT y.1)
      ((fderiv ℝ (pkg.obstructionMap hT) y).comp
        (ContinuousLinearMap.inr ℝ pkg.decCodom.X₁ pkg.decDom.X₀)) y.2 := by
  rw [funext (pkg.obstructionSlice_apply hT y.1)]
  exact hq.hasFDerivAt.comp y.2 ((hasFDerivAt_const y.1 y.2).prodMk (hasFDerivAt_id y.2))

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
      Surjective (fderiv ℝ (pkg.obstructionSlice hT y.1) y.2) := by
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
    simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe]
    exact (EquivLike.surjective_comp e _).symm
  -- The slice derivative is the restriction of `fderiv q` to the second factor.
  have hslice : HasFDerivAt (pkg.obstructionSlice hT y.1)
      ((fderiv ℝ q y).comp (ContinuousLinearMap.inr ℝ pkg.decCodom.X₁ pkg.decDom.X₀)) y.2 := by
    rw [hqdef]
    exact hasFDerivAt_obstructionSlice pkg hT hq
  rw [hstep₁, hufun, surjective_add_coe_iff pkg.decCodom.isTopCompl, hslice.fderiv]
  simp [ContinuousLinearMap.coe_comp, Function.comp_def]

/-- **Sard--Smale, locally.** Near a point where a sufficiently smooth map has Fredholm
derivative there is a neighbourhood on which the critical values form a closed nowhere dense set.
The neighbourhood can be taken inside any prescribed neighbourhood `U` of the point, so the
conclusion can be confined to a region on which `f` is known to be the map of interest.

Completeness of the target enters through Smale's local properness lemma, which supplies the
compactness used to prove that the local critical-value image is closed.

The regularity threshold `(dim ker)² + 1` is the one inherited from the finite-dimensional
Morse--Sard theorem `TauCeti.interior_image_criticalPoints_eq_empty`, which the fibrewise step
applies to the obstruction slice, a map out of `ker (fderiv ℝ f a)`. -/
theorem exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints
    {f : E → F} {a : E} {U : Set E} {n : ℕ∞ω} (hf : ContDiffAt ℝ n f a)
    (hFred : (fderiv ℝ f a).IsFredholm)
    (hn : ((finrank ℝ (fderiv ℝ f a).ker * finrank ℝ (fderiv ℝ f a).ker + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hU : U ∈ 𝓝 a) :
    ∃ N ∈ 𝓝 a, N ⊆ U ∧ IsClosed (f '' (N ∩ {x | ¬ Surjective (fderiv ℝ f x)})) ∧
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
  -- The inclusion of the inessential domain summand as the second normal-form factor.
  set ι := ContinuousLinearMap.inr ℝ pkg.decCodom.X₁ pkg.decDom.X₀ with hιdef
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
      fderiv ℝ (pkg.obstructionSlice hT y.1) y.2 = (fderiv ℝ q y).comp ι := by
    intro y hy
    rw [hqdef, hιdef]
    exact (hasFDerivAt_obstructionSlice pkg hT ((hVP y hy).2.1.differentiableAt hk0)).fderiv
  -- Regularity of `f` on `N` is regularity of the finite-dimensional obstruction slice.
  have hcrit : ∀ x ∈ N, (Surjective (fderiv ℝ f x) ↔
      Surjective (fderiv ℝ (pkg.obstructionSlice hT (Φ x).1) (Φ x).2)) := by
    intro x hx
    obtain ⟨c₁, c₂, c₃, c₄, c₅⟩ := hVP (Φ x) (hNV x hx)
    have hiff := surjective_fderiv_iff_slice pkg hT c₁ (c₂.differentiableAt hk0) c₄
      (c₃.differentiableAt hk0) (c₅.differentiableAt hk0)
    rwa [hNsymm x hx] at hiff
  -- The image of the critical set of `N` has empty interior, fibrewise by Morse--Sard.
  set Λ := Submodule.prodEquivOfIsTopCompl pkg.decCodom.X₁ pkg.decCodom.X₀
    pkg.decCodom.isTopCompl with hΛdef
  set A : Set (pkg.decCodom.X₁ × pkg.decCodom.X₀) :=
    {p | p.2 ∈ pkg.obstructionSlice hT p.1 ''
      ({z | (p.1, z) ∈ V} ∩
        {z | ¬ Surjective (fderiv ℝ (pkg.obstructionSlice hT p.1) z)})} with hAdef
  have hAint : interior A = ∅ := by
    refine interior_eq_empty_of_forall_interior_fiber_eq_empty fun p₁ ↦ ?_
    -- The fibre of `A` over `p₁` is the image of the critical set of the slice at `p₁`.
    have hfiber : {z | (p₁, z) ∈ A} = pkg.obstructionSlice hT p₁ ''
        ({z | (p₁, z) ∈ V} ∩
          {z | ¬ Surjective (fderiv ℝ (pkg.obstructionSlice hT p₁) z)}) := by
      rw [hAdef]
      ext z
      simp only [Set.mem_ofPred_eq]
    rw [hfiber]
    have hUopen : IsOpen {z : pkg.decDom.X₀ | (p₁, z) ∈ V} :=
      hVopen.preimage (by fun_prop)
    have hUC : ∀ z ∈ {z : pkg.decDom.X₀ | (p₁, z) ∈ V},
        ContDiffAt ℝ (k : ℕ∞ω) (pkg.obstructionSlice hT p₁) z := by
      intro z hz
      rw [funext (pkg.obstructionSlice_apply hT p₁), ← hqdef]
      exact ((hVP _ hz).2.1).comp z (contDiffAt_const.prodMk contDiffAt_id)
    exact interior_image_criticalPoints_eq_empty hUopen hUC hkbound
  have himg : f '' (N ∩ {x | ¬ Surjective (fderiv ℝ f x)}) ⊆ Λ '' A := by
    rintro _ ⟨x, ⟨hxN, hxc⟩, rfl⟩
    obtain ⟨c₁, -, -, -, -⟩ := hVP (Φ x) (hNV x hxN)
    refine ⟨((Φ x).1, q (Φ x)), ⟨(Φ x).2, ⟨hNV x hxN, ?_⟩, ?_⟩, ?_⟩
    · exact fun hs ↦ hxc ((hcrit x hxN).2 hs)
    · rw [hqdef]
      exact pkg.obstructionSlice_apply hT (Φ x).1 (Φ x).2
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
  have hWopen : IsOpen {y | y ∈ V ∧ Surjective ((fderiv ℝ q y).comp ι)} := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨hyV, hys⟩
    have hcont : ContinuousAt (fderiv ℝ q) y := ((hVP y hyV).2.1).continuousAt_fderiv hk0
    have hmap : ContinuousAt (fun y' ↦ (fderiv ℝ q y').comp ι) y :=
      hcont.clm_comp continuousAt_const
    filter_upwards [hVopen.mem_nhds hyV,
      hmap (IsOpen.mem_nhds isOpen_setOf_surjective hys)] with y' d₁ d₂
    exact ⟨d₁, d₂⟩
  have hregopen : IsOpen {x | x ∈ N ∧ Surjective (fderiv ℝ f x)} := by
    have heq : {x | x ∈ N ∧ Surjective (fderiv ℝ f x)} =
        N ∩ (Φ.source ∩ Φ ⁻¹' {y | y ∈ V ∧ Surjective ((fderiv ℝ q y).comp ι)}) := by
      ext x
      constructor
      · rintro ⟨hxN, hxs⟩
        have h1 : Surjective ((fderiv ℝ q (Φ x)).comp ι) := by
          rw [← hsliceD (Φ x) (hNV x hxN)]
          exact (hcrit x hxN).1 hxs
        exact ⟨hxN, hxN.1, hNV x hxN, h1⟩
      · rintro ⟨hxN, -, -, hs⟩
        have h2 : Surjective (fderiv ℝ (pkg.obstructionSlice hT (Φ x).1) (Φ x).2) := by
          rw [hsliceD (Φ x) (hNV x hxN)]
          exact hs
        exact ⟨hxN, (hcrit x hxN).2 h2⟩
    rw [heq]
    exact hNopen.inter (Φ.isOpen_inter_preimage hWopen)
  -- Smale's local properness, on a closed ball inside `N`.
  obtain ⟨N₂, hN₂, hprop⟩ := hT.exists_mem_nhds_forall_isCompact_inter_preimage
    hFred.isClosed_range hFred.finite_ker hFred.closedComplemented_ker
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
    (Filter.inter_mem (Filter.inter_mem (hNopen.mem_nhds haN) hN₂) hU)
  set N' : Set E := Metric.closedBall a (r / 2) with hN'def
  have hN'sub : N' ⊆ N ∩ N₂ ∩ U := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hN'ball : N' ⊆ N ∩ N₂ := fun z hz ↦ (hN'sub hz).1
  have hN'U : N' ⊆ U := fun z hz ↦ (hN'sub hz).2
  have hN'nhds : N' ∈ 𝓝 a := Metric.closedBall_mem_nhds a (by linarith)
  have hcritclosed : IsClosed (N' ∩ {x | ¬ Surjective (fderiv ℝ f x)}) := by
    have heq : N' ∩ {x | ¬ Surjective (fderiv ℝ f x)} =
        N' ∩ {x | x ∈ N ∧ Surjective (fderiv ℝ f x)}ᶜ := by
      ext x
      refine ⟨fun hx ↦ ⟨hx.1, fun hc ↦ hx.2 hc.2⟩, fun hx ↦ ⟨hx.1, fun hc ↦ hx.2 ⟨?_, hc⟩⟩⟩
      exact (hN'ball hx.1).1
    rw [heq]
    exact Metric.isClosed_closedBall.inter hregopen.isClosed_compl
  -- Restricted to that closed critical locus, `f` has compact preimages of compact sets, so it is
  -- a proper map and its image is closed.
  have hclosedimg : IsClosed (f '' (N' ∩ {x | ¬ Surjective (fderiv ℝ f x)})) := by
    set S : Set E := N' ∩ {x | ¬ Surjective (fderiv ℝ f x)}
    have hcontOn : ContinuousOn f S := fun x hx ↦
      (hfN x (hN'ball hx.1).1).continuousAt.continuousWithinAt
    have hpre : ∀ K : Set F, IsCompact K → IsCompact (S.domRestrict f ⁻¹' K) := by
      intro K hK
      rw [Subtype.isCompact_iff]
      have himg : ((↑) : S → E) '' (S.domRestrict f ⁻¹' K) = S ∩ (N₂ ∩ f ⁻¹' K) := by
        ext z
        constructor
        · rintro ⟨⟨z, hz⟩, hzK, rfl⟩
          exact ⟨hz, (hN'ball hz.1).2, hzK⟩
        · rintro ⟨hz, -, hzK⟩
          exact ⟨⟨z, hz⟩, hzK, rfl⟩
      rw [himg]
      exact (hprop K hK).inter_left hcritclosed
    have himgclosed := (isProperMap_iff_isCompact_preimage.2
      ⟨hcontOn.domRestrict, fun K hK ↦ hpre K hK⟩).isClosedMap _ isClosed_univ
    rwa [Set.image_univ, Set.range_domRestrict] at himgclosed
  refine ⟨N', hN'nhds, hN'U, hclosedimg, ?_⟩
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
    obtain ⟨N, hN, hNU, -, hNnd⟩ := exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints
      (hf x hx) (hFred x hx) (hn x hx) (hU.mem_nhds hx)
    exact ⟨N, hNU, hN, hNnd⟩
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
