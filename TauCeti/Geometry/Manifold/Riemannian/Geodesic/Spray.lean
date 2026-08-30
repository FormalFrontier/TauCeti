/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Basic

/-!
# The geodesic spray: the Christoffel transformation law

The geodesic spray of a connection is the vector field `S` on the tangent bundle whose integral
curves are the velocity lifts of geodesics.  At a point `z = ⟨x, v⟩` of the tangent bundle its
value is the pair `(v, -Γ_x (v, v))`, where `Γ_x` is the model-space Christoffel map of the
connection in the tangent-bundle trivialization centred at the base point `x` of `z`: the first
component re-states the velocity, the second encodes the acceleration the connection prescribes.

For this local formula to define a global vector field, the Christoffel map must transform
correctly when the tangent-bundle trivialization, equivalently the tangent-bundle chart, is
changed.  This file proves that transformation law, together with the supporting facts about
tangent-bundle charts and the tangent coordinate changes `tangentCoordChange I x y` between the
charts at two base points.

The main result, `TauCeti.CovariantDerivative.christoffelMap_trans`, compares the Christoffel maps
of a covariant derivative on the tangent bundle read in the trivializations centred at two nearby
points `x₀` and `x`: the map read at `x₀`, applied to the `x₀`-coordinates of a tangent vector `V`
at `x`, equals the `x₀`-coordinates of the value of the map read at `x` on `V`, minus the value at
`V` of the derivative at `x` of the coordinate-change function.  It is proved from the
flat-plus-form decomposition of a covariant derivative in a local frame, by comparing the two
frame decompositions of the covariant derivative of the constant section of the trivialization
centred at `x` with value `V`.

This is the key input for the chart-independence of the local spray formula `(v, -Γ_x (v, v))`.
The geodesic spray itself, its chart formula, its smoothness, and its integral curves are built on
this law in the continuation of the Hopf--Rinow roadmap target "The geodesic spray".

## Main results

* `TauCeti.CovariantDerivative.coe_chartAt_snd`: the second component of the tangent-bundle chart
  at a point, read in the charts of the base and the model space.
* `TauCeti.CovariantDerivative.tangentCoordChange_symm_apply`: composing a tangent coordinate
  change with the inverse one gives the identity.
* `TauCeti.CovariantDerivative.contDiffOn_tangentCoordChange` and
  `TauCeti.CovariantDerivative.contMDiffAt_tangentCoordChange`: smoothness of tangent coordinate
  changes on the intersection of the two chart sources.
* `TauCeti.CovariantDerivative.localFrameCoeff_continuousLinearMapAt` and
  `TauCeti.CovariantDerivative.continuousLinearMapAt_symmL_coordChange`: the frame coefficients of
  a section, and the coordinate change, read through the trivialization maps.
* `TauCeti.CovariantDerivative.christoffelMap_trans`: the Christoffel transformation law under a
  change of trivialization.

## References

* [Geodesics, the exponential map, and the Hopf--Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "The geodesic spray".
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2018, Ch. 4.
-/

public section

open Bundle CovariantDerivative Module Set
open scoped Manifold

noncomputable section

namespace TauCeti.CovariantDerivative

/-! ### Charts of the tangent bundle -/

section TangentChart

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {p q : TangentBundle I M}

/-- The second component of the chart of a tangent bundle at `q`, read at a point with base point
in the chart source: the fiber vector read in the chart at the base point of `q`.  Together with
`TangentBundle.coe_chartAt_fst` this describes the tangent-bundle charts completely. -/
theorem coe_chartAt_snd :
    (chartAt (ModelProd H E) q p).2 =
      tangentCoordChange I p.1 q.1 p.1 (show E from p.2) := by
  have hcomp : chartAt (ModelProd H E) q p =
      (chartAt H q.1).prod (OpenPartialHomeomorph.refl E)
        (trivializationAt E (TangentSpace I) q.1 p) := by
    rw [TangentBundle.chartAt]
    rfl
  have h2 : (trivializationAt E (TangentSpace I) q.1 p).2 =
      tangentCoordChange I p.1 q.1 p.1 (show E from p.2) :=
    rfl
  rw [hcomp, OpenPartialHomeomorph.prod_apply]
  simp only [OpenPartialHomeomorph.refl_apply, h2]
  rfl

/-- Composing a tangent coordinate change with the inverse one gives the identity. -/
theorem tangentCoordChange_symm_apply {x y z : M}
    (h : z ∈ (extChartAt I x).source ∩ (extChartAt I y).source) (v : E) :
    tangentCoordChange I x y z (tangentCoordChange I y x z v) = v :=
  (tangentCoordChange_comp (I := I) (w := y) (x := x) (y := y) (z := z) (v := v)
    (h := ⟨⟨h.2, h.1⟩, h.2⟩)).trans (tangentCoordChange_self h.2)

/-- The tangent coordinate change between the charts at `x` and `y` is `C^1` on the overlap of
the two chart sources, read in the chart at `x`.  This is Mathlib's
`contDiffOn_fderiv_coord_change` for the preferred charts at two points. -/
theorem contDiffOn_tangentCoordChange [IsManifold I 2 M] (x y : M) :
    ContDiffOn 𝕜 1 (fun a : E => tangentCoordChange I x y ((extChartAt I x).symm a))
      (((extChartAt I x).symm ≫ extChartAt I y).source) := by
  have : IsManifold I (1 + 1) M := inferInstanceAs (IsManifold I 2 M)
  refine (contDiffOn_fderiv_coord_change (𝕜 := 𝕜) (n := 1) (I := I) (M := M)
    (achart H x) (achart H y)).congr (fun a ha => ?_)
  have ha2 : a ∈ (extChartAt I x).target := by
    rw [PartialEquiv.trans_source] at ha
    exact ha.1
  rw [tangentCoordChange_def, (extChartAt I x).right_inv ha2]
  rfl

/-- The tangent coordinate change between the charts at `x` and `y` is `C^1` at `x`, as a map of
manifolds into the continuous linear endomorphisms of the model space. -/
theorem contMDiffAt_tangentCoordChange [IsManifold I 2 M] {x y : M}
    (hy : x ∈ (extChartAt I y).source) :
    ContMDiffAt I 𝓘(𝕜, E →L[𝕜] E) 1 (tangentCoordChange I x y) x := by
  rw [contMDiffAt_iff]
  refine ⟨?_, ?_⟩
  · refine (continuousOn_tangentCoordChange (I := I) (𝕜 := 𝕜) x y).continuousAt ?_
    exact Filter.inter_mem (extChartAt_source_mem_nhds (I := I) (x := x))
      ((isOpen_extChartAt_source y).mem_nhds hy)
  · have hmem : extChartAt I x x ∈ ((extChartAt I x).symm ≫ extChartAt I y).source := by
      rw [PartialEquiv.trans_source'', PartialEquiv.symm_symm, PartialEquiv.symm_target]
      exact mem_image_of_mem _ ⟨mem_extChartAt_source x, hy⟩
    have hychart : x ∈ (chartAt H y).source := by
      rw [← OpenPartialHomeomorph.extend_source (f := chartAt H y) (I := I)]
      exact hy
    have hset : ((extChartAt I x).symm ≫ extChartAt I y).source
        ∈ nhdsWithin (extChartAt I x x) (range I) :=
      I.extendCoordChange_source_mem_nhdsWithin' (e := chartAt H x) (e' := chartAt H y)
        (ChartedSpace.mem_chart_source x) hychart
    refine ((contDiffOn_tangentCoordChange (I := I) (𝕜 := 𝕜) x y).contDiffWithinAt
      hmem).mono_of_mem_nhdsWithin hset

end TangentChart

/-! ### The Christoffel transformation law -/

section ChristoffelTrans

open TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  {ι : Type*} [Finite ι] (b : Basis ι 𝕜 E)
  {e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)} [MemTrivializationAtlas e]
  {x x₀ y : M}
  {cov : (Π z : M, TangentSpace I z) → (Π z : M, TangentSpace I z →L[𝕜] TangentSpace I z)}

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
/-- The frame coefficient functionals of a linear trivialization compute the model coordinates. -/
theorem localFrameCoeff_continuousLinearMapAt (i : ι) (hx : x ∈ e.baseSet)
    (v : TangentSpace I x) :
    e.localFrameCoeff I b i x v = b.coord i (e.continuousLinearMapAt 𝕜 x v) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hsum : v = ∑ j, e.localFrameCoeff I b j x v • e.localFrame b j x := by
    have h := e.eq_sum_localFrameCoeff_smul (I := I) (b := b)
      (s := FiberBundle.extend E v) hx
    rw [FiberBundle.extend_apply_self E v] at h
    exact h
  have hclm : e.continuousLinearMapAt 𝕜 x v = ∑ j, e.localFrameCoeff I b j x v • b j := by
    rw [congrArg (e.continuousLinearMapAt 𝕜 x) hsum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, continuousLinearMapAt_localFrame b hx j]
  rw [hclm]
  simp only [map_sum, map_smul]
  rw [Finset.sum_eq_single i]
  · simp [Basis.coord_apply]
  · intro j _ hj
    simp [Basis.coord_apply, Ne.symm hj]
  · simp

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- The reading map of the preferred trivialization centred at `x₀` sends the tangent vector at
`y` whose `x`-coordinates are `u` to its `x₀`-coordinates. -/
theorem continuousLinearMapAt_symmL_coordChange
    (hyx : y ∈ (chartAt H x).source) (hyx₀ : y ∈ (chartAt H x₀).source) (u : E) :
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 y
        ((trivializationAt E (TangentSpace I) x).symmL 𝕜 y u)
      = tangentCoordChange I x x₀ y u := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (I := I) (b₀ := x) (b := y) hyx,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) (b₀ := x₀) (b := y)
      hyx₀]
  simp only [tangentBundleCore_coordChange_achart]
  have hy1 : y ∈ (extChartAt I x).source := by rw [extChartAt_source]; exact hyx
  have hy2 : y ∈ (extChartAt I y).source := by
    rw [extChartAt_source]
    exact mem_chart_source H y
  have hy3 : y ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hyx₀
  exact tangentCoordChange_comp (I := I) (w := x) (x := y) (y := x₀) (z := y) (v := u)
    ⟨⟨hy1, hy2⟩, hy3⟩

/-- **The Christoffel transformation law.**  The Christoffel map of a covariant derivative on the
tangent bundle, read in the trivialization centred at `x₀` and evaluated at the `x₀`-coordinates
of a tangent vector `V` at `x`, is the pushforward by `tangentCoordChange I x x₀ x` of its value
read in the trivialization centred at `x`, less the derivative of the tangent coordinate change
between the two charts along `V`. -/
theorem christoffelMap_trans [Fintype ι] [IsManifold I 2 M] (hx₀ : x ∈ (extChartAt I x₀).source)
    (V : TangentSpace I x)
    (hcov : IsCovariantDerivativeOn E cov (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hcov' : IsCovariantDerivativeOn E cov (trivializationAt E (TangentSpace I) x).baseSet) :
    christoffelMap b hcov x (tangentCoordChange I x x₀ x V) (tangentCoordChange I x x₀ x V)
      = tangentCoordChange I x x₀ x (christoffelMap b hcov' x V V)
        - mvfderiv I (fun z => tangentCoordChange I x x₀ z V) x V := by
  classical
  set e₀ := trivializationAt E (TangentSpace I) x₀ with he₀
  set e₁ := trivializationAt E (TangentSpace I) x with he₁
  have hx₀c : x ∈ (chartAt H x₀).source := by
    rw [← OpenPartialHomeomorph.extend_source (f := chartAt H x₀) (I := I)]
    exact hx₀
  have hx₀' : x ∈ e₀.baseSet := hx₀c
  have hx₁' : x ∈ e₁.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  have hopen₀ : e₀.baseSet ∈ nhds x := e₀.open_baseSet.mem_nhds hx₀'
  have hopen₁ : e₁.baseSet ∈ nhds x := e₁.open_baseSet.mem_nhds hx₁'
  set σ : Π z : M, TangentSpace I z := fun z => e₁.symmL 𝕜 z V with hσdef
  have hσx : σ x = V := by
    change (trivializationAt E (TangentSpace I) x).symmL 𝕜 x V = V
    rw [TangentBundle.symmL_trivializationAt_eq_core (I := I) (b₀ := x) (b := x)
      (mem_chart_source H x)]
    exact (tangentBundleCore I M).coordChange_self (achart H x) x (mem_chart_source H x) V
  have hσ : MDifferentiableAt I I.tangent (T% σ) x := by
    have h1 : ContMDiffAt I (I.prod 𝓘(𝕜, E)) 1 (fun z => TotalSpace.mk' E z (σ z)) x := by
      rw [e₁.contMDiffAt_section_iff hx₁']
      have hc : ContMDiffAt I 𝓘(𝕜, E) 1 (fun _ : M => @id E V) x := contMDiffAt_const
      refine ContMDiffAt.congr_of_eventuallyEq hc ?_
      filter_upwards [hopen₁] with z hz
      simp only [hσdef]
      rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) e₁ hz _]
      exact e₁.continuousLinearMapAt_symmL (R := 𝕜) hz V
    exact h1.mdifferentiableAt one_ne_zero
  -- the frame coefficient functions of `σ`, in both frames, near `x`
  have hcoeff₀ (i : ι) : (fun z => e₀.localFrameCoeff I b i z (σ z))
      =ᶠ[nhds x] (fun z => b.coord i (tangentCoordChange I x x₀ z V)) := by
    filter_upwards [hopen₀, hopen₁] with z hz₀ hz₁
    rw [localFrameCoeff_continuousLinearMapAt b i hz₀ _]
    simp only [hσdef]
    rw [continuousLinearMapAt_symmL_coordChange (I := I) (x := x) (x₀ := x₀) (y := z)
      hz₁ hz₀ V]
  have hcoeff₁ (i : ι) : (fun z => e₁.localFrameCoeff I b i z (σ z))
      =ᶠ[nhds x] (fun _ => b.coord i V) := by
    filter_upwards [hopen₁] with z hz
    rw [localFrameCoeff_continuousLinearMapAt b i hz _]
    simp only [hσdef]
    exact congrArg (b.coord i) (e₁.continuousLinearMapAt_symmL (R := 𝕜) hz V)
  -- the family of coordinate changes is differentiable; write its derivative as `A`
  have hcmd : MDifferentiableAt I 𝓘(𝕜, E →L[𝕜] E) (tangentCoordChange I x x₀) x :=
    (contMDiffAt_tangentCoordChange (I := I) (x := x) (y := x₀) hx₀).mdifferentiableAt
      one_ne_zero
  have hgA : MDifferentiableAt I 𝓘(𝕜, E) (fun z => tangentCoordChange I x x₀ z V) x :=
    MDifferentiableAt.clm_apply hcmd mdifferentiableAt_const
  set A : TangentSpace I x →L[𝕜] E := mvfderiv I (fun z => tangentCoordChange I x x₀ z V) x with hA
  -- the flat derivative of `σ` in the frame at `x₀` is `symmL x ∘ A`
  have hflat₀ : frameCovariantDerivative I b e₀ σ x = (e₀.symmL 𝕜 x).comp A := by
    ext v
    rw [frameCovariantDerivative_apply]
    have hterm : ∀ i : ι, mvfderiv I (LinearMap.piApply (e₀.localFrameCoeff I b i) σ) x v
        = b.coord i (A v) := by
      intro i
      have h1 : HasMFDerivAt I 𝓘(𝕜, E) (fun z => tangentCoordChange I x x₀ z V) x A := by
        rw [hA]; exact hgA.hasMFDerivAt
      have h2 : HasMFDerivAt I 𝓘(𝕜, 𝕜)
          (fun z => b.coord i (tangentCoordChange I x x₀ z V)) x
          ((LinearMap.toContinuousLinearMap (b.coord i)).comp A) := by
        let k : E →L[𝕜] 𝕜 := LinearMap.toContinuousLinearMap (b.coord i)
        exact HasMFDerivAt.comp (x := x) (f := fun z => tangentCoordChange I x x₀ z V)
          (g := k) (g' := k) (ContinuousLinearMap.hasMFDerivAt k) h1
      have h3 := h2.congr_of_eventuallyEq (hcoeff₀ i)
      change (mfderiv I 𝓘(𝕜, 𝕜) (LinearMap.piApply (e₀.localFrameCoeff I b i) σ) x) v
        = b.coord i (A v)
      rw [LinearMap.piApply_apply, h3.mfderiv]
      rfl
    simp only [hterm]
    have hsum : ∑ i, b.coord i (A v) • e₀.localFrame b i x = e₀.symmL 𝕜 x (A v) := by
      have h1 : e₀.symmL 𝕜 x (A v) = e₀.symmL 𝕜 x (∑ i, b.coord i (A v) • b i) := by
        congr 1
        simp [Basis.sum_repr, Basis.coord_apply]
      rw [h1, map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by
        rw [map_smul, symmL_basis_eq_localFrame b hx₀' i]
    rw [hsum]
    rfl
  -- the flat derivative of `σ` in the frame at `x` vanishes: `σ` has constant coefficients there
  have hflat₁ : frameCovariantDerivative I b e₁ σ x = 0 := by
    ext v
    rw [frameCovariantDerivative_apply]
    have hterm : ∀ i : ι, mvfderiv I (LinearMap.piApply (e₁.localFrameCoeff I b i) σ) x v
        = (0 : 𝕜) := by
      intro i
      have h4 := hasMFDerivAt_const (I := I) (I' := 𝓘(𝕜, 𝕜)) (b.coord i V) x
      have h3 := h4.congr_of_eventuallyEq (hcoeff₁ i)
      change (mfderiv I 𝓘(𝕜, 𝕜) (LinearMap.piApply (e₁.localFrameCoeff I b i) σ) x) v
        = (0 : 𝕜)
      rw [LinearMap.piApply_apply, h3.mfderiv]
      rfl
    simp only [hterm, zero_smul, Finset.sum_const_zero, zero_apply]
  -- the two frame decompositions of the covariant derivative of `σ` at `x` agree
  have hp₀ := covariantDerivative_eq_add_christoffelForm b hcov hx₀' hσ
  have hp₁ := covariantDerivative_eq_add_christoffelForm b hcov' hx₁' hσ
  rw [hflat₀, hσx] at hp₀
  rw [hflat₁, hσx] at hp₁
  have hform : christoffelForm b hcov x V
      = christoffelForm b hcov' x V - (e₀.symmL 𝕜 x).comp A := by
    linear_combination (norm := module) (hp₀.symm.trans hp₁)
  -- read both Christoffel forms in the model space
  have hw : ∀ u : E, e₀.continuousLinearMapAt 𝕜 x u = tangentCoordChange I x x₀ x u := by
    intro u
    change (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x u
      = tangentCoordChange I x x₀ x u
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
      (I := I) (b₀ := x₀) (b := x) hx₀c]
    rfl
  have hsymmL : ∀ u : E, e₀.symmL 𝕜 x (tangentCoordChange I x x₀ x u) = u := by
    intro u
    rw [← hw u, e₀.symmL_continuousLinearMapAt (R := 𝕜) hx₀' u]
  have hV : e₁.symmL 𝕜 x V = V := hσx
  have hmap' : e₀.continuousLinearMapAt 𝕜 x (christoffelForm b hcov' x V V)
      = tangentCoordChange I x x₀ x (christoffelMap b hcov' x V V) := by
    have h1 : e₁.symmL 𝕜 x (christoffelMap b hcov' x V V)
        = christoffelForm b hcov' x V V := by
      rw [christoffelMap_apply b hcov' hx₁' (V : E) (V : E),
        e₁.symmL_continuousLinearMapAt (R := 𝕜) hx₁']
      simp only [hV]
    rw [← h1, continuousLinearMapAt_symmL_coordChange (I := I) (x := x) (x₀ := x₀) (y := x)
      (mem_chart_source H x) hx₀c (christoffelMap b hcov' x V V)]
  have hfinal : e₀.continuousLinearMapAt 𝕜 x (christoffelForm b hcov x V V)
      + A V = e₀.continuousLinearMapAt 𝕜 x (christoffelForm b hcov' x V V) := by
    have h2 : e₀.continuousLinearMapAt 𝕜 x ((e₀.symmL 𝕜 x ∘SL A) V) = A V :=
      e₀.continuousLinearMapAt_symmL (R := 𝕜) hx₀' (A V)
    rw [hform, sub_apply, map_sub, h2]
    abel
  calc christoffelMap b hcov x (tangentCoordChange I x x₀ x V) (tangentCoordChange I x x₀ x V)
      = e₀.continuousLinearMapAt 𝕜 x (christoffelForm b hcov x V V) := by
        rw [christoffelMap_apply b hcov hx₀', hsymmL (V : E)]
    _ = tangentCoordChange I x x₀ x (christoffelMap b hcov' x V V)
        - mvfderiv I (fun z => tangentCoordChange I x x₀ z V) x V := by
        rw [← hmap', ← hA]
        exact eq_sub_iff_add_eq.mpr hfinal

end ChristoffelTrans

end TauCeti.CovariantDerivative
