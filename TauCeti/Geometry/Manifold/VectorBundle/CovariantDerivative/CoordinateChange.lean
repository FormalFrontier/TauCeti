/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Coordinate changes for Christoffel maps

This file proves the transformation law for the model-space Christoffel map of a covariant
derivative on the tangent bundle.  The law is stated for independent vector and direction
arguments, so its diagonal specialization is available for the geodesic spray.

## Main results

* `TauCeti.Manifold.christoffelMap_coordChange`: the Christoffel transformation law under a
  change of tangent trivialization.

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

namespace TauCeti.Manifold

section CoordinateChange

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type*} (b : Basis ι 𝕜 E)
  {x x₀ y : M}
  {cov : (Π z : M, TangentSpace I z) → (Π z : M, TangentSpace I z →L[𝕜] TangentSpace I z)}

/-- **The Christoffel transformation law.**  The Christoffel map of a covariant derivative on the
tangent bundle, read in the trivialization centred at `x₀` and evaluated at the `x₀`-coordinates
of a tangent vector `V` and direction `U`, is the pushforward by
`tangentCoordChange I x x₀ x` of its value read in the trivialization centred at `x`, less the
derivative of the tangent coordinate change between the two charts along `U` applied to `V`. -/
theorem christoffelMap_coordChange [Fintype ι] [IsManifold I 2 M]
    : haveI : IsManifold I 1 M := IsManifold.of_le (n := 2) one_le_two
      ∀ (_hx₀ : x ∈ (extChartAt I x₀).source) (U V : TangentSpace I x)
        (hcov : IsCovariantDerivativeOn E cov
          (trivializationAt E (TangentSpace I) x₀).baseSet)
        (hcov' : IsCovariantDerivativeOn E cov
          (trivializationAt E (TangentSpace I) x).baseSet),
        christoffelMap b hcov x (tangentCoordChange I x x₀ x V)
            (tangentCoordChange I x x₀ x U)
          = tangentCoordChange I x x₀ x (christoffelMap b hcov' x V U)
            - mvfderiv I (fun z => tangentCoordChange I x x₀ z V) x U := by
  classical
  have hI : IsManifold I 1 M := IsManifold.of_le (n := 2) one_le_two
  intro _hx₀ U V hcov hcov'
  set e₀ := trivializationAt E (TangentSpace I) x₀ with he₀
  set e₁ := trivializationAt E (TangentSpace I) x with he₁
  have hx₀c : x ∈ (chartAt H x₀).source := by
    rw [← OpenPartialHomeomorph.extend_source (f := chartAt H x₀) (I := I)]
    exact _hx₀
  have hx₀' : x ∈ e₀.baseSet := hx₀c
  have hx₁' : x ∈ e₁.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  have hopen₀ : e₀.baseSet ∈ nhds x := e₀.open_baseSet.mem_nhds hx₀'
  have hopen₁ : e₁.baseSet ∈ nhds x := e₁.open_baseSet.mem_nhds hx₁'
  set σ : Π z : M, TangentSpace I z := fun z => e₁.symmL 𝕜 z V with hσdef
  have hσx : σ x = V := by
    simpa only [hσdef, he₁] using (symmL_trivializationAt_self (I := I) x V)
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
    rw [e₀.localFrameCoeff_eq_coeff (b := b) hz₀,
      ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) e₀ hz₀]
    rw [← Basis.coord_apply]
    simp only [hσdef]
    rw [continuousLinearMapAt_symmL_coordChange (I := I) (x := x) (x₀ := x₀) (y := z)
      hz₁ hz₀ V]
  have hcoeff₁ (i : ι) : (fun z => e₁.localFrameCoeff I b i z (σ z))
      =ᶠ[nhds x] (fun _ => b.coord i V) := by
    filter_upwards [hopen₁] with z hz
    rw [e₁.localFrameCoeff_eq_coeff (b := b) hz,
      ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) e₁ hz]
    rw [← Basis.coord_apply]
    simp only [hσdef]
    exact congrArg (b.coord i) (e₁.continuousLinearMapAt_symmL (R := 𝕜) hz V)
  -- the family of coordinate changes is differentiable; write its derivative as `A`
  have hcmd : MDifferentiableAt I 𝓘(𝕜, E →L[𝕜] E) (tangentCoordChange I x x₀) x := by
    -- the `n + 1` regularity hypothesis of the polymorphic theorem, read at `n := 1`
    have : IsManifold I (1 + 1) M := inferInstanceAs (IsManifold I 2 M)
    exact (contMDiffAt_tangentCoordChange (I := I) (n := 1) (x := x) (y := x₀)
      _hx₀).mdifferentiableAt one_ne_zero
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
      rw [mvfderiv_apply_eq_mfderiv_apply]
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
      rw [mvfderiv_apply_eq_mfderiv_apply]
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
    simp only [he₀]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
      (I := I) (b₀ := x₀) (b := x) hx₀c]
    rfl
  have hsymmL : ∀ u : E, e₀.symmL 𝕜 x (tangentCoordChange I x x₀ x u) = u := by
    intro u
    rw [← hw u, e₀.symmL_continuousLinearMapAt (R := 𝕜) hx₀' u]
  have hV : e₁.symmL 𝕜 x V = V := hσx
  have hU : e₁.symmL 𝕜 x U = U := by
    simpa only [he₁] using (symmL_trivializationAt_self (I := I) x U)
  have hmap' : e₀.continuousLinearMapAt 𝕜 x (christoffelForm b hcov' x V U)
      = tangentCoordChange I x x₀ x (christoffelMap b hcov' x V U) := by
    have h1 : e₁.symmL 𝕜 x (christoffelMap b hcov' x V U)
        = christoffelForm b hcov' x V U := by
      rw [christoffelMap_apply b hcov' hx₁' (V : E) (U : E),
        e₁.symmL_continuousLinearMapAt (R := 𝕜) hx₁']
      simp only [hV, hU]
    rw [← h1, continuousLinearMapAt_symmL_coordChange (I := I) (x := x) (x₀ := x₀) (y := x)
      (mem_chart_source H x) hx₀c (christoffelMap b hcov' x V U)]
  have hfinal : e₀.continuousLinearMapAt 𝕜 x (christoffelForm b hcov x V U)
      + A U = e₀.continuousLinearMapAt 𝕜 x (christoffelForm b hcov' x V U) := by
    have h2 : e₀.continuousLinearMapAt 𝕜 x ((e₀.symmL 𝕜 x ∘SL A) U) = A U :=
      e₀.continuousLinearMapAt_symmL (R := 𝕜) hx₀' (A U)
    rw [hform, sub_apply, map_sub, h2]
    abel
  calc christoffelMap b hcov x (tangentCoordChange I x x₀ x V)
        (tangentCoordChange I x x₀ x U) =
      e₀.continuousLinearMapAt 𝕜 x (christoffelForm b hcov x V U) := by
        have hAV := hsymmL (V : E)
        have hAU := hsymmL (U : E)
        rw [christoffelMap_apply b hcov hx₀', hAV, hAU]
    _ = tangentCoordChange I x x₀ x (christoffelMap b hcov' x V U)
        - mvfderiv I (fun z => tangentCoordChange I x x₀ z V) x U := by
        rw [← hmap', ← hA]
        exact eq_sub_iff_add_eq.mpr hfinal

end CoordinateChange

end TauCeti.Manifold
