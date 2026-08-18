/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The intermediate strata in Sard's theorem

This file supplies the local dimension-reduction step for the intermediate strata in the
Morse--Sard proof. Suppose the `i`th iterated derivative of a smooth map vanishes at `a`, but the
derivative of order `i + 1` does not. A scalar component of the `i`th derivative then has a nonzero
differential at `a`. Its zero set is a regular hypersurface containing every nearby point where
the `i`th derivative vanishes.

`TauCeti.exists_parametrization_iteratedFDeriv_eq_zero` makes this reduction explicit. It gives a
`C^r` parametrization `θ` from the kernel of a nonzero scalar functional, whose dimension is one
less than that of the source. Locally, the zero set of the `i`th derivative is contained in the
range of `θ`, and `θ` itself lies in a regular scalar level set containing that zero set. This is
the induction-on-source-dimension input for proving that the images of the intermediate strata
`Σ_i \ Σ_{i+1}` are null.

The scalar component is obtained by Hahn--Banach from a nonzero value of the derivative of
`iteratedFDeriv ℝ i f`. The parametrization is Mathlib's implicit function for that scalar
component. This is the second stratification step following the flat-stratum estimate in
`TauCeti.Analysis.Calculus.Sard.FlatStratum`.

## Main result

* `TauCeti.exists_parametrization_iteratedFDeriv_eq_zero`: near a point of
  `Σ_i \ Σ_{i+1}`, the set `Σ_i` is contained in the image of a `C^r` map from a
  codimension-one space.

## References

The reduction is the intermediate-stratum step in the proof of Sard's theorem given in
J. Milnor, *Topology from the Differentiable Viewpoint*, Section 3, and M. Hirsch,
*Differential Topology*, Chapter 3.
-/

public section

open Filter Function Module Set

open scoped ContDiff Topology

namespace TauCeti

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : E → F} {a : E} {i r : ℕ}

/-- **Local hypersurface reduction for an intermediate Sard stratum.** Suppose `f` is `C^{r+i}`
at `a`, with `r > 0`, its `i`th iterated derivative vanishes at `a`, and its `(i+1)`st derivative
does not. Then there are a scalar component `g` of the `i`th derivative, its nonzero derivative
`g'`, and a `C^r` parametrization `θ` from `ker g'` such that:

* every zero of `iteratedFDeriv ℝ i f` is a zero of `g`;
* locally at `a`, every zero of `iteratedFDeriv ℝ i f` lies in the range of `θ`;
* locally at the origin, `θ` lies in the regular level set `g = 0`; and
* `ker g'` has dimension one less than `E`.

In particular, the intermediate stratum where all derivatives through order `i` vanish but the
next does not is locally carried by a smooth map from a strictly lower-dimensional source. -/
theorem exists_parametrization_iteratedFDeriv_eq_zero
    (hf : ContDiffAt ℝ (r + i : ℕ) f a) (hr : r ≠ 0)
    (hi : iteratedFDeriv ℝ i f a = 0)
    (hnext : iteratedFDeriv ℝ (i + 1) f a ≠ 0) :
    ∃ (g : E → ℝ) (g' : E →L[ℝ] ℝ) (θ : ↥g'.ker → E),
      ContDiffAt ℝ r g a ∧
      HasFDerivAt g g' a ∧
      g'.range = ⊤ ∧
      (∀ x, iteratedFDeriv ℝ i f x = 0 → g x = 0) ∧
      θ 0 = a ∧
      ContDiffAt ℝ r θ 0 ∧
      (∀ᶠ z in 𝓝 0, g (θ z) = 0) ∧
      (∀ᶠ x in 𝓝 a, iteratedFDeriv ℝ i f x = 0 → x ∈ range θ) ∧
      finrank ℝ ↥g'.ker + 1 = finrank ℝ E := by
  let instCompleteE : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hr' : (r : ℕ∞ω) ≠ 0 := by exact_mod_cast hr
  let D : E →L[ℝ] E [×i]→L[ℝ] F := fderiv ℝ (iteratedFDeriv ℝ i f) a
  have hD : D ≠ 0 := by
    intro hDzero
    apply hnext
    rw [iteratedFDeriv_succ_eq_comp_left, comp_apply]
    -- The successor derivative is presented through the currying isometry, while `D` names its
    -- uncurried input; spelling out that input lets injectivity of the isometry do the work.
    change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) ↦ E) F).symm D = 0
    rw [← (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (i + 1) ↦ E) F).symm.map_zero]
    exact congrArg _ hDzero
  obtain ⟨v, hv⟩ : ∃ v : E, D v ≠ 0 := by
    by_contra h
    push Not at h
    exact hD (ContinuousLinearMap.ext h)
  obtain ⟨ell, _, hell⟩ := exists_dual_vector ℝ (D v) (norm_ne_zero_iff.mpr hv)
  let g : E → ℝ := fun x ↦ ell (iteratedFDeriv ℝ i f x)
  let g' : E →L[ℝ] ℝ := ell.comp D
  have hg' : g' ≠ 0 := by
    intro hg'zero
    have happly := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) hg'zero
    simp only [g', ContinuousLinearMap.comp_apply, zero_apply] at happly
    exact (norm_ne_zero_iff.mpr hv) (hell.symm.trans happly)
  have hg'_linear : g'.toLinearMap ≠ 0 := by
    intro hzero
    apply hg'
    ext x
    exact LinearMap.congr_fun hzero x
  have hsurj : g'.range = ⊤ := by
    exact Module.Dual.range_eq_top_of_ne_zero hg'_linear
  have hiter : ContDiffAt ℝ r (iteratedFDeriv ℝ i f) a :=
    hf.iteratedFDeriv_right le_rfl
  have hg : ContDiffAt ℝ r g a := ell.contDiff.contDiffAt.comp a hiter
  have hgderiv : HasFDerivAt g g' a := by
    exact ell.hasFDerivAt.comp a (hiter.differentiableAt hr').hasFDerivAt
  have hga : g a = 0 := by simp [g, hi]
  have hstrict : HasStrictFDerivAt g g' a := hg.hasStrictFDerivAt' hgderiv hr'
  let hker : g'.ker.ClosedComplemented :=
    g'.ker_closedComplemented_of_finiteDimensional_range
  let projection : E →L[ℝ] ↥g'.ker := Classical.choose hker
  let phi : ImplicitFunctionData ℝ E ℝ ↥g'.ker :=
    { leftFun := g
      leftDeriv := g'
      rightFun x := projection (x - a)
      rightDeriv := projection
      pt := a
      hasStrictFDerivAt_leftFun := hstrict
      hasStrictFDerivAt_rightFun :=
        projection.hasStrictFDerivAt.comp a ((hasStrictFDerivAt_id a).sub_const a)
      range_leftDeriv := hsurj
      range_rightDeriv := LinearMap.range_eq_of_proj (Classical.choose_spec hker)
      isCompl_ker := LinearMap.isCompl_of_proj (Classical.choose_spec hker) }
  let theta : ↥g'.ker → E :=
    phi.implicitFunction 0
  have hprod : phi.prodFun phi.pt = (0, (0 : ↥g'.ker)) := by
    ext <;> simp [phi, projection, hga]
  have htheta_zero : theta 0 = a := by
    have hleft : phi.leftFun phi.pt = 0 := by simp [phi, hga]
    have hright : phi.rightFun phi.pt = 0 := by simp [phi, projection]
    dsimp only [theta]
    rw [← hleft, ← hright, ImplicitFunctionData.implicitFunction_apply]
    rw [← ImplicitFunctionData.toOpenPartialHomeomorph_apply]
    simpa only [phi] using
      phi.toOpenPartialHomeomorph.left_inv phi.pt_mem_toOpenPartialHomeomorph_source
  have htheta_smooth : ContDiffAt ℝ r theta 0 := by
    have hright : ContDiffAt ℝ r phi.rightFun phi.pt := by
      simp only [phi]
      fun_prop
    have himplicit : ContDiffAt ℝ r phi.implicitFunction.uncurry (phi.prodFun phi.pt) :=
      phi.contDiffAt_implicitFunction (by simpa only [phi] using hg) hright hr'
    have hin : ContDiffAt ℝ r (fun z : ↥g'.ker ↦ ((0 : ℝ), z)) 0 := by fun_prop
    rw [hprod] at himplicit
    have hcomp := himplicit.comp 0 hin
    have heq : phi.implicitFunction.uncurry ∘ (fun z : ↥g'.ker ↦ ((0 : ℝ), z)) =
        phi.implicitFunction 0 := by
      funext z
      rfl
    rw [heq] at hcomp
    exact hcomp
  have htheta_level : ∀ᶠ z in 𝓝 0, g (theta z) = 0 := by
    have hmap := phi.leftFun_implicitFunction
    have htend : Tendsto (fun z : ↥g'.ker ↦ ((0 : ℝ), z)) (𝓝 0)
        (𝓝 (phi.prodFun phi.pt)) := by
      rw [hprod]
      exact continuousAt_const.prodMk continuousAt_id
    have hmap' := htend hmap
    rw [Filter.mem_map] at hmap'
    have hmap'' : ∀ᶠ z : ↥g'.ker in 𝓝 0,
        phi.leftFun (phi.implicitFunction 0 z) = 0 := by
      exact hmap'
    simpa only [theta, phi] using hmap''
  have hzero : ∀ x, iteratedFDeriv ℝ i f x = 0 → g x = 0 := by
    intro x hx
    simp [g, hx]
  have hcover : ∀ᶠ x in 𝓝 a, iteratedFDeriv ℝ i f x = 0 → x ∈ range theta := by
    filter_upwards [phi.implicitFunction_apply_image] with x hx hxi
    refine ⟨phi.rightFun x, ?_⟩
    dsimp only [theta]
    rw [← hzero x hxi]
    simpa only [phi] using hx
  have hfinrank : finrank ℝ ↥g'.ker + 1 = finrank ℝ E := by
    exact Module.Dual.finrank_ker_add_one_of_ne_zero hg'_linear
  exact ⟨g, g', theta, hg, hgderiv, hsurj, hzero, htheta_zero, htheta_smooth,
    htheta_level, hcover, hfinrank⟩

end TauCeti

end
