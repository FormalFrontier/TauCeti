/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.DiscreteSubset

/-!
# Nondegenerate critical points and Morse functions

A critical point of a real-valued function `f` on a normed space is *nondegenerate* when the
second derivative `fderiv ℝ (fderiv ℝ f) x`, read as a continuous linear map from `E` to its
dual, is a linear homeomorphism. In finite dimensions this is the classical requirement that the
Hessian be a nondegenerate bilinear form; in a Hilbert space it is the condition used in
Palais--Smale Morse theory, and it is genuinely stronger than injectivity of the Hessian.

The point of the definition is that nondegenerate critical points are *isolated*: the differential
`fderiv ℝ f` vanishes at such a point and has invertible derivative there, so the inverse function
theorem makes it locally injective. Consequently a Morse function has a discrete critical locus,
and only finitely many critical points on a compact set. That finiteness is what makes the Morse
chain complex of a compact manifold finitely generated, so it is the first structural input of
Morse homology. Because the first-order term of the chain rule drops out at a critical point, the
second derivative there transforms as a bilinear form, and nondegeneracy is unchanged by a change
of coordinates; this is what will let the notion be read off in any chart.

## Main declarations

* `TauCeti.IsNondegenerateCriticalPt`: the differential vanishes and the second derivative is
  invertible as a map into the dual space.
* `TauCeti.IsMorseOn`: every critical point in a given set is nondegenerate.
* `TauCeti.isNondegenerateCriticalPt_iff`: in finite dimensions, nondegeneracy is the classical
  condition that the Hessian bilinear form have trivial radical.
* `TauCeti.IsNondegenerateCriticalPt.eventually_fderiv_ne_zero`: a nondegenerate critical point is
  isolated among critical points.
* `TauCeti.IsMorseOn.isDiscrete_setOf_fderiv_eq_zero`: the critical locus of a Morse function is
  discrete.
* `TauCeti.IsMorseOn.finite_setOf_fderiv_eq_zero`: a Morse function has finitely many critical
  points on a compact set.
* `TauCeti.fderiv_fderiv_comp_apply`: at a critical point the second derivative of a composition
  is the pullback of the second derivative along the differential.
* `TauCeti.IsNondegenerateCriticalPt.comp`: nondegeneracy is invariant under a change of
  coordinates with bijective differential.
* `TauCeti.isNondegenerateCriticalPt_quadratic`: the local model. A symmetric invertible bilinear
  form `B` makes `z ↦ B z z` a function with a nondegenerate critical point at the origin.

The second derivative used here is `fderiv ℝ (fderiv ℝ f) x`, which Mathlib also packages as
`bilinearIteratedFDerivTwo` and evaluates through `iteratedFDeriv_two_apply`; its symmetry at a
twice differentiable point is `ContDiffAt.isSymmSndFDerivAt`.

## References

* M. Audin, M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014, Chapter 1.
* [Heegaard Floer homology roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/HeegaardFloer/README.md),
  Lane M, "Morse homology".
-/

public section

open Filter Function Module Set Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → ℝ} {x : E}

/-- A real-valued function is critical at `x` in the sense of Sard's theorem, that is, its
differential at `x` fails to be surjective, exactly when that differential vanishes. -/
theorem not_surjective_fderiv_iff (f : E → ℝ) (x : E) :
    ¬ Surjective (fderiv ℝ f x) ↔ fderiv ℝ f x = 0 := by
  refine ⟨fun h ↦ by_contra fun h0 ↦ h ?_, fun h ↦ ?_⟩
  · exact LinearMap.surjective_iff_ne_zero.2 fun hc ↦
      h0 (ContinuousLinearMap.coe_injective (by simpa using hc))
  · intro hsurj
    obtain ⟨v, hv⟩ := hsurj 1
    rw [h] at hv
    exact one_ne_zero hv.symm

/-- `f` has a **nondegenerate critical point** at `x` when its differential vanishes at `x` and its
second derivative at `x`, viewed as a continuous linear map from `E` to the dual space
`E →L[ℝ] ℝ`, is a linear homeomorphism. -/
structure IsNondegenerateCriticalPt (f : E → ℝ) (x : E) : Prop where
  /-- The differential of `f` vanishes at `x`. -/
  fderiv_eq_zero : fderiv ℝ f x = 0
  /-- The second derivative of `f` at `x` is invertible as a map into the dual space. -/
  isInvertible : (fderiv ℝ (fderiv ℝ f) x).IsInvertible

/-- `f` is a **Morse function on `s`** when every critical point of `f` lying in `s` is
nondegenerate. -/
def IsMorseOn (f : E → ℝ) (s : Set E) : Prop :=
  ∀ ⦃x⦄, x ∈ s → fderiv ℝ f x = 0 → IsNondegenerateCriticalPt f x

/-- At a nondegenerate critical point the Hessian bilinear form has trivial radical. -/
theorem IsNondegenerateCriticalPt.eq_zero_of_fderiv_fderiv_eq_zero
    (h : IsNondegenerateCriticalPt f x) {v : E} (hv : ∀ w, fderiv ℝ (fderiv ℝ f) x v w = 0) :
    v = 0 := by
  obtain ⟨e, he⟩ := h.isInvertible
  have h1 : e v = 0 := by
    rw [← ContinuousLinearEquiv.coe_coe e, he]
    ext w
    exact hv w
  exact e.injective (h1.trans (map_zero e).symm)

/-- In finite dimensions, invertibility of the second derivative is the classical nondegeneracy of
the Hessian: no nonzero vector is annihilated by the Hessian form. -/
theorem isNondegenerateCriticalPt_iff [FiniteDimensional ℝ E] :
    IsNondegenerateCriticalPt f x ↔
      fderiv ℝ f x = 0 ∧ ∀ v : E, (∀ w : E, fderiv ℝ (fderiv ℝ f) x v w = 0) → v = 0 := by
  refine ⟨fun h ↦ ⟨h.fderiv_eq_zero, fun _ hv ↦ h.eq_zero_of_fderiv_fderiv_eq_zero hv⟩,
    fun ⟨h0, hnd⟩ ↦ ⟨h0, ?_⟩⟩
  have hinj : Injective (fderiv ℝ (fderiv ℝ f) x : E →ₗ[ℝ] E →L[ℝ] ℝ) := by
    intro u v huv
    have hsub : fderiv ℝ (fderiv ℝ f) x (u - v) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact huv
    exact sub_eq_zero.1 (hnd (u - v) fun w ↦ by rw [hsub]; rfl)
  have hrank : finrank ℝ E = finrank ℝ (E →L[ℝ] ℝ) := by
    rw [← LinearEquiv.finrank_eq
      (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ)]
    exact Subspace.dual_finrank_eq.symm
  have hbij : Bijective (fderiv ℝ (fderiv ℝ f) x : E →ₗ[ℝ] E →L[ℝ] ℝ) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj⟩
  exact ⟨(LinearEquiv.ofBijective _ hbij).toContinuousLinearEquiv, by ext v; simp⟩

/-- **A nondegenerate critical point is isolated.** Near such a point the differential of `f`
vanishes only at the point itself, because the inverse function theorem makes `fderiv ℝ f` locally
injective there. -/
theorem IsNondegenerateCriticalPt.eventually_fderiv_ne_zero [CompleteSpace E]
    (h : IsNondegenerateCriticalPt f x) (hf : ContDiffAt ℝ 2 f x) :
    ∀ᶠ y in 𝓝[≠] x, fderiv ℝ f y ≠ 0 := by
  obtain ⟨e, he⟩ := h.isInvertible
  have hstrict : HasStrictFDerivAt (fderiv ℝ f) (e : E →L[ℝ] E →L[ℝ] ℝ) x := by
    rw [he]
    exact (ContDiffAt.fderiv_right (m := 1) hf (by norm_num)).hasStrictFDerivAt one_ne_zero
  have hleft := hstrict.eventually_left_inverse
  have hx : hstrict.localInverse _ _ _ (fderiv ℝ f x) = x := hleft.self_of_nhds
  filter_upwards [nhdsWithin_le_nhds hleft, self_mem_nhdsWithin] with y hy hyx h0
  refine hyx ?_
  rw [← hy, h0, ← h.fderiv_eq_zero, hx]
  rfl

/-- The critical locus of a Morse function is discrete. -/
theorem IsMorseOn.isDiscrete_setOf_fderiv_eq_zero [CompleteSpace E] {s : Set E}
    (hf : ∀ x ∈ s, ContDiffAt ℝ 2 f x) (hM : IsMorseOn f s) :
    IsDiscrete {x ∈ s | fderiv ℝ f x = 0} := by
  rw [isDiscrete_iff_nhdsNE]
  rintro y ⟨hys, hy0⟩
  rw [inf_principal_eq_bot]
  filter_upwards [(hM hys hy0).eventually_fderiv_ne_zero (hf y hys)] with z hz
  simpa using fun _ ↦ hz

/-- **A Morse function has finitely many critical points on a compact set.** This is the finiteness
that makes the Morse complex of a compact manifold finitely generated. -/
theorem IsMorseOn.finite_setOf_fderiv_eq_zero [CompleteSpace E] {K : Set E} (hK : IsCompact K)
    (hf : ∀ x ∈ K, ContDiffAt ℝ 2 f x) (hM : IsMorseOn f K) :
    {x ∈ K | fderiv ℝ f x = 0}.Finite := by
  by_contra hinf
  obtain ⟨z, hzK, hz⟩ := (Set.not_finite.1 hinf).exists_accPt_of_subset_isCompact hK
    fun _ hy ↦ hy.1
  have hLne : (𝓝[≠] z ⊓ 𝓟 {x ∈ K | fderiv ℝ f x = 0}).NeBot := hz
  have hmem : {x ∈ K | fderiv ℝ f x = 0} ∈ 𝓝[≠] z ⊓ 𝓟 {x ∈ K | fderiv ℝ f x = 0} :=
    mem_inf_of_right (mem_principal_self _)
  have hcont : ContinuousAt (fderiv ℝ f) z :=
    (ContDiffAt.fderiv_right (m := 1) (hf z hzK) (by norm_num)).continuousAt
  have hle : 𝓝[≠] z ⊓ 𝓟 {x ∈ K | fderiv ℝ f x = 0} ≤ 𝓝 z :=
    inf_le_left.trans nhdsWithin_le_nhds
  have hz0 : fderiv ℝ f z = 0 := by
    refine tendsto_nhds_unique (hcont.tendsto.mono_left hle) ?_
    exact tendsto_const_nhds.congr' <| by filter_upwards [hmem] with y hy using hy.2.symm
  have hne := ((hM hzK hz0).eventually_fderiv_ne_zero (hf z hzK)).filter_mono
    (inf_le_left (b := 𝓟 {x ∈ K | fderiv ℝ f x = 0}))
  refine hLne.ne (eventually_false_iff_eq_bot.1 ?_)
  filter_upwards [hne, hmem] with y hy hy2 using hy hy2.2

/-! ### Change of coordinates

At a critical point the first-order term of the chain rule drops out, so the second derivative
transforms as a bilinear form. This is why the Hessian at a critical point, and hence
nondegeneracy, does not depend on the choice of chart.
-/

/-- **The Hessian at a critical point is a bilinear form pullback.** If `φ b` is a critical point
of `f`, then the second derivative of `f ∘ φ` at `b` is the second derivative of `f` at `φ b`
evaluated on the images of the differential of `φ`. -/
theorem fderiv_fderiv_comp_apply {φ : F → E} {b : F} (hf : ContDiffAt ℝ 2 f (φ b))
    (hφ : ContDiffAt ℝ 2 φ b) (hc : fderiv ℝ f (φ b) = 0) (v w : F) :
    fderiv ℝ (fderiv ℝ (f ∘ φ)) b v w =
      fderiv ℝ (fderiv ℝ f) (φ b) (fderiv ℝ φ b v) (fderiv ℝ φ b w) := by
  have hf1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (φ b)) (φ b) :=
    ((ContDiffAt.fderiv_right (m := 1) hf (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hφ1 : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) b) b :=
    ((ContDiffAt.fderiv_right (m := 1) hφ (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hφ0 : HasFDerivAt φ (fderiv ℝ φ b) b := (hφ.differentiableAt (by norm_num)).hasFDerivAt
  have hA : HasFDerivAt (fun y ↦ fderiv ℝ f (φ y))
      ((fderiv ℝ (fderiv ℝ f) (φ b)).comp (fderiv ℝ φ b)) b := hf1.comp b hφ0
  have hev : ∀ᶠ y in 𝓝 b, fderiv ℝ (f ∘ φ) y = (fderiv ℝ f (φ y)).comp (fderiv ℝ φ y) := by
    have h1 : ∀ᶠ y in 𝓝 b, DifferentiableAt ℝ φ y := by
      filter_upwards [hφ.eventually (by norm_num)] with y hy
        using hy.differentiableAt (by norm_num)
    have h2 : ∀ᶠ y in 𝓝 b, DifferentiableAt ℝ f (φ y) := by
      filter_upwards [hφ.continuousAt.eventually (hf.eventually (by norm_num))] with y hy
        using hy.differentiableAt (by norm_num)
    filter_upwards [h1, h2] with y hy1 hy2 using fderiv_comp (x := y) hy2 hy1
  rw [((hA.clm_comp hφ1).congr_of_eventuallyEq hev).fderiv]
  simp [hc]

/-- **Nondegeneracy of a critical point does not depend on the coordinates.** If the differential
of `φ` at `b` is bijective, a nondegenerate critical point of `f` at `φ b` pulls back to a
nondegenerate critical point of `f ∘ φ` at `b`. -/
theorem IsNondegenerateCriticalPt.comp [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {φ : F → E} {b : F} (h : IsNondegenerateCriticalPt f (φ b)) (hf : ContDiffAt ℝ 2 f (φ b))
    (hφ : ContDiffAt ℝ 2 φ b) (hbij : Bijective (fderiv ℝ φ b)) :
    IsNondegenerateCriticalPt (f ∘ φ) b := by
  rw [isNondegenerateCriticalPt_iff]
  refine ⟨?_, fun v hv ↦ ?_⟩
  · rw [fderiv_comp (x := b) (hf.differentiableAt (by norm_num))
      (hφ.differentiableAt (by norm_num)), h.fderiv_eq_zero]
    simp
  · have hv0 : fderiv ℝ φ b v = 0 := by
      refine h.eq_zero_of_fderiv_fderiv_eq_zero fun u ↦ ?_
      obtain ⟨w, rfl⟩ := hbij.2 u
      rw [← fderiv_fderiv_comp_apply hf hφ h.fderiv_eq_zero v w]
      exact hv w
    exact hbij.1 (by rw [hv0, map_zero])

/-! ### The quadratic model

A nondegenerate critical point looks, to second order, like a nondegenerate quadratic form. The
computations below record that the model itself has a nondegenerate critical point, so the
definition above is not vacuous.
-/

/-- The derivative of the quadratic function attached to a continuous bilinear form. -/
theorem hasFDerivAt_quadratic (B : E →L[ℝ] E →L[ℝ] F) (y : E) :
    HasFDerivAt (fun z ↦ B z z) (B.flip y + B y) y := by
  have hdiag : HasFDerivAt (fun z : E ↦ (z, z))
      ((ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E)) y :=
    (hasFDerivAt_id y).prodMk (hasFDerivAt_id y)
  have h : HasFDerivAt (fun z : E ↦ B z z)
      ((B.isBoundedBilinearMap.deriv (y, y)).comp
        ((ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E))) y :=
    HasFDerivAt.comp (f := fun z : E ↦ (z, z)) y
      (B.isBoundedBilinearMap.hasFDerivAt (y, y)) hdiag
  convert h using 1
  ext v
  simp [add_comm]

/-- The differential of the quadratic function attached to a continuous bilinear form is its
polarization `B.flip + B`. -/
theorem fderiv_quadratic (B : E →L[ℝ] E →L[ℝ] F) (y : E) :
    fderiv ℝ (fun z ↦ B z z) y = B.flip y + B y :=
  (hasFDerivAt_quadratic B y).fderiv

/-- The second derivative of the quadratic function attached to a continuous bilinear form is the
constant `B.flip + B`. -/
theorem fderiv_fderiv_quadratic (B : E →L[ℝ] E →L[ℝ] F) (y : E) :
    fderiv ℝ (fderiv ℝ fun z ↦ B z z) y = B.flip + B := by
  have hEq : (fderiv ℝ fun z ↦ B z z) = fun z ↦ (B.flip + B) z := by
    funext z
    rw [fderiv_quadratic, add_apply]
  rw [hEq]
  exact (B.flip + B).fderiv

/-- **The local model of a nondegenerate critical point.** If `B` is a symmetric continuous
bilinear form on `E` which is invertible as a map into the dual space, then the quadratic function
`z ↦ B z z` has a nondegenerate critical point at the origin. -/
theorem isNondegenerateCriticalPt_quadratic (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ v w, B v w = B w v) (hB : B.IsInvertible) :
    IsNondegenerateCriticalPt (fun z ↦ B z z) 0 := by
  have hflip : B.flip + B = (2 : ℝ) • B := by
    ext v w
    simp [hsymm w v, two_smul]
  refine ⟨by rw [fderiv_quadratic]; simp, ?_⟩
  rw [fderiv_fderiv_quadratic, hflip]
  obtain ⟨e, rfl⟩ := hB
  refine ContinuousLinearMap.IsInvertible.of_inverse
    (g := (2 : ℝ)⁻¹ • (e.symm : (E →L[ℝ] ℝ) →L[ℝ] E)) ?_ ?_ <;> ext v <;> simp [smul_smul]

end TauCeti

end
