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
Hessian be a nondegenerate bilinear form; in infinite dimensions it is the standard strong
nondegeneracy condition of Morse theory on Banach and Hilbert spaces, and it is genuinely stronger
than injectivity of the Hessian. It is unrelated to the Palais--Smale condition, which is not a
condition at a critical point at all but a separate global compactness hypothesis, asking that
every sequence along which `f` is bounded and `fderiv ℝ f` tends to `0` have a convergent
subsequence.

The point of the definition is that nondegenerate critical points are *isolated*: the differential
`fderiv ℝ f` vanishes at such a point and has invertible derivative there, so the inverse function
theorem makes it locally injective. Consequently a Morse function has a discrete critical locus,
and only finitely many critical points on a compact set. That finiteness is what makes the Morse
chain complex of a compact manifold finitely generated, so it is the first structural input of
Morse homology. Because the first-order term of the chain rule drops out at a critical point, the
second derivative there transforms as a bilinear form, and nondegeneracy is unchanged by a change
of coordinates; this is what will let the notion be read off in any chart.

## Main declarations

* `TauCeti.IsNondegenerateCriticalPoint`: the differential vanishes and the second derivative is
  invertible as a map into the dual space.
* `TauCeti.IsMorseOn`: every critical point in a given set is nondegenerate.
* `TauCeti.isNondegenerateCriticalPoint_iff`: in finite dimensions, nondegeneracy is the classical
  condition that the Hessian bilinear form have trivial radical.
* `TauCeti.IsNondegenerateCriticalPoint.eventually_fderiv_ne_zero`: a nondegenerate critical point
  is isolated among critical points.
* `TauCeti.IsMorseOn.isDiscrete_setOf_fderiv_eq_zero`: the critical locus of a Morse function is
  discrete.
* `TauCeti.IsMorseOn.finite_setOf_fderiv_eq_zero`: a Morse function has finitely many critical
  points on a compact set.
* `TauCeti.fderiv_fderiv_comp_apply`: at a critical point the second derivative of a composition
  is the pullback of the second derivative along the differential.
* `TauCeti.IsNondegenerateCriticalPoint.comp`: nondegeneracy is invariant under a change of
  coordinates with invertible differential.
* `TauCeti.isNondegenerateCriticalPoint_quadratic`: the local model. A symmetric invertible
  bilinear form `B` makes `z ↦ B z z` a function with a nondegenerate critical point at the origin.

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

/-- `f` has a **nondegenerate critical point** at `x` when its differential vanishes at `x` and its
second derivative at `x`, viewed as a continuous linear map from `E` to the dual space
`E →L[ℝ] ℝ`, is a linear homeomorphism. -/
structure IsNondegenerateCriticalPoint (f : E → ℝ) (x : E) : Prop where
  /-- The differential of `f` vanishes at `x`. -/
  fderiv_eq_zero : fderiv ℝ f x = 0
  /-- The second derivative of `f` at `x` is invertible as a map into the dual space. -/
  isInvertible : (fderiv ℝ (fderiv ℝ f) x).IsInvertible

/-- `f` is a **Morse function on `s`** when every critical point of `f` lying in `s` is
nondegenerate. -/
def IsMorseOn (f : E → ℝ) (s : Set E) : Prop :=
  ∀ ⦃x⦄, x ∈ s → fderiv ℝ f x = 0 → IsNondegenerateCriticalPoint f x

/-- At a nondegenerate critical point the Hessian bilinear form has trivial radical. -/
theorem IsNondegenerateCriticalPoint.eq_zero_of_fderiv_fderiv_eq_zero
    (h : IsNondegenerateCriticalPoint f x) {v : E} (hv : ∀ w, fderiv ℝ (fderiv ℝ f) x v w = 0) :
    v = 0 := by
  obtain ⟨e, he⟩ := h.isInvertible
  have h1 : e v = 0 := by
    rw [← ContinuousLinearEquiv.coe_coe e, he]
    ext w
    exact hv w
  exact e.injective (h1.trans (map_zero e).symm)

/-- In finite dimensions, invertibility of the second derivative is the classical nondegeneracy of
the Hessian: no nonzero vector is annihilated by the Hessian form. -/
theorem isNondegenerateCriticalPoint_iff [FiniteDimensional ℝ E] :
    IsNondegenerateCriticalPoint f x ↔
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
theorem IsNondegenerateCriticalPoint.eventually_fderiv_ne_zero [CompleteSpace E]
    (h : IsNondegenerateCriticalPoint f x) (hf : ContDiffAt ℝ 2 f x) :
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

/-- The critical locus of a Morse function is discrete. Only the regularity of `f` at its critical
points enters, since that is where isolation has to be proved. -/
theorem IsMorseOn.isDiscrete_setOf_fderiv_eq_zero [CompleteSpace E] {s : Set E}
    (hf : ∀ x ∈ s, fderiv ℝ f x = 0 → ContDiffAt ℝ 2 f x) (hM : IsMorseOn f s) :
    IsDiscrete {x ∈ s | fderiv ℝ f x = 0} := by
  rw [isDiscrete_iff_nhdsNE]
  rintro y ⟨hys, hy0⟩
  rw [inf_principal_eq_bot]
  filter_upwards [(hM hys hy0).eventually_fderiv_ne_zero (hf y hys hy0)] with z hz
  simpa using fun _ ↦ hz

/-- **A Morse function has finitely many critical points on a compact set.** This is the finiteness
that makes the Morse complex of a compact manifold finitely generated. Continuity of `fderiv ℝ f`
on `K` closes the critical locus, and second-order regularity at the critical points makes it
discrete. -/
theorem IsMorseOn.finite_setOf_fderiv_eq_zero [CompleteSpace E] {K : Set E} (hK : IsCompact K)
    (hcont : ContinuousOn (fderiv ℝ f) K)
    (hf : ∀ x ∈ K, fderiv ℝ f x = 0 → ContDiffAt ℝ 2 f x) (hM : IsMorseOn f K) :
    {x ∈ K | fderiv ℝ f x = 0}.Finite := by
  have hclosed : IsClosed {x ∈ K | fderiv ℝ f x = 0} := by
    have h := hcont.preimage_isClosed_of_isClosed hK.isClosed (isClosed_singleton (x := 0))
    convert h using 1
    ext y
    simp
  exact (hK.of_isClosed_subset hclosed fun _ hx ↦ hx.1).finite
    (hM.isDiscrete_setOf_fderiv_eq_zero hf)

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
of `φ` at `b` is invertible, a nondegenerate critical point of `f` at `φ b` pulls back to a
nondegenerate critical point of `f ∘ φ` at `b`. -/
theorem IsNondegenerateCriticalPoint.comp {φ : F → E} {b : F}
    (h : IsNondegenerateCriticalPoint f (φ b)) (hf : ContDiffAt ℝ 2 f (φ b))
    (hφ : ContDiffAt ℝ 2 φ b) (hinv : (fderiv ℝ φ b).IsInvertible) :
    IsNondegenerateCriticalPoint (f ∘ φ) b := by
  obtain ⟨e, he⟩ := hinv
  refine ⟨?_, ?_⟩
  · rw [fderiv_comp (x := b) (hf.differentiableAt (by norm_num))
      (hφ.differentiableAt (by norm_num)), h.fderiv_eq_zero]
    simp
  · -- The Hessian pulls back as `ψ ↦ ψ ∘ e` composed with the Hessian composed with `e`, and
    -- each of the three factors is invertible.
    have hEq : fderiv ℝ (fderiv ℝ (f ∘ φ)) b =
        (e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ) : (E →L[ℝ] ℝ) →L[ℝ] F →L[ℝ] ℝ) ∘L
          fderiv ℝ (fderiv ℝ f) (φ b) ∘L (e : F →L[ℝ] E) := by
      ext v w
      rw [fderiv_fderiv_comp_apply hf hφ h.fderiv_eq_zero, ← he]
      simp
    rw [hEq]
    simpa using h.isInvertible

/-! ### The quadratic model

A nondegenerate critical point looks, to second order, like a nondegenerate quadratic form. The
computations below record that the model itself has a nondegenerate critical point, so the
definition above is not vacuous.
-/

/-- The derivative of the quadratic function attached to a continuous bilinear form. -/
theorem hasFDerivAt_quadratic (B : E →L[ℝ] E →L[ℝ] F) (y : E) :
    HasFDerivAt (fun z ↦ B z z) (B.flip y + B y) y := by
  have h : HasFDerivAt (fun z ↦ B z z)
      (B.precompR E y (ContinuousLinearMap.id ℝ E) +
        B.precompL E (ContinuousLinearMap.id ℝ E) y) y :=
    B.hasFDerivAt_of_bilinear (hasFDerivAt_id y) (hasFDerivAt_id y)
  convert h using 1
  ext v
  simp [add_comm]

/-- The differential of the quadratic function attached to a continuous bilinear form is its
polarization `B.flip + B`. -/
@[simp]
theorem fderiv_quadratic (B : E →L[ℝ] E →L[ℝ] F) (y : E) :
    fderiv ℝ (fun z ↦ B z z) y = B.flip y + B y :=
  (hasFDerivAt_quadratic B y).fderiv

/-- The second derivative of the quadratic function attached to a continuous bilinear form is the
constant `B.flip + B`. -/
@[simp]
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
theorem isNondegenerateCriticalPoint_quadratic (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ v w, B v w = B w v) (hB : B.IsInvertible) :
    IsNondegenerateCriticalPoint (fun z ↦ B z z) 0 := by
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
