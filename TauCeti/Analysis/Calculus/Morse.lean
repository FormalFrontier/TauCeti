/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
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

The point of the definition is that nondegenerate critical points are *isolated*. Neither
`IsNondegenerateCriticalPoint` nor `IsMorseOn` contains any regularity assumption on `f`, so every
statement below carries the regularity it needs as a separate hypothesis: `ContDiffAt ℝ 2 f` at
the critical points, and, for the finiteness statement, continuity of `fderiv ℝ f` on the compact
set. Under those hypotheses a Morse function has a discrete critical locus, and only finitely many
critical points on a compact set. That finiteness is what makes the Morse chain complex of a
compact manifold finitely generated, so it is the first structural input of Morse homology.
Because the first-order term of the chain rule drops out at a critical point, the second
derivative there transforms as a bilinear form, and nondegeneracy is unchanged by a change of
coordinates; this is what will let the notion be read off in any chart.

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
* `TauCeti.fderiv_fderiv_comp_apply_of_fderiv_eq_zero`: at a critical point the second derivative
  of a composition is the pullback of the second derivative along the differential.
* `TauCeti.IsNondegenerateCriticalPoint.comp`: nondegeneracy is invariant under a change of
  coordinates with invertible differential.
* `TauCeti.isNondegenerateCriticalPoint_apply_self`: the local model. A continuous bilinear form
  `B` whose polarization `B.flip + B` is invertible makes `z ↦ B z z` a function with a
  nondegenerate critical point at the origin.

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

/-! ### The second derivative as a derivative

The second derivative `fderiv 𝕜 (fderiv 𝕜 g) x` is the derivative at `x` of the map `fderiv 𝕜 g`.
Every statement below goes through that identification, so it is recorded once here.
-/

section SecondDerivative

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- At a twice continuously differentiable point, `fderiv 𝕜 g` is strictly differentiable, with
derivative the second derivative of `g`. -/
theorem ContDiffAt.hasStrictFDerivAt_fderiv {g : E → F} {x : E} (h : ContDiffAt 𝕜 2 g x) :
    HasStrictFDerivAt (fderiv 𝕜 g) (fderiv 𝕜 (fderiv 𝕜 g) x) x :=
  (h.fderiv_right (m := 1) (by norm_num)).hasStrictFDerivAt one_ne_zero

end SecondDerivative

section Morse

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
nondegenerate. Unlike the classical notion, no regularity of `f` is part of the definition; the
statements that need it take it as a separate hypothesis. -/
def IsMorseOn (f : E → ℝ) (s : Set E) : Prop :=
  ∀ ⦃x⦄, x ∈ s → fderiv ℝ f x = 0 → IsNondegenerateCriticalPoint f x

/-- The introduction and elimination rule for `IsMorseOn`: `f` is Morse on `s` exactly when every
critical point of `f` in `s` is nondegenerate. -/
theorem isMorseOn_iff {s : Set E} :
    IsMorseOn f s ↔ ∀ ⦃x⦄, x ∈ s → fderiv ℝ f x = 0 → IsNondegenerateCriticalPoint f x :=
  Iff.rfl

/-- A function that is Morse on `t` is Morse on any subset of `t`. -/
theorem IsMorseOn.mono {s t : Set E} (hM : IsMorseOn f t) (hst : s ⊆ t) : IsMorseOn f s :=
  fun _ hx ↦ hM (hst hx)

/-- At a nondegenerate critical point the Hessian bilinear form has trivial radical. -/
theorem IsNondegenerateCriticalPoint.eq_zero_of_ortho (h : IsNondegenerateCriticalPoint f x)
    {v : E} (hv : ∀ w, fderiv ℝ (fderiv ℝ f) x v w = 0) : v = 0 := by
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
  refine ⟨fun h ↦ ⟨h.fderiv_eq_zero, fun _ hv ↦ h.eq_zero_of_ortho hv⟩, fun ⟨h0, hnd⟩ ↦ ⟨h0, ?_⟩⟩
  have hinj : Injective (fderiv ℝ (fderiv ℝ f) x : E →ₗ[ℝ] E →L[ℝ] ℝ) :=
    (injective_iff_map_eq_zero _).2 fun v hv ↦ hnd v fun w ↦ by
      simp only [ContinuousLinearMap.coe_coe] at hv
      simp [hv]
  have hrank : finrank ℝ E = finrank ℝ (E →L[ℝ] ℝ) := by
    rw [← LinearEquiv.finrank_eq
      (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ)]
    exact Subspace.dual_finrank_eq.symm
  have hbij : Bijective (fderiv ℝ (fderiv ℝ f) x : E →ₗ[ℝ] E →L[ℝ] ℝ) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj⟩
  exact ⟨(LinearEquiv.ofBijective _ hbij).toContinuousLinearEquiv, by ext v; simp⟩

/-- **A nondegenerate critical point is isolated.** Near such a point the differential of `f`
vanishes only at the point itself. -/
theorem IsNondegenerateCriticalPoint.eventually_fderiv_ne_zero
    (h : IsNondegenerateCriticalPoint f x) (hf : ContDiffAt ℝ 2 f x) :
    ∀ᶠ y in 𝓝[≠] x, fderiv ℝ f y ≠ 0 := by
  obtain ⟨e, he⟩ := h.isInvertible
  have hd : HasFDerivAt (fderiv ℝ f) (e : E →L[ℝ] E →L[ℝ] ℝ) x := by
    rw [he]
    exact (ContDiffAt.hasStrictFDerivAt_fderiv hf).hasFDerivAt
  exact hd.eventually_ne ⟨_, e.antilipschitz⟩

/-- The critical locus of a Morse function is discrete, provided `f` is twice continuously
differentiable at its critical points. -/
theorem IsMorseOn.isDiscrete_setOf_fderiv_eq_zero {s : Set E}
    (hf : ∀ x ∈ s, fderiv ℝ f x = 0 → ContDiffAt ℝ 2 f x) (hM : IsMorseOn f s) :
    IsDiscrete {x ∈ s | fderiv ℝ f x = 0} := by
  rw [isDiscrete_iff_nhdsNE]
  rintro y ⟨hys, hy0⟩
  rw [inf_principal_eq_bot]
  filter_upwards [(hM hys hy0).eventually_fderiv_ne_zero (hf y hys hy0)] with z hz
  simpa using fun _ ↦ hz

/-- **A Morse function has finitely many critical points on a compact set.** This is the finiteness
that makes the Morse complex of a compact manifold finitely generated. -/
theorem IsMorseOn.finite_setOf_fderiv_eq_zero {K : Set E} (hK : IsCompact K)
    (hcont : ContinuousOn (fderiv ℝ f) K)
    (hf : ∀ x ∈ K, fderiv ℝ f x = 0 → ContDiffAt ℝ 2 f x) (hM : IsMorseOn f K) :
    {x ∈ K | fderiv ℝ f x = 0}.Finite := by
  -- Continuity of `fderiv ℝ f` on `K` makes the critical locus a closed subset of `K`.
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
theorem fderiv_fderiv_comp_apply_of_fderiv_eq_zero {φ : F → E} {b : F} (hf : ContDiffAt ℝ 2 f (φ b))
    (hφ : ContDiffAt ℝ 2 φ b) (hc : fderiv ℝ f (φ b) = 0) (v w : F) :
    fderiv ℝ (fderiv ℝ (f ∘ φ)) b v w =
      fderiv ℝ (fderiv ℝ f) (φ b) (fderiv ℝ φ b v) (fderiv ℝ φ b w) := by
  have hf1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (φ b)) (φ b) :=
    (ContDiffAt.hasStrictFDerivAt_fderiv hf).hasFDerivAt
  have hφ1 : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) b) b :=
    (ContDiffAt.hasStrictFDerivAt_fderiv hφ).hasFDerivAt
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
      rw [fderiv_fderiv_comp_apply_of_fderiv_eq_zero hf hφ h.fderiv_eq_zero, ← he]
      simp
    rw [hEq]
    simpa using h.isInvertible

end Morse

/-! ### The quadratic model

A nondegenerate critical point looks, to second order, like a nondegenerate quadratic form. The
computations below record that the model itself has a nondegenerate critical point, so the
definition above is not vacuous.
-/

section Bilinear

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace ContinuousLinearMap

/-- The map `z ↦ B z z` attached to a continuous bilinear map `B` is strictly differentiable, with
derivative the polarization of `B`. -/
theorem hasStrictFDerivAt_apply_self (B : E →L[𝕜] E →L[𝕜] F) (y : E) :
    HasStrictFDerivAt (fun z ↦ B z z) (B.flip y + B y) y := by
  have h : HasStrictFDerivAt (fun z ↦ B z z)
      (B.precompR E y (ContinuousLinearMap.id 𝕜 E) +
        B.precompL E (ContinuousLinearMap.id 𝕜 E) y) y :=
    B.hasStrictFDerivAt_of_bilinear (hasStrictFDerivAt_id y) (hasStrictFDerivAt_id y)
  convert h using 1
  ext v
  simp [add_comm]

/-- The map `z ↦ B z z` attached to a continuous bilinear map `B` is differentiable, with
derivative the polarization of `B`. -/
theorem hasFDerivAt_apply_self (B : E →L[𝕜] E →L[𝕜] F) (y : E) :
    HasFDerivAt (fun z ↦ B z z) (B.flip y + B y) y :=
  (hasStrictFDerivAt_apply_self B y).hasFDerivAt

/-- The differential of `z ↦ B z z` is the polarization `B.flip + B`. -/
@[simp]
theorem fderiv_apply_self (B : E →L[𝕜] E →L[𝕜] F) (y : E) :
    fderiv 𝕜 (fun z ↦ B z z) y = B.flip y + B y :=
  (hasFDerivAt_apply_self B y).fderiv

/-- The second derivative of `z ↦ B z z` is the constant `B.flip + B`. -/
@[simp]
theorem fderiv_fderiv_apply_self (B : E →L[𝕜] E →L[𝕜] F) (y : E) :
    fderiv 𝕜 (fderiv 𝕜 fun z ↦ B z z) y = B.flip + B := by
  have hEq : (fderiv 𝕜 fun z ↦ B z z) = fun z ↦ (B.flip + B) z := by
    funext z
    rw [fderiv_apply_self, add_apply]
  rw [hEq]
  exact (B.flip + B).fderiv

end ContinuousLinearMap

end Bilinear

section Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The local model of a nondegenerate critical point.** If the polarization `B.flip + B` of a
continuous bilinear form `B` on `E` is invertible as a map into the dual space, then the quadratic
function `z ↦ B z z` has a nondegenerate critical point at the origin. -/
theorem isNondegenerateCriticalPoint_apply_self (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : (B.flip + B).IsInvertible) : IsNondegenerateCriticalPoint (fun z ↦ B z z) 0 :=
  ⟨by simp, by rw [ContinuousLinearMap.fderiv_fderiv_apply_self]; exact hB⟩

/-- A symmetric continuous bilinear form `B` on `E` which is invertible as a map into the dual
space makes `z ↦ B z z` a function with a nondegenerate critical point at the origin: its
polarization is then `2 • B`. -/
theorem isNondegenerateCriticalPoint_apply_self_of_flip_eq_self (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : B.flip = B) (hB : B.IsInvertible) :
    IsNondegenerateCriticalPoint (fun z ↦ B z z) 0 := by
  refine isNondegenerateCriticalPoint_apply_self B ?_
  obtain ⟨e, rfl⟩ := hB
  have hflip : (e : E →L[ℝ] E →L[ℝ] ℝ).flip + (e : E →L[ℝ] E →L[ℝ] ℝ) =
      (2 : ℝ) • (e : E →L[ℝ] E →L[ℝ] ℝ) := by
    rw [hsymm]
    exact (two_smul ℝ _).symm
  rw [hflip]
  refine ContinuousLinearMap.IsInvertible.of_inverse
    (g := (2 : ℝ)⁻¹ • (e.symm : (E →L[ℝ] ℝ) →L[ℝ] E)) ?_ ?_ <;> ext v <;> simp [smul_smul]

end Model

end TauCeti

end
