/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import TauCeti.Analysis.Calculus.Morse.Basic
public import TauCeti.Analysis.Calculus.ParametricIntegral
public import TauCeti.Analysis.Normed.Algebra.SquareRoot

/-!
# The Morse lemma

Near a nondegenerate critical point a smooth function is, in suitable coordinates, exactly its
Hessian quadratic form.  This file proves that, for a real-valued smooth function on a Banach
space, in the form
`TauCeti.IsNondegenerateCriticalPoint.exists_openPartialHomeomorph`: there is a chart `ψ` at the
critical point `x`, carrying `x` to `0` and smooth in both directions, with

`f y = f x + 2⁻¹ * fderiv ℝ (fderiv ℝ f) x (ψ y) (ψ y)`

on the whole of its source.  Nondegeneracy is the one from
`TauCeti.Analysis.Calculus.Morse.Basic`: the second derivative, read as a map from the space to
its dual, is a linear homeomorphism.  In finite dimensions that is the classical condition that
the Hessian be a nondegenerate bilinear form, so this is the classical Morse lemma; in infinite
dimensions it is the strong nondegeneracy of Morse theory on Banach and Hilbert manifolds, and
the statement is the Morse--Palais lemma.

The proof is Palais's.  Write `f (x + v) - f x - fderiv ℝ f x v = 2⁻¹ * B v v v`, where `B v` is
the **averaged Hessian** `TauCeti.hessianAverage f x v`, the average of the second derivative
along the segment from `x` to `x + v`, weighted so that `B 0` is the Hessian itself.  Then `B` is
a smooth family of symmetric continuous bilinear forms with `B 0` invertible, so
`TauCeti.exists_congruence_of_symmetric_family` produces a smooth family of operators `R v`,
equal to the identity at `v = 0`, with `B v w w' = B 0 (R v w) (R v w')`.  Taking `w = w' = v`
turns the second-order term into the Hessian evaluated at `φ v = R v v`, and `φ` has derivative
the identity at `0`, so it is a chart by the inverse function theorem.

The weight `2 * (1 - t)` is what makes `B 0` the Hessian on the nose.  Iterating the smooth
Hadamard factorisation of `TauCeti.Analysis.Calculus.Hadamard` twice would also produce a smooth
family with `f (x + v) - f x = B v v v` at a critical point, but its value at `0` is then the
derivative of a parametrised integral rather than the Hessian, and it is not symmetric; both are
needed here.

The family `R` is manufactured from a square root: the operator `C v = (B 0)⁻¹ ∘ B v` is close to
the identity for `v` close to `0`, so it has a unique square root there
(`TauCeti.sqrtNearOne`), and that square root is automatically self-adjoint for the pairing
`B 0`, because the adjoint of a square root is a square root of the adjoint and the two are close
to the identity.  Self-adjointness is exactly what turns `R v * R v = C v` into the congruence
identity.

This is Lane M of the analytic Heegaard Floer roadmap, which asks for Morse homology built the
way Floer homology is built.  The Morse lemma is what makes the local model of a Morse function
available: the index of the critical point, the local handle structure, and the local form of the
gradient flow are all read off it.  Everything here is stated for `C^∞` functions, which is the
standing regularity of Morse theory; the refinement giving a `C^k` chart for a `C^{k+2}` function
is not proved.

## Main declarations

* `TauCeti.hessianAverage`: the averaged Hessian along a segment, normalised so that
  `TauCeti.hessianAverage_zero` identifies its value at `0` with the Hessian.
* `TauCeti.map_add_eq_add_hessianAverage`: the second-order Taylor formula it satisfies.
* `TauCeti.exists_congruence_of_symmetric_family`: a smooth family of symmetric continuous
  bilinear forms whose value at `0` is invertible is, near `0`, the congruence of that value by a
  smooth family of operators equal to the identity at `0`.
* `TauCeti.IsNondegenerateCriticalPoint.exists_normalForm`: **the Morse lemma**, in the form of a
  smooth map `φ` fixing `0` with derivative the identity there.
* `TauCeti.IsNondegenerateCriticalPoint.exists_openPartialHomeomorph`: the Morse lemma as a chart
  at the critical point.

## References

* R. S. Palais, *Morse theory on Hilbert manifolds*, Topology **2** (1963), 299--340, Section 2,
  for the proof by an operator square root used here.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, 1963, Lemma 2.2, for the classical
  finite-dimensional statement.
* M. Audin, M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014, Chapter 1.
* [Heegaard Floer homology roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HeegaardFloer/README.md),
  Lane M, "Morse homology".
-/

public section

noncomputable section

open Filter MeasureTheory Topology

open scoped ContDiff

namespace TauCeti

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}

-- `NormedSpace.toIsBoundedSMul` does not fire on an iterated space of continuous linear maps,
-- because the `SMul` instance found there is `ContinuousLinearMap.instSMul` rather than the one
-- coming from the module structure; the two are definitionally equal, and this restatement makes
-- the instance available to `ContDiff.smul` and `Continuous.smul` below.
private theorem isBoundedSMul_clm : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  @NormedSpace.toIsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) _ _ _

section HessianAverage

/-- The **averaged Hessian** of `f` at `x` in the direction `v`: the average of the second
derivative of `f` along the segment from `x` to `x + v`, against the weight `2 * (1 - t)`.  The
weight is normalised so that the value at `v = 0` is the Hessian at `x` itself
(`TauCeti.hessianAverage_zero`), while `TauCeti.map_add_eq_add_hessianAverage` says that
`f (x + v)` differs from its first-order Taylor polynomial by `2⁻¹ * hessianAverage f x v v v`. -/
def hessianAverage (f : E → ℝ) (x v : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  ∫ t in (0 : ℝ)..1, (2 * (1 - t)) • fderiv ℝ (fderiv ℝ f) (x + t • v)

/-- The averaged Hessian as an integral over the compact unit interval, the shape in which the
regularity theorem for parametrised integrals applies to it. -/
theorem hessianAverage_eq_integral_Icc (f : E → ℝ) (x : E) :
    hessianAverage f x = fun v ↦ ∫ t in Set.Icc (0 : ℝ) 1,
      (2 * (1 - t)) • fderiv ℝ (fderiv ℝ f) (x + t • v) := by
  funext v
  rw [hessianAverage, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]

/-- At the basepoint the averaged Hessian is the Hessian: the weight `2 * (1 - t)` has integral
`1` over the unit interval. -/
@[simp]
theorem hessianAverage_zero (f : E → ℝ) (x : E) :
    hessianAverage f x 0 = fderiv ℝ (fderiv ℝ f) x := by
  simp only [hessianAverage, smul_zero, add_zero]
  have hI : (∫ t in (0 : ℝ)..1, 2 * (1 - t)) = 1 := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    norm_num [integral_id]
  refine (intervalIntegral.integral_smul_const (𝕜 := ℝ) (fun t : ℝ ↦ 2 * (1 - t))
    (fderiv ℝ (fderiv ℝ f) x)).trans ?_
  rw [hI, one_smul]

/-- The averaged Hessian of a smooth function depends smoothly on the direction. -/
theorem contDiff_hessianAverage (hf : ContDiff ℝ ∞ f) (x : E) :
    ContDiff ℝ ∞ (hessianAverage f x) := by
  rw [hessianAverage_eq_integral_Icc]
  have hd : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  refine contDiff_integral_Icc_of_contDiff ⊤
    (fun v t ↦ (2 * (1 - t)) • fderiv ℝ (fderiv ℝ f) (x + t • v)) ?_
  have h1 : ContDiff ℝ ∞ fun p : E × ℝ ↦ 2 * (1 - p.2) := by fun_prop
  have h2 : ContDiff ℝ ∞ fun p : E × ℝ ↦ fderiv ℝ (fderiv ℝ f) (x + p.2 • p.1) :=
    hd.comp (by fun_prop)
  have := isBoundedSMul_clm (E := E)
  have key : ContDiff ℝ ∞
      fun p : E × ℝ ↦ (2 * (1 - p.2)) • fderiv ℝ (fderiv ℝ f) (x + p.2 • p.1) := h1.smul h2
  exact key

private theorem continuous_hessianAverage_integrand (hf : ContDiff ℝ ∞ f) (x v : E) :
    Continuous fun t : ℝ ↦ (2 * (1 - t)) • fderiv ℝ (fderiv ℝ f) (x + t • v) := by
  have := isBoundedSMul_clm (E := E)
  have hd : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    ((hf.fderiv_right (m := ∞) (by simp)).fderiv_right (m := 0) (by simp)).continuous
  exact (by fun_prop : Continuous fun t : ℝ ↦ 2 * (1 - t)).smul (hd.comp (by fun_prop))

/-- Evaluating the averaged Hessian on a pair of vectors commutes with the integral. -/
theorem hessianAverage_apply (hf : ContDiff ℝ ∞ f) (x v w w' : E) :
    hessianAverage f x v w w'
      = ∫ t in (0 : ℝ)..1, (2 * (1 - t)) * fderiv ℝ (fderiv ℝ f) (x + t • v) w w' := by
  have h1 := continuous_hessianAverage_integrand hf x v
  have h2 : Continuous fun t : ℝ ↦ ((2 * (1 - t)) • fderiv ℝ (fderiv ℝ f) (x + t • v)) w :=
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) w).continuous.comp h1
  rw [hessianAverage, ContinuousLinearMap.intervalIntegral_apply (h1.intervalIntegrable 0 1) w,
    ContinuousLinearMap.intervalIntegral_apply (h2.intervalIntegrable 0 1) w']
  simp

/-- The averaged Hessian is a symmetric bilinear form, since each second derivative along the
segment is. -/
theorem hessianAverage_symm (hf : ContDiff ℝ ∞ f) (x v w w' : E) :
    hessianAverage f x v w w' = hessianAverage f x v w' w := by
  rw [hessianAverage_apply hf, hessianAverage_apply hf]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [(hf.contDiffAt.isSymmSndFDerivAt (by simp) : IsSymmSndFDerivAt ℝ f (x + t • v)) w w']

/-- **Taylor's formula to second order**, with the remainder written as the averaged Hessian
evaluated twice on the increment. -/
theorem map_add_eq_add_hessianAverage (hf : ContDiff ℝ ∞ f) (x v : E) :
    f (x + v) = f x + fderiv ℝ f x v + (2 : ℝ)⁻¹ * hessianAverage f x v v v := by
  have h := map_add_eq_sum_add_integral_iteratedFDeriv (n := 1) (x := x) (y := v)
    (fun t _ ↦ hf.contDiffAt.of_le (by simp))
  norm_num [Finset.sum_range_succ] at h
  rw [show (1 : ℕ) + 1 = 2 from rfl] at h
  simp only [iteratedFDeriv_two_apply] at h
  rw [h, hessianAverage_apply hf, ← intervalIntegral.integral_const_mul]
  refine congrArg (fun z ↦ f x + fderiv ℝ f x v + z) ?_
  exact intervalIntegral.integral_congr fun t _ ↦ by ring

end HessianAverage

section Congruence

variable [CompleteSpace E]

/-- A smooth family `B` of symmetric continuous bilinear forms on a Banach space whose value at
`0` is invertible is, near `0`, the congruence of that value by a smooth family of continuous
linear operators equal to the identity at `0`: there is `R` with `R 0 = 1` and
`B₀ (R v w) (R v w') = B v w w'`.

This is the linear-algebraic heart of the Morse lemma, and it is where the square root of an
operator close to the identity is used: the comparison operator `C v = B₀⁻¹ ∘ B v` is
self-adjoint for the pairing `B₀`, hence so is its square root `R v`, hence
`B₀ (R v w) (R v w') = B₀ w ((R v * R v) w') = B₀ w (C v w') = B v w w'`. -/
theorem exists_congruence_of_symmetric_family
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} (hB : ContDiff ℝ ∞ B)
    (hsymm : ∀ v w w', B v w w' = B v w' w)
    (B₀ : E ≃L[ℝ] (E →L[ℝ] ℝ)) (hB₀ : (B₀ : E →L[ℝ] E →L[ℝ] ℝ) = B 0) :
    ∃ R : E → (E →L[ℝ] E), R 0 = 1 ∧ ContDiffAt ℝ ∞ R 0 ∧
      ∀ᶠ v in 𝓝 (0 : E), ∀ w w', B₀ (R v w) (R v w') = B v w w' := by
  -- the adjoint of an operator for the pairing given by `B₀`
  set adj : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E (B₀.symm : (E →L[ℝ] ℝ) →L[ℝ] E)).comp
      (((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) (E →L[ℝ] ℝ)).flip
          (B₀ : E →L[ℝ] E →L[ℝ] ℝ)).comp
        ((ContinuousLinearMap.compL ℝ E E ℝ).flip)) with hadjdef
  have adj_spec : ∀ (T : E →L[ℝ] E) (w w' : E), B₀ (adj T w) w' = B₀ w (T w') := by
    intro T w w'
    simp [hadjdef]
  have hdet : ∀ T₁ T₂ : E →L[ℝ] E, (∀ w w', B₀ (T₁ w) w' = B₀ (T₂ w) w') → T₁ = T₂ := by
    intro T₁ T₂ h
    ext w
    refine B₀.injective ?_
    ext w'
    exact h w w'
  have adj_one : adj 1 = 1 := by
    refine hdet _ _ fun w w' ↦ ?_
    rw [adj_spec]
    simp
  have adj_mul : ∀ S T : E →L[ℝ] E, adj (S * T) = adj T * adj S := by
    intro S T
    refine hdet _ _ fun w w' ↦ ?_
    rw [adj_spec, mul_apply_eq_comp, mul_apply_eq_comp, adj_spec, adj_spec]
  have hB₀symm : ∀ w w' : E, B₀ w w' = B₀ w' w := by
    intro w w'
    have h := hsymm 0 w w'
    rw [← hB₀] at h
    simpa using h
  -- the comparison operator `B₀⁻¹ ∘ B v`
  set C : E → (E →L[ℝ] E) := fun v ↦ (B₀.symm : (E →L[ℝ] ℝ) →L[ℝ] E).comp (B v) with hCdef
  have hCapply : ∀ (v w w' : E), B₀ (C v w) w' = B v w w' := by
    intro v w w'
    simp [hCdef]
  have hC0 : C 0 = 1 := by
    refine hdet _ _ fun w w' ↦ ?_
    rw [hCapply, ← hB₀]
    simp
  have hCsmooth : ContDiff ℝ ∞ C := by
    have h := (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E
      (B₀.symm : (E →L[ℝ] ℝ) →L[ℝ] E)).contDiff.comp hB
    exact h
  have hCadj : ∀ v, adj (C v) = C v := by
    intro v
    refine hdet _ _ fun w w' ↦ ?_
    rw [adj_spec, hCapply, hB₀symm, hCapply, hsymm]
  refine ⟨fun v ↦ sqrtNearOne (E →L[ℝ] E) (C v), ?_, ?_, ?_⟩
  · have key : sqrtNearOne (E →L[ℝ] E) (C 0) = 1 := by rw [hC0, sqrtNearOne_one]
    exact key
  · exact (hC0 ▸ contDiffAt_sqrtNearOne).comp 0 hCsmooth.contDiffAt
  · have hten : Filter.Tendsto C (𝓝 (0 : E)) (𝓝 1) :=
      hC0 ▸ hCsmooth.continuous.continuousAt
    have htenR : Filter.Tendsto (fun v ↦ sqrtNearOne (E →L[ℝ] E) (C v)) (𝓝 (0 : E)) (𝓝 1) := by
      simpa [Function.comp_def] using
        (continuousAt_sqrtNearOne (A := E →L[ℝ] E)).tendsto.comp hten
    have htenA : Filter.Tendsto (fun v ↦ adj (sqrtNearOne (E →L[ℝ] E) (C v)))
        (𝓝 (0 : E)) (𝓝 1) := by
      simpa [adj_one, Function.comp_def] using (adj.continuous.tendsto 1).comp htenR
    have e1 := hten.eventually (eventually_mul_self_sqrtNearOne (A := E →L[ℝ] E))
    have e2 := htenA.eventually (eventually_sqrtNearOne_mul_self (A := E →L[ℝ] E))
    filter_upwards [e1, e2] with v h1 h2
    have h3 : adj (sqrtNearOne (E →L[ℝ] E) (C v)) * adj (sqrtNearOne (E →L[ℝ] E) (C v)) = C v := by
      rw [← adj_mul, h1, hCadj]
    have h4 : sqrtNearOne (E →L[ℝ] E) (C v) = adj (sqrtNearOne (E →L[ℝ] E) (C v)) := by
      rw [h3] at h2
      exact h2
    have hself : ∀ w w' : E, B₀ (sqrtNearOne (E →L[ℝ] E) (C v) w) w'
        = B₀ w (sqrtNearOne (E →L[ℝ] E) (C v) w') := by
      intro w w'
      conv_lhs => rw [h4]
      exact adj_spec _ w w'
    intro w w'
    calc B₀ (sqrtNearOne (E →L[ℝ] E) (C v) w) (sqrtNearOne (E →L[ℝ] E) (C v) w')
        = B₀ w (sqrtNearOne (E →L[ℝ] E) (C v) (sqrtNearOne (E →L[ℝ] E) (C v) w')) :=
          hself w _
      _ = B₀ w ((sqrtNearOne (E →L[ℝ] E) (C v) * sqrtNearOne (E →L[ℝ] E) (C v)) w') := by
          rw [mul_apply_eq_comp]
      _ = B₀ w (C v w') := by rw [h1]
      _ = B v w w' := by
          rw [hB₀symm w (C v w'), hCapply v w' w]
          exact hsymm v w' w

end Congruence

section MorseLemma

variable [CompleteSpace E]

/-- **The Morse lemma.** Near a nondegenerate critical point `x` of a smooth function `f` there is
a smooth map `φ`, fixing `0` and with derivative the identity there, in terms of which `f` is
exactly its Hessian quadratic form:
`f (x + v) = f x + 2⁻¹ * fderiv ℝ (fderiv ℝ f) x (φ v) (φ v)` for `v` near `0`.

`TauCeti.IsNondegenerateCriticalPoint.exists_openPartialHomeomorph` repackages this as a chart at
`x`. -/
theorem IsNondegenerateCriticalPoint.exists_normalForm (hf : ContDiff ℝ ∞ f)
    (h : IsNondegenerateCriticalPoint f x) :
    ∃ φ : E → E, φ 0 = 0 ∧ ContDiffAt ℝ ∞ φ 0 ∧
      HasFDerivAt φ (ContinuousLinearMap.id ℝ E) 0 ∧
      ∀ᶠ v in 𝓝 (0 : E),
        f (x + v) = f x + (2 : ℝ)⁻¹ * fderiv ℝ (fderiv ℝ f) x (φ v) (φ v) := by
  obtain ⟨B₀, hB₀⟩ := h.isInvertible
  obtain ⟨R, hR0, hRsmooth, hRspec⟩ :=
    exists_congruence_of_symmetric_family (B := hessianAverage f x) (contDiff_hessianAverage hf x)
      (fun v w w' ↦ hessianAverage_symm hf x v w w') B₀ (by rw [hB₀, hessianAverage_zero])
  refine ⟨fun v ↦ R v v, by simp [hR0], hRsmooth.clm_apply contDiffAt_id, ?_, ?_⟩
  · have hd : HasFDerivAt (fun v ↦ R v v)
        ((R 0).comp (ContinuousLinearMap.id ℝ E) + (fderiv ℝ R 0).flip 0) 0 :=
      ((hRsmooth.differentiableAt (by simp)).hasFDerivAt).clm_apply
        (hasFDerivAt_id (𝕜 := ℝ) (0 : E))
    have he : (R 0).comp (ContinuousLinearMap.id ℝ E) + (fderiv ℝ R 0).flip 0
        = ContinuousLinearMap.id ℝ E := by
      rw [hR0]
      ext w
      simp
    rw [← he]
    exact hd
  · filter_upwards [hRspec] with v hv
    rw [map_add_eq_add_hessianAverage hf, ← hv v v, ← hB₀]
    simp [h.fderiv_eq_zero]

/-- **The Morse lemma, as a chart.** At a nondegenerate critical point `x` of a smooth function
`f` there is a chart `ψ` sending `x` to `0`, smooth in both directions, on whose whole source `f`
is its Hessian quadratic form read in that chart. -/
theorem IsNondegenerateCriticalPoint.exists_openPartialHomeomorph (hf : ContDiff ℝ ∞ f)
    (h : IsNondegenerateCriticalPoint f x) :
    ∃ ψ : OpenPartialHomeomorph E E, x ∈ ψ.source ∧ ψ x = 0 ∧
      ContDiffAt ℝ ∞ ψ x ∧ ContDiffAt ℝ ∞ ψ.symm 0 ∧
      ∀ y ∈ ψ.source, f y = f x + (2 : ℝ)⁻¹ * fderiv ℝ (fderiv ℝ f) x (ψ y) (ψ y) := by
  obtain ⟨φ, hφ0, hφsmooth, hφderiv, hφeq⟩ := h.exists_normalForm hf
  have hsub : HasFDerivAt (fun y : E ↦ y - x) (ContinuousLinearMap.id ℝ E) x := by
    simpa using (hasFDerivAt_id (𝕜 := ℝ) x).sub_const x
  have hΨderiv : HasFDerivAt (φ ∘ fun y : E ↦ y - x)
      (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) x := by
    have hc : HasFDerivAt (φ ∘ fun y : E ↦ y - x)
        ((ContinuousLinearMap.id ℝ E).comp (ContinuousLinearMap.id ℝ E)) x :=
      HasFDerivAt.comp x (by simpa using hφderiv) hsub
    simpa using hc
  have hΨsmooth : ContDiffAt ℝ ∞ (φ ∘ fun y : E ↦ y - x) x :=
    ContDiffAt.comp x (by simpa using hφsmooth) (by fun_prop)
  have hΨx : (φ ∘ fun y : E ↦ y - x) x = 0 := by simp [hφ0]
  have hΨeq : ∀ᶠ y in 𝓝 x, f y = f x + (2 : ℝ)⁻¹ *
      fderiv ℝ (fderiv ℝ f) x ((φ ∘ fun y : E ↦ y - x) y) ((φ ∘ fun y : E ↦ y - x) y) := by
    have hten : Filter.Tendsto (fun y : E ↦ y - x) (𝓝 x) (𝓝 0) := by
      have hc : Continuous (fun y : E ↦ y - x) := by fun_prop
      simpa using hc.tendsto x
    filter_upwards [hten.eventually hφeq] with y hy
    simpa using hy
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.1 hΨeq
  refine ⟨(hΨsmooth.toOpenPartialHomeomorph _ hΨderiv (by simp)).restrOpen U hUopen, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hΨsmooth.mem_toOpenPartialHomeomorph_source hΨderiv (by simp), hxU⟩
  · simpa using hΨx
  · simpa using hΨsmooth
  · have h0 := hΨsmooth.to_localInverse hΨderiv (by simp)
    rw [hΨx] at h0
    exact h0
  · intro y hy
    rw [OpenPartialHomeomorph.restrOpen_source] at hy
    simpa using hUsub hy.2

end MorseLemma

end TauCeti
